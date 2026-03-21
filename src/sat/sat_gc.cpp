/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_solver.cpp

Abstract:

    SAT solver main class.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/


#include <algorithm>
#include <cstdint>

#include "sat/sat_solver.h"

namespace sat {

    // -----------------------
    //
    // GC
    //
    // -----------------------

    /**
       \brief Sort clause pointer vectors by address (CaDiCaL collect.cpp lines 427-428).
       After GC or defragmentation, sorting by address ensures that subsequent
       linear scans over the clause vectors (e.g., during reduce) follow memory
       layout order, maximizing hardware prefetch benefit.
    */
    void solver::sort_clauses_by_address() {
        auto addr_lt = [](clause const* a, clause const* b) {
            return reinterpret_cast<uintptr_t>(a) < reinterpret_cast<uintptr_t>(b);
        };
        if (m_learned.size() > 1)
            std::sort(m_learned.begin(), m_learned.end(), addr_lt);
        if (m_clauses.size() > 1)
            std::sort(m_clauses.begin(), m_clauses.end(), addr_lt);
    }

    bool solver::should_gc() const {
        return 
            m_conflicts_since_gc > m_gc_threshold &&
            (m_config.m_gc_strategy != GC_DYN_PSM || at_base_lvl());
    }

    void solver::do_gc() {
        if (!should_gc()) return;
        struct gc_profile_guard {
            stopwatch& sw;
            gc_profile_guard(stopwatch& s) : sw(s) { sw.start(); }
            ~gc_profile_guard() { sw.stop(); }
        };
        gc_profile_guard _gpg(m_profile_gc);
        TRACE(sat, tout << m_conflicts_since_gc << " " << m_gc_threshold << "\n";);
        uint64_t gc = m_stats.m_gc_clause;
        m_conflicts_since_gc = 0;
        m_gc_threshold += m_config.m_gc_increment;
        IF_VERBOSE(10, verbose_stream() << "(sat.gc)\n";);
        CASSERT("sat_gc_bug", check_invariant());
        switch (m_config.m_gc_strategy) {
        case GC_GLUE:
            gc_glue();
            break;
        case GC_PSM:
            gc_psm();
            break;
        case GC_GLUE_PSM:
            gc_glue_psm();
            break;
        case GC_PSM_GLUE:
            gc_psm_glue();
            break;
        case GC_DYN_PSM:
            if (!m_assumptions.empty()) {
                gc_glue_psm();
                break;
            }
            if (!at_base_lvl()) 
                return;
            gc_dyn_psm();
            break;
        default:
            UNREACHABLE();
            break;
        }
        if (m_ext) m_ext->gc();
        // CaDiCaL-style: shrink oversized watch lists after GC to reclaim
        // excess capacity from deleted clauses. (CaDiCaL collect.cpp:225)
        shrink_watches();
        if (gc > 0 && should_defrag()) {
            defrag_clauses();
        }
        // CaDiCaL-style: sort clause vectors by pointer address after GC
        // so that subsequent linear scans follow memory layout, maximizing
        // sequential prefetch benefit. (CaDiCaL collect.cpp lines 427-428)
        sort_clauses_by_address();
        CASSERT("sat_gc_bug", check_invariant());
    }

    /**
       \brief Lex on (glue, size)
    */
    struct glue_lt {
        bool operator()(clause const * c1, clause const * c2) const {
            if (c1->glue() < c2->glue()) return true;
            return c1->glue() == c2->glue() && c1->size() < c2->size();
        }
    };

    /**
       \brief Lex on (psm, size)
    */
    struct psm_lt {
        bool operator()(clause const * c1, clause const * c2) const {
            if (c1->psm() < c2->psm()) return true;
            return c1->psm() == c2->psm() && c1->size() < c2->size();
        }
    };

    /**
       \brief Lex on (glue, psm, size)
    */
    struct glue_psm_lt {
        bool operator()(clause const * c1, clause const * c2) const {
            if (c1->glue() < c2->glue()) return true;
            if (c1->glue() > c2->glue()) return false;
            if (c1->psm() < c2->psm()) return true;
            if (c1->psm() > c2->psm()) return false;
            return c1->size() < c2->size();
        }
    };

    /**
       \brief Lex on (psm, glue, size)
    */
    struct psm_glue_lt {
        bool operator()(clause const * c1, clause const * c2) const {
            if (c1->psm() < c2->psm()) return true;
            if (c1->psm() > c2->psm()) return false;
            if (c1->glue() < c2->glue()) return true;
            if (c1->glue() > c2->glue()) return false;
            return c1->size() < c2->size();
        }
    };

    /**
       \brief Partition m_learned with CaDiCaL-style usage-based aging.
       Three-phase partition:
         1. CORE clauses: always kept (indices [0, core_end))
         2. TIER1 with used>0: kept, usage decayed (indices [core_end, protected_end))
            TIER1 with used==0: demoted to TIER2
         3. TIER2 with used>0: kept, usage decayed (indices [protected_end, cand_start))
            TIER2 with used==0: candidates for deletion (indices [cand_start, end))
       Returns the index where deletion candidates start.
    */
    unsigned solver::partition_tier2() {
        unsigned sz = m_learned.size();

        // Pass 1: Age TIER1 clauses. Demote unused ones to TIER2.
        for (unsigned i = 0; i < sz; ++i) {
            clause& c = *(m_learned[i]);
            if (c.is_tier1()) {
                if (c.was_used()) {
                    c.decay_used();
                }
                else {
                    c.set_tier(clause::TIER2);
                }
            }
        }

        // Pass 2: Partition into [protected | candidates].
        // Protected = CORE + TIER1 + used-TIER2.
        // Candidates = unused-TIER2 + unused hyper clauses (any tier).
        // CaDiCaL-style: hyper clauses (from probing) get no grace period --
        // if not used since last reduce, they become candidates regardless of tier.
        unsigned j = 0;
        for (unsigned i = 0; i < sz; ++i) {
            clause& c = *(m_learned[i]);
            bool keep_protected;
            if (c.is_hyper()) {
                // Hyper clauses: protected only if recently used, regardless of tier
                if (c.was_used()) {
                    c.decay_used();
                    keep_protected = true;
                }
                else {
                    keep_protected = false;
                }
            }
            else if (c.is_core() || c.is_tier1()) {
                keep_protected = true;
            }
            else {
                // TIER2: protect if recently used, candidate otherwise
                if (c.was_used()) {
                    c.decay_used();
                    keep_protected = true;
                }
                else {
                    keep_protected = false;
                }
            }
            if (keep_protected) {
                std::swap(m_learned[i], m_learned[j]);
                j++;
            }
        }
        TRACE(sat, tout << "partition_tier2: protected=" << j
              << " candidates=" << (sz - j) << "\n";);
        return j;
    }

    void solver::gc_glue() {
        unsigned cand_start = partition_tier2();
        unsigned cand_sz = m_learned.size() - cand_start;
        if (cand_sz >= 2)
            std::nth_element(m_learned.begin() + cand_start, m_learned.begin() + cand_start + cand_sz/2, m_learned.end(), glue_lt());
        gc_tier2("glue", cand_start);
    }

    void solver::gc_psm() {
        save_psm();
        unsigned cand_start = partition_tier2();
        unsigned cand_sz = m_learned.size() - cand_start;
        if (cand_sz >= 2)
            std::nth_element(m_learned.begin() + cand_start, m_learned.begin() + cand_start + cand_sz/2, m_learned.end(), psm_lt());
        gc_tier2("psm", cand_start);
    }

    void solver::gc_glue_psm() {
        save_psm();
        unsigned cand_start = partition_tier2();
        unsigned cand_sz = m_learned.size() - cand_start;
        if (cand_sz >= 2)
            std::nth_element(m_learned.begin() + cand_start, m_learned.begin() + cand_start + cand_sz/2, m_learned.end(), glue_psm_lt());
        gc_tier2("glue-psm", cand_start);
    }

    void solver::gc_psm_glue() {
        save_psm();
        unsigned cand_start = partition_tier2();
        unsigned cand_sz = m_learned.size() - cand_start;
        if (cand_sz >= 2)
            std::nth_element(m_learned.begin() + cand_start, m_learned.begin() + cand_start + cand_sz/2, m_learned.end(), psm_glue_lt());
        gc_tier2("psm-glue", cand_start);
    }

    /**
       \brief Compute the psm of all learned clauses.
    */
    void solver::save_psm() {
        for (clause* cp : m_learned) {
            cp->set_psm(psm(*cp));
        }
    }

    /**
       \brief GC deletion candidates using lazy two-phase collection.
       Clauses at indices [0, cand_start) are protected (CORE, active TIER1,
       recently-used TIER2). Of the candidate portion [cand_start, end),
       the better half (lower indices after nth_element) is kept, and
       the worse half is marked garbage if can_delete.
       Then collect_garbage batch-flushes all watches and frees memory.
    */
    void solver::gc_tier2(char const * st_name, unsigned cand_start) {
        TRACE(sat, tout << "gc tier2\n";);
        unsigned sz       = m_learned.size();
        unsigned cand_sz  = sz - cand_start;
        unsigned keep     = cand_start + cand_sz / 2;
        unsigned marked   = 0;
        for (unsigned i = keep; i < sz; ++i) {
            clause & c = *(m_learned[i]);
            if (can_delete(c)) {
                mark_garbage(c);
                marked++;
            }
        }
        if (marked > 0)
            collect_garbage();
        unsigned deleted = sz - m_learned.size();
        m_stats.m_gc_clause += deleted;
        IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat-gc :strategy " << st_name
                   << " :candidates " << cand_sz << " :protected " << cand_start
                   << " :deleted " << deleted << ")\n";);
    }

    // Keep gc_half for backward compatibility with gc_dyn_psm path.
    // Uses lazy two-phase collection: mark garbage, then batch flush+free.
    void solver::gc_half(char const * st_name) {
        TRACE(sat, tout << "gc\n";);
        unsigned sz     = m_learned.size();
        unsigned new_sz = sz / 2;
        unsigned marked = 0;
        for (unsigned i = new_sz; i < sz; ++i) {
            clause & c = *(m_learned[i]);
            if (can_delete(c)) {
                mark_garbage(c);
                marked++;
            }
        }
        if (marked > 0)
            collect_garbage();
        unsigned deleted = sz - m_learned.size();
        m_stats.m_gc_clause += deleted;
        IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat-gc :strategy " << st_name << " :deleted " << deleted << ")\n";);
    }

    bool solver::can_delete(clause const & c) const {
        // CORE clauses are never deleted -- unless they are hyper (probing-derived)
        if (c.is_core() && !c.is_hyper())
            return false;
        if (c.on_reinit_stack())
            return false;
        // Check both watched literals: either c[0] or c[1] could be the
        // propagated literal (c[1] is propagated in attach_nary_clause when
        // c[0] is false at attachment time).
        for (unsigned i = 0; i < 2; ++i) {
            literal li = c[i];
            if (value(li) == l_true) {
                justification const& jst = m_justification[li.var()];
                if (jst.is_clause() && cls_allocator().get_clause(jst.get_clause_offset()) == &c)
                    return false;
            }
        }
        return true;
    }

    /**
       \brief Use gc based on dynamic psm. Clauses are initially frozen.

       Uses lazy two-phase collection for active TIER2 deletions:
       mark_garbage in the main loop, then collect_garbage at the end.
       Frozen clause operations (freeze/unfreeze) still use immediate
       detach/attach because frozen clauses must not participate in BCP.
    */
    void solver::gc_dyn_psm() {
        TRACE(sat, tout << "gc\n";);
        SASSERT(at_base_lvl());
        // compute d_tk
        unsigned h = 0;
        unsigned V_tk = 0;
        for (bool_var v = 0; v < num_vars(); ++v) {
            if (m_assigned_since_gc[v]) {
                V_tk++;
                m_assigned_since_gc[v] = false;
            }
            if (m_phase[v] != m_prev_phase[v]) {
                h++;
                m_prev_phase[v] = m_phase[v];
            }
        }
        double d_tk = V_tk == 0 ? static_cast<double>(num_vars() + 1) : static_cast<double>(h)/static_cast<double>(V_tk);
        if (d_tk < m_min_d_tk)
            m_min_d_tk = d_tk;
        TRACE(sat_frozen, tout << "m_min_d_tk: " << m_min_d_tk << "\n";);
        unsigned frozen    = 0;
        unsigned deleted   = 0;
        unsigned activated = 0;
        unsigned marked    = 0;
        // Buffer for garbage-marked clause pointers. These are removed from
        // m_learned immediately (via continue) but freed only after the batch
        // watch-list flush at the end.
        clause_vector garbage_buf;
        clause_vector::iterator it  = m_learned.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = m_learned.end();
        for (; it != end; ++it) {
            clause & c = *(*it);
            if (!c.frozen()) {
                // CaDiCaL-style: hyper clauses (from probing) get no grace period.
                // If not used since last reduce, immediately mark for deletion.
                if (c.is_hyper()) {
                    if (c.was_used()) {
                        c.decay_used();
                    }
                    else {
                        mark_garbage(c);
                        garbage_buf.push_back(&c);
                        marked++;
                        deleted++;
                        m_stats.m_gc_clause++;
                        continue;
                    }
                }
                // Active clause: CORE clauses are never deleted or frozen
                else if (c.is_core()) {
                    // keep as-is
                }
                else if (c.is_tier2()) {
                    // TIER2 clauses: aggressively managed with usage-based aging
                    if (c.was_used()) {
                        c.reset_inact_rounds();
                        c.decay_used();
                    }
                    else {
                        c.inc_inact_rounds();
                        if (c.inact_rounds() > m_config.m_gc_k) {
                            // Lazy: mark garbage, save pointer, drop from m_learned.
                            // flush_all_watches + dealloc happens after the loop.
                            mark_garbage(c);
                            garbage_buf.push_back(&c);
                            marked++;
                            deleted++;
                            m_stats.m_gc_clause++;
                            continue;
                        }
                    }
                    if (psm(c) > static_cast<unsigned>(c.size() * m_min_d_tk)) {
                        // move to frozen: requires immediate detach (frozen clause must not
                        // participate in BCP), so this path stays synchronous.
                        TRACE(sat_frozen, tout << "freezing size: " << c.size() << " psm: " << psm(c) << " " << c << "\n";);
                        detach_clause(c);
                        c.reset_inact_rounds();
                        c.freeze();
                        m_num_frozen++;
                        frozen++;
                    }
                }
                else if (c.is_tier1()) {
                    // TIER1 clauses: usage-based aging with demotion to TIER2
                    if (c.was_used()) {
                        c.reset_inact_rounds();
                        c.decay_used();
                    }
                    else {
                        // No recent usage: demote to TIER2
                        c.set_tier(clause::TIER2);
                        c.reset_inact_rounds();
                    }
                }
            }
            else {
                // frozen clause (only TIER2 can be frozen) -- already detached from watches
                clause & c2 = *(*it);
                if (psm(c2) <= static_cast<unsigned>(c2.size() * m_min_d_tk)) {
                    c2.unfreeze();
                    m_num_frozen--;
                    activated++;
                    if (!activate_frozen_clause(c2)) {
                        // clause was satisfied, reduced to a conflict, unit or binary clause.
                        // Already detached (was frozen), just free.
                        del_clause(c2);
                        continue;
                    }
                }
                else {
                    c2.inc_inact_rounds();
                    if (c2.inact_rounds() > m_config.m_gc_k) {
                        // Frozen clause already detached from watches -- just free it.
                        del_clause(c2);
                        m_stats.m_gc_clause++;
                        deleted++;
                        continue;
                    }
                }
            }
            *it2 = *it;
            ++it2;
        }
        m_learned.set_end(it2);
        // Batch-collect: flush watch entries of garbage-marked clauses, then free.
        if (marked > 0) {
            flush_all_watches();
            for (clause* cp : garbage_buf)
                dealloc_clause(cp);
        }
        IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat-gc :d_tk " << d_tk << " :min-d_tk " << m_min_d_tk <<
                   " :frozen " << frozen << " :activated " << activated << " :deleted " << deleted << ")\n";);
    }

    // return true if should keep the clause, and false if we should delete it.
    bool solver::activate_frozen_clause(clause & c) {
        TRACE(sat_gc, tout << "reactivating:\n" << c << "\n";);
        SASSERT(at_base_lvl());
        // do some cleanup
        unsigned sz = c.size();
        unsigned j  = 0;
        for (unsigned i = 0; i < sz; ++i) {
            literal l = c[i];
            switch (value(l)) {
            case l_true:
                return false;
            case l_false:
                break;
            case l_undef:
                if (i != j) {
                    std::swap(c[i], c[j]);
                }
                j++;
                break;
            }
        }
        TRACE(sat, tout << "after cleanup:\n" << mk_lits_pp(j, c.begin()) << "\n";);
        unsigned new_sz = j;
        switch (new_sz) {
        case 0:
            if (m_config.m_drat) m_drat.add();
            set_conflict();
            return false;
        case 1:
            assign_unit(c[0]);
            return false;
        case 2:
            mk_bin_clause(c[0], c[1], true);
            return false;
        default:
            shrink(c, sz, new_sz);
            attach_clause(c);
            return true;
        }
    }

    /**
       \brief Compute phase saving measure for the given clause.
    */
    unsigned solver::psm(clause const & c) const {
        unsigned r  = 0;
        for (literal l : c) {
            if (l.sign() ^ m_phase[l.var()]) {
                r++;
            }
        }
        return r;
    }

    // -------------------------------------------------------
    //
    // CaDiCaL-style lazy two-phase garbage collection
    //
    // Phase 1: mark_garbage -- O(1) per clause, sets flag, handles DRAT.
    // Phase 2: collect_garbage -- batch-flushes ALL watch lists in
    //          O(total_watches), then frees all collectible clauses.
    //
    // -------------------------------------------------------

    /**
       \brief Mark clause as garbage (logically deleted). O(1).
       Handles DRAT proof logging but does NOT touch watch lists.
       The clause remains in the watch lists until collect_garbage
       batch-flushes them.
    */
    void solver::mark_garbage(clause& c) {
        SASSERT(!c.is_garbage());
        if (!c.was_removed() && m_config.m_drat && !m_drat.is_cleaned(c))
            m_drat.del(c);
        c.set_garbage(true);
    }

    /**
       \brief Walk the trail and set m_reason=true on any garbage clause
       currently used as a reason (justification) for an assignment.
       This prevents collect_garbage from freeing clauses that are still
       needed to explain the current partial assignment.
    */
    void solver::protect_reasons() {
        for (literal lit : m_trail) {
            bool_var v = lit.var();
            justification const& jst = m_justification[v];
            if (!jst.is_clause())
                continue;
            clause& c = get_clause(jst.get_clause_offset());
            if (c.is_garbage())
                c.set_reason(true);
        }
    }

    /**
       \brief Clear the reason flag on all protected reason clauses.
       Also clear the garbage flag on those clauses -- they survived GC
       because they were still needed as reasons, so they must be kept
       alive until the next GC cycle re-evaluates them.
    */
    void solver::unprotect_reasons() {
        for (literal lit : m_trail) {
            bool_var v = lit.var();
            justification const& jst = m_justification[v];
            if (!jst.is_clause())
                continue;
            clause& c = get_clause(jst.get_clause_offset());
            if (c.is_reason()) {
                c.set_reason(false);
                // Clause survived this GC round as a reason. Un-mark garbage
                // so mark_garbage's SASSERT(!is_garbage()) won't fire next time.
                if (c.is_garbage())
                    c.set_garbage(false);
            }
        }
    }

    /**
       \brief Single-pass flush of ALL clause watch lists (m_watches).
       Removes watch entries pointing to collectible (garbage && !reason) clauses.
       Binary and ext_constraint entries are always kept.
       This is O(total_watches) -- much cheaper than per-clause erase_clause_watch.
    */
    void solver::flush_all_watches() {
        unsigned nv = num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            for (unsigned sign = 0; sign < 2; ++sign) {
                literal lit(v, sign != 0);
                watch_list& wlist = get_wlist(lit);
                if (wlist.empty())
                    continue;
                watch_list::iterator it = wlist.begin(), end2 = wlist.end(), j = it;
                for (; it != end2; ++it) {
                    if (it->is_clause()) {
                        clause& c = get_clause(it->get_clause_offset());
                        if (c.collectible())
                            continue; // drop this watch entry
                    }
                    *j++ = *it;
                }
                wlist.set_end(j);
            }
        }
    }

    /**
       \brief Shrink watch list capacity after GC (CaDiCaL collect.cpp:225).
       After flushing garbage entries, watch lists may have significant
       excess capacity from deleted clauses. Right-size any list where
       capacity > 2 * size to reclaim memory and reduce cache pollution.
       Uses the swap trick since Z3's vector::shrink only adjusts size,
       not capacity.
    */
    void solver::shrink_watches() {
        for (watch_list& wl : m_watches) {
            unsigned sz = wl.size();
            unsigned cap = wl.capacity();
            if (cap <= 8 || sz * 2 >= cap)
                continue;
            // Build a right-sized copy via push_back (capacity ~1.5*sz),
            // then swap to replace the oversized original.
            watch_list tight;
            for (watched const& w : wl)
                tight.push_back(w);
            wl.swap(tight);
        }
    }

    /**
       \brief Compact a clause vector, freeing all collectible clauses.
       Non-collectible clauses are shifted forward in-place.
    */
    void solver::collect_garbage_clauses(clause_vector& clauses) {
        unsigned j = 0;
        for (unsigned i = 0; i < clauses.size(); ++i) {
            clause& c = *(clauses[i]);
            if (c.collectible()) {
                if (!c.is_learned())
                    m_stats.m_non_learned_generation++;
                if (c.frozen())
                    --m_num_frozen;
                dealloc_clause(&c);
                if (m_searching)
                    m_stats.m_del_clause++;
            }
            else {
                clauses[j++] = clauses[i];
            }
        }
        clauses.shrink(j);
    }

    /**
       \brief Full lazy GC cycle (CaDiCaL-style):
       1. Protect reason clauses from collection.
       2. Batch-flush all watch lists (single pass over m_watches).
       3. Compact m_learned, freeing collectible clauses.
       4. Unprotect reason clauses.
    */
    void solver::collect_garbage() {
        protect_reasons();
        flush_all_watches();
        collect_garbage_clauses(m_learned);
        unprotect_reasons();
    }

    /**
     * Control the size of the reinit-stack.
     * by agressively garbage collecting lemmas that are not asserting.
     */

    void solver::gc_reinit_stack(unsigned num_scopes) {
        return;
    }

    void solver::gc_vars(bool_var max_var) {
        init_visited();
        m_aux_literals.reset();
        auto gc_watch = [&](literal lit) {
            auto& bwl = get_bin_wlist(lit);
            for (auto w : bwl) {
                SASSERT(w.is_binary_clause());
                if (w.get_literal().var() < max_var && !is_visited(w.get_literal())) {
                    m_aux_literals.push_back(w.get_literal());
                    mark_visited(w.get_literal());
                }
            }
            bwl.reset();
            get_wlist(lit).reset();
        };
        for (unsigned v = max_var; v < num_vars(); ++v) {
            gc_watch(literal(v, false));
            gc_watch(literal(v, true));
        }

        for (literal lit : m_aux_literals) {
            auto& bwl2 = get_bin_wlist(~lit);
            unsigned j = 0;
            for (auto w2 : bwl2)
                if (w2.get_literal().var() < max_var)
                    bwl2[j++] = w2;
            bwl2.shrink(j);
        }
        m_aux_literals.reset();

        // Mark clauses containing removed variables as garbage, then
        // batch-flush all watch lists in a single pass (CaDiCaL-style).
        // This replaces per-clause detach_clause which does O(wlist_len)
        // linear scans; the batch flush is O(total_watches) regardless
        // of how many clauses are removed.
        unsigned marked = 0;
        auto mark_clauses = [&](clause_vector& clauses) {
            for (clause* c : clauses) {
                bool should_remove = false;
                for (auto lit : *c)
                    should_remove |= lit.var() >= max_var;
                if (should_remove) {
                    SASSERT(!c->on_reinit_stack());
                    mark_garbage(*c);
                    marked++;
                }
            }
        };
        mark_clauses(m_learned);
        mark_clauses(m_clauses);
        if (marked > 0) {
            flush_all_watches();
            collect_garbage_clauses(m_learned);
            collect_garbage_clauses(m_clauses);
        }

        if (m_ext)
            m_ext->gc_vars(max_var);
        
        unsigned j = 0;
        for (literal lit : m_trail) {
            SASSERT(lvl(lit) == 0);
            if (lit.var() < max_var)
                m_trail[j++] = lit;
        }
        m_trail.shrink(j);
        shrink_vars(max_var);
    }

    // -------------------------------------------------------
    //
    // Variable compaction (CaDiCaL-style)
    //
    // -------------------------------------------------------

    bool solver::should_compact() const {
        if (!at_base_lvl())
            return false;
        if (num_user_scopes() > 0)
            return false;
        if (m_is_probing)
            return false;
        if (m_config.m_drat)
            return false;
        // Don't compact when there are model converter entries.
        // The mc entries store variable indices from the pre-compaction space.
        // After compaction, consumers (sat2goal, inc_sat_solver) would see
        // mixed old/new indices causing corrupt model reconstruction.
        if (!m_mc.empty())
            return false;

        unsigned nv = num_vars();
        if (nv < 200)
            return false;

        // Count inactive variables: eliminated or in free list.
        unsigned inactive = m_free_vars.size();
        for (bool_var v = 0; v < nv; ++v) {
            if (m_eliminated[v])
                inactive++;
        }

        // At least 100 inactive vars AND at least 10% of total.
        return inactive >= 100 && inactive * 10 >= nv;
    }

    /**
     * \brief Compact variables by remapping all active variables to a
     * contiguous range [0, new_num_vars). Eliminates holes left by
     * eliminated and freed variables.
     *
     * PRECONDITIONS:
     *   - at_base_lvl() (decision level 0)
     *   - no user scopes active
     *   - DRAT not active
     *
     * This remaps ALL variable-indexed data structures, clause literals,
     * watch lists, justifications, trail, and the extension layer.
     */
    void solver::compact_vars() {
        SASSERT(at_base_lvl());
        SASSERT(num_user_scopes() == 0);
        SASSERT(!m_config.m_drat);

        unsigned old_num_vars = num_vars();

        // Build variable mapping (old -> new).
        // var_map[old_var] = new_var for active vars, UINT_MAX for inactive.
        unsigned_vector var_map(old_num_vars, UINT_MAX);
        unsigned new_num_vars = 0;

        for (bool_var v = 0; v < old_num_vars; ++v) {
            if (m_eliminated[v])
                continue;
            if (m_free_vars.contains(v))
                continue;
            var_map[v] = new_num_vars++;
        }

        // Build reverse mapping (new_var -> old_var) for model converter.
        m_compact_old_num_vars = old_num_vars;
        m_compact_new_to_old.reset();
        m_compact_new_to_old.resize(new_num_vars, UINT_MAX);
        for (bool_var v = 0; v < old_num_vars; ++v) {
            if (var_map[v] != UINT_MAX)
                m_compact_new_to_old[var_map[v]] = v;
        }

        if (new_num_vars == old_num_vars)
            return;

        IF_VERBOSE(2, verbose_stream() << "(sat.compact :old-vars " << old_num_vars
                   << " :new-vars " << new_num_vars
                   << " :eliminated " << (old_num_vars - new_num_vars)
                   << " :clauses " << m_clauses.size()
                   << " :learned " << m_learned.size()
                   << " :trail " << m_trail.size() << ")\n");

        // Helper: remap a literal using the variable mapping.
        auto map_lit = [&](literal l) -> literal {
            VERIFY(var_map[l.var()] != UINT_MAX);
            return literal(var_map[l.var()], l.sign());
        };

        // Remap literals in all clauses (in-place).
        auto remap_clauses = [&](clause_vector& clauses) {
            for (clause* cp : clauses) {
                clause& c = *cp;
                for (unsigned i = 0; i < c.size(); ++i) {
                    VERIFY(var_map[c[i].var()] != UINT_MAX);
                    c[i] = map_lit(c[i]);
                }
            }
        };
        remap_clauses(m_clauses);
        remap_clauses(m_learned);

        // Remap blocking/binary literals in all watch entries BEFORE
        // we move watch lists to new positions.
        for (unsigned idx = 0; idx < m_watches.size(); ++idx) {
            for (auto& w : m_watches[idx]) {
                if (w.is_binary_clause()) {
                    VERIFY(var_map[w.get_literal().var()] != UINT_MAX);
                    w.set_literal(map_lit(w.get_literal()));
                }
                else if (w.is_clause()) {
                    VERIFY(var_map[w.get_blocked_literal().var()] != UINT_MAX);
                    w.set_blocked_literal(map_lit(w.get_blocked_literal()));
                }
            }
        }
        for (unsigned idx = 0; idx < m_bin_watches.size(); ++idx) {
            for (auto& w : m_bin_watches[idx]) {
                VERIFY(w.is_binary_clause());
                VERIFY(var_map[w.get_literal().var()] != UINT_MAX);
                w.set_literal(map_lit(w.get_literal()));
            }
        }

        // Rebuild watch lists at new literal indices.
        {
            vector<watch_list> new_watches;
            new_watches.resize(2 * new_num_vars);
            for (bool_var v = 0; v < old_num_vars; ++v) {
                unsigned nv = var_map[v];
                if (nv == UINT_MAX) continue;
                for (unsigned sign = 0; sign < 2; ++sign) {
                    literal old_lit(v, sign != 0);
                    literal new_lit(nv, sign != 0);
                    new_watches[new_lit.index()].swap(m_watches[old_lit.index()]);
                }
            }
            m_watches.swap(new_watches);
        }
        {
            vector<watch_list> new_bin_watches;
            new_bin_watches.resize(2 * new_num_vars);
            for (bool_var v = 0; v < old_num_vars; ++v) {
                unsigned nv = var_map[v];
                if (nv == UINT_MAX) continue;
                for (unsigned sign = 0; sign < 2; ++sign) {
                    literal old_lit(v, sign != 0);
                    literal new_lit(nv, sign != 0);
                    new_bin_watches[new_lit.index()].swap(m_bin_watches[old_lit.index()]);
                }
            }
            m_bin_watches.swap(new_bin_watches);
        }

        // Remap variable-indexed arrays: copy arr[old] -> new_arr[new].
        auto remap_var_array = [&](auto& arr) {
            using T = std::remove_reference_t<decltype(arr)>;
            T new_arr;
            new_arr.resize(new_num_vars);
            for (bool_var v = 0; v < old_num_vars; ++v) {
                unsigned nv = var_map[v];
                if (nv == UINT_MAX) continue;
                new_arr[nv] = arr[v];
            }
            arr.swap(new_arr);
        };

        // Remap literal-indexed arrays (index = 2*var + sign).
        auto remap_lit_array = [&](auto& arr) {
            using T = std::remove_reference_t<decltype(arr)>;
            T new_arr;
            new_arr.resize(2 * new_num_vars);
            for (bool_var v = 0; v < old_num_vars; ++v) {
                unsigned nv = var_map[v];
                if (nv == UINT_MAX) continue;
                new_arr[2 * nv]     = arr[2 * v];
                new_arr[2 * nv + 1] = arr[2 * v + 1];
            }
            arr.swap(new_arr);
        };

        remap_lit_array(m_assignment);

        // Special case: justification needs explicit initialization
        // (justification(0) for level-0 default).
        // Z3's vector::reserve acts as resize, so just use resize directly.
        {
            svector<justification> new_just;
            new_just.resize(new_num_vars, justification(0));
            for (bool_var v = 0; v < old_num_vars; ++v) {
                unsigned nv = var_map[v];
                if (nv == UINT_MAX) continue;
                new_just[nv] = m_justification[v];
            }
            m_justification.swap(new_just);
        }

        remap_var_array(m_decision);
        remap_var_array(m_eliminated);
        remap_var_array(m_external);
        remap_var_array(m_var_scope);
        remap_var_array(m_touched);
        remap_var_array(m_activity);
        remap_var_array(m_polarity_belief);
        if (m_config.m_branching_heuristic == BH_ADAM || m_config.m_branching_heuristic == BH_COMBINED) {
            remap_var_array(m_adam_m1);
            remap_var_array(m_adam_m2);
            remap_var_array(m_adam_last_update);
        }
        remap_var_array(m_mark);
        remap_lit_array(m_lit_mark);
        remap_var_array(m_phase);
        remap_var_array(m_best_phase);
        remap_var_array(m_prev_phase);
        remap_var_array(m_target_phase);
        remap_var_array(m_assigned_since_gc);
        remap_var_array(m_last_conflict);
        remap_var_array(m_last_propagation);
        remap_var_array(m_participated);
        remap_var_array(m_canceled);
        remap_var_array(m_reasoned);

        // Remap arrays added by CaDiCaL optimization patches.
        remap_var_array(m_trail_pos);
        remap_var_array(m_poison);
        remap_var_array(m_removable);
        // m_shrinkable is lazily allocated (may be smaller than num_vars).
        // At base level (compact_vars precondition), it should be all-false.
        // Just clear and let it regrow lazily during future conflict analysis.
        m_shrinkable.reset();
        m_shrinkable_vars.reset();

        // Remap justifications that store literal indices.
        for (bool_var nv = 0; nv < new_num_vars; ++nv) {
            justification& j = m_justification[nv];
            if (j.is_binary_clause()) {
                literal old_lit = j.get_literal();
                VERIFY(var_map[old_lit.var()] != UINT_MAX);
                j = justification(j.level(), map_lit(old_lit));
            }
        }

        // Remap the trail.
        {
            unsigned j = 0;
            for (unsigned i = 0; i < m_trail.size(); ++i) {
                literal old_lit = m_trail[i];
                unsigned nv = var_map[old_lit.var()];
                if (nv == UINT_MAX) continue;
                m_trail[j++] = literal(nv, old_lit.sign());
            }
            m_trail.shrink(j);
        }
        m_qhead = m_trail.size();
        m_qhead_binary = m_trail.size();

        // Rebuild m_trail_pos from the remapped trail.
        for (unsigned i = 0; i < new_num_vars; ++i)
            m_trail_pos[i] = UINT_MAX;
        for (unsigned i = 0; i < m_trail.size(); ++i)
            m_trail_pos[m_trail[i].var()] = i;

        // Rebuild the case split queue (VSIDS heap).
        {
            m_case_split_queue.reset();
            for (bool_var nv = 0; nv < new_num_vars; ++nv)
                m_case_split_queue.mk_var_eh(nv);
            // Remove assigned variables from queue.
            for (bool_var nv = 0; nv < new_num_vars; ++nv) {
                if (value(literal(nv, false)) != l_undef)
                    m_case_split_queue.del_var_eh(nv);
            }
        }

        // Rebuild the VMTF queue if dual-mode is enabled.
        if (m_config.m_dual_mode && !m_vmtf_links.empty()) {
            // Collect active variables sorted by their old bump timestamp
            // so we can rebuild the linked list in the correct order.
            svector<std::pair<uint64_t, bool_var>> by_bumped;
            for (bool_var v = 0; v < old_num_vars; ++v) {
                unsigned nv = var_map[v];
                if (nv == UINT_MAX) continue;
                if (v < m_vmtf_bumped.size())
                    by_bumped.push_back({m_vmtf_bumped[v], nv});
            }
            std::sort(by_bumped.begin(), by_bumped.end());

            // Remap bumped timestamps.
            svector<uint64_t> new_bumped;
            new_bumped.resize(new_num_vars, 0);
            for (bool_var v = 0; v < old_num_vars; ++v) {
                unsigned nv = var_map[v];
                if (nv == UINT_MAX || v >= m_vmtf_bumped.size()) continue;
                new_bumped[nv] = m_vmtf_bumped[v];
            }
            m_vmtf_bumped.swap(new_bumped);

            // Rebuild the linked list from scratch in bumped order.
            m_vmtf_links.reset();
            m_vmtf_links.resize(new_num_vars);
            m_vmtf_queue_head = null_bool_var;
            m_vmtf_queue_tail = null_bool_var;
            m_vmtf_search = null_bool_var;
            for (auto& [ts, nv] : by_bumped) {
                vmtf_enqueue(nv);
                if (value(literal(nv, false)) == l_undef)
                    m_vmtf_search = nv;
            }
        }

        // Remap clauses_to_reinit (should be empty at base level).
        {
            unsigned j = 0;
            for (unsigned i = 0; i < m_clauses_to_reinit.size(); ++i) {
                clause_wrapper cw = m_clauses_to_reinit[i];
                if (cw.is_binary()) {
                    literal l1 = cw[0], l2 = cw[1];
                    if (var_map[l1.var()] == UINT_MAX || var_map[l2.var()] == UINT_MAX)
                        continue;
                    m_clauses_to_reinit[j++] = clause_wrapper(map_lit(l1), map_lit(l2));
                }
                else {
                    // Nary clause: literals already remapped in the clause itself.
                    m_clauses_to_reinit[j++] = cw;
                }
            }
            m_clauses_to_reinit.shrink(j);
        }

        // Model converter entries are not remapped during compaction.
        // should_compact() prevents compaction when mc is non-empty,
        // so all entries here remain in the current (only) index space.
        SASSERT(m_mc.empty());

        // Update bookkeeping arrays.
        m_active_vars.reset();
        for (bool_var nv = 0; nv < new_num_vars; ++nv)
            m_active_vars.push_back(nv);
        m_free_vars.reset();
        m_vars_to_free.reset();
        m_vars_to_reinit.reset();

        // Reset probing cache (uses literal indices).
        for (bool_var v = 0; v < new_num_vars; ++v) {
            m_probing.reset_cache(literal(v, true));
            m_probing.reset_cache(literal(v, false));
        }
        m_simplifier.reset_todos();

        // Notify extension about variable remapping.
        if (m_ext) {
            m_ext->compact_vars(var_map.data(), new_num_vars);
        }

        CASSERT("sat_compact", check_invariant());
    }

}
