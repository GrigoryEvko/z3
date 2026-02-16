/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_asymm_branch.cpp

Abstract:

    SAT solver asymmetric branching

Author:

    Leonardo de Moura (leonardo) 2011-05-30.

Revision History:

--*/
#include "sat/sat_asymm_branch.h"
#include "sat/sat_asymm_branch_params.hpp"
#include "sat/sat_solver.h"
#include "sat/sat_big.h"
#include "util/stopwatch.h"
#include "util/trace.h"

namespace sat {

    asymm_branch::asymm_branch(solver & _s, params_ref const & p):
        s(_s),
        m_params(p),
        m_counter(0) {
        updt_params(p);
        reset_statistics();
        m_calls = 0;
        m_touch_index = 0;
    }

    // Jeroslow-Wang top-2 literal occurrence score for vivification scheduling.
    // Clauses with high-occurrence literals are vivified first (more propagation power).
    static int64_t jw_clause_score(clause const& c, svector<int64_t> const& occ) {
        int64_t best1 = 0, best2 = 0;
        for (literal lit : c) {
            int64_t v = occ[lit.index()];
            if (v > best1) { best2 = best1; best1 = v; }
            else if (v > best2) { best2 = v; }
        }
        return best1 + best2;
    }

    struct asymm_branch::report {
        asymm_branch & m_asymm_branch;
        stopwatch      m_watch;
        unsigned       m_elim_literals;
        unsigned       m_elim_learned_literals;
        unsigned       m_tr;
        unsigned       m_prefix_subsumed;
        unsigned       m_vivify_retries;
        unsigned       m_reused_decisions;
        unsigned       m_units;
        report(asymm_branch & a):
            m_asymm_branch(a),
            m_elim_literals(a.m_elim_literals),
            m_elim_learned_literals(a.m_elim_learned_literals),
            m_tr(a.m_tr),
            m_prefix_subsumed(a.m_prefix_subsumed),
            m_vivify_retries(a.m_vivify_retries),
            m_reused_decisions(a.m_reused_decisions),
            m_units(a.s.init_trail_size()) {
            m_watch.start();
        }

        ~report() {
            m_watch.stop();
            IF_VERBOSE(2,
                       unsigned num_learned = (m_asymm_branch.m_elim_learned_literals - m_elim_learned_literals);
                       unsigned num_total = (m_asymm_branch.m_elim_literals - m_elim_literals);
                       unsigned num_units = (m_asymm_branch.s.init_trail_size() - m_units);
                       unsigned elim_lits = (num_total - num_learned);
                       unsigned tr = (m_asymm_branch.m_tr - m_tr);
                       unsigned psub = (m_asymm_branch.m_prefix_subsumed - m_prefix_subsumed);
                       unsigned vret = (m_asymm_branch.m_vivify_retries - m_vivify_retries);
                       unsigned vreuse = (m_asymm_branch.m_reused_decisions - m_reused_decisions);
                       verbose_stream() << " (sat-asymm-branch";
                       if (elim_lits > 0)   verbose_stream() << " :elim-literals " << elim_lits;
                       if (num_learned > 0) verbose_stream() << " :elim-learned-literals " << num_learned;
                       if (num_units > 0)   verbose_stream() << " :units " << num_units;
                       if (tr > 0)          verbose_stream() << " :hte " << tr;
                       if (psub > 0)        verbose_stream() << " :prefix-subsumed " << psub;
                       if (vret > 0)        verbose_stream() << " :vivify-retries " << vret;
                       if (vreuse > 0)      verbose_stream() << " :vivify-reused " << vreuse;
                       verbose_stream() << " :cost " << m_asymm_branch.m_counter;
                       verbose_stream() << mem_stat();
                       verbose_stream() << m_watch << ")\n";);
        }
    };

    void asymm_branch::process_bin(big& big) {
        m_tr += big.reduce_tr(s);
    }

    bool asymm_branch::process(big& big, bool learned) {
        unsigned elim0 = m_elim_literals;
        unsigned eliml0 = m_elim_learned_literals;
        for (unsigned i = 0; i < m_asymm_branch_rounds; ++i) {
            unsigned elim = m_elim_literals + m_tr;
            big.init(s, learned);
            process(&big, s.m_clauses);
            process(&big, s.m_learned);
            process_bin(big);
            s.propagate(false); 
            if (s.m_inconsistent)
                break;
            unsigned num_elim = m_elim_literals + m_tr - elim;
            IF_VERBOSE(4, verbose_stream() << "(sat-asymm-branch-step :elim " << num_elim << ")\n";);
            if (num_elim == 0)
                break;
        }        
        IF_VERBOSE(4, if (m_elim_learned_literals > eliml0) 
                          verbose_stream() << "(sat-asymm-branch :elim " << m_elim_learned_literals - eliml0 << ")\n";);
        return m_elim_literals > elim0;
    }

    bool asymm_branch::process(bool learned) {
        unsigned eliml0 = m_elim_learned_literals;
        unsigned elim = m_elim_literals;
        process(nullptr, s.m_clauses);
        if (learned) process(nullptr, s.m_learned);
        s.propagate(false); 
        IF_VERBOSE(4, if (m_elim_learned_literals > eliml0) 
                          verbose_stream() << "(sat-asymm-branch :elim " << m_elim_learned_literals - eliml0 << ")\n";);
        return m_elim_literals > elim;
    }


    // CaDiCaL-style prefix subsumption (vivify.cpp:372-419).
    // Sort each clause's literals by literal index to get a canonical order,
    // then sort all clauses lexicographically.  A linear scan detects when
    // a shorter clause is a prefix of the immediately following longer one,
    // which means the longer clause is subsumed and can be deleted.
    void asymm_branch::prefix_subsume(clause_vector& clauses) {
        unsigned n = clauses.size();
        if (n < 2) return;

        // Build a parallel array of sorted literal sequences.
        // All sorted literals are concatenated into a flat buffer;
        // offsets[i] and sizes[i] locate clause i's segment.
        svector<unsigned> offsets;
        svector<unsigned> sizes;
        literal_vector flat;

        offsets.resize(n);
        sizes.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            clause& c = *clauses[i];
            offsets[i] = flat.size();
            sizes[i] = c.size();
            for (literal l : c)
                flat.push_back(l);
            std::sort(flat.data() + offsets[i], flat.data() + offsets[i] + sizes[i]);
        }

        // Build an index permutation and sort lexicographically
        // (shorter clauses first when literal prefixes are equal).
        svector<unsigned> perm;
        perm.resize(n);
        for (unsigned i = 0; i < n; ++i) perm[i] = i;

        std::sort(perm.begin(), perm.end(),
            [&](unsigned a, unsigned b) {
                unsigned sa = sizes[a], sb = sizes[b];
                literal const* la = flat.data() + offsets[a];
                literal const* lb = flat.data() + offsets[b];
                unsigned m = std::min(sa, sb);
                for (unsigned k = 0; k < m; ++k) {
                    if (la[k] != lb[k]) return la[k] < lb[k];
                }
                return sa < sb;
            });

        // Linear scan: if prev is a prefix of cur, cur is subsumed.
        // Track deleted indices via bool vector to avoid use-after-free
        // (del_clause frees memory, so clauses[cur] becomes dangling).
        bool_vector deleted;
        deleted.resize(n, false);
        unsigned subsumed = 0;
        unsigned prev = perm[0];
        for (unsigned i = 1; i < n; ++i) {
            unsigned cur = perm[i];
            if (deleted[cur]) continue;
            if (deleted[prev]) { prev = cur; continue; }

            unsigned sp = sizes[prev], sc = sizes[cur];
            if (sc >= sp) {
                literal const* lp = flat.data() + offsets[prev];
                literal const* lc = flat.data() + offsets[cur];
                unsigned k = 0;
                for (; k < sp; ++k) {
                    if (lp[k] != lc[k]) break;
                }
                if (k == sp) {
                    clause& cc = *clauses[cur];
                    s.detach_clause(cc);
                    s.del_clause(cc);
                    deleted[cur] = true;
                    ++subsumed;
                    continue;  // prev can still subsume subsequent clauses
                }
            }
            prev = cur;
        }

        if (subsumed > 0) {
            unsigned j = 0;
            for (unsigned i = 0; i < n; ++i) {
                if (!deleted[i])
                    clauses[j++] = clauses[i];
            }
            clauses.shrink(j);
            m_prefix_subsumed += subsumed;
            IF_VERBOSE(4, verbose_stream() << "(sat-asymm-branch :prefix-subsumed " << subsumed << ")\n";);
        }
    }

    // CaDiCaL-style decision reuse for vivification (vivify.cpp:972-988).
    // Instead of push/pop per clause, maintain a persistent multi-level trail.
    // Consecutive clauses that share a common prefix of negated literals
    // reuse existing decisions, backtracking only to the divergence point.
    // This saves 30-50% of decisions and propagations.
    //
    // Each clause's literals are sorted by JW occurrence (descending),
    // and clauses are sorted lexicographically by their sorted literal
    // sequences so that adjacent clauses share maximal prefixes.
    void asymm_branch::process_with_reuse(clause_vector& clauses, int64_t limit) {
        unsigned n = clauses.size();
        if (n == 0) return;

        // Build sorted literal arrays for each clause.
        // Sort by JW occurrence descending (high-occurrence literals first).
        svector<unsigned> offsets, sizes;
        literal_vector flat;
        offsets.resize(n);
        sizes.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            clause& c = *clauses[i];
            offsets[i] = flat.size();
            sizes[i] = c.size();
            for (literal l : c)
                flat.push_back(l);
            literal* begin = flat.data() + offsets[i];
            literal* end_p = begin + sizes[i];
            std::sort(begin, end_p, [this](literal a, literal b) {
                return m_jw_occ[a.index()] > m_jw_occ[b.index()];
            });
        }

        // Sort clauses lexicographically by their sorted literal sequences.
        svector<unsigned> perm;
        perm.resize(n);
        for (unsigned i = 0; i < n; ++i) perm[i] = i;
        std::sort(perm.begin(), perm.end(),
            [&](unsigned a, unsigned b) {
                unsigned sa = sizes[a], sb = sizes[b];
                literal const* la = flat.data() + offsets[a];
                literal const* lb = flat.data() + offsets[b];
                unsigned m = std::min(sa, sb);
                for (unsigned k = 0; k < m; ++k) {
                    if (la[k] != lb[k]) return la[k].index() < lb[k].index();
                }
                return sa < sb;
            });

        // Process clauses with decision reuse.
        m_decisions.reset();
        SASSERT(s.scope_lvl() == 0);

        for (unsigned pi = 0; pi < n; ++pi) {
            unsigned ci = perm[pi];
            clause& c = *clauses[ci];

            if (s.inconsistent()) break;
            if (m_counter < limit) break;
            if (c.was_removed()) continue;
            if (m_vivified.contains(c.id())) continue;

            s.checkpoint();

            // Check if clause is satisfied at level 0.
            bool satisfied = false;
            for (literal l : c) {
                if (s.value(l) == l_true && s.lvl(l) == 0) {
                    satisfied = true;
                    break;
                }
            }
            if (satisfied) {
                if (s.scope_lvl() > 0) {
                    s.pop(s.scope_lvl());
                    m_decisions.reset();
                }
                s.detach_clause(c);
                s.del_clause(c);
                m_vivified.remove(c.id());
                continue;
            }

            unsigned csz = sizes[ci];
            literal const* sorted = flat.data() + offsets[ci];

            // Find prefix match with current decisions on the trail.
            // m_decisions[k] holds the negated literal decided at scope level k+1.
            // For this clause we want: ~sorted[0], ~sorted[1], ...
            unsigned match_len = 0;
            unsigned cur_depth = m_decisions.size();
            for (unsigned k = 0; k < std::min(cur_depth, csz); ++k) {
                if (m_decisions[k] == ~sorted[k]) {
                    ++match_len;
                } else {
                    break;
                }
            }

            // Backtrack to the divergence point.
            if (cur_depth > match_len) {
                s.pop(cur_depth - match_len);
                m_decisions.shrink(match_len);
            }
            m_reused_decisions += match_len;

            if (s.inconsistent()) break;

            m_counter -= csz;

            // Detach the clause so it cannot self-propagate.
            bool was_frozen = c.frozen();
            if (!was_frozen) s.detach_clause(c);

            // Assign negated literals one per scope level, propagating after each.
            // Track which literal positions (in the sorted order) are "responsible"
            // decisions vs. skipped (already implied or untouched).
            m_to_delete.reset();
            bool found_conflict = false;
            bool found_implied = false;

            for (unsigned k = match_len; k < csz && !found_conflict && !found_implied; ++k) {
                literal lit = sorted[k];
                literal neg = ~lit;

                lbool val = s.value(neg);
                if (val == l_true) {
                    // ~lit already true (lit is false) from earlier BCP.
                    // This literal is redundant -- implied false by prior decisions.
                    // Don't decide, skip it. It won't be in m_decisions.
                    continue;
                }
                if (val == l_false) {
                    // ~lit is false -> lit is true from BCP.
                    // A clause literal is implied true by prior decisions.
                    // All remaining undecided literals are redundant.
                    for (unsigned j = k + 1; j < csz; ++j)
                        m_to_delete.push_back(sorted[j]);
                    found_implied = true;
                    break;
                }

                // l_undef: make a decision.
                if (!is_touched(neg.var())) continue;

                SASSERT(!s.inconsistent());
                SASSERT(s.m_qhead == s.m_trail.size());
                s.push();
                m_decisions.push_back(neg);
                s.assign_scoped(neg);
                s.propagate_core(false);

                if (s.inconsistent()) {
                    found_conflict = true;
                    // Pop the conflicting level to clear inconsistency.
                    s.pop(1);
                    m_decisions.pop_back();
                    // Mark all literals AFTER position k as redundant.
                    for (unsigned j = k + 1; j < csz; ++j)
                        m_to_delete.push_back(sorted[j]);
                    break;
                }

                // Check if any remaining clause literals got implied true.
                for (unsigned j = k + 1; j < csz; ++j) {
                    if (s.value(sorted[j]) == l_true) {
                        // sorted[j] implied true: everything after j is redundant.
                        for (unsigned jj = j + 1; jj < csz; ++jj)
                            m_to_delete.push_back(sorted[jj]);
                        found_implied = true;
                        break;
                    }
                }
            }

            // Also check: any sorted literal whose negation was already on
            // the trail as implied (not decided) before we started? Those
            // literals are redundant in the clause.
            // This handles "implied false" literals that were detected during
            // the prefix-matching phase (they'd already be false from reused
            // decisions' propagation).
            for (unsigned k = 0; k < csz; ++k) {
                literal lit = sorted[k];
                // If lit is false AND it wasn't one of our decisions (i.e.,
                // ~lit wasn't a decision we made but was implied), then lit
                // is implied false and can be removed.
                if (s.value(lit) == l_false) {
                    // Check: is ~lit one of our decisions?
                    bool is_decision = false;
                    for (literal d : m_decisions) {
                        if (d == ~lit) { is_decision = true; break; }
                    }
                    if (!is_decision) {
                        // Implied false by other decisions' BCP. Redundant.
                        bool already_marked = false;
                        for (literal dl : m_to_delete) {
                            if (dl == lit) { already_marked = true; break; }
                        }
                        if (!already_marked)
                            m_to_delete.push_back(lit);
                    }
                }
            }

            // Apply the vivification result.
            unsigned old_sz = c.size();
            unsigned new_sz = old_sz;

            if (!m_to_delete.empty()) {
                unsigned j = 0;
                for (unsigned i = 0; i < old_sz; ++i) {
                    bool del = false;
                    for (literal dl : m_to_delete) {
                        if (c[i] == dl) { del = true; break; }
                    }
                    if (!del) {
                        if (i != j) std::swap(c[i], c[j]);
                        ++j;
                    }
                }
                new_sz = j;
            }

            unsigned elim = old_sz - new_sz;
            if (elim > 0) {
                m_elim_literals += elim;
                if (c.is_learned()) m_elim_learned_literals += elim;
            }

            if (new_sz == old_sz) {
                // No change. Reattach and mark vivified.
                if (!was_frozen) {
                    s.attach_clause(c);
                }
                m_vivified.insert(c.id());
            }
            else if (new_sz >= 3) {
                // Shortened but still multi-literal. Shrink and reattach.
                s.shrink(c, old_sz, new_sz);
                if (!was_frozen) {
                    s.attach_clause(c);
                }
                m_vivified.remove(c.id());
                m_retry_queue.push_back(&c);
            }
            else {
                // Reduced to 0, 1, or 2 literals. Must pop to level 0.
                if (s.scope_lvl() > 0) {
                    s.pop(s.scope_lvl());
                    m_decisions.reset();
                }
                switch (new_sz) {
                case 0:
                    s.set_conflict();
                    s.del_clause(c);
                    break;
                case 1:
                    s.assign_unit(c[0]);
                    s.propagate_core(false);
                    s.del_clause(c);
                    break;
                case 2:
                    if (s.value(c[0]) == l_undef && s.value(c[1]) == l_undef) {
                        s.mk_bin_clause(c[0], c[1], c.is_learned());
                        if (s.m_trail.size() > s.m_qhead) s.propagate_core(false);
                    }
                    s.del_clause(c);
                    break;
                }
                m_vivified.remove(c.id());
            }
        }

        // Pop all remaining levels back to 0.
        if (s.scope_lvl() > 0) {
            s.pop(s.scope_lvl());
            m_decisions.reset();
        }
    }


    void asymm_branch::process(big* big, clause_vector& clauses) {
        int64_t limit = -m_asymm_branch_limit;

        // Prefix subsumption: cheap linear-time pass.
        prefix_subsume(clauses);

        // Jeroslow-Wang scoring.
        unsigned num_lits = s.num_vars() * 2;
        m_jw_occ.reserve(num_lits, 0);
        for (unsigned i = 0; i < num_lits; ++i)
            m_jw_occ[i] = 0;
        for (clause* cp : clauses) {
            if (cp->was_removed()) continue;
            int shift = 12 - static_cast<int>(cp->size());
            int64_t w = shift < 1 ? 1 : (1LL << shift);
            for (literal lit : *cp)
                m_jw_occ[lit.index()] += w;
        }

        // Non-BIG path: use CaDiCaL-style decision reuse.
        if (!big) {
            m_counter -= clauses.size();
            m_retry_queue.reset();

            try {
                process_with_reuse(clauses, limit);

                // Retry pass: re-vivify strengthened clauses.
                unsigned const MAX_RETRIES = 3;
                for (unsigned retry_round = 0;
                     retry_round < MAX_RETRIES && !m_retry_queue.empty();
                     ++retry_round) {
                    clause_vector current_retry;
                    current_retry.swap(m_retry_queue);
                    for (clause* cp : current_retry) {
                        if (s.inconsistent() || m_counter < limit)
                            break;
                        clause& c = *cp;
                        if (c.was_removed())
                            continue;
                        s.checkpoint();
                        unsigned elim_before = m_elim_literals;
                        bool survived = process(c);
                        if (!survived) {
                            m_vivified.remove(c.id());
                            continue;
                        }
                        if (m_elim_literals > elim_before) {
                            m_vivified.remove(c.id());
                            m_retry_queue.push_back(cp);
                            ++m_vivify_retries;
                        }
                        else {
                            m_vivified.insert(c.id());
                        }
                    }
                }
                m_retry_queue.reset();
            }
            catch (solver_exception & ex) {
                // Ensure we're at level 0 on exception.
                if (s.scope_lvl() > 0) {
                    s.pop(s.scope_lvl());
                    m_decisions.reset();
                }
                m_retry_queue.reset();
                // Compact out deleted clauses.
                clause_vector::iterator it2 = clauses.begin();
                for (clause* cp : clauses) {
                    if (!cp->was_removed()) {
                        *it2 = cp;
                        ++it2;
                    }
                }
                clauses.set_end(it2);
                m_counter = -m_counter;
                throw ex;
            }

            // Post-compaction: remove deleted clauses.
            clause_vector::iterator it2 = clauses.begin();
            for (clause* cp : clauses) {
                if (!cp->was_removed()) {
                    *it2 = cp;
                    ++it2;
                }
            }
            clauses.set_end(it2);
            return;
        }

        // BIG path: per-clause processing with JW scoring (no decision reuse).
        unsigned n = clauses.size();
        svector<std::pair<int64_t, unsigned>> scored;
        scored.resize(n);
        for (unsigned i = 0; i < n; ++i)
            scored[i] = { jw_clause_score(*clauses[i], m_jw_occ), i };
        std::sort(scored.begin(), scored.end(),
                  [](std::pair<int64_t, unsigned> const& a,
                     std::pair<int64_t, unsigned> const& b) {
                      return a.first > b.first;
                  });
        clause_vector tmp;
        tmp.resize(n);
        for (unsigned i = 0; i < n; ++i)
            tmp[i] = clauses[scored[i].second];
        for (unsigned i = 0; i < n; ++i)
            clauses[i] = tmp[i];

        m_counter -= clauses.size();
        m_retry_queue.reset();
        clause_vector::iterator it  = clauses.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = clauses.end();
        try {
            for (; it != end; ++it) {
                if (s.inconsistent()) {
                    for (; it != end; ++it, ++it2) {
                        *it2 = *it;
                    }
                    break;
                }
                clause & c = *(*it);
                if (m_counter < limit || s.inconsistent() || c.was_removed()) {
                    *it2 = *it;
                    ++it2;
                    continue;
                }
                if (m_vivified.contains(c.id())) {
                    *it2 = *it;
                    ++it2;
                    continue;
                }
                s.checkpoint();
                unsigned elim_before = m_elim_literals;
                if (!process_sampled(*big, c)) {
                    m_vivified.remove(c.id());
                    continue;
                }
                *it2 = *it;
                ++it2;
                if (m_elim_literals > elim_before) {
                    m_vivified.remove(c.id());
                    m_retry_queue.push_back(*it);
                }
                else {
                    m_vivified.insert(c.id());
                }
            }
            clauses.set_end(it2);

            // Retry pass for BIG path.
            unsigned const MAX_RETRIES = 3;
            for (unsigned retry_round = 0;
                 retry_round < MAX_RETRIES && !m_retry_queue.empty();
                 ++retry_round) {
                clause_vector current_retry;
                current_retry.swap(m_retry_queue);
                for (clause* cp : current_retry) {
                    if (s.inconsistent() || m_counter < limit)
                        break;
                    clause& c = *cp;
                    if (c.was_removed())
                        continue;
                    s.checkpoint();
                    unsigned elim_before = m_elim_literals;
                    bool survived = process_sampled(*big, c);
                    if (!survived) {
                        m_vivified.remove(c.id());
                        continue;
                    }
                    if (m_elim_literals > elim_before) {
                        m_vivified.remove(c.id());
                        m_retry_queue.push_back(cp);
                        ++m_vivify_retries;
                    }
                    else {
                        m_vivified.insert(c.id());
                    }
                }
            }
            m_retry_queue.reset();

            it2 = clauses.begin();
            for (clause* cp : clauses) {
                if (!cp->was_removed()) {
                    *it2 = cp;
                    ++it2;
                }
            }
            clauses.set_end(it2);
        }
        catch (solver_exception & ex) {
            for (; it != end; ++it, ++it2) {
                *it2 = *it;
            }
            if (it2 != clauses.begin()) {
                clauses.set_end(it2);
            }
            it2 = clauses.begin();
            for (clause* cp : clauses) {
                if (!cp->was_removed()) {
                    *it2 = cp;
                    ++it2;
                }
            }
            clauses.set_end(it2);
            m_counter = -m_counter;
            m_retry_queue.reset();
            throw ex;
        }
    }
    
    
    void asymm_branch::operator()(bool force) {
        ++m_calls;
        if (m_calls <= m_asymm_branch_delay)
            return;
        if (!m_asymm_branch && !m_asymm_branch_all && !m_asymm_branch_sampled)
            return;
        s.propagate(false); // must propagate, since it uses s.push()
        if (s.m_inconsistent)
            return;
        if (!force && m_counter > 0) {
            m_counter /= 100;
            return;
        }
        CASSERT("asymm_branch", s.check_invariant());
        TRACE(asymm_branch_detail, s.display(tout););
        report rpt(*this);
        bool_vector saved_phase(s.m_phase);
        flet<bool> _is_probing(s.m_is_probing, true);

        bool change = true;
        unsigned counter = 0;
        while (change && counter < 2) {
            ++counter;
            change = false;
            s.m_touch_index++;
            if (m_asymm_branch_sampled) {
                big big(s.m_rand);
                if (process(big, true)) change = true;
            }
            if (m_asymm_branch_sampled) {
                big big(s.m_rand);
                if (process(big, false)) change = true;
            }
            if (m_asymm_branch) {
                m_counter  = 0; 
                if (process(false)) change = true;
                m_counter = -m_counter;
            }
            m_touch_index = s.m_touch_index;
        }

        s.m_phase = saved_phase;
        m_asymm_branch_limit *= 2;
        if (m_asymm_branch_limit > UINT_MAX)
            m_asymm_branch_limit = UINT_MAX;

        CASSERT("asymm_branch", s.check_invariant());

    }

    /**
       \brief try asymmetric branching on all literals in clause.        
    */

    bool asymm_branch::process_all(clause & c) {
        scoped_detach scoped_d(s, c);  // clause must not be used for propagation
        unsigned sz = c.size();
        SASSERT(sz > 0);
        unsigned i = 0, new_sz = sz;
        for (i = sz; i-- > 0; ) {
            if (flip_literal_at(c, i, new_sz))
                return cleanup(scoped_d, c, i, new_sz);
        }
        return true;
    }

    struct asymm_branch::compare_left {
        big& s;
        compare_left(big& s): s(s) {}
        bool operator()(literal u, literal v) const {
            return s.get_left(u) < s.get_left(v);
        }
    };

    bool asymm_branch::is_touched(bool_var v) const { 
        return s.m_touched[v] >= m_touch_index; 
    }

    void asymm_branch::sort(big& big, clause const& c) {
        sort(big, c.begin(), c.end());
    }

    void asymm_branch::sort(big& big, literal const* begin, literal const* end) {
        m_pos.reset(); m_neg.reset();
        for (; begin != end; ++begin) {
            literal l = *begin;
            m_pos.push_back(l);
            m_neg.push_back(~l);
        }
        compare_left cmp(big);
        std::sort(m_pos.begin(), m_pos.end(), cmp);
        std::sort(m_neg.begin(), m_neg.end(), cmp);

        IF_VERBOSE(100, 
                   for (literal l : m_pos) verbose_stream() << big.get_left(l) << " "; 
                   verbose_stream() << "\n";
                   for (literal l : m_neg) verbose_stream() << big.get_left(l) << " "; 
                   verbose_stream() << "\n";
                   );
    }

    bool asymm_branch::uhte(big& big, clause & c) {
        unsigned pindex = 0, nindex = 0;
        literal lpos = m_pos[pindex++];
        literal lneg = m_neg[nindex++];
        while (true) {
            if (big.get_left(lneg) > big.get_left(lpos)) {
                if (pindex == m_pos.size()) return false;
                lpos = m_pos[pindex++];
            }
            else if (big.get_right(lneg) < big.get_right(lpos) ||
                     (m_pos.size() == 2 && (lpos == ~lneg || big.get_parent(lpos) == lneg))) {
                if (nindex == m_neg.size()) return false;
                lneg = m_neg[nindex++];
            }
            else {
                return true;
            }
        }
        return false;
    }

    void asymm_branch::uhle(big& big) {
        m_to_delete.reset();
        if (m_to_delete.empty()) {
            int right = big.get_right(m_pos.back());
            for (unsigned i = m_pos.size() - 1; i-- > 0; ) {
                literal lit = m_pos[i];
                int right2 = big.get_right(lit);
                if (right2 > right) {
                    // lit => last, so lit can be deleted
                    m_to_delete.push_back(lit);
                }
                else {
                    right = right2;
                }
            }
        }
        if (m_to_delete.empty()) {
            int right = big.get_right(m_neg[0]);
            for (unsigned i = 1; i < m_neg.size(); ++i) {
                literal lit = m_neg[i];
                int right2 = big.get_right(lit);
                if (right > right2) {
                    // ~first => ~lit
                    m_to_delete.push_back(~lit);
                }
                else {
                    right = right2;
                }
            }
        }
    }

    bool asymm_branch::uhle(scoped_detach& scoped_d, big& big, clause & c) {
        uhle(big);
        if (!m_to_delete.empty()) {
            unsigned j = 0;
            for (unsigned i = 0; i < c.size(); ++i) {
                literal lit = c[i];
                switch (s.value(lit)) {
                case l_true:
                    scoped_d.del_clause();
                    return false;
                case l_false:    
                    break;
                default:
                    if (!m_to_delete.contains(lit)) {
                        if (i != j) {
                            std::swap(c[i], c[j]);
                        }
                        j++;
                    }
                    break;
                }
            }
            return re_attach(scoped_d, c, j);
        }
        else {
            return true;
        }
    }


    bool asymm_branch::propagate_literal(clause const& c, literal l) {
        if (!is_touched(l.var())) {
            return false;
        }
        SASSERT(!s.inconsistent());
        TRACE(asymm_branch_detail, tout << "assigning: " << l << "\n";);
        s.assign_scoped(l);
        s.propagate_core(false); // must not use propagate(), since check_missed_propagation may fail for c
        return s.inconsistent();
    }

    bool asymm_branch::flip_literal_at(clause const& c, unsigned flip_index, unsigned& new_sz) {
        VERIFY(s.m_trail.size() == s.m_qhead);
        bool found_conflict = false;
        unsigned i = 0, sz = c.size();        
        s.push();
        for (i = 0; !found_conflict && i < sz; ++i) {
            if (i == flip_index) continue;
            found_conflict = propagate_literal(c, ~c[i]);
        }
        if (!found_conflict) {
            SASSERT(sz == i);
            found_conflict = propagate_literal(c, c[flip_index]);
        }
        s.pop(1);
        new_sz = i;
        return found_conflict;
    }
    
    bool asymm_branch::cleanup(scoped_detach& scoped_d, clause& c, unsigned skip_idx, unsigned new_sz) {
        unsigned j = 0;
        for (unsigned i = 0; i < new_sz; ++i) {            
            if (skip_idx == i) continue;
            literal l = c[i];
            switch (s.value(l)) {
            case l_undef:
                if (i != j) {
                    std::swap(c[i], c[j]);
                }
                j++;
                break;
            case l_false:
                break;
            case l_true:
                UNREACHABLE();
                break;
            }
        }
        new_sz = j;                
        return re_attach(scoped_d, c, new_sz);
    }

    bool asymm_branch::re_attach(scoped_detach& scoped_d, clause& c, unsigned new_sz) {
        VERIFY(s.m_trail.size() == s.m_qhead);
        unsigned old_sz = c.size();
        m_elim_literals += old_sz - new_sz;
        if (c.is_learned()) {
            m_elim_learned_literals += old_sz - new_sz; 
        }

        switch (new_sz) {
        case 0:
            s.set_conflict();
            return false;
        case 1:
            TRACE(asymm_branch, tout << "produced unit clause: " << c[0] << "\n";);
            s.assign_unit(c[0]);
            s.propagate_core(false); 
            scoped_d.del_clause();
            return false; // check_missed_propagation() may fail, since m_clauses is not in a consistent state.
        case 2:
            SASSERT(s.value(c[0]) == l_undef && s.value(c[1]) == l_undef);
            VERIFY(s.value(c[0]) == l_undef && s.value(c[1]) == l_undef);
            s.mk_bin_clause(c[0], c[1], c.is_learned());
            if (s.m_trail.size() > s.m_qhead) s.propagate_core(false);
            scoped_d.del_clause();
            return false;
        default:
            s.shrink(c, old_sz, new_sz);
            return true;
        }
    }

    /**
     * CaDiCaL-style vivification with full conflict analysis.
     *
     * For clause (l1 v l2 v ... v ln):
     * 1. Assign ~l1 at level 1, propagate; ~l2 at level 2, propagate; etc.
     * 2. On conflict: analyze to find which decisions contributed.
     *    The strengthened clause = { lj : decision ~lj participated }.
     *    This can remove MULTIPLE literals at once.
     * 3. If literal c[j] becomes FALSE (i.e. ~c[j] is true by propagation):
     *    literal is implied false, skip it (don't need to assign).
     * 4. If literal c[j] becomes TRUE (i.e. it's satisfied):
     *    clause is satisfied, stop.
     * 5. If all literals assigned without conflict: try instantiation
     *    (reverse last decision, propagate, check for conflict).
     *
     * Returns true if clause survives (possibly strengthened),
     * false if clause was removed (satisfied, became unit/binary, or conflict).
     */
    bool asymm_branch::vivify_clause(clause& c) {
        SASSERT(s.scope_lvl() == 0);
        SASSERT(!s.inconsistent());

        scoped_detach scoped_d(s, c);
        unsigned sz = c.size();
        unsigned num_pushed = 0;

        // Track which clause indices had decisions vs were skipped/implied.
        // decided[i] = true if we pushed a level and assigned ~c[i].
        bool_vector decided;
        decided.resize(sz, false);

        bool found_conflict = false;
        bool clause_satisfied = false;
        unsigned last_decided_idx = UINT_MAX;

        for (unsigned i = 0; i < sz && !found_conflict && !clause_satisfied; ++i) {
            literal lit = c[i];

            // Check current value of the clause literal.
            lbool val = s.value(lit);

            if (val == l_false) {
                // c[i] is already false -> ~c[i] is true by propagation.
                // This literal is implied false, will be removed. Skip it.
                continue;
            }

            if (val == l_true) {
                // c[i] is true -> clause is satisfied. Stop.
                clause_satisfied = true;
                break;
            }

            // val == l_undef: assign ~c[i] as a decision at a new level.
            SASSERT(val == l_undef);
            VERIFY(s.m_trail.size() == s.m_qhead);
            s.push();
            num_pushed++;
            decided[i] = true;
            last_decided_idx = i;

            s.assign_scoped(~lit);
            s.propagate_core(false);

            if (s.inconsistent()) {
                found_conflict = true;
                break;
            }
        }

        if (clause_satisfied) {
            s.pop(num_pushed);
            scoped_d.del_clause();
            return false;
        }

        if (found_conflict) {
            // Perform conflict analysis: walk implication graph backward,
            // collect the decision literals that contributed.
            vivify_analyze(c, num_pushed);
            s.pop(num_pushed);

            // m_tmp now contains the strengthened clause literals.
            unsigned new_sz = m_tmp.size();
            if (new_sz >= sz) {
                // Analysis didn't eliminate anything. Shouldn't normally happen.
                return true;
            }

            // Rewrite clause: move surviving literals to front.
            unsigned j = 0;
            for (literal surv : m_tmp) {
                for (unsigned k = j; k < sz; ++k) {
                    if (c[k] == surv) {
                        if (k != j) std::swap(c[k], c[j]);
                        j++;
                        break;
                    }
                }
            }
            SASSERT(j == new_sz);
            return re_attach(scoped_d, c, new_sz);
        }

        // No conflict after all assignments. Try instantiation:
        // reverse the last decision (~c[last]) and assign c[last] instead.
        // If this causes a conflict, that literal is redundant.
        if (last_decided_idx != UINT_MAX && num_pushed > 0) {
            // Pop the last decision level.
            s.pop(1);
            num_pushed--;

            literal pos_lit = c[last_decided_idx];
            if (s.value(pos_lit) == l_undef) {
                VERIFY(s.m_trail.size() == s.m_qhead);
                s.push();
                num_pushed++;
                s.assign_scoped(pos_lit);
                s.propagate_core(false);

                if (s.inconsistent()) {
                    // Conflict with positive literal -> it's forced false by
                    // the remaining decisions. Analyze without the last decision.
                    vivify_analyze(c, num_pushed);
                    s.pop(num_pushed);

                    unsigned new_sz = m_tmp.size();
                    if (new_sz < sz) {
                        unsigned j = 0;
                        for (literal surv : m_tmp) {
                            for (unsigned k = j; k < sz; ++k) {
                                if (c[k] == surv) {
                                    if (k != j) std::swap(c[k], c[j]);
                                    j++;
                                    break;
                                }
                            }
                        }
                        return re_attach(scoped_d, c, j);
                    }
                    return true;
                }
            }
        }

        // No strengthening possible.
        s.pop(num_pushed);
        return true;
    }

    /**
     * Analyze conflict during vivification.
     * Walk the implication graph backward from the conflict, collecting
     * which decision literals (the negated clause literals we assigned)
     * participated in deriving the conflict.
     *
     * Result is placed in m_tmp: the subset of original clause literals
     * whose negations were decisions contributing to the conflict.
     *
     * This is simpler than full 1-UIP conflict analysis: we trace all the
     * way back to decisions, collecting every decision variable on the path.
     * The result is a "decision-only" clause.
     */
    void asymm_branch::vivify_analyze(clause const& c, unsigned num_levels) {
        (void)num_levels;
        m_tmp.reset();

        // Use solver's m_mark (per-variable bool). Track what we mark so
        // we can clean up afterward.
        svector<bool_var> marked_vars;

        auto mark_var = [&](bool_var v) {
            if (s.is_marked(v) || s.lvl(v) == 0) return;
            s.mark(v);
            marked_vars.push_back(v);
        };

        // Seed from the conflict clause.
        justification js = s.m_conflict;
        literal not_l = s.m_not_l;

        if (not_l != null_literal) {
            mark_var(not_l.var());
        }

        switch (js.get_kind()) {
        case justification::NONE:
            break;
        case justification::BINARY:
            mark_var(js.get_literal().var());
            break;
        case justification::CLAUSE: {
            clause& conf = s.get_clause(js);
            for (literal l : conf)
                mark_var(l.var());
            break;
        }
        default:
            break;
        }

        // Walk trail backward. For each marked variable:
        // - If decision (NONE justification): this is one of our ~c[i].
        //   Add ~(~c[i]) = c[i] to the result (the positive literal).
        // - If propagated: resolve through its reason (mark its antecedents).
        for (unsigned idx = s.m_trail.size(); idx-- > 0;) {
            literal tlit = s.m_trail[idx];
            bool_var tv = tlit.var();
            if (!s.is_marked(tv)) continue;

            justification tj = s.m_justification[tv];
            if (tj.is_none()) {
                // Decision literal. In vivification, we assigned ~c[i],
                // so tlit = ~c[i], meaning c[i] = ~tlit goes into the result.
                m_tmp.push_back(~tlit);
            }
            else {
                // Propagated: resolve through its reason clause.
                switch (tj.get_kind()) {
                case justification::BINARY:
                    mark_var(tj.get_literal().var());
                    break;
                case justification::CLAUSE: {
                    clause& reason = s.get_clause(tj);
                    for (literal l : reason) {
                        if (l.var() != tv)
                            mark_var(l.var());
                    }
                    break;
                }
                default:
                    break;
                }
            }
        }

        // Clean up marks.
        for (bool_var v : marked_vars)
            s.reset_mark(v);

        // Safety: if analysis produced nothing, keep original clause.
        if (m_tmp.empty()) {
            for (literal l : c)
                m_tmp.push_back(l);
        }
    }

    bool asymm_branch::process_sampled(big& big, clause & c) {
        scoped_detach scoped_d(s, c);
        sort(big, c);
        if (uhte(big, c)) {
            // don't touch hidden tautologies.
            // ATE takes care of them.
            return true;
        }
        return uhle(scoped_d, big, c);
    }

    bool asymm_branch::process(clause & c) {
        TRACE(asymm_branch_detail, tout << "processing: " << c << "\n";);
        SASSERT(s.scope_lvl() == 0);
        SASSERT(!s.inconsistent());

        unsigned sz = c.size();
        SASSERT(sz > 0);
        unsigned i;
        // Check if the clause is already satisfied.
        for (i = 0; i < sz; ++i) {
            if (s.value(c[i]) == l_true) {
                s.detach_clause(c);
                s.del_clause(c);
                return false;
            }
        }
        m_counter -= c.size();

        if (m_asymm_branch_all) return process_all(c);

        // CaDiCaL-style vivification with full conflict analysis.
        return vivify_clause(c);
    }
    
    void asymm_branch::updt_params(params_ref const & _p) {
        sat_asymm_branch_params p(_p);
        m_asymm_branch         = p.asymm_branch();
        m_asymm_branch_rounds  = p.asymm_branch_rounds();
        m_asymm_branch_delay   = p.asymm_branch_delay();
        m_asymm_branch_sampled = p.asymm_branch_sampled();
        m_asymm_branch_limit   = p.asymm_branch_limit();
        m_asymm_branch_all     = p.asymm_branch_all();
        if (m_asymm_branch_limit > UINT_MAX)
            m_asymm_branch_limit = UINT_MAX;
    }

    void asymm_branch::collect_param_descrs(param_descrs & d) {
        sat_asymm_branch_params::collect_param_descrs(d);
    }
    
    void asymm_branch::collect_statistics(statistics & st) const {
        st.update("sat elim literals", m_elim_literals);
        st.update("sat tr", m_tr);
        st.update("sat prefix subsumed", m_prefix_subsumed);
        st.update("sat vivify retries", m_vivify_retries);
        st.update("sat vivify reused", m_reused_decisions);
    }

    void asymm_branch::reset_statistics() {
        m_elim_literals = 0;
        m_elim_learned_literals = 0;
        m_tr = 0;
        m_prefix_subsumed = 0;
        m_vivify_retries = 0;
        m_reused_decisions = 0;
    }

};
