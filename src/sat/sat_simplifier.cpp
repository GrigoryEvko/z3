/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_simplifier.cpp

Abstract:

    SAT simplification procedures that use a "full" occurrence list:
    Subsumption, Blocked Clause Removal, Variable Elimination, ...


Author:

    Leonardo de Moura (leonardo) 2011-05-24.

Revision History:

--*/
#include "sat/sat_simplifier.h"
#include "sat/sat_simplifier_params.hpp"
#include "sat/sat_solver.h"
#include "sat/sat_integrity_checker.h"
#include "util/stopwatch.h"
#include "util/trace.h"

namespace sat {

    void use_list::init(unsigned num_vars) {
        m_use_list.reset();
        unsigned num_lits = 2 * num_vars;
        m_use_list.resize(num_lits);
    }

    void use_list::insert(clause & c) {
        for (literal l : c) 
            m_use_list[l.index()].insert(c);
    }

    void use_list::erase(clause & c) {
        for (literal l : c) 
            m_use_list[l.index()].erase(c);
    }

    void use_list::erase(clause & c, literal l) {
        for (literal l2 : c) 
            if (l2 != l)
                m_use_list[l2.index()].erase(c);
    }

    void use_list::block(clause& c) {
        for (literal l : c) 
            m_use_list[l.index()].block(c);
    }

    void use_list::unblock(clause& c) {
        for (literal l : c) 
            m_use_list[l.index()].unblock(c);
    }

    simplifier::simplifier(solver & _s, params_ref const & p):
        s(_s),
        m_num_calls(0),
        m_elim_heap(0, elim_cost_lt(this)),
        m_elim_bound(0),
        m_elim_bound_max(16),
        m_gate_type(GATE_NONE),
        m_xor_lim(5) {
        updt_params(p);
        reset_statistics();
    }

    simplifier::~simplifier() {
        finalize();
    }

    watch_list & simplifier::get_wlist(literal l) { return s.get_wlist(l); }

    watch_list const & simplifier::get_wlist(literal l) const { return s.get_wlist(l); }

    watch_list & simplifier::get_bin_wlist(literal l) { return s.get_bin_wlist(l); }

    watch_list const & simplifier::get_bin_wlist(literal l) const { return s.get_bin_wlist(l); }

    bool simplifier::is_external(bool_var v) const { 
        if (!s.is_external(v))
            return s.is_assumption(v);
        if (s.is_incremental())
            return true;
        if (!s.m_ext)
            return false;
        if (s.m_ext->is_external(v))
            return true;
        if (m_ext_use_list.contains(v))
            return true;
        return false;
    }

    inline bool simplifier::was_eliminated(bool_var v) const { return s.was_eliminated(v); }

    lbool simplifier::value(bool_var v) const { return s.value(v); }

    lbool simplifier::value(literal l) const { return s.value(l); }

    inline void simplifier::checkpoint() { s.checkpoint(); }

    bool simplifier::single_threaded() const { return s.m_config.m_num_threads == 1; }

    bool simplifier::bce_enabled_base() const {
        return 
            !m_incremental_mode && !s.tracking_assumptions() && 
            !m_learned_in_use_lists && m_num_calls >= m_bce_delay && single_threaded();
    }

    bool simplifier::ate_enabled()  const { return m_num_calls >= m_bce_delay && m_ate; }
    bool simplifier::bce_enabled()  const { return bce_enabled_base() && (m_bce || m_bce_at == m_num_calls || m_acce || m_abce || m_cce); }
    bool simplifier::acce_enabled() const { return bce_enabled_base() && m_acce; }
    bool simplifier::cce_enabled()  const { return bce_enabled_base() && (m_cce || m_acce); }
    bool simplifier::abce_enabled() const { return bce_enabled_base() && m_abce; }
    bool simplifier::bca_enabled()  const { return bce_enabled_base() && m_bca; }
    bool simplifier::elim_vars_enabled() const {
        return !m_incremental_mode && !s.tracking_assumptions() && m_elim_vars && single_threaded();
    }

    bool simplifier::bva_enabled() const {
        return !m_incremental_mode && !s.tracking_assumptions() && m_bva && single_threaded();
    }

    void simplifier::mark_subsume(clause const & c) {
        for (literal lit : c) {
            bool_var v = lit.var();
            if (v < m_subsume_flag.size())
                m_subsume_flag[v] = true;
        }
    }

    bool simplifier::has_subsume_overlap(clause const & c) const {
        unsigned count = 0;
        for (literal lit : c) {
            bool_var v = lit.var();
            if (v < m_subsume_flag.size() && m_subsume_flag[v]) {
                if (++count >= 2)
                    return true;
            }
        }
        return false;
    }

    void simplifier::register_clauses(clause_vector & cs) {
        std::stable_sort(cs.begin(), cs.end(), size_lt());
        for (clause* c : cs) {
            if (!c->frozen()) {
                // All clauses MUST be registered in the use list.
                // Variable elimination iterates the use list to find ALL
                // clauses containing a variable. Skipping clauses here
                // causes elimination to produce incomplete resolvents,
                // silently losing information (soundness bug).
                m_use_list.insert(*c);
                if (c->strengthened()) {
                    mark_subsume(*c);
                    m_sub_todo.insert(*c);
                }
            }
        }
    }

    inline void simplifier::remove_clause(clause & c, bool is_unique) {
        if (!c.was_removed()) {
            if (s.m_config.m_drat && is_unique) {
                s.m_drat.del(c);
            }
            for (literal l : c) {
                insert_elim_todo(l.var());
            }
            m_sub_todo.erase(c);
            c.set_removed(true);
            TRACE(sat_simplifier, tout << "del_clause: " << c << "\n";);
            m_need_cleanup = true;
            m_use_list.erase(c);
        }
    }

    inline void simplifier::set_learned(clause & c) {
        m_need_cleanup = true;
        s.set_learned(c, true);
        m_use_list.block(c);
    }

    inline void simplifier::set_learned(literal l1, literal l2) {
        m_sub_bin_todo.erase(bin_clause(l1, l2, false));
        m_sub_bin_todo.erase(bin_clause(l2, l1, false));
        m_sub_bin_todo.push_back(bin_clause(l1, l2, true));
        m_sub_bin_todo.push_back(bin_clause(l2, l1, true));
    }

    void simplifier::init_visited() {
        m_visited.reset();
        m_visited.resize(2*s.num_vars(), false);
    }

    void simplifier::finalize() {
        m_use_list.finalize();
        m_sub_todo.finalize();
        m_sub_bin_todo.finalize();
        m_elim_todo.finalize();
        m_elim_heap.reset();
        m_elim_costs.finalize();
        m_elim_heap_dirty.finalize();
        m_subsume_flag.finalize();
        m_visited.finalize();
        m_bs_cs.finalize();
        m_bs_ls.finalize();
        m_ext_use_list.finalize();
    }

    void simplifier::initialize() {
        m_need_cleanup = false;
        s.m_cleaner(true);
        m_last_sub_trail_sz = s.m_trail.size();
        m_use_list.init(s.num_vars());
        if (s.m_ext) s.m_ext->init_use_list(m_ext_use_list);
        m_sub_todo.reset();
        m_sub_bin_todo.reset();
        m_elim_todo.reset();
        m_subsume_flag.reset();
        m_subsume_flag.resize(s.num_vars(), false);
        init_visited();
        TRACE(after_cleanup, s.display(tout););
        CASSERT("sat_solver", s.check_invariant());
    }

    void simplifier::operator()(bool learned) {

        if (s.inconsistent())
            return;
        if (!m_subsumption && !bce_enabled() && !bca_enabled() && !elim_vars_enabled() && !bva_enabled())
            return;
       
        initialize();

        CASSERT("sat_solver", s.check_invariant());
        TRACE(sat_simplifier, s.display(tout););

        s.m_cleaner(true);
        TRACE(after_cleanup, s.display(tout););
        CASSERT("sat_solver", s.check_invariant());
        m_need_cleanup = false;
        m_use_list.init(s.num_vars());
        m_learned_in_use_lists = learned;
        if (learned) {
            register_clauses(s.m_learned);
        }
        register_clauses(s.m_clauses);

        if (!learned) {
            m_num_calls++;
        }

        m_sub_counter  = m_subsumption_limit;
        m_elim_counter = m_res_limit;
        m_old_num_elim_vars = m_num_elim_vars;

        for (bool_var v = 0; v < s.num_vars(); ++v) {
            if (!s.m_eliminated[v] && !is_external(v)) {
                insert_elim_todo(v);
            }
        }

        bool bce_applicable = !learned && (bce_enabled() || bca_enabled() || ate_enabled());
        bool elim_applicable = !learned && elim_vars_enabled();

        // Interleaved simplification loop (CaDiCaL-style).
        //
        // CaDiCaL's elimination phase (elim.cpp:1069-1109) interleaves:
        //   elim_round -> subsume_round -> block -> cover -> fixpoint
        // Each step can remove clauses or strengthen them, creating new
        // elimination candidates. We follow the same principle:
        //   subsumption -> variable elimination -> BCE/CCE
        // and repeat while any step makes progress.
        //
        // Key insight: BCE marks clauses as learned, reducing
        // num_irredundant() in occurrence lists. This can make
        // previously unprofitable variable eliminations profitable
        // (fewer clauses to resolve over, lower cost).
        unsigned round = 0;
        unsigned const max_rounds = 10;
        do {
            bool progress = false;

            // Step 1: Subsumption removes subsumed clauses and strengthens.
            // remove_clause() and elim_lit() insert affected variables
            // into m_elim_todo, seeding step 2.
            if (m_subsumption) {
                unsigned old_subsumed = m_num_subsumed;
                unsigned old_sub_res  = m_num_sub_res;
                subsume();
                if (m_num_subsumed > old_subsumed || m_num_sub_res > old_sub_res)
                    progress = true;
            }
            if (s.inconsistent())
                return;

            // Step 2: Variable elimination via bounded resolution.
            if (elim_applicable) {
                unsigned old_elim = m_num_elim_vars;
                elim_vars();
                if (m_num_elim_vars > old_elim)
                    progress = true;
            }
            if (s.inconsistent())
                return;

            // Step 3: Blocked clause elimination (BCE/CCE/ACCE/ABCE/ATE).
            // Blocking clauses reduces irredundant occurrence counts,
            // which can enable new variable eliminations in the next round.
            // elim_blocked_clauses_tracked() re-seeds m_elim_todo with
            // all eligible variables after successful blocking.
            if (bce_applicable) {
                if (elim_blocked_clauses_tracked())
                    progress = true;
            }
            if (s.inconsistent())
                return;

            ++round;
            m_num_elim_rounds++;

            TRACE(sat_simplifier, tout << "interleaved round " << round
                  << " progress=" << progress
                  << " sub_todo=" << m_sub_todo.size()
                  << " elim_todo=" << m_elim_todo.size() << "\n";);

            if (!progress)
                break;
            if (m_sub_counter < 0 && m_elim_counter < 0)
                break;
        }
        while (round < max_rounds);

        IF_VERBOSE(SAT_VB_LVL,
                   if (round > 1)
                       verbose_stream() << " (sat-simplifier-rounds " << round << ")\n";);

        if (!learned && bva_enabled() && !s.inconsistent()) {
            bva();
        }

        bool vars_eliminated = m_num_elim_vars > m_old_num_elim_vars;

        // Elimination bound escalation (CaDiCaL / GlueMiniSAT style).
        // After a complete simplification phase where elimination was active
        // and variables were eliminated, increase the bound so the next
        // simplification call allows more clause growth during elimination.
        // The escalation is persistent across inprocessing rounds.
        if (elim_applicable && vars_eliminated && m_elim_counter >= 0) {
            increase_elim_bound();
        }

        if (m_need_cleanup || vars_eliminated) {
            TRACE(after_simplifier, tout << "cleanning watches...\n";);
            cleanup_watches();
            move_clauses(s.m_learned, true);
            move_clauses(s.m_clauses, false);
            cleanup_clauses(s.m_learned, true, vars_eliminated);
            cleanup_clauses(s.m_clauses, false, vars_eliminated);
        }

        CASSERT("sat_solver", s.check_invariant());
        TRACE(sat_simplifier, s.display(tout); tout << "model_converter:\n"; s.m_mc.display(tout););

        finalize();
    }

    /**
       \brief Eliminate all ternary and clause watches.
    */
    void simplifier::cleanup_watches() {
        for (watch_list& wlist : s.m_watches) {
            watch_list::iterator it2    = wlist.begin();
            watch_list::iterator itprev = it2;
            watch_list::iterator end2   = wlist.end();
            for (; it2 != end2; ++it2) {
                switch (it2->get_kind()) {
                case watched::CLAUSE:
                    // consume
                    break;
                default:
                    *itprev = *it2;
                    itprev++;
                    break;
                }
            }
            wlist.set_end(itprev);            
        }
    }

    void simplifier::move_clauses(clause_vector& cs, bool learned) {
        clause_vector::iterator it  = cs.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = cs.end();
        for (; it != end; ++it) {
            clause & c = *(*it);
            if (learned && !c.is_learned()) {
                s.m_clauses.push_back(&c);
            }
            else if (!learned && c.is_learned()) {
                s.m_learned.push_back(&c);
            }
            else {
                *it2 = *it;
                ++it2;
            }
        }
        cs.set_end(it2);
    }

    void simplifier::cleanup_clauses(clause_vector & cs, bool learned, bool vars_eliminated) {
        TRACE(sat, tout << "cleanup_clauses\n";);
        clause_vector::iterator it  = cs.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = cs.end();
        for (; it != end; ++it) {
            clause & c = *(*it);
            VERIFY(learned == c.is_learned());
            if (c.was_removed()) {
                s.del_clause(c);
                continue;
            }

            if (learned && vars_eliminated) {
                unsigned sz = c.size();
                unsigned i;
                for (i = 0; i < sz; ++i) {
                    if (was_eliminated(c[i].var()))
                        break;
                }
                if (i < sz) {
                    s.del_clause(c);
                    continue;
                }
            }

            unsigned sz0 = c.size();
            if (cleanup_clause(c)) {
                s.del_clause(c);
                continue;
            }
            unsigned sz = c.size();
            switch(sz) {
            case 0:
                s.set_conflict();
                for (; it != end; ++it, ++it2) {
                    *it2 = *it;                  
                }
                cs.set_end(it2);
                return;                
            case 1:
                s.assign_unit(c[0]);
                c.restore(sz0);
                s.del_clause(c);
                break;
            case 2:
                s.mk_bin_clause(c[0], c[1], c.is_learned());
                c.restore(sz0);
                s.del_clause(c);
                break;
            default:
                s.shrink(c, sz0, sz);
                *it2 = *it;
                it2++;
                if (!c.frozen()) {
                    s.attach_clause(c);
                }
                break;
            }
        }
        cs.set_end(it2);
    }

    void simplifier::mark_all_but(clause const & c, literal l1) {
        for (literal l2 : c) 
            if (l2 != l1)
                mark_visited(l2);
    }

    void simplifier::unmark_all(clause const & c) {
        for (literal l : c)
            unmark_visited(l);
    }

    /**
       \brief Return the variable in c with the minimal number positive+negative occurrences.
    */
    bool_var simplifier::get_min_occ_var(clause const & c) const {
        literal l_best = null_literal;
        unsigned best = UINT_MAX;
        for (literal l : c) {
            unsigned num = m_use_list.get(l).size() + m_use_list.get(~l).size();
            if (num < best) {
                l_best = l;
                best   = num;
            }
        }
        return l_best.var();
    }

    /**
       If c1 subsumes c2, return true
       If c2 can self subsumed by c1, return true and store the literal that can be removed from c2 in l.
       Otherwise return false
    */
    bool simplifier::subsumes1(clause const & c1, clause const & c2, literal & l) {
        for (literal lit : c2) 
            mark_visited(lit);

        bool r = true;
        l = null_literal;
        for (literal lit : c1) {
            if (!is_marked(lit)) {
                if (l == null_literal && is_marked(~lit)) {
                    l = ~lit;
                }
                else {
                    l = null_literal;
                    r = false;
                    break;
                }
            }
        }

        for (literal lit : c2) 
            unmark_visited(lit);
        return r;
    }

    /**
       \brief Return the clauses subsumed by c1 and the clauses that can be subsumed resolved using c1.
       The collections is populated using the use list of target.
    */
    void simplifier::collect_subsumed1_core(clause const & c1, clause_vector & out, literal_vector & out_lits,
                                            literal target) {
        clause_use_list const & cs = m_use_list.get(target);
        for (auto it = cs.mk_iterator(); !it.at_end(); it.next()) {
            clause & c2 = it.curr();
            CTRACE(sat_simplifier, c2.was_removed(), tout << "clause has been removed:\n" << c2 << "\n";);
            SASSERT(!c2.was_removed());
            if (&c2 != &c1 &&
                c1.size() <= c2.size() &&
                approx_subset(c1.approx(), c2.approx())) {
                m_sub_counter -= c1.size() + c2.size();
                literal l;
                if (subsumes1(c1, c2, l)) {
                    out.push_back(&c2);
                    out_lits.push_back(l);
                }
            }
        }
    }

    /**
       \brief Return the clauses subsumed by c1 and the clauses that can be subsumed resolved using c1.
    */
    void simplifier::collect_subsumed1(clause const & c1, clause_vector & out, literal_vector & out_lits) {
        bool_var v = get_min_occ_var(c1);
        collect_subsumed1_core(c1, out, out_lits, literal(v, false));
        collect_subsumed1_core(c1, out, out_lits, literal(v, true));
    }

    /**
       \brief Perform backward subsumption and self-subsumption resolution using c1.
    */
    void simplifier::back_subsumption1(clause & c1) {
        m_bs_cs.reset();
        m_bs_ls.reset();
        collect_subsumed1(c1, m_bs_cs, m_bs_ls);
        SASSERT(m_bs_cs.size() == m_bs_ls.size());
        clause_vector::iterator it    = m_bs_cs.begin();
        clause_vector::iterator end   = m_bs_cs.end();
        literal_vector::iterator l_it = m_bs_ls.begin();
        for (; it != end; ++it, ++l_it) {
            clause & c2 = *(*it);
            if (!c2.was_removed() && *l_it == null_literal) {
                // c2 was subsumed
                if (c1.is_learned() && !c2.is_learned()) {
                    s.set_learned(c1, false);
                }
                TRACE(subsumption, tout << c1 << " subsumed " << c2 << "\n";);
                remove_clause(c2, false);
                m_num_subsumed++;
            }
            else if (!c2.was_removed()) {
                // subsumption resolution
                TRACE(subsumption_resolution, tout << c1 << " sub-ref(" << *l_it << ") " << c2 << "\n";);
                elim_lit(c2, *l_it);
                m_num_sub_res++;
                TRACE(subsumption_resolution, tout << "result: " << c2 << "\n";);
            }
            if (s.inconsistent())
                break;
        }
    }

    void simplifier::back_subsumption1(literal l1, literal l2, bool learned) {
        m_dummy.set(l1, l2, learned);
        clause & c = *(m_dummy.get());
        back_subsumption1(c);
    }

    /**
       \brief Return the literal in c with the minimal number of occurrences.
    */
    literal simplifier::get_min_occ_var0(clause const & c) const {
        literal l_best = null_literal;
        unsigned best = UINT_MAX;
        for (literal l : c) {
            unsigned num = m_use_list.get(l).size();
            if (num < best) {
                l_best = l;
                best   = num;
            }
        }
        return l_best;
    }

    /**
       If c1 subsumes c2, return true
       Otherwise return false
    */
    bool simplifier::subsumes0(clause const & c1, clause const & c2) {
        for (literal l : c2) 
            mark_visited(l);

        bool r = true;
        for (literal l : c1) {
            if (!is_marked(l)) {
                r = false;
                break;
            }
        }

        for (literal l : c2)
            unmark_visited(l);

        return r;
    }

    /**
       \brief Collect the clauses subsumed by c1 (using the occurrence list of target).
    */
    void simplifier::collect_subsumed0_core(clause const & c1, clause_vector & out, literal target) {
        clause_use_list const & cs = m_use_list.get(target);
        clause_use_list::iterator it = cs.mk_iterator();
        for (; !it.at_end(); it.next()) {
            clause & c2 = it.curr();
            SASSERT(!c2.was_removed());
            if (&c2 != &c1 &&
                c1.size() <= c2.size() &&
                approx_subset(c1.approx(), c2.approx())) {
                m_sub_counter -= c1.size() + c2.size();
                if (subsumes0(c1, c2)) {
                    out.push_back(&c2);
                }
            }
        }
    }

    /**
       \brief Collect the clauses subsumed by c1
    */
    void simplifier::collect_subsumed0(clause const & c1, clause_vector & out) {
        literal l = get_min_occ_var0(c1);
        collect_subsumed0_core(c1, out, l);
    }


    /**
       \brief Perform backward subsumption using c1.
    */
    void simplifier::back_subsumption0(clause & c1) {
        m_bs_cs.reset();
        collect_subsumed0(c1, m_bs_cs);
        for (clause* cp : m_bs_cs) {
            clause & c2 = *cp;
            // c2 was subsumed
            if (c1.is_learned() && !c2.is_learned())
                s.set_learned(c1, false);
            TRACE(subsumption, tout << c1 << " subsumed " << c2 << "\n";);
            remove_clause(c2, false);
            m_num_subsumed++;
        }
    }

    /**
       \brief Eliminate false literals from c, and update occurrence lists

       Return true if the clause is satisfied
    */
    bool simplifier::cleanup_clause(clause & c) {
        bool r = false;
        unsigned sz = c.size();
        unsigned j  = 0;
        for (unsigned i = 0; i < sz; ++i) {
            literal l = c[i];
            switch (value(l)) {
            case l_undef:
                if (i != j) {
                    std::swap(c[j], c[i]);
                }
                j++;
                break;
            case l_false:
                m_need_cleanup = true;
                break;
            case l_true:
                r = true;
                if (i != j) {
                    std::swap(c[j], c[i]);
                }
                j++;
                break;
            }
        }
        if (j < sz && !r) {
            if (j > 2) {
                s.shrink(c, sz, j);
            }
            else {
                c.shrink(j);
            }
        }
        return r;
    }

    /**
       \brief Eliminate false literals from c.

       Return true if the clause is satisfied
    */
    bool simplifier::cleanup_clause(literal_vector & c) {
        unsigned sz = c.size();
        unsigned j  = 0;
        for (unsigned i = 0; i < sz; ++i) {
            literal l = c[i];
            switch (value(l)) {
            case l_undef:
                if (i != j) {
                    std::swap(c[j], c[i]);
                }
                j++;
                break;
            case l_false:
                break;
            case l_true:
                return true;
            }
        }
        c.shrink(j);            
        return false;
    }

    inline void simplifier::propagate_unit(literal l) {
        unsigned old_trail_sz = s.m_trail.size();
        unsigned num_clauses = s.m_clauses.size();
        s.assign_scoped(l);
        s.propagate_core(false); // must not use propagate(), since s.m_clauses is not in a consistent state.
        if (s.inconsistent())
            return;
        m_use_list.reserve(s.num_vars());
        unsigned new_trail_sz = s.m_trail.size();
        for (unsigned i = old_trail_sz; i < new_trail_sz; ++i) {
            literal l = s.m_trail[i];
            // Mark the propagated variable as subsume-relevant:
            // clauses containing ~l are effectively strengthened.
            if (l.var() < m_subsume_flag.size())
                m_subsume_flag[l.var()] = true;
            // put clauses with literals assigned to false back into todo-list
            for (auto it = m_use_list.get(~l).mk_iterator(); !it.at_end(); it.next()) {
                m_sub_todo.insert(it.curr());
            }
            clause_use_list& cs = m_use_list.get(l);
            for (auto it = cs.mk_iterator(); !it.at_end(); ) {
                clause & c = it.curr();
                it.next();
                remove_clause(c, true);
            }
            cs.reset();            
        }
        for (unsigned i = num_clauses; i < s.m_clauses.size(); ++i) {
            clause & c = *s.m_clauses[i];
            m_use_list.insert(c);
        }
    }

    void simplifier::elim_lit(clause & c, literal l) {
        TRACE(elim_lit, tout << "processing: " << l << " @ " << c << "\n";);
        m_need_cleanup = true;
        m_num_elim_lits++;
        insert_elim_todo(l.var());
        if (s.m_config.m_drat && c.contains(l)) {
            unsigned sz = c.size();
            c.elim(l);
            s.m_drat.add(c, status::redundant());
            c.restore(sz);
            s.m_drat.del(c);
            c.shrink(sz-1);
        }
        else {
            c.elim(l);
        }
        clause_use_list & occurs = m_use_list.get(l);
        occurs.erase_not_removed(c);
        m_sub_counter -= occurs.size()/2;

        unsigned sz0 = c.size();
        if (cleanup_clause(c)) {
            // clause was satisfied
            TRACE(elim_lit, tout << "clause was satisfied\n";);
            remove_clause(c, true);
            return;
        }
        unsigned sz = c.size();
        switch (sz) {
        case 0:
            TRACE(elim_lit, tout << "clause is empty\n";);
            s.set_conflict();
            break;
        case 1:
            TRACE(elim_lit, tout << "clause became unit: " << c[0] << "\n";);
            c.restore(sz0);
            propagate_unit(c[0]);
            // unit propagation removes c
            break;
        case 2:
            TRACE(elim_lit, tout << "clause became binary: " << c[0] << " " << c[1] << "\n";);
            c.restore(sz0);
            s.mk_bin_clause(c[0], c[1], c.is_learned());
            m_sub_bin_todo.push_back(bin_clause(c[0], c[1], c.is_learned()));            
            remove_clause(c, sz0 != sz);
            break;
        default:
            TRACE(elim_lit, tout << "result: " << c << "\n";);
            // CaDiCaL: clamp glue to size-1 after literal elimination.
            if (c.is_learned() && c.glue() >= c.size())
                c.set_glue(c.size() - 1);
            mark_subsume(c);
            m_sub_todo.insert(c);
            break;
        }
    }

    /**
       \brief CaDiCaL-style tight binary subsumption check for a single clause.

       Marks all literals of c, then for each literal l in c, scans binary
       watches of l.  If binary (l, other) and other is also in c, c is
       subsumed.  If binary (l, other) and ~other is in c, c can be
       strengthened by removing ~other (self-subsumption resolution).

       Returns true if c was subsumed (removed).
       On strengthening, calls elim_lit and returns false (caller should
       re-check c if needed).
    */
    bool simplifier::try_subsume_by_binary(clause & c) {
        if (c.was_removed())
            return true;
        unsigned sz = c.size();
        if (sz <= 2)
            return false;

        for (unsigned i = 0; i < sz; ++i)
            mark_visited(c[i]);

        bool subsumed = false;
        literal strengthen_lit = null_literal;

        for (unsigned i = 0; i < sz && !subsumed && strengthen_lit == null_literal; ++i) {
            literal l = c[i];
            // get_bin_wlist(~l) contains watched entries for binaries (l, other)
            watch_list const & bwlist = get_bin_wlist(~l);
            for (auto const & w : bwlist) {
                SASSERT(w.is_binary_clause());
                if (w.is_learned())
                    continue;
                literal other = w.get_literal();
                if (is_marked(other)) {
                    // Binary (l, other) subsumes c -- both l and other are in c
                    TRACE(subsumption, tout << "binary (" << l << " " << other << ") subsumes " << c << "\n";);
                    subsumed = true;
                    break;
                }
                if (is_marked(~other)) {
                    // Binary (l, other) can strengthen c: remove ~other from c
                    // (self-subsumption resolution: (l, other) resolves with c on other)
                    TRACE(subsumption, tout << "binary (" << l << " " << other << ") strengthens " << c
                          << " by removing " << ~other << "\n";);
                    strengthen_lit = ~other;
                    break;
                }
            }
        }

        for (unsigned i = 0; i < sz; ++i)
            unmark_visited(c[i]);

        if (subsumed) {
            remove_clause(c, false);
            m_num_subsumed++;
            return true;
        }

        if (strengthen_lit != null_literal) {
            m_sub_counter -= c.size();
            elim_lit(c, strengthen_lit);
            m_num_sub_res++;
            return false;
        }

        return false;
    }

    /**
       \brief CaDiCaL-style binary subsumption: for each longer clause,
       check whether any non-learned binary subsumes or strengthens it.

       This is the inverse of the old approach (which iterated over binaries
       and searched use-lists).  The new approach iterates over clauses once
       and scans binary watches per literal -- much tighter for typical
       instances where binaries vastly outnumber longer clauses.
    */
    bool simplifier::subsume_with_binaries() {
        clause_vector to_check;
        for (clause * cp : s.m_clauses)
            if (!cp->frozen() && !cp->was_removed() && cp->size() > 2)
                to_check.push_back(cp);
        if (m_learned_in_use_lists) {
            for (clause * cp : s.m_learned)
                if (!cp->frozen() && !cp->was_removed() && cp->size() > 2)
                    to_check.push_back(cp);
        }

        for (clause * cp : to_check) {
            checkpoint();
            clause & c = *cp;
            if (c.was_removed())
                continue;

            // Iteratively apply binary subsumption/strengthening.
            // After strengthening, re-check since new binary matches may appear.
            bool strengthened_this_round = true;
            while (strengthened_this_round && !c.was_removed() && c.size() > 2 && !s.inconsistent()) {
                strengthened_this_round = false;
                unsigned sz_before = c.size();
                if (try_subsume_by_binary(c))
                    break; // subsumed -- removed
                // try_subsume_by_binary returns false on strengthening;
                // detect it by clause shrinkage or the strengthened flag.
                if (!c.was_removed() && (c.size() < sz_before || c.strengthened())) {
                    c.unmark_strengthened();
                    strengthened_this_round = true;
                }
            }

            if (s.inconsistent())
                return false;
            if (m_sub_counter < 0)
                break;
        }
        return true;
    }

    void simplifier::mark_as_not_learned_core(watch_list & wlist, literal l2) {
        for (watched & w : wlist) {
            if (w.is_binary_clause() && w.get_literal() == l2 && w.is_learned()) {
                w.set_learned(false);
                return;
            }
        }
    }

    void simplifier::mark_as_not_learned(literal l1, literal l2) {
        mark_as_not_learned_core(get_bin_wlist(~l1), l2);
        mark_as_not_learned_core(get_bin_wlist(~l2), l1);
    }

    struct bin_lt {
        bool operator()(watched const & w1, watched const & w2) const {
            if (!w1.is_binary_clause()) return false;
            if (!w2.is_binary_clause()) return true;
            unsigned l1_idx = w1.get_literal().index();
            unsigned l2_idx = w2.get_literal().index();
            if (l1_idx < l2_idx) return true;
            if (l1_idx == l2_idx && !w1.is_learned() && w2.is_learned()) return true;
            return false;
        }
    };

    /**
       \brief Eliminate duplicated binary clauses.
    */
    void simplifier::elim_dup_bins() {
#ifdef _TRACE
        unsigned l_idx = 0;
#endif
        unsigned elim = 0;
        for (watch_list & bwlist : s.m_bin_watches) {
            checkpoint();
            // All entries in m_bin_watches are binary, so just sort by literal
            std::stable_sort(bwlist.begin(), bwlist.end(), bin_lt());
            literal last_lit   = null_literal;
            watch_list::iterator it    = bwlist.begin();
            watch_list::iterator itprev = it;
            watch_list::iterator end   = bwlist.end();
            for (; it != end; ++it) {
                SASSERT(it->is_binary_clause());
                if (it->get_literal() == last_lit) {
                    TRACE(subsumption, tout << "eliminating: " << ~to_literal(l_idx)
                          << " " << it->get_literal() << "\n";);
                    elim++;
                }
                else {
                    last_lit = it->get_literal();
                    *itprev = *it;
                    itprev++;
                }
            }
            bwlist.set_end(itprev);
            TRACE_CODE(l_idx++;);
        }
        m_num_subsumed += elim/2; // each binary clause is "eliminated" twice.
    }

    struct simplifier::subsumption_report {
        simplifier & m_simplifier;
        stopwatch    m_watch;
        unsigned     m_num_subsumed;
        unsigned     m_num_sub_res;
        subsumption_report(simplifier & s):
            m_simplifier(s),
            m_num_subsumed(s.m_num_subsumed),
            m_num_sub_res(s.m_num_sub_res) {
            m_watch.start();
        }

        ~subsumption_report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL,
                       verbose_stream() << " (sat-subsumer :subsumed "
                       << (m_simplifier.m_num_subsumed - m_num_subsumed)
                       << " :subsumption-resolution " << (m_simplifier.m_num_sub_res - m_num_sub_res)
                       << " :threshold " << m_simplifier.m_sub_counter
                       << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }
    };

    void simplifier::subsume() {
        subsumption_report rpt(*this);
        elim_dup_bins();
        subsume_with_binaries();
        TRACE(subsumption_bug, s.display(tout););
        while (true) {
            TRACE(subsumption, tout << "sub_todo size: " << m_sub_todo.size() << "\n";);

            m_sub_counter -= m_sub_bin_todo.size();
            while (!m_sub_bin_todo.empty()) {
                checkpoint();
                m_dummy.set(m_sub_bin_todo.back());
                m_sub_bin_todo.pop_back();
                clause & c = *(m_dummy.get());
                bool was_learned = c.is_learned();
                back_subsumption1(c);
                if (was_learned && !c.is_learned()) {
                    mark_as_not_learned(c[0], c[1]);
                }
            }

            checkpoint();

            TRACE(subsumption_bug, s.display(tout););

            if (m_sub_todo.empty()) {
                m_last_sub_trail_sz = s.m_trail.size();
                break;
            }

            if (m_sub_counter < 0)
                break;

            clause & c = m_sub_todo.erase();

            // Per-variable subsume filter (CaDiCaL-style): skip clauses
            // that share fewer than 2 variables with recently-changed
            // clauses.  Such clauses are unlikely to find new subsumption
            // targets, saving significant work in later inprocessing rounds.
            if (!c.strengthened() && !has_subsume_overlap(c)) {
                continue;
            }

            c.unmark_strengthened();
            m_sub_counter--;
            TRACE(subsumption, tout << "next: " << c << "\n";);
            if (s.m_trail.size() > m_last_sub_trail_sz) {
                unsigned sz0 = c.size();
                if (cleanup_clause(c)) {
                    remove_clause(c, true);
                    continue;
                }
                unsigned sz = c.size();
                switch (sz) {
                case 0:
                    s.set_conflict();
                    return;
                case 1:
                    c.restore(sz0);
                    propagate_unit(c[0]);
                    // unit propagation removes c
                    continue;
                case 2:
                    TRACE(subsumption, tout << "clause became binary: " << c << "\n";);
                    s.mk_bin_clause(c[0], c[1], c.is_learned());
                    m_sub_bin_todo.push_back(bin_clause(c[0], c[1], c.is_learned()));
                    c.restore(sz0);
                    remove_clause(c, sz != sz0);
                    continue;
                default:
                    break;
                }
            }
            // Fast binary subsumption/strengthening before full use-list scan.
            // If the clause is subsumed by a binary, skip the expensive back_subsumption1.
            // If strengthened, the clause may shrink; re-enter the loop for further checks.
            if (c.size() > 2 && try_subsume_by_binary(c)) {
                // c was subsumed by a binary -- already removed
                continue;
            }
            if (c.was_removed())
                continue;
            if (s.inconsistent())
                return;

            TRACE(subsumption, tout << "using: " << c << "\n";);
            back_subsumption1(c);
        }
    }

    struct simplifier::blocked_clause_elim {
        class literal_lt {
            use_list const &   m_use_list;
            vector<watch_list> const & m_watches;
            vector<watch_list> const & m_bin_watches;
        public:
            literal_lt(use_list const & l, vector<watch_list> const & ws, vector<watch_list> const & bws):m_use_list(l), m_watches(ws), m_bin_watches(bws) {}

            unsigned weight(unsigned l_idx) const {
                return 2*m_use_list.get(~to_literal(l_idx)).size() + m_watches[l_idx].size() + m_bin_watches[l_idx].size();
            }

            bool operator()(unsigned l_idx1, unsigned l_idx2) const {
                return weight(l_idx1) < weight(l_idx2);
            }
        };

        class clause_ante {
            bool    m_from_ri;
            literal m_lit1;
            literal m_lit2;
            clause* m_clause;
        public:
            clause_ante():
                m_from_ri(false), m_lit1(null_literal), m_lit2(null_literal), m_clause(nullptr) {}
            clause_ante(literal l1, bool from_ri):
                m_from_ri(from_ri), m_lit1(l1), m_lit2(null_literal), m_clause(nullptr) {}
            clause_ante(literal l1, literal l2):
                m_from_ri(false), m_lit1(l1), m_lit2(l2), m_clause(nullptr) {}
            clause_ante(clause& c):
                m_from_ri(false), m_lit1(null_literal), m_lit2(null_literal), m_clause(&c) {}            
            literal lit1() const { return m_lit1; }
            literal lit2() const { return m_lit2; }
            clause* cls() const { return m_clause; }
            bool from_ri() const { return m_from_ri; }
            bool operator==(clause_ante const& a) const {
                return a.m_lit1 == m_lit1 && a.m_lit2 == m_lit2 && a.m_clause == m_clause;
            }
            std::ostream& display(std::ostream& out, literal lit) const {
                if (cls()) {
                    out << *cls() << " ";
                }
                else {
                    out << "(" << ~lit;
                }
                if (lit1() != null_literal) {
                    out << " " << lit1();
                }
                if (lit2() != null_literal) {
                    out << " " << lit2();
                }
                if (!cls()) out << ")";
                if (from_ri()) out << "ri";
                out << "\n";
                return out;
            }
        };

        class queue {
            heap<literal_lt> m_queue;
        public:
            queue(use_list const & l, vector<watch_list> const & ws, vector<watch_list> const & bws):m_queue(128, literal_lt(l, ws, bws)) {}
            void insert(literal l) {
                unsigned idx = l.index();
                m_queue.reserve(idx + 1);
                SASSERT(!m_queue.contains(idx));
                m_queue.insert(idx);
            }
            void decreased(literal l) {
                unsigned idx = l.index();
                if (m_queue.contains(idx))
                    m_queue.decreased(idx);
                else 
                    m_queue.insert(idx);
            }
            literal next() { SASSERT(!empty()); return to_literal(m_queue.erase_min()); }
            bool empty() const { return m_queue.empty(); }
            void reset() { m_queue.reset(); }
            unsigned size() const { return m_queue.size(); }
        };

        simplifier &      s;
        int               m_counter;
        model_converter & m_mc;
        queue             m_queue;

        literal_vector m_covered_clause;              // covered clause
        svector<clause_ante> m_covered_antecedent;    // explanations for literals in covered clause
        literal_vector m_intersection;                // current resolution intersection
        literal_vector m_tautology;                   // literals that are used in blocking tautology
        literal_vector m_new_intersection;
        bool_vector  m_in_intersection;
        unsigned       m_ala_qhead;
        clause_wrapper m_clause;
        unsigned       m_ala_cost;
        unsigned       m_ala_benefit;
        unsigned       m_ala_max_cost;
        bool_vector    m_mark2;
        literal_vector m_mark2_stack;

        blocked_clause_elim(simplifier & _s, unsigned limit, model_converter & _mc, use_list & l,
                            vector<watch_list> & wlist, vector<watch_list> & bwlist):
            s(_s),
            m_counter(limit),
            m_mc(_mc),
            m_queue(l, wlist, bwlist),
            m_clause(null_literal, null_literal),
            m_ala_cost(0),
            m_ala_benefit(0) {
            m_in_intersection.resize(s.s.num_vars() * 2, false);
            m_mark2.resize(s.s.num_vars() * 2, false);
            m_ala_max_cost = (s.s.m_clauses.size() * s.m_num_calls)/5;
        }

        void insert(literal l) {
            SASSERT(process_var(l.var()));
            m_queue.insert(l);
        }

        bool process_var(bool_var v) {
            return !s.s.is_assumption(v) && !s.was_eliminated(v) && !s.is_external(v) && s.value(v) == l_undef;
        }

        // Secondary marking for candidate filtering (Opt C) and impossible pre-check (Opt B).
        // Uses m_mark2 bitvector indexed by literal index, with m_mark2_stack for O(1) cleanup.
        void set_mark2(literal l) {
            unsigned idx = l.index();
            if (!m_mark2[idx]) {
                m_mark2[idx] = true;
                m_mark2_stack.push_back(l);
            }
        }
        bool is_marked2(literal l) const { return m_mark2[l.index()]; }
        void reset_mark2() {
            for (literal l : m_mark2_stack) m_mark2[l.index()] = false;
            m_mark2_stack.reset();
        }

        bool reached_max_cost() {
            return m_ala_benefit <= m_ala_cost * 100 && m_ala_cost > m_ala_max_cost;
        }

        enum elim_type {
            bce_t,
            cce_t,
            acce_t,
            abce_t,
            ate_t,
            no_t
        };

        void operator()() {
            if (s.acce_enabled()) {
                cce<acce_t>();
            }
            if (s.ate_enabled() && !s.abce_enabled() && !s.acce_enabled()) {
                cce<ate_t>();
            }
            if (s.cce_enabled() && !s.acce_enabled()) {
                cce<cce_t>();
            }
            if (s.abce_enabled() && !s.acce_enabled()) {
                cce<abce_t>();
            }
            if (s.bce_enabled() && !s.cce_enabled() && !s.abce_enabled()) {
                cce<bce_t>();
            }
            if (s.bca_enabled()) {
                bca();
            }
        }

        void insert_queue() {
            m_queue.reset();
            unsigned num_vars = s.s.num_vars();
            for (bool_var v = 0; v < num_vars; ++v) {
                if (process_var(v)) {
                    insert(literal(v, false));
                    insert(literal(v, true));
                }
            }
        }

        void reset_intersection() {
            for (literal l : m_intersection) m_in_intersection[l.index()] = false;
            m_intersection.reset();
        }

        void add_intersection(literal lit) {
            m_intersection.push_back(lit);
            m_in_intersection[lit.index()] = true;
        }        
        
        //
        // Resolve intersection
        // Find literals that are in the intersection of all resolvents with l.
        //
        bool resolution_intersection(literal l, bool adding) {
            unsigned tsz = m_tautology.size();
            reset_intersection();
            if (!process_var(l.var())) return false;
            bool first = true;
            VERIFY(s.value(l) == l_undef);
            for (watched & w : s.get_bin_wlist(l)) {
                // when adding a blocked clause, then all non-learned clauses have to be considered for the
                // resolution intersection.
                bool process_bin = adding ? w.is_binary_clause() : w.is_binary_non_learned_clause();
                if (process_bin) {
                    literal lit = w.get_literal();
                    if (s.is_marked(~lit) && lit != ~l) {
                        m_tautology.push_back(~lit);
                        continue; // tautology
                    }
                    if (!first || s.is_marked(lit)) {
                        reset_intersection();
                        m_tautology.shrink(tsz);
                        return false; // intersection is empty or does not add anything new.
                    }
                    first = false;
                    SASSERT(m_intersection.empty());
                    add_intersection(lit);
                }
            }
            clause_use_list & neg_occs = s.m_use_list.get(~l);
            for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
                bool tautology = false;
                clause & c = it.curr();
                if (c.is_learned() && !adding) continue;
                if (c.was_removed()) continue;
                for (literal lit : c) {
                    if (s.is_marked(~lit) && lit != ~l) {
                        m_tautology.push_back(~lit);
                        tautology = true;
                        break;
                    }
                }
                if (!tautology) {
                    if (first) {
                        for (literal lit : c) 
                            if (lit != ~l && !s.is_marked(lit)) 
                                add_intersection(lit);
                        first = false;
                    }
                    else {
                        m_new_intersection.reset();
                        for (literal lit : c) 
                            if (m_in_intersection[lit.index()]) 
                                m_new_intersection.push_back(lit);
                        reset_intersection();
                        for (literal lit : m_new_intersection) 
                            add_intersection(lit);
                    }
                    if (m_intersection.empty()) {
                        // Move-to-front heuristic (CaDiCaL): move the clause that
                        // caused the intersection to become empty to the front of
                        // the occurrence list so it is found faster next time.
                        neg_occs.move_to_front(c);
                        m_tautology.shrink(tsz);
                        return false;
                    }
                }
            }
            // remove tautology literals if literal has no resolution intersection
            if (m_intersection.empty() && !first) {
                m_tautology.shrink(tsz);
            }
            return first;
        }

        // Candidate filtering (CaDiCaL block_candidates adaptation).
        // For pivot literal l in clause c = m_covered_clause[0..sz0):
        // Mark all literals appearing in clauses containing ~l (the "negative" clauses).
        // Then check: does any literal in c (other than l) have its negation in the mark set?
        // If not, no resolvent of c on l can be tautological, so l is not a viable pivot.
        bool is_viable_pivot(literal l, unsigned sz0) {
            if (!process_var(l.var())) return false;
            // Mark all literals in binary clauses ~l \/ lit (watch list of l).
            for (watched & w : s.get_bin_wlist(l)) {
                if (w.is_binary_non_learned_clause())
                    set_mark2(w.get_literal());
            }
            // Mark all literals in long clauses containing ~l.
            clause_use_list & neg_occs = s.m_use_list.get(~l);
            for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
                clause & c = it.curr();
                if (c.is_learned() || c.was_removed()) continue;
                for (literal lit : c)
                    if (lit != ~l) set_mark2(lit);
            }
            // Check if any literal in the candidate clause has its negation marked.
            bool viable = false;
            for (unsigned i = 0; i < sz0; ++i) {
                literal lit = m_covered_clause[i];
                if (lit != l && is_marked2(~lit)) {
                    viable = true;
                    break;
                }
            }
            reset_mark2();
            return viable;
        }

        // Impossible pre-check (CaDiCaL block_impossible adaptation).
        // Given pivot l and clause c already marked via s.mark_visited:
        // Check if there exists a clause containing ~l where NO literal (other than ~l)
        // has its negation in c. Such a clause produces a non-tautological resolvent,
        // making it impossible to block c on l.
        bool is_impossible_pivot(literal l) {
            if (!process_var(l.var())) return true;
            // Binary clauses: ~l \/ lit. Non-tautological iff ~lit not in c.
            for (watched & w : s.get_bin_wlist(l)) {
                if (w.is_binary_non_learned_clause()) {
                    if (!s.is_marked(~w.get_literal()))
                        return true;
                }
            }
            // Long clauses containing ~l.
            clause_use_list & neg_occs = s.m_use_list.get(~l);
            for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
                clause & c = it.curr();
                if (c.is_learned() || c.was_removed()) continue;
                bool has_complement = false;
                for (literal lit : c) {
                    if (lit != ~l && s.is_marked(~lit)) {
                        has_complement = true;
                        break;
                    }
                }
                if (!has_complement) {
                    neg_occs.move_to_front(c);
                    return true;
                }
            }
            return false;
        }

        bool check_abce_tautology(literal l) {
            unsigned tsz = m_tautology.size();
            if (!process_var(l.var())) return false;
            for (watched & w : s.get_bin_wlist(l)) {
                if (w.is_binary_non_learned_clause()) {
                    literal lit = w.get_literal();
                    VERIFY(lit != ~l);
                    if (!s.is_marked(~lit)) {
                        m_tautology.shrink(tsz);
                        return false;
                    }
                    m_tautology.push_back(~lit);
                }
            }
            clause_use_list & neg_occs = s.m_use_list.get(~l);
            for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
                clause & c = it.curr();
                if (c.is_learned() || c.was_removed()) continue;
                bool tautology = false;
                for (literal lit : c) {
                    if (s.is_marked(~lit) && lit != ~l) {
                        tautology = true;
                        m_tautology.push_back(~lit);
                        break;
                    }
                }
                if (!tautology) {
                    // Move-to-front: this clause prevents blocking on l.
                    neg_occs.move_to_front(c);
                    m_tautology.shrink(tsz);
                    return false;
                }
            }
            return true;
        }

        bool revisit_binary(literal l1, literal l2) const {
            return m_clause.is_binary() && 
                ((m_clause[0] == l1 && m_clause[1] == l2) ||
                 (m_clause[0] == l2 && m_clause[1] == l1));
        }

        bool revisit_clause(clause const& c) const {
            return !m_clause.is_binary() && (m_clause.get_clause() == &c);
        }

        /**
           \brief idx is the index of the blocked literal.
           m_tautology contains literals that were used to establish that the current members of m_covered_clause is blocked.
           This routine removes literals that were not relevant to establishing it was blocked.

           It has a bug: literals that are used to prune tautologies during resolution intersection should be included
           in the dependencies. They may get used in some RI prunings and then they have to be included to avoid flipping
           RI literals.
         */
        void minimize_covered_clause(unsigned idx) {
            for (literal l : m_tautology) VERIFY(s.is_marked(l));
            for (literal l : m_covered_clause) s.unmark_visited(l);
            for (literal l : m_tautology) s.mark_visited(l);
            s.mark_visited(m_covered_clause[idx]);
            for (unsigned i = 0; i < m_covered_clause.size(); ++i) {
                literal lit = m_covered_clause[i];
                if (m_covered_antecedent[i] == clause_ante()) s.mark_visited(lit);
                if (s.is_marked(lit)) idx = i; 
            }
            for (unsigned i = idx; i > 0; --i) {
                literal lit = m_covered_clause[i];
                if (!s.is_marked(lit)) continue;
                clause_ante const& ante = m_covered_antecedent[i];
                if (ante.cls()) {
                    for (literal l : *ante.cls()) {
                        if (l != ~lit) s.mark_visited(l);
                    }
                }
                if (ante.lit1() != null_literal) {
                    s.mark_visited(ante.lit1());
                }
                if (ante.lit2() != null_literal) {
                    s.mark_visited(ante.lit2());
                }
            }
            unsigned j = 0;
            literal blocked = null_literal;
            for (unsigned i = 0; i <= idx; ++i) {
                literal lit = m_covered_clause[i];
                if (s.is_marked(lit)) {
                    // 
                    // Record that the resolving literal for 
                    // resolution intersection can be flipped.
                    // 
                    clause_ante const& ante = m_covered_antecedent[i];
                    if (ante.from_ri() && blocked != ante.lit1()) {
                        blocked = ante.lit1();
                        VERIFY(s.value(blocked) == l_undef);
                        m_mc.stackv().push_back(std::make_pair(j, blocked));
                    }
                    m_covered_clause[j++] = lit;
                    s.unmark_visited(lit);
                }
            }
            for (literal l : m_covered_clause) VERIFY(!s.is_marked(l)); 
            for (bool_var v = 0; v < s.s.num_vars(); ++v) VERIFY(!s.is_marked(literal(v, true)) && !s.is_marked(literal(v, false)));

            // unsigned sz0 = m_covered_clause.size();
            m_covered_clause.resize(j);
            VERIFY(j >= m_clause.size());
        }

        /*
         * C \/ l     l \/ lit
         * -------------------
         *    C \/ l \/ ~lit
         *
         * C \/ lit \/ l   l \/ lit
         * ------------------------
         *        l \/ lit              C \/ lit \/ l can be removed
         *
         * C \/ l1 \/ ... \/ lk     l1 \/ ... \/ lk \/ lit
         * -----------------------------------------------
         *      C \/ l1 \/ ... \/ lk \/ ~lit
         * unless C contains lit, and it is a tautology.
         */
        bool add_ala() {
            unsigned init_size = m_covered_clause.size();
            for (; m_ala_qhead < m_covered_clause.size() && m_ala_qhead < 5*init_size && !reached_max_cost(); ++m_ala_qhead) {
                ++m_ala_cost;
                literal l = m_covered_clause[m_ala_qhead];
                for (watched & w : s.get_bin_wlist(~l)) {
                    if (w.is_binary_non_learned_clause()) {
                        literal lit = w.get_literal();
                        if (revisit_binary(l, lit)) continue;
                        if (s.is_marked(lit)) {
                            ++m_ala_benefit;
                            return true;
                        }
                        if (!s.is_marked(~lit)) {
                            m_covered_clause.push_back(~lit);
                            m_covered_antecedent.push_back(clause_ante(l, false));
                            s.mark_visited(~lit);
                        }
                    }
                }
                clause_use_list & pos_occs = s.m_use_list.get(l);
                clause_use_list::iterator it = pos_occs.mk_iterator();
                for (; !it.at_end(); it.next()) {
                    clause & c = it.curr();
                    if (c.is_learned() || c.was_removed()) continue;
                    if (revisit_clause(c)) continue;
                    literal lit1 = null_literal;
                    bool ok = true;
                    for (literal lit : c) {
                        if (lit == l) continue;
                        if (s.is_marked(lit)) continue;
                        if (!s.is_marked(~lit) && lit1 == null_literal) {
                            lit1 = lit;
                        }
                        else {
                            ok = false;
                            break;
                        }
                    }
                    if (!ok) continue;
                    if (lit1 == null_literal) {
                        ++m_ala_benefit;
                        return true;
                    }
                    m_covered_clause.push_back(~lit1);
                    m_covered_antecedent.push_back(clause_ante(c));
                    s.mark_visited(~lit1);
                }
            }
            return false;
        }


        /*
         *  C \/ l    ~l \/ lit \/ D_i   for i = 1...N all the clauses that have ~l
         *  -------------------------
         *      C \/ l \/ lit
         *
         *
         */
        bool add_cla(literal& blocked) {
            for (unsigned i = 0; i < m_covered_clause.size(); ++i) {
                literal lit = m_covered_clause[i];
                if (resolution_intersection(lit, false)) {
                    blocked = m_covered_clause[i];                    
                    minimize_covered_clause(i);
                    return true;
                }
                for (literal l : m_intersection) {
                    if (!s.is_marked(l)) {
                        s.mark_visited(l);
                        m_covered_clause.push_back(l);
                        m_covered_antecedent.push_back(clause_ante(lit, true));
                    }
                }
            }
            return false;
        }

        bool above_threshold(unsigned sz0) const {
            return sz0 * 400 < m_covered_clause.size();
        }

        void reset_mark() {
            for (literal l : m_covered_clause) s.unmark_visited(l);
        }

        template<elim_type et>
        elim_type cce(literal& blocked, model_converter::kind& k) {
            bool first = true;
            unsigned sz = 0, sz0 = m_covered_clause.size();     
            for (literal l : m_covered_clause) s.mark_visited(l);
            shuffle<literal>(m_covered_clause.size(), m_covered_clause.data(), s.s.m_rand);
            m_tautology.reset();
            m_mc.stackv().reset();
            m_ala_qhead = 0;

            switch (et) {
            case cce_t:
                k = model_converter::CCE;
                break;
            case acce_t:
                k = model_converter::ACCE;
                break;
            default:
                k = model_converter::BCE;
                break;
            }

            /*
             * For blocked clause elimination with asymmetric literal addition (ABCE) 
             * it suffices to check if one of the original
             * literals in the clause is blocked modulo the additional literals added to the clause.
             * So we record sz0, the original set of literals in the clause, mark additional literals, 
             * and then check if any of the first sz0 literals are blocked.
             */

            if (et == ate_t) {
                bool ala = add_ala();
                reset_mark();
                m_covered_clause.shrink(sz0);
                return ala ? ate_t : no_t;
            }

            while (m_covered_clause.size() > sz && !above_threshold(sz0)) {

                if ((et == abce_t || et == acce_t) && add_ala()) {
                    reset_mark();
                    if (first) {
                        m_covered_clause.shrink(sz0);
                    }
                    else {
                        /*
                         * tautology depends on resolution intersection. 
                         * literals used for resolution intersection may have to be flipped.
                         */
                        for (literal l : m_covered_clause) {
                            m_tautology.push_back(l);
                            s.mark_visited(l);
                        }
                        minimize_covered_clause(m_covered_clause.size()-1);
                    }
                    return ate_t;                               
                }

                if (first) {
                    for (unsigned i = 0; i < sz0; ++i) {
                        literal l = m_covered_clause[i];
                        // Candidate filtering (CaDiCaL): skip if l is not a viable
                        // pivot, i.e., no literal in the clause has its negation in
                        // any negative clause of ~l.
                        if (et == bce_t && !is_viable_pivot(l, sz0))
                            continue;
                        // Impossible pre-check (CaDiCaL): if some negative clause of ~l
                        // has no complement in the candidate clause, blocking is impossible.
                        if (et == bce_t && is_impossible_pivot(l))
                            continue;
                        if (check_abce_tautology(l)) {
                            blocked = l;
                            reset_mark();
                            m_covered_clause.shrink(sz0);
                            if (et == bce_t) return bce_t;
                            k = model_converter::ABCE;
                            return abce_t;
                        }
                    }
                }
                first = false;
                
                if (et == abce_t || et == bce_t) {
                    break;
                }
                
                /*
                 * Add resolution intersection while checking if the clause becomes a tautology.
                 */
                sz = m_covered_clause.size();
                if ((et == cce_t || et == acce_t) && add_cla(blocked)) {
                    reset_mark();
                    return et;
                }
            }
            reset_mark();
            return no_t;
        }

        // perform covered clause elimination.
        // first extract the covered literal addition (CLA).
        // then check whether the CLA is blocked.
        template<elim_type et>
        elim_type cce(clause& c, literal& blocked, model_converter::kind& k) {
            m_clause = clause_wrapper(c);
            m_covered_clause.reset();
            m_covered_antecedent.reset();
            for (literal l : c) { 
                m_covered_clause.push_back(l);
                m_covered_antecedent.push_back(clause_ante());
            }
            return cce<et>(blocked, k);
        }

        template<elim_type et>
        elim_type cce(literal l1, literal l2, literal& blocked, model_converter::kind& k) {
            m_clause = clause_wrapper(l1, l2);
            m_covered_clause.reset();
            m_covered_antecedent.reset();
            m_covered_clause.push_back(l1);
            m_covered_clause.push_back(l2);
            m_covered_antecedent.push_back(clause_ante());
            m_covered_antecedent.push_back(clause_ante());
            return cce<et>(blocked, k);            
        }
        
        template<elim_type et>
        void cce() {
            insert_queue();
            // CaDiCaL-style: reset covered flags at the start of each CCE epoch
            // so that clauses become eligible for re-evaluation after structural
            // changes from the previous round (e.g., new unit propagations).
            for (clause* cp : s.s.m_clauses)
                cp->set_covered(false);
            cce_clauses<et>();
            cce_binary<et>();
        }

        template<elim_type et>
        void cce_binary() {
            m_ala_cost = 0;
            m_ala_benefit = 0;
            while (!m_queue.empty() && m_counter >= 0 && !reached_max_cost()) {
                s.checkpoint();
                process_cce_binary<et>(m_queue.next());
            }
        }

        template<elim_type et>
        void process_cce_binary(literal l) {
            literal blocked = null_literal;
            watch_list & wlist = s.get_bin_wlist(~l);
            m_counter -= wlist.size();
            model_converter::kind k;
            for (watched& w : wlist) {
                if (!w.is_binary_non_learned_clause()) continue;
                if (!select_clause<et>(2)) continue;
                literal l2 = w.get_literal();
                elim_type r = cce<et>(l, l2, blocked, k); 
                inc_bc(r);
                switch (r) {
                case ate_t:
                    w.set_learned(true);
                    s.s.set_learned1(l2, l, true);
                    m_mc.add_ate(m_covered_clause);
                    break;
                case no_t:
                    break;
                default:
                    w.set_learned(true);
                    s.s.set_learned1(l2, l, true);
                    block_covered_binary(w, l, blocked, k);
                    break;
                }
                s.checkpoint();
            }
        }

        template<elim_type et>
        void cce_clauses() {
            literal blocked;
            m_ala_cost = 0;
            m_ala_benefit = 0;
            model_converter::kind k;
            unsigned start = s.s.m_rand(); 
            unsigned sz = s.s.m_clauses.size();
            for (unsigned i = 0; i < sz; ++i) {
                clause& c = *s.s.m_clauses[(i + start) % sz];
                if (c.was_removed() || c.is_learned()) continue;
                // CaDiCaL-style: skip clauses already tried in this CCE epoch
                if (c.is_covered()) continue;
                if (!select_clause<et>(c.size())) continue;
                c.set_covered(true);
                elim_type r = cce<et>(c, blocked, k);
                inc_bc(r);
                switch (r) {
                case ate_t:
                    m_mc.add_ate(m_covered_clause);
                    s.set_learned(c);                    
                    break;
                case no_t:
                    break;
                default:
                    block_covered_clause(c, blocked, k);
                    s.set_learned(c);
                    break;
                }
                s.checkpoint();
                if (reached_max_cost()) {
                    break;
                }
            }            
        }

        void inc_bc(elim_type et) {
            switch (et) {
            case cce_t: s.m_num_cce++; break;
            case acce_t: s.m_num_acce++; break;
            case abce_t: s.m_num_abce++; break;
            case ate_t: s.m_num_ate++; break;
            case bce_t: s.m_num_bce++; break;
            default: break;
            }
        }

        // select 25% of clauses size 2, 3
        // always try to remove larger clauses.
        template<elim_type et>
        bool select_clause(unsigned sz) {
            return (sz > 3) || s.s.m_rand(4) == 0;
        }

        void block_covered_clause(clause& c, literal l, model_converter::kind k) {
            TRACE(blocked_clause, tout << "new blocked clause: " << c << "\n";);
            SASSERT(!s.is_external(l));
            model_converter::entry& new_entry = m_mc.mk(k, l.var());
            for (literal lit : c) {
                if (lit != l && process_var(lit.var())) 
                    m_queue.decreased(~lit);                
            }
            m_mc.insert(new_entry, m_covered_clause);
            m_mc.set_clause(new_entry, c);
        }
        
        void block_covered_binary(watched const& w, literal l1, literal blocked, model_converter::kind k) {
            SASSERT(!s.is_external(blocked));
            model_converter::entry& new_entry = m_mc.mk(k, blocked.var());
            literal l2 = w.get_literal();
            TRACE(blocked_clause, tout << "new blocked clause: " << l2 << " " << l1 << "\n";);
            s.set_learned(l1, l2);
            m_mc.insert(new_entry, m_covered_clause);
            m_mc.set_clause(new_entry, l1, l2);
            if (process_var(l2.var()))
                m_queue.decreased(~l2);
        }

        void bca() {
            m_queue.reset();
            insert_queue();
            while (!m_queue.empty() && m_counter >= 0) {
                s.checkpoint();
                bca(m_queue.next());
            }
        }

        /*
          \brief blocked binary clause addition for literal l
          Let RI be the resolution intersection with l, e.g, RI are the literals
          that are in all clauses of the form ~l \/ C.
          If RI is non-empty, then let l' be a literal in RI.
          Then the following binary clause is blocked: l \/ ~l'
         */
        void bca(literal l) {
            m_tautology.reset();
            if (resolution_intersection(l, true)) {
                // this literal is pure. 
                return;
            }
            for (literal l2 : m_intersection) {
                watched* w = find_binary_watch(s.get_bin_wlist(~l), ~l2);
                if (!w) {
                    s.s.mk_bin_clause(l, ~l2, true);
                    ++s.m_num_bca;
                }
            }
        }

        bool all_tautology(literal l) {
            watch_list & wlist = s.get_bin_wlist(l);
            m_counter -= wlist.size();
            for (auto const& w : wlist) {
                if (w.is_binary_non_learned_clause() &&
                    !s.is_marked(~w.get_literal()))
                    return false;
            }

            clause_use_list & neg_occs = s.m_use_list.get(~l);
            clause_use_list::iterator it = neg_occs.mk_iterator();
            for (; !it.at_end(); it.next()) {
                clause & c = it.curr();
                if (c.is_learned()) continue;
                if (c.was_removed()) continue;
                m_counter -= c.size();
                unsigned sz = c.size();
                unsigned i;
                for (i = 0; i < sz; ++i) {
                    if (s.is_marked(~c[i]))
                        break;
                }
                if (i == sz) {
                    // Move-to-front: this clause prevents blocking on l.
                    neg_occs.move_to_front(c);
                    return false;
                }
            }

            if (s.s.m_ext) {
                ext_constraint_list const& ext_list = s.m_ext_use_list.get(~l);
                for (ext_constraint_idx idx : ext_list) {
                    if (!s.s.m_ext->is_blocked(l, idx)) {
                        return false;
                    }
                }
            }
            return true;
        }
    };

    struct simplifier::blocked_cls_report {
        simplifier & m_simplifier;
        stopwatch    m_watch;
        unsigned     m_num_bce;
        unsigned     m_num_cce;
        unsigned     m_num_acce;
        unsigned     m_num_abce;
        unsigned     m_num_ate;
        unsigned     m_num_bca;
        blocked_cls_report(simplifier & s):
            m_simplifier(s),
            m_num_bce(s.m_num_bce),
            m_num_cce(s.m_num_cce),
            m_num_acce(s.m_num_acce),
            m_num_abce(s.m_num_abce),
            m_num_ate(s.m_num_ate),
            m_num_bca(s.m_num_bca) {
            m_watch.start();
        }

        ~blocked_cls_report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL,
                       verbose_stream() << " (sat-blocked-clauses";
                       report(m_simplifier.m_num_ate,  m_num_ate,  " :ate ");
                       report(m_simplifier.m_num_bce,  m_num_bce,  " :bce ");
                       report(m_simplifier.m_num_abce, m_num_abce, " :abce ");
                       report(m_simplifier.m_num_cce,  m_num_cce,  " :cce ");
                       report(m_simplifier.m_num_bca,  m_num_bca,  " :bca ");
                       report(m_simplifier.m_num_acce, m_num_acce, " :acce ");
                       verbose_stream() << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }

        void report(unsigned n, unsigned m, char const* s) {
            if (n > m) verbose_stream() << s << (n - m);
        }
    };

    void simplifier::elim_blocked_clauses() {
        TRACE(blocked_clause_bug, tout << "trail: " << s.m_trail.size() << "\n"; s.display_watches(tout); s.display(tout););
        blocked_cls_report rpt(*this);
        blocked_clause_elim elim(*this, m_blocked_clause_limit, s.m_mc, m_use_list, s.m_watches, s.m_bin_watches);
        elim();
    }

    bool simplifier::elim_blocked_clauses_tracked() {
        unsigned old_bce  = m_num_bce;
        unsigned old_cce  = m_num_cce;
        unsigned old_acce = m_num_acce;
        unsigned old_abce = m_num_abce;
        unsigned old_ate  = m_num_ate;
        elim_blocked_clauses();
        unsigned blocked = (m_num_bce - old_bce) + (m_num_cce - old_cce) +
                           (m_num_acce - old_acce) + (m_num_abce - old_abce) +
                           (m_num_ate - old_ate);
        if (blocked > 0) {
            for (bool_var v = 0; v < s.num_vars(); ++v) {
                if (!s.m_eliminated[v] && !is_external(v) && value(v) == l_undef)
                    insert_elim_todo(v);
            }
        }
        return blocked > 0;
    }

    unsigned simplifier::num_nonlearned_bin(literal l) const {
        unsigned r = 0;
        watch_list const & wlist = get_bin_wlist(~l);
        for (auto & w : wlist) {
            if (w.is_binary_non_learned_clause())
                r++;
        }
        return r;
    }

    unsigned simplifier::get_to_elim_cost(bool_var v) const {
        literal pos_l(v, false);
        literal neg_l(v, true);
        unsigned num_pos = m_use_list.get(pos_l).size();
        unsigned num_neg = m_use_list.get(neg_l).size();
        unsigned num_bin_pos = num_nonlearned_bin(pos_l);
        unsigned num_bin_neg = num_nonlearned_bin(neg_l);
        unsigned cost = 2 * num_pos * num_neg + num_pos * num_bin_neg + num_neg * num_bin_pos;
        CTRACE(sat_simplifier, cost == 0, tout << v << " num_pos: " << num_pos << " num_neg: " << num_neg << " num_bin_pos: " << num_bin_pos
               << " num_bin_neg: " << num_bin_neg << " cost: " << cost << "\n";);
        return cost;
    }

    // -------------------------------------------------------
    // Dynamic elimination heap (CaDiCaL-style).
    //
    // Comparator for the min-heap: lower cost = higher priority.
    // Ties broken by variable index (lower first) for determinism.
    // -------------------------------------------------------

    bool simplifier::elim_cost_lt::operator()(int v1, int v2) const {
        unsigned c1 = m_simp->m_elim_costs[v1];
        unsigned c2 = m_simp->m_elim_costs[v2];
        if (c1 != c2) return c1 < c2;
        return v1 < v2;
    }

    void simplifier::elim_heap_update_var(bool_var v) {
        if (was_eliminated(v) || is_external(v) || value(v) != l_undef)
            return;
        if (static_cast<unsigned>(v) >= m_elim_costs.size())
            return;
        unsigned new_cost = get_to_elim_cost(v);
        m_elim_costs[v] = new_cost;
        if (m_elim_heap.contains(v)) {
            // Re-position in heap based on updated cost.
            // erase + re-insert is O(log n) and always correct.
            m_elim_heap.erase(v);
            m_elim_heap.insert(v);
        }
        else {
            // Variable not in heap -- reschedule it (CaDiCaL-style).
            // When a neighbor's occurrence counts change due to an
            // elimination, it may become newly eliminable.
            m_elim_heap.insert(v);
        }
    }

    void simplifier::mark_elim_heap_dirty(bool_var v) {
        if (!was_eliminated(v) && !is_external(v) && value(v) == l_undef)
            m_elim_heap_dirty.insert(v);
    }

    void simplifier::flush_elim_heap_dirty() {
        for (bool_var v : m_elim_heap_dirty)
            elim_heap_update_var(v);
        m_elim_heap_dirty.reset();
    }

    typedef std::pair<bool_var, unsigned> bool_var_and_cost;

    struct bool_var_and_cost_lt {
        bool operator()(bool_var_and_cost const & p1, bool_var_and_cost const & p2) const { return p1.second < p2.second; }
    };

    void simplifier::order_vars_for_elim(bool_var_vector & r) {
        svector<bool_var_and_cost> tmp;
        for (bool_var v : m_elim_todo) {
            if (is_external(v))
                continue;
            if (was_eliminated(v))
                continue;
            if (value(v) != l_undef)
                continue;
            unsigned c = get_to_elim_cost(v);
            tmp.push_back(bool_var_and_cost(v, c));
        }
        m_elim_todo.reset();
        std::stable_sort(tmp.begin(), tmp.end(), bool_var_and_cost_lt());
        TRACE(sat_simplifier,
              for (auto& [v, c] : tmp) tout << "(" << v << ", " << c << ") ";
              tout << "\n";);
        for (auto& [v, c] : tmp)
            r.push_back(v);
    }

    /**
       \brief Collect clauses and binary clauses containing l.
    */
    void simplifier::collect_clauses(literal l, clause_wrapper_vector & r) {
        clause_use_list const & cs = m_use_list.get(l);
        for (auto it = cs.mk_iterator(); !it.at_end(); it.next()) {
            clause& c = it.curr();
            if (!c.is_learned() && !c.was_removed()) {
                r.push_back(clause_wrapper(c));
                SASSERT(r.back().contains(l));
                SASSERT(r.back().size() == c.size());
            }
        }

        watch_list & wlist = get_bin_wlist(~l);
        for (auto & w : wlist) {
            if (w.is_binary_non_learned_clause()) {
                r.push_back(clause_wrapper(l, w.get_literal()));
                SASSERT(r.back().size() == 2);
            }
        }
    }

    /**
       \brief Resolve clauses c1 and c2.
       c1 must contain l.
       c2 must contain ~l.
       Store result in r.
       Return false if the result is a tautology
    */
    bool simplifier::resolve(clause_wrapper const & c1, clause_wrapper const & c2, literal l, literal_vector & r) {
        CTRACE(resolve_bug, !c1.contains(l) || !c2.contains(~l), tout << c1 << "\n" << c2 << "\nl: " << l << "\n";);
        if (m_visited.size() <= 2*s.num_vars())
            m_visited.resize(2*s.num_vars(), false);
        if (c1.was_removed() && !c1.contains(l))
            return false;
        if (c2.was_removed() && !c2.contains(~l))
            return false;
        SASSERT(c1.contains(l));
        SASSERT(c2.contains(~l));
        bool res = true;
        m_elim_counter -= c1.size() + c2.size();
        unsigned sz1 = c1.size();
        for (unsigned i = 0; i < sz1; ++i) {
            literal l1 = c1[i];
            if (l == l1)
                continue;
            m_visited[l1.index()] = true;
            r.push_back(l1);
        }

        literal not_l = ~l;
        unsigned sz2 = c2.size();
        for (unsigned i = 0; i < sz2; ++i) {
            literal l2 = c2[i];
            if (not_l == l2)
                continue;
            if ((~l2).index() >= m_visited.size()) {
                //s.display(std::cout << l2 << " " << s.num_vars() << " " << m_visited.size() << "\n");
                UNREACHABLE();
            }
            if (m_visited[(~l2).index()]) {
                res = false;
                break;
            }
            if (!m_visited[l2.index()])
                r.push_back(l2);
        }

        for (unsigned i = 0; i < sz1; ++i) {
            literal l1 = c1[i];
            m_visited[l1.index()] = false;
        }
        return res;
    }

    void simplifier::save_clauses(model_converter::entry & mc_entry, clause_wrapper_vector const & cs) {
        for (auto & e : cs) {
            s.m_mc.insert(mc_entry, e);
        }
    }

    void simplifier::add_non_learned_binary_clause(literal l1, literal l2) {
        s.mk_bin_clause(l1, l2, false);
    }

    /**
       \brief Eliminate the binary clauses watched by l, when l.var() is being eliminated
    */
    void simplifier::remove_bin_clauses(literal l) {
        watch_list & wlist = get_bin_wlist(~l);
        for (auto & w : wlist) {
            if (w.is_binary_clause()) {
                literal l2 = w.get_literal();
                // m_drat.del(l, l2);
                watch_list & wlist2 = get_bin_wlist(~l2);
                watch_list::iterator it2  = wlist2.begin();
                watch_list::iterator itprev = it2;
                watch_list::iterator end2 = wlist2.end();
                for (; it2 != end2; ++it2) {
                    if (it2->is_binary_clause() && it2->get_literal() == l) {
                        TRACE(bin_clause_bug, tout << "removing: " << l << " " << it2->get_literal() << "\n";);
                        m_sub_bin_todo.erase(bin_clause(l2, l, it2->is_learned()));
                        continue;
                    }
                    *itprev = *it2;
                    itprev++;
                }
                wlist2.set_end(itprev);
                m_sub_bin_todo.erase(bin_clause(l, l2, w.is_learned()));
            }
        }
        TRACE(bin_clause_bug, tout << "collapsing watch_list of: " << l << "\n";);
        wlist.finalize();
    }

    /**
       \brief Eliminate the clauses where the variable being eliminated occur.
    */
    void simplifier::remove_clauses(clause_use_list const & cs, literal l) {
        for (auto it = cs.mk_iterator(); !it.at_end(); ) {
            clause & c = it.curr();
            it.next();
            SASSERT(c.contains(l));
            if (!c.was_removed()) {
                if (s.m_config.m_drat) {
                    s.m_drat.del(c);
                }
                c.set_removed(true);
                m_use_list.erase(c, l);
                m_sub_todo.erase(c);
                TRACE(sat_simplifier, tout << "del_clause (elim_var): " << c << "\n";);
                m_need_cleanup = true;
            }
        }
    }

    // Gate detection methods for CaDiCaL-style gate-aware variable elimination.
#include "sat/sat_gate_elim.inc"

    bool simplifier::try_eliminate(bool_var v) {
        if (value(v) != l_undef)
            return false;

        literal pos_l(v, false);
        literal neg_l(v, true);
        unsigned num_bin_pos = num_nonlearned_bin(pos_l);
        unsigned num_bin_neg = num_nonlearned_bin(neg_l);
        clause_use_list & pos_occs = m_use_list.get(pos_l);
        clause_use_list & neg_occs = m_use_list.get(neg_l);
        unsigned num_pos = pos_occs.num_irredundant() + num_bin_pos;
        unsigned num_neg = neg_occs.num_irredundant() + num_bin_neg;

        TRACE(sat_simplifier, tout << v << " num_pos: " << num_pos << " neg_pos: " << num_neg << "\n";);

        if (num_pos >= m_res_occ_cutoff && num_neg >= m_res_occ_cutoff)
            return false;

        unsigned before_lits = num_bin_pos*2 + num_bin_neg*2;

        for (auto it = pos_occs.mk_iterator(); !it.at_end(); it.next()) {
            if (!it.curr().is_learned())
                before_lits += it.curr().size();
        }

        for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
            if (!it.curr().is_learned())
                before_lits += it.curr().size();
        }

        TRACE(sat_simplifier, tout << v << " num_pos: " << num_pos << " neg_pos: " << num_neg << " before_lits: " << before_lits << "\n";);

        if (num_pos >= m_res_occ_cutoff3 && num_neg >= m_res_occ_cutoff3 && before_lits > m_res_lit_cutoff3 && s.m_clauses.size() > m_res_cls_cutoff2)
            return false;
        if (num_pos >= m_res_occ_cutoff2 && num_neg >= m_res_occ_cutoff2 && before_lits > m_res_lit_cutoff2 &&
            s.m_clauses.size() > m_res_cls_cutoff1 && s.m_clauses.size() <= m_res_cls_cutoff2)
            return false;
        if (num_pos >= m_res_occ_cutoff1 && num_neg >= m_res_occ_cutoff1 && before_lits > m_res_lit_cutoff1 &&
            s.m_clauses.size() <= m_res_cls_cutoff1)
            return false;

        m_pos_cls.reset();
        m_neg_cls.reset();
        collect_clauses(pos_l, m_pos_cls);
        collect_clauses(neg_l, m_neg_cls);

        // --- Gate detection (CaDiCaL-style) ---
        // Try to detect structural gates to reduce the number of resolution pairs.
        // With a gate, only (gate, non-gate) pairs are resolved, skipping
        // (gate, gate) and (non-gate, non-gate) pairs.
        m_gate_type = GATE_NONE;
        literal eq_lit = null_literal;

        if (num_pos >= 2 && num_neg >= 2) {
            if (find_equivalence(v, eq_lit)) {
                m_gate_type = GATE_EQUIV;
            } else if (find_and_gate(v)) {
                m_gate_type = GATE_AND;
            } else if (find_ite_gate(v)) {
                m_gate_type = GATE_ITE;
            } else if (find_xor_gate(v)) {
                m_gate_type = GATE_XOR;
            }
        }

        TRACE(sat_simplifier, {
            tout << "collecting number of after_clauses";
            switch (m_gate_type) {
            case GATE_EQUIV: tout << " [equiv]"; break;
            case GATE_AND:   tout << " [AND]"; break;
            case GATE_ITE:   tout << " [ITE]"; break;
            case GATE_XOR:   tout << " [XOR]"; break;
            default: break;
            }
            tout << "\n";
        });
        unsigned before_clauses = num_pos + num_neg;
        unsigned after_clauses  = 0;
        for (unsigned i = 0; i < m_pos_cls.size(); ++i) {
            clause_wrapper & c1 = m_pos_cls[i];
            bool c1_is_gate = (m_gate_type != GATE_NONE) && m_gate_marks[i];
            for (unsigned j = 0; j < m_neg_cls.size(); ++j) {
                clause_wrapper & c2 = m_neg_cls[j];
                bool c2_is_gate = (m_gate_type != GATE_NONE) && m_gate_marks[m_pos_cls.size() + j];
                // Gate-aware skipping: skip (gate, gate) pairs (always tautological).
                if (m_gate_type != GATE_NONE && c1_is_gate && c2_is_gate)
                    continue;
                m_new_cls.reset();
                if (resolve(c1, c2, pos_l, m_new_cls)) {
                    // On-the-fly self-subsumption heuristic (Han & Somenzi, SAT'09):
                    // If the resolvent is strictly smaller than a non-binary antecedent,
                    // it would subsume that antecedent minus its pivot.  We skip
                    // counting such resolvents to make the cost estimate more favorable,
                    // enabling more eliminations.  The resolvent is still produced in
                    // the adding phase (physical OTFS strengthening is not applied due
                    // to unsound interactions with propagation during elimination).
                    unsigned rsz = m_new_cls.size();
                    if ((!c1.is_binary() && c1.size() > rsz) ||
                        (!c2.is_binary() && c2.size() > rsz)) {
                        TRACE(sat_simplifier, tout << "otf self-sub detected (counting): "
                              << c1 << " x " << c2 << " resolvent size " << rsz << "\n";);
                        continue; // don't count this resolvent
                    }
                    TRACE(sat_simplifier, tout << c1 << "\n" << c2 << "\n-->\n";
                          for (literal l : m_new_cls) tout << l << " "; tout << "\n";);
                    after_clauses++;
                    if (after_clauses > before_clauses + static_cast<unsigned>(m_elim_bound)) {
                        TRACE(sat_simplifier, tout << "too many after clauses: " << after_clauses
                              << " > " << before_clauses << " + " << m_elim_bound << "\n";);
                        return false;
                    }
                }
            }
        }
        TRACE(sat_simplifier, {
              tout << "eliminate " << v << ", before: " << before_clauses << " after: " << after_clauses;
              switch (m_gate_type) {
              case GATE_EQUIV: tout << " [equiv gate]"; break;
              case GATE_AND:   tout << " [AND gate]"; break;
              case GATE_ITE:   tout << " [ITE gate]"; break;
              case GATE_XOR:   tout << " [XOR gate]"; break;
              default: break;
              }
              tout << "\npos\n";
              for (auto & c : m_pos_cls)
                  tout << c << "\n";
              tout << "neg\n";
              for (auto & c : m_neg_cls)
                  tout << c << "\n";
        });
        // Budget charged per-pair inside resolve() — no bulk pre-charge needed.
        if (m_gate_type != GATE_NONE)
            m_num_elim_gate++;

        // eliminate variable
        ++s.m_stats.m_elim_var_res;
        VERIFY(!is_external(v));
        model_converter::entry & mc_entry = s.m_mc.mk(model_converter::ELIM_VAR, v);
        save_clauses(mc_entry, m_pos_cls);
        save_clauses(mc_entry, m_neg_cls);
        s.set_eliminated(v, true);

        // Mark variables in old clauses as needing heap rescore.
        // Their occurrence counts will change when these clauses are removed.
        for (auto & cw : m_pos_cls) {
            for (unsigned k = 0; k < cw.size(); ++k) {
                bool_var w = cw[k].var();
                if (w != v) mark_elim_heap_dirty(w);
            }
        }
        for (auto & cw : m_neg_cls) {
            for (unsigned k = 0; k < cw.size(); ++k) {
                bool_var w = cw[k].var();
                if (w != v) mark_elim_heap_dirty(w);
            }
        }

        for (unsigned i = 0; i < m_pos_cls.size(); ++i) {
            clause_wrapper & c1 = m_pos_cls[i];
            // Skip wrappers whose clause was removed or lost its pivot
            // via on-the-fly self-subsumption in a previous iteration.
            if (!c1.is_binary() && (c1.was_removed() || !c1.contains(pos_l)))
                continue;
            if (c1.is_binary() && !c1.contains(pos_l))
                continue;
            bool c1_is_gate = (m_gate_type != GATE_NONE) && m_gate_marks[i];
            for (unsigned j = 0; j < m_neg_cls.size(); ++j) {
                clause_wrapper & c2 = m_neg_cls[j];
                if (!c2.is_binary() && (c2.was_removed() || !c2.contains(neg_l)))
                    continue;
                if (c2.is_binary() && !c2.contains(neg_l))
                    continue;
                bool c2_is_gate = (m_gate_type != GATE_NONE) && m_gate_marks[m_pos_cls.size() + j];
                // Gate-aware skipping: skip (gate, gate) pairs (always tautological).
                if (m_gate_type != GATE_NONE && c1_is_gate && c2_is_gate)
                    continue;
                m_new_cls.reset();
                if (!resolve(c1, c2, pos_l, m_new_cls))
                    continue;

                TRACE(sat_simplifier, tout << c1 << "\n" << c2 << "\n-->\n" << m_new_cls << "\n";);
                if (cleanup_clause(m_new_cls)) {
                    continue; // clause is already satisfied.
                }
                // Mark resolvent variables for heap update.
                for (literal lit : m_new_cls)
                    mark_elim_heap_dirty(lit.var());
                switch (m_new_cls.size()) {
                case 0:
                    s.set_conflict();
                    break;
                case 1:
                    propagate_unit(m_new_cls[0]);
                    break;
                case 2:
                    s.m_stats.m_mk_bin_clause++;
                    add_non_learned_binary_clause(m_new_cls[0], m_new_cls[1]);
                    back_subsumption1(m_new_cls[0], m_new_cls[1], false);
                    break;
                default:
                    if (m_new_cls.size() == 3)
                        s.m_stats.m_mk_ter_clause++;
                    else
                        s.m_stats.m_mk_clause++;
                    clause * new_c = s.alloc_clause(m_new_cls.size(), m_new_cls.data(), false);

                    if (s.m_config.m_drat) s.m_drat.add(*new_c, status::redundant());
                    s.m_clauses.push_back(new_c);

                    m_use_list.insert(*new_c);
                    mark_subsume(*new_c);
                    if (m_sub_counter > 0)
                        back_subsumption1(*new_c);
                    else
                        back_subsumption0(*new_c);
                    break;
                }
                if (s.inconsistent())
                    return true;
            }
        }
        remove_bin_clauses(pos_l);
        remove_bin_clauses(neg_l);
        {
            clause_use_list& pos_occs = m_use_list.get(pos_l);
            clause_use_list& neg_occs = m_use_list.get(neg_l);
            remove_clauses(pos_occs, pos_l);
            remove_clauses(neg_occs, neg_l);
            pos_occs.reset();
            neg_occs.reset();
        }
        return true;
    }

    struct simplifier::elim_var_report {
        simplifier & m_simplifier;
        stopwatch    m_watch;
        unsigned     m_num_elim_vars;
        elim_var_report(simplifier & s):
            m_simplifier(s),
            m_num_elim_vars(s.m_num_elim_vars) {
            m_watch.start();
        }

        ~elim_var_report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL,
                       verbose_stream() << " (sat-resolution :elim-vars "
                       << (m_simplifier.m_num_elim_vars - m_num_elim_vars)
                       << " :threshold " << m_simplifier.m_elim_counter
                       << " :elim-bound " << m_simplifier.m_elim_bound
                       << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }
    };

    /**
     * Double the elimination bound (CaDiCaL / GlueMiniSAT escalation).
     * Progression: 0 -> 1 -> 2 -> 4 -> 8 -> 16.
     * After increasing, reschedule all non-eliminated, non-external variables
     * so they get retried with the relaxed bound on the next simplification call.
     */
    void simplifier::increase_elim_bound() {
        if (m_elim_bound >= m_elim_bound_max)
            return;

        if (m_elim_bound <= 0)
            m_elim_bound = 1;
        else
            m_elim_bound *= 2;

        if (m_elim_bound > m_elim_bound_max)
            m_elim_bound = m_elim_bound_max;

        IF_VERBOSE(SAT_VB_LVL,
                   verbose_stream() << " (sat-elim-bound :new-bound " << m_elim_bound << ")\n";);
        TRACE(sat_simplifier, tout << "increased elimination bound to " << m_elim_bound << "\n";);
    }

    void simplifier::elim_vars() {
        if (!elim_vars_enabled())
            return;
        elim_var_report rpt(*this);

        // Initialize the dynamic elimination heap with all eligible variables.
        unsigned nv = s.num_vars();
        m_elim_heap.reset();
        m_elim_heap.set_bounds(nv);
        m_elim_costs.reset();
        m_elim_costs.resize(nv, 0);
        m_elim_heap_dirty.reset();

        for (bool_var v : m_elim_todo) {
            if (is_external(v))
                continue;
            if (was_eliminated(v))
                continue;
            if (value(v) != l_undef)
                continue;
            m_elim_costs[v] = get_to_elim_cost(v);
            m_elim_heap.insert(v);
        }
        m_elim_todo.reset();

        TRACE(sat_simplifier, tout << "dynamic elim heap: " << m_elim_heap.size() << " variables\n";);

        // Process variables from the heap.  After each successful
        // elimination, flush_elim_heap_dirty() rescores and re-inserts
        // affected neighbors, enabling cascading eliminations.
        while (!m_elim_heap.empty()) {
            checkpoint();
            if (m_elim_counter < 0)
                break;
            if (s.inconsistent())
                break;
            bool_var v = static_cast<bool_var>(m_elim_heap.erase_min());
            if (is_external(v))
                continue;
            if (was_eliminated(v))
                continue;
            if (value(v) != l_undef)
                continue;
            if (try_eliminate(v)) {
                m_num_elim_vars++;
                // Rescore and reschedule affected neighbors.
                flush_elim_heap_dirty();
            }
            else {
                // Elimination failed; discard any stale dirty marks.
                m_elim_heap_dirty.reset();
            }
        }

        m_elim_heap.reset();
        m_elim_costs.finalize();
        m_elim_heap_dirty.reset();
        m_pos_cls.finalize();
        m_neg_cls.finalize();
        m_new_cls.finalize();
    }

    // -------------------------------------------------------
    // Bounded Variable Addition (BVA)
    //
    // BVA introduces fresh variables to reduce the total number
    // of literal occurrences in the clause database.
    //
    // Given N clauses that share literal l and a common "tail" S:
    //   C_i = {a_i} U S  for i = 1..N
    // where l is in S and the a_i are distinct differing literals,
    // we introduce a fresh variable x and replace the N clauses with:
    //   {x} U S           (the shared clause, with x standing for the disjunction)
    //   {~x, a_i}         for i = 1..N   (definition clauses)
    //
    // Cost analysis (literal occurrences):
    //   Before: N * (|S| + 1) literals
    //   After:  (|S| + 1) + 2*N literals
    //   Saving: (N-1)*(|S|+1) - 2*N = (N-1)*|S| - (N+1)
    //   Profitable when (N-1)*|S| > N+1
    //
    // For model reconstruction, x is an internal variable that gets
    // eliminated via the standard ELIM_VAR model converter mechanism.
    // We record all original clauses so the model converter can
    // reconstruct proper assignments.
    // -------------------------------------------------------

    struct simplifier::bva_report {
        simplifier & m_simplifier;
        stopwatch    m_watch;
        unsigned     m_num_bva;
        bva_report(simplifier & s):
            m_simplifier(s),
            m_num_bva(s.m_num_bva) {
            m_watch.start();
        }

        ~bva_report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL,
                       verbose_stream() << " (sat-bva :eliminated "
                       << (m_simplifier.m_num_bva - m_num_bva)
                       << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }
    };

    // =============================================================
    // Multi-factor BVA (CaDiCaL-style iterative factorization)
    //
    // For a given initial literal, we build a chain of factors by
    // iteratively finding co-occurring literals across clauses that
    // share a common quotient. This discovers multi-way factorizations
    // that the single-pass hash approach misses entirely.
    // =============================================================

    void simplifier::bva_factoring::release_all() {
        for (bva_quotient * q = first, * nxt; q; q = nxt) {
            nxt = q->next;
            dealloc(q);
        }
        first = last = nullptr;
    }

    unsigned simplifier::bva_occ_count(literal l) const {
        unsigned cnt = m_use_list.get(l).num_irredundant();
        cnt += num_nonlearned_bin(l);
        return cnt;
    }

    simplifier::bva_quotient * simplifier::bva_new_quotient(bva_factoring & fctx, literal factor) {
        SASSERT(!bva_is_marked(factor, BVA_FACTORS));
        bva_mark(factor, BVA_FACTORS);

        bva_quotient * q = alloc(bva_quotient, factor);
        q->next = nullptr;
        q->prev = fctx.last;

        if (fctx.last) {
            SASSERT(fctx.first);
            q->id = fctx.last->id + 1;
            fctx.last->next = q;
        } else {
            SASSERT(!fctx.first);
            fctx.first = q;
            q->id = 0;
        }
        fctx.last = q;

        TRACE(sat_simplifier, tout << "bva: new quotient[" << q->id << "] factor " << factor << "\n";);
        return q;
    }

    void simplifier::bva_release_quotients(bva_factoring & fctx) {
        for (bva_quotient * q = fctx.first, * nxt; q; q = nxt) {
            nxt = q->next;
            bva_unmark(q->factor, BVA_FACTORS);
            dealloc(q);
        }
        fctx.first = fctx.last = nullptr;
    }

    unsigned simplifier::bva_first_factor(bva_factoring & fctx, literal factor) {
        SASSERT(!fctx.first);
        bva_quotient * q = bva_new_quotient(fctx, factor);
        clause_vector & qlauses = q->qlauses;

        clause_use_list const & occs = m_use_list.get(factor);
        for (auto it = occs.mk_iterator(); !it.at_end(); it.next()) {
            clause & c = it.curr();
            if (c.is_learned() || c.was_removed()) continue;
            qlauses.push_back(&c);
            fctx.budget -= static_cast<int>(c.size());
        }

        unsigned cnt = qlauses.size();
        TRACE(sat_simplifier, tout << "bva: first_factor " << factor << " -> " << cnt << " clauses\n";);
        return cnt;
    }

    // Among clauses in the last quotient, find the literal that co-occurs
    // most frequently as the single "differing" literal in sibling clauses.
    //
    // For each clause C in the current quotient:
    //   1. Mark all non-factor literals in C as QUOTIENT.
    //   2. Find the literal with minimum occurrence count (min_lit).
    //   3. Scan min_lit's occurrence list for clauses D of the same size
    //      where D differs from C by exactly one literal (the "next" candidate).
    //   4. Count how many times each candidate appears.
    //
    // Return the candidate with the highest count (>= 2), breaking ties
    // by occurrence list size (prefer larger for more factoring potential).
    literal simplifier::bva_next_factor(bva_factoring & fctx, unsigned & next_count) {
        bva_quotient * last_q = fctx.last;
        SASSERT(last_q);
        clause_vector & last_clauses = last_q->qlauses;
        svector<unsigned> & count = fctx.count;
        svector<unsigned> & counted = fctx.counted;
        SASSERT(counted.empty());

        svector<unsigned> nounted_indices;
        bool_vector swept;

        for (clause * c : last_clauses) {
            literal min_lit = null_literal;
            unsigned factors_seen = 0;
            unsigned min_occ = UINT_MAX;
            fctx.budget--;

            for (literal lit : *c) {
                if (bva_is_marked(lit, BVA_FACTORS)) {
                    factors_seen++;
                    if (factors_seen > 1) break;
                } else {
                    bva_mark(lit, BVA_QUOTIENT);
                    unsigned occ = bva_occ_count(lit);
                    if (min_lit == null_literal || occ < min_occ) {
                        min_lit = lit;
                        min_occ = occ;
                    }
                }
            }

            if (factors_seen <= 1 && min_lit != null_literal) {
                unsigned c_size = c->size();
                clause_use_list const & min_occs = m_use_list.get(min_lit);
                fctx.budget -= static_cast<int>(min_occs.size());

                for (auto it = min_occs.mk_iterator(); !it.at_end(); it.next()) {
                    clause & d = it.curr();
                    if (&d == c) continue;
                    if (d.is_learned() || d.was_removed()) continue;
                    fctx.budget--;
                    if (d.id() < swept.size() && swept[d.id()]) continue;
                    if (d.size() != c_size) continue;

                    literal next_candidate = null_literal;
                    bool valid = true;
                    for (literal lit : d) {
                        if (bva_is_marked(lit, BVA_QUOTIENT))
                            continue;
                        if (bva_is_marked(lit, BVA_FACTORS)) { valid = false; break; }
                        if (bva_is_marked(lit, BVA_NOUNTED)) { valid = false; break; }
                        if (next_candidate != null_literal) { valid = false; break; }
                        next_candidate = lit;
                    }

                    if (!valid || next_candidate == null_literal) continue;
                    if (is_external(next_candidate.var())) continue;
                    if (was_eliminated(next_candidate.var())) continue;
                    if (value(next_candidate) != l_undef) continue;

                    bva_mark(next_candidate, BVA_NOUNTED);
                    nounted_indices.push_back(next_candidate.index());

                    if (d.id() >= swept.size()) swept.resize(d.id() + 1, false);
                    swept[d.id()] = true;

                    unsigned idx = next_candidate.index();
                    if (idx >= count.size()) count.resize(idx + 1, 0);
                    if (count[idx] == 0) counted.push_back(idx);
                    count[idx]++;
                }

                for (unsigned idx : nounted_indices)
                    bva_unmark(to_literal(idx), BVA_NOUNTED);
                nounted_indices.reset();
            }

            for (literal lit : *c)
                bva_unmark(lit, BVA_QUOTIENT);

            if (fctx.budget < 0) break;
        }

        unsigned best_count = 0;
        literal best = null_literal;
        if (fctx.budget >= 0) {
            unsigned ties = 0;
            for (unsigned idx : counted) {
                unsigned cnt = count[idx];
                if (cnt < best_count) continue;
                if (cnt == best_count) { ties++; }
                else { best_count = cnt; best = to_literal(idx); ties = 1; }
            }

            if (best_count < 2) {
                best = null_literal;
            } else if (ties > 1) {
                unsigned best_occ = 0;
                for (unsigned idx : counted) {
                    if (count[idx] != best_count) continue;
                    literal lit = to_literal(idx);
                    unsigned occ = bva_occ_count(lit);
                    if (occ > best_occ) { best_occ = occ; best = lit; }
                }
            }
        }

        for (unsigned idx : counted) count[idx] = 0;
        counted.reset();

        next_count = best_count;
        return best;
    }

    void simplifier::bva_factorize_next(bva_factoring & fctx, literal next, unsigned expected_count) {
        bva_quotient * last_q = fctx.last;
        bva_quotient * next_q = bva_new_quotient(fctx, next);

        SASSERT(last_q);
        clause_vector & last_clauses = last_q->qlauses;
        clause_vector & next_clauses = next_q->qlauses;
        svector<unsigned> & matches = next_q->matches;

        bool_vector swept;
        unsigned i = 0;

        for (clause * c : last_clauses) {
            literal min_lit = null_literal;
            unsigned factors_seen = 0;
            unsigned min_occ = UINT_MAX;
            fctx.budget--;

            for (literal lit : *c) {
                if (bva_is_marked(lit, BVA_FACTORS)) {
                    factors_seen++;
                    if (factors_seen > 1) break;
                } else {
                    bva_mark(lit, BVA_QUOTIENT);
                    unsigned occ = bva_occ_count(lit);
                    if (min_lit == null_literal || occ < min_occ) {
                        min_lit = lit;
                        min_occ = occ;
                    }
                }
            }

            if (factors_seen <= 1 && min_lit != null_literal) {
                unsigned c_size = c->size();
                clause_use_list const & min_occs = m_use_list.get(min_lit);
                fctx.budget -= static_cast<int>(min_occs.size());

                for (auto it = min_occs.mk_iterator(); !it.at_end(); it.next()) {
                    clause & d = it.curr();
                    if (&d == c) continue;
                    if (d.is_learned() || d.was_removed()) continue;
                    if (d.id() < swept.size() && swept[d.id()]) continue;
                    if (d.size() != c_size) continue;
                    fctx.budget--;

                    bool valid = true;
                    for (literal lit : d) {
                        if (bva_is_marked(lit, BVA_QUOTIENT)) continue;
                        if (lit != next) { valid = false; break; }
                    }

                    if (valid) {
                        next_clauses.push_back(&d);
                        matches.push_back(i);
                        if (d.id() >= swept.size()) swept.resize(d.id() + 1, false);
                        swept[d.id()] = true;
                        break;
                    }
                }
            }

            for (literal lit : *c) bva_unmark(lit, BVA_QUOTIENT);
            i++;
        }

        SASSERT(expected_count <= next_clauses.size());
        (void)expected_count;
    }

    void simplifier::bva_flush_unmatched(bva_quotient * q) {
        bva_quotient * prev = q->prev;
        SASSERT(prev);
        svector<unsigned> & q_matches = q->matches;
        clause_vector & q_clauses = q->qlauses;
        clause_vector & prev_clauses = prev->qlauses;
        svector<unsigned> & prev_matches = prev->matches;
        unsigned n = q_clauses.size();
        SASSERT(n == q_matches.size());
        bool prev_is_first = (prev->id == 0);

        for (unsigned i = 0; i < n; i++) {
            unsigned j = q_matches[i];
            q_matches[i] = i;
            SASSERT(i <= j);
            if (!prev_is_first && j < prev_matches.size()) {
                if (i < prev_matches.size())
                    prev_matches[i] = prev_matches[j];
            }
            prev_clauses[i] = prev_clauses[j];
        }

        if (!prev_is_first) prev_matches.resize(n);
        prev_clauses.resize(n);
    }

    simplifier::bva_quotient * simplifier::bva_best_quotient(bva_factoring & fctx, unsigned & reduction) {
        unsigned factors = 1;
        unsigned best_reduction = 0;
        bva_quotient * best = nullptr;

        for (bva_quotient * q = fctx.first; q; q = q->next) {
            unsigned quotients = q->qlauses.size();
            unsigned before = quotients * factors;
            unsigned after = quotients + factors;

            if (before > after) {
                unsigned delta = before - after;
                if (!best || delta > best_reduction) {
                    best_reduction = delta;
                    best = q;
                }
            }
            factors++;
        }

        reduction = best_reduction;
        TRACE(sat_simplifier, {
            if (best) tout << "bva: best quotient[" << best->id << "] reduction=" << best_reduction << "\n";
            else tout << "bva: no profitable quotient found\n";
        });
        return best;
    }

    bool simplifier::bva_self_subsuming_factor(bva_quotient * q) {
        for (bva_quotient * p = q; p; p = p->prev)
            mark_visited(p->factor);

        bool found = false;
        bva_quotient * x_q = nullptr, * y_q = nullptr;
        for (bva_quotient * p = q; p; p = p->prev) {
            if (is_marked(~p->factor)) {
                found = true;
                x_q = p;
                for (bva_quotient * r = q; r; r = r->prev) {
                    if (r->factor == ~p->factor && r != p) { y_q = r; break; }
                }
                break;
            }
        }
        for (bva_quotient * p = q; p; p = p->prev)
            unmark_visited(p->factor);

        if (!found || !x_q || !y_q) return false;

        TRACE(sat_simplifier, tout << "bva: self-subsuming factor " << x_q->factor << " vs " << y_q->factor << "\n";);

        for (clause * c : x_q->qlauses) {
            literal_vector resolvent;
            for (literal lit : *c) {
                if (lit == x_q->factor) continue;
                resolvent.push_back(lit);
            }

            if (resolvent.size() == 1) {
                literal unit = resolvent[0];
                lbool val = value(unit);
                if (val == l_undef)
                    s.assign_scoped(unit);
                else if (val == l_false) {
                    s.set_conflict();
                    return true;
                }
            } else if (resolvent.size() == 2) {
                s.mk_bin_clause(resolvent[0], resolvent[1], false);
            } else {
                clause * new_c = s.alloc_clause(resolvent.size(), resolvent.data(), false);
                if (s.m_config.m_drat) s.m_drat.add(*new_c, status::redundant());
                s.m_clauses.push_back(new_c);
                m_use_list.insert(*new_c);
                mark_subsume(*new_c);
                m_sub_todo.insert(*new_c);
            }
        }
        return true;
    }

    void simplifier::bva_delete_unfactored(bva_quotient * q) {
        for (clause * c : q->qlauses) {
            if (!c->was_removed())
                remove_clause(*c, true);
        }
    }

    bool simplifier::bva_apply_factoring(bva_factoring & fctx, bva_quotient * q) {
        for (bva_quotient * p = q; p->prev; p = p->prev)
            bva_flush_unmatched(p);

        if (bva_self_subsuming_factor(q)) {
            for (bva_quotient * p = q; p; p = p->prev)
                bva_delete_unfactored(p);
            return true;
        }

        bool_var x = s.mk_var(false, true);
        literal fresh(x, false);
        literal not_fresh(x, true);

        if (m_visited.size() <= 2 * x + 1)
            m_visited.resize(2 * (x + 1), false);
        m_use_list.reserve(s.num_vars());
        bva_ensure_marks(2 * (x + 1));

        TRACE(sat_simplifier, {
            tout << "bva: apply factoring, fresh var=" << x << "\n";
            tout << "  factors:";
            for (bva_quotient * p = q; p; p = p->prev) tout << " " << p->factor;
            tout << "\n  quotient clauses: " << q->qlauses.size() << "\n";
        });

        for (bva_quotient * p = q; p; p = p->prev)
            s.mk_bin_clause(fresh, p->factor, false);

        for (clause * c : q->qlauses) {
            literal_vector new_cls;
            for (literal lit : *c) {
                if (bva_is_marked(lit, BVA_FACTORS)) continue;
                new_cls.push_back(lit);
            }
            new_cls.push_back(not_fresh);

            if (new_cls.size() == 2) {
                s.mk_bin_clause(new_cls[0], new_cls[1], false);
            } else {
                clause * nc = s.alloc_clause(new_cls.size(), new_cls.data(), false);
                if (s.m_config.m_drat) s.m_drat.add(*nc, status::redundant());
                s.m_clauses.push_back(nc);
                m_use_list.insert(*nc);
                mark_subsume(*nc);
                m_sub_todo.insert(*nc);
            }
        }

        for (bva_quotient * p = q; p; p = p->prev)
            bva_delete_unfactored(p);

        unsigned total_eliminated = 0;
        for (bva_quotient * p = q; p; p = p->prev)
            total_eliminated += p->qlauses.size();
        m_num_bva += total_eliminated;

        insert_elim_todo(x);
        for (bva_quotient * p = q; p; p = p->prev)
            insert_elim_todo(p->factor.var());
        for (clause * c : q->qlauses)
            for (literal lit : *c)
                insert_elim_todo(lit.var());

        return true;
    }

    // Legacy single-pass BVA stub (no longer called from bva()).
    bool simplifier::try_bva(literal l, int & counter) {
        (void)l; (void)counter;
        return false;
    }

    // Main BVA entry point using multi-factor algorithm.
    void simplifier::bva() {
        if (!bva_enabled())
            return;

        bva_report rpt(*this);
        int budget = m_bva_limit;

        unsigned num_lits = 2 * s.num_vars();
        m_bva_marks.reset();
        m_bva_marks.resize(num_lits, 0);

        struct lit_occ { unsigned lit_idx; unsigned occ; };
        svector<lit_occ> schedule;

        unsigned num_vars = s.num_vars();
        for (bool_var v = 0; v < num_vars; ++v) {
            if (was_eliminated(v)) continue;
            if (value(v) != l_undef) continue;
            if (is_external(v)) continue;

            literal pos_l(v, false);
            literal neg_l(v, true);
            unsigned pos_occ = bva_occ_count(pos_l);
            unsigned neg_occ = bva_occ_count(neg_l);

            if (pos_occ >= 2) { lit_occ lo; lo.lit_idx = pos_l.index(); lo.occ = pos_occ; schedule.push_back(lo); }
            if (neg_occ >= 2) { lit_occ lo; lo.lit_idx = neg_l.index(); lo.occ = neg_occ; schedule.push_back(lo); }
        }

        std::sort(schedule.begin(), schedule.end(),
                  [](lit_occ const & a, lit_occ const & b) {
                      if (a.occ != b.occ) return a.occ < b.occ;
                      return a.lit_idx < b.lit_idx;
                  });

        for (auto const & lo : schedule) {
            if (budget < 0) break;
            checkpoint();
            if (s.inconsistent()) return;

            literal first_lit = to_literal(lo.lit_idx);
            if (was_eliminated(first_lit.var())) continue;
            if (value(first_lit) != l_undef) continue;
            if (bva_occ_count(first_lit) < 2) continue;

            bva_factoring fctx;
            fctx.budget = budget;

            unsigned first_count = bva_first_factor(fctx, first_lit);
            if (first_count > 1) {
                for (;;) {
                    unsigned next_count = 0;
                    literal next = bva_next_factor(fctx, next_count);
                    if (next == null_literal) break;
                    if (next_count < 2) break;
                    bva_factorize_next(fctx, next, next_count);
                    if (fctx.budget < 0) break;
                }

                unsigned reduction = 0;
                bva_quotient * best = bva_best_quotient(fctx, reduction);
                if (best && reduction > 0)
                    bva_apply_factoring(fctx, best);
            }

            budget = fctx.budget;
            bva_release_quotients(fctx);
        }

        m_bva_marks.reset();
    }

    void simplifier::updt_params(params_ref const & _p) {
        sat_simplifier_params p(_p);
        m_cce                     = p.cce();
        m_acce                    = p.acce();
        m_bca                     = false && p.bca(); // disabled
        m_abce                    = p.abce();
        m_ate                     = p.ate();
        m_bce_delay               = p.bce_delay();
        m_bce                     = p.bce();
        m_bce_at                  = p.bce_at();
        m_retain_blocked_clauses  = p.retain_blocked_clauses();
        m_blocked_clause_limit    = p.blocked_clause_limit();
        m_res_limit               = p.resolution_limit();
        m_res_occ_cutoff          = p.resolution_occ_cutoff();
        m_res_occ_cutoff1         = p.resolution_occ_cutoff_range1();
        m_res_occ_cutoff2         = p.resolution_occ_cutoff_range2();
        m_res_occ_cutoff3         = p.resolution_occ_cutoff_range3();
        m_res_lit_cutoff1         = p.resolution_lit_cutoff_range1();
        m_res_lit_cutoff2         = p.resolution_lit_cutoff_range2();
        m_res_lit_cutoff3         = p.resolution_lit_cutoff_range3();
        m_res_cls_cutoff1         = p.resolution_cls_cutoff1();
        m_res_cls_cutoff2         = p.resolution_cls_cutoff2();
        m_subsumption             = p.subsumption();
        m_subsumption_limit       = p.subsumption_limit();
        m_elim_vars               = p.elim_vars();
        m_bva                     = p.bva();
        m_bva_limit               = p.bva_limit();
        m_incremental_mode        = s.get_config().m_incremental && !p.override_incremental();
    }

    void simplifier::collect_param_descrs(param_descrs & r) {
        sat_simplifier_params::collect_param_descrs(r);
    }

    void simplifier::collect_statistics(statistics & st) const {
        st.update("sat subsumed", m_num_subsumed);
        st.update("sat subs resolution", m_num_sub_res);
        st.update("sat elim literals", m_num_elim_lits);
        st.update("sat bce",  m_num_bce);
        st.update("sat cce",  m_num_cce);
        st.update("sat acce", m_num_acce);
        st.update("sat abce", m_num_abce);
        st.update("sat bca",  m_num_bca);
        st.update("sat ate",  m_num_ate);
        st.update("sat bva",  m_num_bva);
        st.update("sat elim otf subsumption", m_num_elim_otf_sub);
        st.update("sat elim rounds", m_num_elim_rounds);
        st.update("sat elim gate", m_num_elim_gate);
    }

    void simplifier::reset_statistics() {
        m_num_bce = 0;
        m_num_cce = 0;
        m_num_acce = 0;
        m_num_abce = 0;
        m_num_subsumed = 0;
        m_num_sub_res = 0;
        m_num_elim_lits = 0;
        m_num_elim_vars = 0;
        m_num_bca = 0;
        m_num_ate = 0;
        m_num_bva = 0;
        m_num_elim_otf_sub = 0;
        m_num_elim_rounds = 0;
        m_num_elim_gate = 0;
    }
};
