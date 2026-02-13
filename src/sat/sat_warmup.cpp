/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_warmup.cpp

Abstract:

    CaDiCaL-style warmup propagation before local search.

    Assigns all unassigned variables using the current phase heuristic,
    propagating after each decision but DELIBERATELY IGNORING all conflicts.
    This leverages CDCL's strength (propagating long implication chains)
    to give local search a propagation-consistent starting point.

    The result is stored in m_best_phase so that bounded_local_search
    (and ddfw/walksat) pick up a high-quality initial assignment.

    Reference: CaDiCaL warmup.cpp (Biere, 2024)

Author:

    Grigory (2024)

--*/

#include "sat/sat_solver.h"

namespace sat {

    // Lightweight assignment for warmup: sets the assignment array and pushes
    // to the trail, but does NOT log to DRAT, update activity stats, or
    // require a scope level.  This avoids all the side effects of assign_core
    // that are inappropriate during warmup (scope management, extension
    // callbacks, anti-exploration, etc).
    static void warmup_assign(solver& s, literal l,
                              svector<lbool>& assignment,
                              literal_vector& trail,
                              bool_vector& phase) {
        SASSERT(assignment[l.index()] == l_undef);
        assignment[l.index()]    = l_true;
        assignment[(~l).index()] = l_false;
        phase[l.var()] = !l.sign();
        trail.push_back(l);
    }

    bool solver::warmup_propagate(literal l) {
        // Propagate literal l through binary and long-clause watch lists,
        // but IGNORE conflicts instead of setting m_inconsistent.
        // Watch lists are maintained correctly (watches are moved as usual)
        // since the 2-watched invariant does not require watched literals
        // to be assigned -- the updates remain valid after unassignment.

        literal not_l = ~l;

        // Phase 1: binary watch propagation (ignoring conflicts)
        {
            watch_list& bin_wlist = m_bin_watches[l.index()];
            for (auto const& w : bin_wlist) {
                literal l1 = w.get_literal();
                switch (value(l1)) {
                case l_false:
                    // Conflict in binary clause -- deliberately ignored
                    break;
                case l_undef:
                    warmup_assign(*this, l1, m_assignment, m_trail, m_phase);
                    break;
                default:
                    break;
                }
            }
        }

        // Phase 2: long-clause watch propagation (ignoring conflicts)
        // Mirrors propagate_literal() but replaces set_conflict with skip.
        watch_list& wlist = m_watches[l.index()];
        watch_list::iterator it  = wlist.begin();
        watch_list::iterator it2 = it;
        watch_list::iterator end = wlist.end();

        for (; it != end; ++it) {
            switch (it->get_kind()) {
            case watched::BINARY:
                UNREACHABLE();
                *it2 = *it;
                it2++;
                break;

            case watched::CLAUSE: {
                // Fast path: blocked literal satisfied
                if (value(it->get_blocked_literal()) == l_true) {
                    *it2 = *it;
                    it2++;
                    break;
                }

                clause_offset cls_off = it->get_clause_offset();
                clause& c = get_clause(cls_off);

                // Normalize: ensure c[1] == not_l
                if (c[0] == not_l)
                    std::swap(c[0], c[1]);

                // Skip removed/stale clauses
                if (c.was_removed() || c.size() == 1 || c[1] != not_l) {
                    *it2 = *it;
                    it2++;
                    break;
                }

                // If c[0] (other watch) is satisfied, update blocked literal
                if (value(c[0]) == l_true) {
                    it2->set_clause(c[0], cls_off);
                    it2++;
                    break;
                }

                unsigned sz = c.size();

                if (value(c[0]) == l_undef) {
                    // c[0] is unassigned: scan for a satisfied or unassigned replacement
                    bool found = false;
                    for (unsigned i = 2; i < sz; ++i) {
                        literal lit = c[i];
                        switch (value(lit)) {
                        case l_true:
                            it2->set_clause(lit, cls_off);
                            it2++;
                            found = true;
                            break;
                        case l_undef:
                            set_watch(c, i, cls_off);
                            found = true;
                            break;
                        default:
                            break;
                        }
                        if (found) break;
                    }
                    if (found)
                        goto warmup_end_clause;

                    // No replacement: all others false, c[0] is undef -> unit propagation
                    *it2 = *it;
                    it2++;
                    warmup_assign(*this, c[0], m_assignment, m_trail, m_phase);
                }
                else {
                    // c[0] is false: scan for any satisfied or undef replacement
                    SASSERT(value(c[0]) == l_false);
                    unsigned undef_index = 0;
                    bool found = false;

                    for (unsigned i = 2; i < sz; ++i) {
                        literal lit = c[i];
                        switch (value(lit)) {
                        case l_true:
                            it2->set_clause(lit, cls_off);
                            it2++;
                            found = true;
                            break;
                        case l_undef:
                            if (undef_index == 0)
                                undef_index = i;
                            break;
                        default:
                            break;
                        }
                        if (found) break;
                    }
                    if (found)
                        goto warmup_end_clause;

                    if (undef_index != 0) {
                        // Found an undef literal: move watch there and propagate
                        set_watch(c, undef_index, cls_off);
                        std::swap(c[0], c[1]);
                        warmup_assign(*this, c[0], m_assignment, m_trail, m_phase);
                        goto warmup_end_clause;
                    }

                    // All literals false: conflict -- deliberately ignored
                    *it2 = *it;
                    it2++;
                }
            warmup_end_clause:
                break;
            }

            case watched::EXT_CONSTRAINT:
                // External constraints skipped during warmup
                *it2 = *it;
                it2++;
                break;

            default:
                *it2 = *it;
                it2++;
                break;
            }
        }

        if (it2 != end)
            wlist.set_end(it2);

        return true;
    }

    void solver::warmup_phases() {
        if (inconsistent())
            return;
        if (!at_base_lvl())
            return;

        unsigned saved_trail_sz  = m_trail.size();
        unsigned saved_qhead     = m_qhead;

        unsigned warmup_decisions = 0;
        unsigned warmup_propagations = 0;

        // Assign every unassigned, non-eliminated variable using its
        // current phase, then propagate ignoring conflicts.
        // We use warmup_assign (lightweight) instead of assign_core
        // to avoid scope requirements, DRAT logging, activity updates,
        // and extension callbacks.
        unsigned nv = num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            if (value(v) != l_undef)
                continue;
            if (was_eliminated(v))
                continue;

            // Decide using cached CDCL phase (m_phase[v])
            bool phase = m_phase[v];
            literal decision_lit(v, !phase);

            warmup_assign(*this, decision_lit, m_assignment, m_trail, m_phase);
            warmup_decisions++;

            // Propagate to fixpoint, ignoring conflicts
            while (m_qhead < m_trail.size()) {
                literal prop_lit = m_trail[m_qhead];
                m_qhead++;
                warmup_propagate(prop_lit);
                warmup_propagations++;
            }
        }

        // Record the warmup assignment into m_best_phase.
        // After warmup, every non-eliminated variable should be assigned.
        for (unsigned v = 0; v < nv; ++v) {
            if (was_eliminated(v))
                continue;
            lbool val = value(v);
            if (val != l_undef)
                m_best_phase[v] = (val == l_true);
        }

        // Undo all warmup assignments.
        // We walk the trail backwards and clear assignments.
        // No need to touch the VSIDS queue since warmup_assign
        // never removed variables from it.
        for (unsigned i = m_trail.size(); i-- > saved_trail_sz; ) {
            literal l = m_trail[i];
            m_assignment[l.index()]    = l_undef;
            m_assignment[(~l).index()] = l_undef;
        }
        m_trail.shrink(saved_trail_sz);
        m_qhead = saved_qhead;

        IF_VERBOSE(3, verbose_stream() << "(sat-warmup"
            << " decisions:" << warmup_decisions
            << " propagations:" << warmup_propagations
            << ")\n");
    }

}
