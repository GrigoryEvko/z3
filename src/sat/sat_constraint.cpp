/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_constraint.cpp

Abstract:

    CaDiCaL-style constraint clause manager for SAT solver.

    Implements temporary disjunctive constraint clauses that live for
    exactly one solve call.  See sat_constraint.h for the full API
    description and intended call sequence.

    Reference: CaDiCaL constrain.cpp, external.cpp:296-316, assume.cpp:236-246

Author:

    Z3 contributors

--*/

#include "sat/sat_constraint.h"
#include "sat/sat_solver.h"

namespace sat {

    // -----------------------------------------------------------------------
    // clean -- deduplicate, remove tautologies and root-falsified literals
    //
    // Mirrors CaDiCaL constrain.cpp:12-47.  Must be called at base level
    // so that root-level assignments are visible.
    //
    // After cleaning:
    //   - m_constraint contains only unassigned, unique literals
    //   - m_constraint is empty if the clause was satisfied at root level
    //   - m_unsat_constraint is set if ALL literals were root-falsified
    // -----------------------------------------------------------------------
    void constraint_manager::clean(solver& s) {
        SASSERT(s.at_base_lvl());

        bool satisfied = false;
        unsigned j = 0;

        // Mark literals we keep, detect tautology and duplicates.
        // Uses the solver's lit_mark infrastructure, cleaned up after.
        for (unsigned i = 0; i < m_constraint.size(); ++i) {
            literal lit = m_constraint[i];
            SASSERT(lit.var() < s.num_vars());

            // Tautology: both lit and ~lit present.
            if (s.is_marked_lit(~lit)) {
                satisfied = true;
                break;
            }

            // Duplicate: skip.
            if (s.is_marked_lit(lit))
                continue;

            // Root-level assignment check.
            lbool val = s.value(lit);
            if (val == l_false)
                continue;
            if (val == l_true) {
                satisfied = true;
                break;
            }

            // Unassigned, unique literal -- keep it.
            s.mark_lit(lit);
            m_constraint[j++] = lit;
        }

        // Clean up all marks.
        for (unsigned i = 0; i < j; ++i)
            s.unmark_lit(m_constraint[i]);

        m_constraint.shrink(j);

        if (satisfied) {
            m_constraint.reset();
            return;
        }

        if (m_constraint.empty()) {
            m_unsat_constraint = true;
        }
    }

    // -----------------------------------------------------------------------
    // constrain -- set the constraint for the next solve call
    //
    // Replaces any existing unconsumed constraint.  Cleans the input
    // and freezes constraint variables.
    //
    // Reference: CaDiCaL constrain.cpp:5-51, external.cpp:296-299
    // -----------------------------------------------------------------------
    void constraint_manager::constrain(solver& s, unsigned num_lits, literal const* lits) {
        if (has_constraint())
            reset(s);

        SASSERT(s.at_base_lvl());
        SASSERT(m_constraint.empty());
        SASSERT(m_frozen_vars.empty());
        SASSERT(!m_unsat_constraint);
        SASSERT(!m_active);
        SASSERT(m_clause == nullptr);

        m_constraint.append(num_lits, lits);
        clean(s);

        if (m_unsat_constraint)
            return;

        // Freeze constraint variables by marking them external.
        // Track which ones we froze so we only unfreeze those.
        for (literal lit : m_constraint) {
            bool_var v = lit.var();
            if (!s.is_external(v)) {
                s.set_external(v);
                m_frozen_vars.push_back(v);
            }
        }
    }

    // -----------------------------------------------------------------------
    // activate -- add the constraint clause to the solver
    //
    // Called at the start of solve, after init_assumptions.
    // Returns false if the constraint is trivially UNSAT.
    //
    // Three cases by constraint size:
    //   1 literal:  assign as a scoped literal
    //   2 literals: add binary watches directly
    //   3+ lits:    allocate nary clause via mk_nary_clause
    // -----------------------------------------------------------------------
    bool constraint_manager::activate(solver& s) {
        if (m_unsat_constraint)
            return false;

        if (m_constraint.empty())
            return true;

        m_active = true;
        unsigned sz = m_constraint.size();

        if (sz == 1) {
            literal lit = m_constraint[0];
            if (s.value(lit) == l_undef) {
                s.assign_scoped(lit);
            }
            else if (s.value(lit) == l_false) {
                m_unsat_constraint = true;
                return false;
            }
            // l_true: constraint already satisfied.
            return true;
        }

        if (sz == 2) {
            // Add binary watch entries directly.  This avoids the complex
            // logic in mk_bin_clause that may elide the watches if the
            // clause already exists or triggers propagation.
            literal l1 = m_constraint[0];
            literal l2 = m_constraint[1];
            m_added_bin = true;
            s.get_bin_wlist(~l1).push_back(watched(l2, true));
            s.get_bin_wlist(~l2).push_back(watched(l1, true));
            if (s.m_config.m_drat)
                s.m_drat.add(l1, l2, status::redundant());
            return true;
        }

        // Nary clause (>= 3 literals).
        // mk_nary_clause allocates, attaches watches, and pushes to m_learned.
        literal_vector tmp(m_constraint);
        m_clause = s.mk_nary_clause(tmp.size(), tmp.data(),
                                     status::redundant());
        return true;
    }

    // -----------------------------------------------------------------------
    // reset -- remove the constraint and unfreeze variables
    //
    // Called after solve completes.  Removes the temporary clause,
    // unfreezes constraint variables, clears state.
    //
    // Reference: CaDiCaL constrain.cpp:55-61
    // -----------------------------------------------------------------------
    void constraint_manager::reset(solver& s) {
        // Remove nary clause: detach watches, remove from m_learned, free.
        if (m_clause) {
            s.detach_clause(*m_clause);
            // Remove from m_learned to prevent dangling pointer during GC.
            clause_vector& learned = s.m_learned;
            for (unsigned i = learned.size(); i-- > 0; ) {
                if (learned[i] == m_clause) {
                    learned[i] = learned.back();
                    learned.pop_back();
                    break;
                }
            }
            s.del_clause(*m_clause);
            m_clause = nullptr;
        }

        // Remove binary watch entries if we added them.
        if (m_added_bin && m_constraint.size() == 2) {
            literal l1 = m_constraint[0];
            literal l2 = m_constraint[1];
            s.get_bin_wlist(~l1).erase(watched(l2, true));
            s.get_bin_wlist(~l2).erase(watched(l1, true));
            if (s.m_config.m_drat)
                s.m_drat.del(l1, l2);
            m_added_bin = false;
        }

        // Unfreeze variables we froze.
        for (bool_var v : m_frozen_vars)
            s.set_non_external(v);
        m_frozen_vars.reset();

        // Clear state.
        m_constraint.reset();
        m_unsat_constraint = false;
        m_active = false;
    }

} // namespace sat
