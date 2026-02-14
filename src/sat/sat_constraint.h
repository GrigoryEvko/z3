/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_constraint.h

Abstract:

    CaDiCaL-style constraint clause manager for SAT solver.

    A constraint clause is a temporary disjunctive clause that is active only
    for a single solve call, then automatically reset.  This avoids the need
    for selector variables in model-checking patterns (IC3/PDR).

    The intended call sequence is:
        constrain(lits)  -- set the constraint for the next solve
        activate(s)      -- called at the start of solve to add the clause
        failed()         -- after UNSAT, query whether the constraint caused it
        reset(s)         -- called after solve to remove the clause and unfreeze

    If constrain() is called again before solve, the previous constraint is
    replaced (the old one is reset first).

    Reference: CaDiCaL constrain.cpp, external.cpp:296-316, assume.cpp:236-246

Author:

    Z3 contributors

--*/
#pragma once

#include "sat/sat_types.h"

namespace sat {

    class solver;

    class constraint_manager {
        /// The constraint literals (cleaned).
        literal_vector  m_constraint;

        /// Variables we marked external that were NOT already external.
        /// Only these are unmarked on reset.
        bool_var_vector m_frozen_vars;

        /// The clause pointer if the constraint was added as a clause.
        clause*         m_clause = nullptr;

        /// True when the constraint was non-empty but became empty after
        /// cleaning (all literals were root-level falsified), meaning the
        /// constraint is trivially UNSAT.
        bool            m_unsat_constraint = false;

        /// True when the constraint is currently active (between activate
        /// and reset).
        bool            m_active = false;

        /// True when we added binary watch entries directly (sz == 2 case).
        /// Used to know whether to remove them on reset.
        bool            m_added_bin = false;

        /// Clean the raw constraint: remove duplicates, tautologies, and
        /// root-level falsified literals.  If the constraint becomes empty,
        /// sets m_unsat_constraint.  If the constraint is satisfied at root
        /// level, clears it entirely (trivially satisfied).
        /// Must be called at base level (level 0).
        void clean(solver& s);

    public:
        constraint_manager() = default;

        /// Set a disjunctive constraint clause for the next solve call.
        /// If a constraint already exists (from a previous constrain() call
        /// that was not yet activated), it is replaced.
        /// The solver must be at base level.
        ///
        /// This cleans the input (dedup, tautology, falsified-lit removal),
        /// freezes constraint variables (marks them external to prevent
        /// elimination), and stores the result.
        ///
        /// Reference: CaDiCaL constrain.cpp:5-51, external.cpp:296-299
        void constrain(solver& s, unsigned num_lits, literal const* lits);
        void constrain(solver& s, literal_vector const& lits) {
            constrain(s, lits.size(), lits.data());
        }

        /// Called at the start of solve.  If the constraint is non-empty,
        /// adds it as a temporary clause to the solver.
        /// Returns false if the constraint was trivially UNSAT (empty after
        /// cleaning), in which case the solver should return UNSAT.
        bool activate(solver& s);

        /// Called after solve completes.  Removes the temporary clause,
        /// unfreezes constraint variables, and clears state.
        /// Reference: CaDiCaL constrain.cpp:55-61
        void reset(solver& s);

        /// After an UNSAT result, returns true if the UNSAT was caused by
        /// the constraint being falsified (all its literals were false
        /// under the current assignment/assumptions).
        /// Reference: CaDiCaL constrain.cpp:53
        bool failed() const { return m_unsat_constraint; }

        /// Returns true if a constraint is currently set (may or may not
        /// be activated yet).
        bool has_constraint() const { return !m_constraint.empty() || m_unsat_constraint; }

        /// Returns the constraint literals.
        literal_vector const& literals() const { return m_constraint; }

        /// Returns true if the constraint is currently active (between
        /// activate and reset).
        bool is_active() const { return m_active; }

        /// Mark the constraint as falsified.  Called from the UNSAT core
        /// extraction path when the solver determines that the conflict
        /// was caused by the constraint.
        void set_unsat_constraint() { m_unsat_constraint = true; }
    };

};
