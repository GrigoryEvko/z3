/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_lucky.cpp

Abstract:

    Lucky phase pre-solving (CaDiCaL-style).

    Before entering the main CDCL loop, try up to 8 cheap satisfiability
    checks.  If any succeeds, we skip CDCL entirely and return SAT.  The
    cost of each check is O(clauses * max_clause_width) -- negligible
    compared to even a single restart.

    The 8 strategies are:
      1. trivially_false  - all variables false (every clause has a negative literal)
      2. trivially_true   - all variables true
      3. forward_false    - iterate vars 0..n, assign false, propagate
      4. forward_true     - mirror
      5. backward_false   - iterate vars n..0
      6. backward_true    - mirror
      7. positive_horn    - iterate clauses, first unassigned positive lit -> true
      8. negative_horn    - mirror

Author:

    Adapted from CaDiCaL lucky.cpp (Armin Biere) for Z3.

--*/

#include "sat/sat_solver.h"

namespace sat {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    // Undo all lucky-phase assignments and clear any conflict.
    // Returns |res| unchanged (pass-through for chaining).
    lbool solver::lucky_undo(lbool res) {
        if (scope_lvl() > m_search_lvl)
            pop(scope_lvl() - m_search_lvl);
        m_inconsistent = false;
        return res;
    }

    // Push a new decision level, assign literal, propagate.
    // Returns true if propagation succeeded (no conflict).
    bool solver::lucky_assign_propagate(literal lit) {
        push();
        assign_scoped(lit);
        return propagate(false);
    }

    // When a lucky decision at |dec| leads to conflict:
    //   - If we are more than one level above search level, backtrack one
    //     level and try the opposite polarity.
    //   - At the first decision level above search, just give up on this
    //     strategy (we cannot cheaply learn a unit without full analysis).
    //
    // Returns true if the strategy should abort (conflict irrecoverable).
    // Returns false if the opposite polarity was tried and propagation
    // succeeded (caller should re-check whether |dec.var()| is now assigned
    // and possibly continue to the next variable).
    bool solver::lucky_backtrack_flip(literal dec) {
        SASSERT(inconsistent());
        unsigned lvl_above_search = scope_lvl() - m_search_lvl;
        if (lvl_above_search > 1) {
            // Backtrack one level (undo the failed decision).
            m_inconsistent = false;
            pop(1);
            // Try opposite polarity.
            push();
            assign_scoped(~dec);
            if (propagate(false))
                return false;  // opposite worked
            return true;       // both polarities conflict at this depth
        }
        // At the bottom decision level -- cannot recover cheaply.
        return true;
    }

    // -----------------------------------------------------------------------
    // Strategy 1: Trivially false satisfiable
    // -----------------------------------------------------------------------
    // Check whether every irredundant clause contains a negative literal
    // (i.e., a literal whose variable appears negated).  If so, setting all
    // variables to false satisfies the formula.

    lbool solver::lucky_trivially_false() {
        // Check n-ary clauses.
        for (clause* cp : m_clauses) {
            clause& c = *cp;
            if (c.was_removed()) continue;
            bool satisfied = false;
            bool found_neg = false;
            for (literal lit : c) {
                lbool v = value(lit);
                if (v == l_true) { satisfied = true; break; }
                if (v == l_false) continue;
                // lit is unassigned
                if (lit.sign()) { found_neg = true; break; }
            }
            if (satisfied || found_neg) continue;
            return l_undef;  // clause has only positive unassigned lits
        }

        // Check binary clauses.
        unsigned sz = m_bin_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l1 = to_literal(l_idx);
            l1.neg();  // the actual literal in the clause
            for (watched const& w : m_bin_watches[l_idx]) {
                if (!w.is_binary_clause()) continue;
                if (w.is_learned()) continue;
                literal l2 = w.get_literal();
                if (l1.index() > l2.index()) continue;  // avoid duplicates
                lbool v1 = value(l1), v2 = value(l2);
                if (v1 == l_true || v2 == l_true) continue;  // satisfied
                // Need at least one negative unassigned literal.
                bool has_neg = false;
                if (v1 == l_undef && l1.sign()) has_neg = true;
                if (!has_neg && v2 == l_undef && l2.sign()) has_neg = true;
                if (!has_neg) return l_undef;
            }
        }

        // Every clause has a negative literal.  Assign all unassigned vars false.
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (value(v) != l_undef) continue;
            if (was_eliminated(v)) continue;
            if (!lucky_assign_propagate(literal(v, true)))  // v = false means literal(v, true) since sign=true means negated
                return lucky_undo(l_undef);
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.lucky trivially-false)\n");
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Strategy 2: Trivially true satisfiable
    // -----------------------------------------------------------------------

    lbool solver::lucky_trivially_true() {
        // Check n-ary clauses.
        for (clause* cp : m_clauses) {
            clause& c = *cp;
            if (c.was_removed()) continue;
            bool satisfied = false;
            bool found_pos = false;
            for (literal lit : c) {
                lbool v = value(lit);
                if (v == l_true) { satisfied = true; break; }
                if (v == l_false) continue;
                if (!lit.sign()) { found_pos = true; break; }
            }
            if (satisfied || found_pos) continue;
            return l_undef;
        }

        // Check binary clauses.
        unsigned sz = m_bin_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l1 = to_literal(l_idx);
            l1.neg();
            for (watched const& w : m_bin_watches[l_idx]) {
                if (!w.is_binary_clause()) continue;
                if (w.is_learned()) continue;
                literal l2 = w.get_literal();
                if (l1.index() > l2.index()) continue;
                lbool v1 = value(l1), v2 = value(l2);
                if (v1 == l_true || v2 == l_true) continue;
                bool has_pos = false;
                if (v1 == l_undef && !l1.sign()) has_pos = true;
                if (!has_pos && v2 == l_undef && !l2.sign()) has_pos = true;
                if (!has_pos) return l_undef;
            }
        }

        // Assign all unassigned vars true.
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (value(v) != l_undef) continue;
            if (was_eliminated(v)) continue;
            if (!lucky_assign_propagate(literal(v, false)))  // v = true
                return lucky_undo(l_undef);
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.lucky trivially-true)\n");
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Strategy 3: Forward false satisfiable
    // -----------------------------------------------------------------------
    // Iterate variables in increasing order.  Assign each to false, propagate.
    // On conflict, try true via lucky_backtrack_flip.

    lbool solver::lucky_forward_false() {
        for (unsigned v = 0; v < num_vars(); ++v) {
        retry_ff:
            if (value(v) != l_undef) continue;
            if (was_eliminated(v)) continue;
            literal dec = literal(v, true);  // false assignment
            if (!lucky_assign_propagate(dec)) {
                if (lucky_backtrack_flip(dec))
                    return lucky_undo(l_undef);
                goto retry_ff;  // re-check: v may now be assigned by flip propagation
            }
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.lucky forward-false)\n");
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Strategy 4: Forward true satisfiable
    // -----------------------------------------------------------------------

    lbool solver::lucky_forward_true() {
        for (unsigned v = 0; v < num_vars(); ++v) {
        retry_ft:
            if (value(v) != l_undef) continue;
            if (was_eliminated(v)) continue;
            literal dec = literal(v, false);  // true assignment
            if (!lucky_assign_propagate(dec)) {
                if (lucky_backtrack_flip(dec))
                    return lucky_undo(l_undef);
                goto retry_ft;
            }
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.lucky forward-true)\n");
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Strategy 5: Backward false satisfiable
    // -----------------------------------------------------------------------

    lbool solver::lucky_backward_false() {
        for (unsigned v = num_vars(); v-- > 0; ) {
        retry_bf:
            if (value(v) != l_undef) continue;
            if (was_eliminated(v)) continue;
            literal dec = literal(v, true);
            if (!lucky_assign_propagate(dec)) {
                if (lucky_backtrack_flip(dec))
                    return lucky_undo(l_undef);
                goto retry_bf;
            }
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.lucky backward-false)\n");
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Strategy 6: Backward true satisfiable
    // -----------------------------------------------------------------------

    lbool solver::lucky_backward_true() {
        for (unsigned v = num_vars(); v-- > 0; ) {
        retry_bt:
            if (value(v) != l_undef) continue;
            if (was_eliminated(v)) continue;
            literal dec = literal(v, false);
            if (!lucky_assign_propagate(dec)) {
                if (lucky_backtrack_flip(dec))
                    return lucky_undo(l_undef);
                goto retry_bt;
            }
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.lucky backward-true)\n");
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Strategy 7: Positive Horn satisfiable
    // -----------------------------------------------------------------------
    // For each irredundant clause, if it is not yet satisfied, find the first
    // unassigned positive literal and assign it true.  This handles Horn-like
    // formulas where each clause has at most one positive literal.

    lbool solver::lucky_positive_horn() {
        // Iterate n-ary clauses.
        for (clause* cp : m_clauses) {
            clause& c = *cp;
            if (c.was_removed()) continue;
            bool satisfied = false;
            literal pos_lit = null_literal;
            for (literal lit : c) {
                lbool v = value(lit);
                if (v == l_true) { satisfied = true; break; }
                if (v == l_false) continue;
                // unassigned
                if (!lit.sign() && pos_lit == null_literal) {
                    pos_lit = lit;
                    break;  // take first positive unassigned
                }
            }
            if (satisfied) continue;
            if (pos_lit == null_literal) return lucky_undo(l_undef);  // no positive unassigned
            if (!lucky_assign_propagate(pos_lit))
                return lucky_undo(l_undef);
        }

        // Handle binary clauses: iterate and find unsatisfied ones with a positive lit.
        unsigned sz = m_bin_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l1 = to_literal(l_idx);
            l1.neg();
            for (watched const& w : m_bin_watches[l_idx]) {
                if (!w.is_binary_clause()) continue;
                if (w.is_learned()) continue;
                literal l2 = w.get_literal();
                if (l1.index() > l2.index()) continue;
                lbool v1 = value(l1), v2 = value(l2);
                if (v1 == l_true || v2 == l_true) continue;  // satisfied
                // Find first positive unassigned literal.
                literal pos_lit = null_literal;
                if (v1 == l_undef && !l1.sign()) pos_lit = l1;
                else if (v2 == l_undef && !l2.sign()) pos_lit = l2;
                if (pos_lit == null_literal) return lucky_undo(l_undef);
                if (!lucky_assign_propagate(pos_lit))
                    return lucky_undo(l_undef);
            }
        }

        // Assign remaining unassigned variables to false.
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (value(v) != l_undef) continue;
            if (was_eliminated(v)) continue;
            if (!lucky_assign_propagate(literal(v, true)))
                return lucky_undo(l_undef);
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.lucky positive-horn)\n");
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Strategy 8: Negative Horn satisfiable
    // -----------------------------------------------------------------------

    lbool solver::lucky_negative_horn() {
        // Iterate n-ary clauses.
        for (clause* cp : m_clauses) {
            clause& c = *cp;
            if (c.was_removed()) continue;
            bool satisfied = false;
            literal neg_lit = null_literal;
            for (literal lit : c) {
                lbool v = value(lit);
                if (v == l_true) { satisfied = true; break; }
                if (v == l_false) continue;
                if (lit.sign() && neg_lit == null_literal) {
                    neg_lit = lit;
                    break;
                }
            }
            if (satisfied) continue;
            if (neg_lit == null_literal) return lucky_undo(l_undef);
            if (!lucky_assign_propagate(neg_lit))
                return lucky_undo(l_undef);
        }

        // Binary clauses.
        unsigned sz = m_bin_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l1 = to_literal(l_idx);
            l1.neg();
            for (watched const& w : m_bin_watches[l_idx]) {
                if (!w.is_binary_clause()) continue;
                if (w.is_learned()) continue;
                literal l2 = w.get_literal();
                if (l1.index() > l2.index()) continue;
                lbool v1 = value(l1), v2 = value(l2);
                if (v1 == l_true || v2 == l_true) continue;
                literal neg_lit = null_literal;
                if (v1 == l_undef && l1.sign()) neg_lit = l1;
                else if (v2 == l_undef && l2.sign()) neg_lit = l2;
                if (neg_lit == null_literal) return lucky_undo(l_undef);
                if (!lucky_assign_propagate(neg_lit))
                    return lucky_undo(l_undef);
            }
        }

        // Assign remaining unassigned variables to true.
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (value(v) != l_undef) continue;
            if (was_eliminated(v)) continue;
            if (!lucky_assign_propagate(literal(v, false)))
                return lucky_undo(l_undef);
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.lucky negative-horn)\n");
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Main entry point
    // -----------------------------------------------------------------------

    lbool solver::try_lucky_phases() {
        if (!m_config.m_lucky_phase)
            return l_undef;

        // Lucky phases only work when there is no extension (pure SAT).
        // With SMT theories, we cannot shortcut -- the theory solver must
        // validate any candidate model.
        if (m_ext)
            return l_undef;

        // Do not attempt if assumptions are present -- the interaction with
        // assumption levels is complex and the payoff is small.
        if (tracking_assumptions())
            return l_undef;

        SASSERT(scope_lvl() == m_search_lvl);

        IF_VERBOSE(2, verbose_stream() << "(sat.lucky trying 8 strategies)\n");

        lbool res;

        res = lucky_trivially_false();
        if (res != l_undef) goto done;

        res = lucky_trivially_true();
        if (res != l_undef) goto done;

        res = lucky_forward_false();
        if (res != l_undef) goto done;

        res = lucky_forward_true();
        if (res != l_undef) goto done;

        res = lucky_backward_false();
        if (res != l_undef) goto done;

        res = lucky_backward_true();
        if (res != l_undef) goto done;

        res = lucky_positive_horn();
        if (res != l_undef) goto done;

        res = lucky_negative_horn();
        if (res != l_undef) goto done;

        return l_undef;

    done:
        if (res == l_true) {
            mk_model();
            return l_true;
        }
        return res;
    }

}  // namespace sat
