/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_flip.cpp

Abstract:

    Post-solve literal flipper for model improvement.

    Checks whether a variable's assignment can be toggled in a satisfying
    assignment without falsifying any clause, and if so, performs the
    flip including watch list updates.

    Key differences from CaDiCaL's flip.cpp:
      - Z3 separates binary watches (m_bin_watches) from large clause
        watches (m_watches). CaDiCaL has a unified watch list.
      - Z3 does not have CaDiCaL's propergate() mechanism. Instead,
        flippable() uses blocking literals for fast skip (read-only),
        while flip() ignores blocking literals and inspects clauses
        directly to ensure correctness.
      - Z3 has external constraint watches (EXT_CONSTRAINT). We
        conservatively reject flips for variables with ext constraints.
      - Assignment is stored as m_assignment[literal.index()] = l_true/l_false.

    Reference: CaDiCaL flip.cpp (Biere, Fleury, Heisinger 2020).

Author:

    Grigory Fedyukovich 2024

--*/

#include "sat/sat_flip.h"
#include "sat/sat_solver.h"

namespace sat {

    literal_flipper::literal_flipper(solver& s) : m_solver(s) {}

    // ---------------------------------------------------------------
    // Binary clause check (shared logic for flippable and flip).
    //
    // For a variable being flipped, the literal 'lit' is currently
    // TRUE. Binary clauses containing 'lit' are stored in
    // m_bin_watches[(~lit).index()] — these fire when lit is falsified.
    // Each watch entry stores the partner literal. If ANY partner is
    // false, the clause would become all-false after the flip.
    // ---------------------------------------------------------------

    bool literal_flipper::check_binary(literal lit) const {
        watch_list const& bwl = m_solver.get_bin_wlist(~lit);
        for (watched const& w : bwl) {
            SASSERT(w.is_binary_clause());
            if (m_solver.value(w.get_literal()) != l_true)
                return false;
        }
        return true;
    }

    // ---------------------------------------------------------------
    // Large clause flippable check (read-only, uses blocking literals).
    //
    // Scans m_watches[(~lit).index()] for CLAUSE watches. These are
    // clauses where 'lit' is a watched literal. When lit is falsified
    // (by the flip), we need the clause to still be satisfied.
    //
    // Uses blocking literals for fast path: if the blocking literal
    // is true, the clause is definitely satisfied regardless.
    //
    // For clauses where the blocking literal is not true, we inspect
    // the clause directly:
    //   1. Check the other watched literal. If true, clause is fine
    //      (update blocking literal as hint).
    //   2. Scan non-watched positions (starting from saved pos) for
    //      any true or undef literal. If found, clause survives
    //      (update saved pos and blocking literal).
    //   3. If nothing found, flip is impossible.
    //
    // This matches CaDiCaL's flippable() which uses blocking literals
    // and updates them as it goes.
    // ---------------------------------------------------------------

    bool literal_flipper::check_large(literal lit) {
        watch_list& wl = m_solver.m_watches[(~lit).index()];
        for (auto it = wl.begin(); it != wl.end(); ++it) {
            if (it->is_ext_constraint())
                return false;
            if (!it->is_clause())
                continue;

            // Fast path: blocking literal is true => clause satisfied
            if (m_solver.value(it->get_blocked_literal()) == l_true)
                continue;

            clause_offset cls_off = it->get_clause_offset();
            clause& c = m_solver.get_clause(cls_off);

            if (c.was_removed() || c.is_garbage())
                continue;

            // Find the other watched literal via XOR (CaDiCaL idiom).
            // c[0] and c[1] are the two watched literals. One of them
            // is 'lit'. The other is 'other'.
            literal other = to_literal(c[0].to_uint() ^ c[1].to_uint() ^ lit.to_uint());

            if (m_solver.value(other) == l_true) {
                // Other watched literal satisfies the clause.
                // Update blocking literal as optimization hint.
                it->set_blocked_literal(other);
                continue;
            }

            // Need to find a true literal among non-watched positions.
            unsigned sz = c.size();
            unsigned saved = c.pos();
            if (saved < 2) saved = 2;
            if (saved >= sz) saved = 2;

            bool found = false;

            // Scan from saved position to end
            for (unsigned k = saved; k < sz; ++k) {
                if (m_solver.value(c[k]) == l_true) {
                    c.set_pos(k);
                    it->set_blocked_literal(c[k]);
                    found = true;
                    break;
                }
            }

            if (!found) {
                // Wrap around: scan from position 2 to saved position
                for (unsigned k = 2; k < saved; ++k) {
                    if (m_solver.value(c[k]) == l_true) {
                        c.set_pos(k);
                        it->set_blocked_literal(c[k]);
                        found = true;
                        break;
                    }
                }
            }

            if (!found)
                return false;
        }
        return true;
    }

    // ---------------------------------------------------------------
    // Destructive watch replacement for flip().
    //
    // When we actually flip 'lit' from true to false, every large
    // clause that had 'lit' as a watched literal needs a replacement
    // watch. This is structurally identical to propagation: we scan
    // m_watches[(~lit).index()], and for each clause watch, try to
    // find a non-false literal to replace 'lit' as the watched
    // literal. If found, we move the watch entry to the replacement
    // literal's watch list and compact 'lit's list. If not found but
    // the other watched literal is true, the clause is fine (we keep
    // the watch). If neither, the flip fails.
    //
    // IMPORTANT: We do NOT use blocking literals here. CaDiCaL's
    // flip() also ignores blocking literals because the blocking
    // literal optimization can mask clauses that actually need watch
    // restructuring after a flip. This is why CaDiCaL has propergate().
    // ---------------------------------------------------------------

    bool literal_flipper::replace_watches(literal lit) {
        watch_list& wl = m_solver.m_watches[(~lit).index()];
        auto it = wl.begin();
        auto it2 = it;
        auto end = wl.end();
        bool ok = true;

        while (it != end) {
            // Copy-advance pattern (same as propagation)
            *it2 = *it;
            ++it;

            if (it2->is_ext_constraint()) {
                // Conservative: cannot reason about external constraints
                ok = false;
                ++it2;
                break;
            }

            if (!it2->is_clause()) {
                // Binary watches should not appear in m_watches
                ++it2;
                continue;
            }

            clause_offset cls_off = it2->get_clause_offset();
            clause& c = m_solver.get_clause(cls_off);

            if (c.was_removed() || c.is_garbage()) {
                // Skip removed/garbage clauses (drop the watch)
                // it2 not advanced => entry overwritten next iteration
                continue;
            }

            // Find the other watched literal.
            // One of c[0], c[1] is 'lit'; the other is 'other'.
            literal other = to_literal(c[0].to_uint() ^ c[1].to_uint() ^ lit.to_uint());
            lbool other_val = m_solver.value(other);

            if (other_val == l_true) {
                // Clause is satisfied by the other watched literal.
                // Keep the watch but update blocking literal.
                it2->set_blocked_literal(other);
                ++it2;
                continue;
            }

            // Normalize: put 'other' at c[0], 'lit' at c[1]
            c[0] = other;
            c[1] = lit;

            // Search for a replacement literal that is not false.
            unsigned sz = c.size();
            unsigned saved = c.pos();
            if (saved < 2) saved = 2;
            if (saved >= sz) saved = 2;

            bool found_replacement = false;

            // Scan from saved position to end
            for (unsigned k = saved; k < sz; ++k) {
                lbool v = m_solver.value(c[k]);
                if (v != l_false) {
                    // Found a replacement: swap c[k] into c[1] position
                    // and install a new watch for c[k]'s literal.
                    c.set_pos(k);
                    literal replacement = c[k];
                    c[1] = replacement;
                    c[k] = lit;

                    // Add watch to replacement literal's list.
                    // blocked literal = c[0] (the other watched literal).
                    m_solver.m_watches[(~replacement).index()].push_back(
                        watched(c[0], cls_off));

                    // Don't advance it2 => entry removed from lit's list
                    found_replacement = true;
                    break;
                }
            }

            if (!found_replacement) {
                // Wrap around: scan from position 2 to saved
                for (unsigned k = 2; k < saved; ++k) {
                    lbool v = m_solver.value(c[k]);
                    if (v != l_false) {
                        c.set_pos(k);
                        literal replacement = c[k];
                        c[1] = replacement;
                        c[k] = lit;

                        m_solver.m_watches[(~replacement).index()].push_back(
                            watched(c[0], cls_off));

                        found_replacement = true;
                        break;
                    }
                }
            }

            if (!found_replacement) {
                // All non-watched literals are false, AND 'other' (c[0])
                // is false (the true case was handled above). After the
                // flip, 'lit' goes false too => entire clause falsified.
                SASSERT(other_val != l_true);
                ok = false;
                ++it2;
                break;
            }
        }

        // Compact: copy remaining entries
        while (it != end) {
            *it2 = *it;
            ++it;
            ++it2;
        }
        wl.set_end(it2);

        return ok;
    }

    // ---------------------------------------------------------------
    // flippable(v): read-only check
    // ---------------------------------------------------------------

    bool literal_flipper::flippable(bool_var v) {
        if (v >= m_solver.num_vars())
            return false;

        lbool val = m_solver.value(v);
        if (val == l_undef)
            return false;

        // The literal currently assigned TRUE for this variable
        literal lit = literal(v, val == l_false);
        SASSERT(m_solver.value(lit) == l_true);

        // Phase 1: binary clauses (cheap, high failure rate)
        if (!check_binary(lit))
            return false;

        // Phase 2: large clauses (read-only with blocking literal optimization)
        if (!check_large(lit))
            return false;

        return true;
    }

    // ---------------------------------------------------------------
    // flip(v): destructive flip with watch list update
    // ---------------------------------------------------------------

    bool literal_flipper::flip(bool_var v) {
        if (v >= m_solver.num_vars())
            return false;

        lbool val = m_solver.value(v);
        if (val == l_undef)
            return false;

        // The literal currently TRUE for this variable
        literal lit = literal(v, val == l_false);
        SASSERT(m_solver.value(lit) == l_true);

        // Phase 1: check binary clauses (no watch modification needed
        // for binaries since both literals remain in both watch lists)
        if (!check_binary(lit))
            return false;

        // Phase 2: replace watches in large clauses
        if (!replace_watches(lit))
            return false;

        // Success: flip the assignment
        m_solver.m_assignment[lit.index()] = l_false;
        m_solver.m_assignment[(~lit).index()] = l_true;

        // Update phase to match new assignment.
        // Before flip: lit was TRUE, so m_phase[v] = !lit.sign().
        // After flip: ~lit is TRUE, so m_phase[v] = !(~lit).sign() = lit.sign().
        m_solver.m_phase[v] = lit.sign();

        return true;
    }

}
