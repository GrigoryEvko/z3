/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_flip.h

Abstract:

    Post-solve literal flipper for model improvement.

    Given a satisfying assignment, checks whether individual variable
    assignments can be toggled without falsifying any clause. This enables
    MaxSAT solvers, optimization passes, and neighborhood exploration of
    satisfying assignments.

    Ported from CaDiCaL's flip.cpp (Biere, Fleury, Heisinger 2020).
    Adapted to Z3's split watch list architecture (separate binary and
    large clause watches) and blocking literal conventions.

Author:

    Grigory Fedyukovich 2024

--*/
#pragma once

#include "sat/sat_types.h"

namespace sat {

    class solver;

    class literal_flipper {
        solver& m_solver;

        // Check all binary clauses containing 'lit' (currently true).
        // Returns false if any binary partner is false (flip would
        // create an all-false binary clause).
        bool check_binary(literal lit) const;

        // Check all large clause watches for 'lit' (currently true).
        // Uses blocking literals for fast skip, updates blocking
        // literals and clause pos as optimization hints (same as
        // CaDiCaL's flippable). Not const because of these updates.
        // Returns false if any watched large clause would become
        // all-false after the flip.
        bool check_large(literal lit);

        // Destructively process large clause watches for 'lit':
        // find replacement watches for each clause where 'lit' was
        // watched, move the watch to the replacement literal, and
        // compact the watch list. Returns false if any clause cannot
        // find a replacement AND has no other true literal (meaning
        // the flip would falsify it). On failure, the watch list may
        // be partially modified (caller must not flip the assignment).
        bool replace_watches(literal lit);

    public:
        explicit literal_flipper(solver& s);

        // Can variable v be flipped without falsifying any clause?
        // Updates blocking literals and saved clause positions as
        // optimization hints (not logically const).
        bool flippable(bool_var v);

        // Flip variable v's assignment and update watch lists.
        // Returns true on success, false if the flip would falsify
        // a clause (assignment unchanged in that case, but watch
        // lists for large clauses may have been partially reorganized).
        bool flip(bool_var v);
    };

}
