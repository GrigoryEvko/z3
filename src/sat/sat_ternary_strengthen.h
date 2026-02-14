/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_ternary_strengthen.h

Abstract:

    CaDiCaL-style ternary clause strengthening via binary extraction.

    For each ternary clause (a, b, c), if a binary clause (-x, y) exists
    where x is one of {a, b, c} and y is another, then by resolution we
    derive a new binary clause from the remaining two literals. If the
    derived binary subsumes the ternary, the ternary is marked for deletion.

    Reference: CaDiCaL congruence.cpp:202-327 (extract_binaries)

Author:

    Grigory (2024)

--*/
#pragma once

#include "util/statistics.h"
#include "sat/sat_types.h"

namespace sat {

    class solver;

    class ternary_strengthen {
        solver&  m_solver;
        unsigned m_num_derived;   // new binary clauses derived
        unsigned m_num_subsumed;  // ternary clauses subsumed by derived binaries

        // Compact binary representation for sorted lookup.
        // Stores (lit1, lit2) where lit1.index() <= lit2.index().
        struct compact_binary {
            unsigned lit1;  // smaller literal index
            unsigned lit2;  // larger literal index
        };

        // Sorted array of compact binaries, partitioned by lit1.
        // For each literal index l, offset_table[l] = {begin, end}
        // into m_binaries where all entries have lit1 == l.
        svector<compact_binary>                    m_binaries;
        svector<std::pair<unsigned, unsigned>>      m_offset_table;

        void collect_and_sort_binaries();
        bool find_binary(literal l1, literal l2) const;
        void scan_ternaries();

    public:
        ternary_strengthen(solver& s);

        unsigned operator()();

        void collect_statistics(statistics& st) const;
        void reset_statistics();
    };

}
