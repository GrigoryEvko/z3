/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_ternary_strengthen.cpp

Abstract:

    CaDiCaL-style ternary clause strengthening via binary extraction.

    For each ternary clause (a, b, c), if a binary implication (-x, y)
    exists where x in {a,b,c} and y in {a,b,c}\{x}, then by resolution
    we derive a binary clause over the remaining two literals.

    Algorithm:
    1. Collect all irredundant binary clauses into a sorted compact array.
    2. Build a per-literal offset table for O(log n) binary-search lookup.
    3. For each irredundant ternary clause (a,b,c) with all literals
       unassigned, check all 6 possible resolution partners.
    4. If a new binary (l,k) is derived and not already present, add it.

    Reference: CaDiCaL congruence.cpp:202-327 (extract_binaries)

Author:

    Grigory (2024)

--*/
#include "sat/sat_ternary_strengthen.h"
#include "sat/sat_solver.h"
#include "util/stopwatch.h"
#include "util/trace.h"

#include <algorithm>

namespace sat {

    ternary_strengthen::ternary_strengthen(solver& s) : m_solver(s) {
        reset_statistics();
    }

    //
    // Collect all irredundant binary clauses into m_binaries in canonical
    // form (lit1.index() <= lit2.index()), then sort by (lit1, lit2).
    // Build m_offset_table so that m_offset_table[l] = {begin, end}
    // gives the range in m_binaries where all entries have lit1 == l.
    //
    void ternary_strengthen::collect_and_sort_binaries() {
        m_binaries.reset();

        unsigned num_lits = m_solver.num_vars() * 2;

        // Walk binary watch lists to collect all irredundant binaries.
        // Convention: m_bin_watches[~l] contains watched(l2) meaning
        // binary clause (l, l2). We only collect each clause once by
        // requiring l.index() < l2.index() (the watch is symmetric).
        for (unsigned l_idx = 0; l_idx < num_lits; ++l_idx) {
            literal l1 = ~to_literal(l_idx);
            watch_list const& wl = m_solver.get_bin_wlist(to_literal(l_idx));
            for (watched const& w : wl) {
                SASSERT(w.is_binary_clause());
                if (w.is_learned())
                    continue;
                literal l2 = w.get_literal();
                // Only collect once: smaller index first.
                if (l1.index() > l2.index())
                    continue;
                compact_binary cb;
                cb.lit1 = l1.index();
                cb.lit2 = l2.index();
                m_binaries.push_back(cb);
            }
        }

        // Sort by (lit1, lit2).
        std::sort(m_binaries.begin(), m_binaries.end(),
            [](compact_binary const& a, compact_binary const& b) {
                return a.lit1 < b.lit1 || (a.lit1 == b.lit1 && a.lit2 < b.lit2);
            });

        // Build offset table: for each literal index l,
        // m_offset_table[l] = {first_pos, past_end_pos} in m_binaries.
        m_offset_table.reset();
        m_offset_table.resize(num_lits, std::make_pair(0u, 0u));

        unsigned sz = m_binaries.size();
        unsigned i = 0;
        while (i < sz) {
            unsigned l = m_binaries[i].lit1;
            unsigned j = i;
            while (j < sz && m_binaries[j].lit1 == l)
                ++j;
            m_offset_table[l] = std::make_pair(i, j);
            i = j;
        }
    }

    //
    // O(log n) lookup: does an irredundant binary clause (l1, l2) exist?
    // Canonicalizes so the smaller literal index comes first.
    //
    bool ternary_strengthen::find_binary(literal l1, literal l2) const {
        unsigned idx1 = l1.index();
        unsigned idx2 = l2.index();
        if (idx1 > idx2)
            std::swap(idx1, idx2);

        if (idx1 >= m_offset_table.size())
            return false;

        auto const& range = m_offset_table[idx1];
        unsigned begin = range.first;
        unsigned end = range.second;
        if (begin >= end)
            return false;

        // Binary search for idx2 within the range where lit1 == idx1.
        compact_binary target;
        target.lit1 = idx1;
        target.lit2 = idx2;

        auto it = std::lower_bound(
            m_binaries.data() + begin,
            m_binaries.data() + end,
            target,
            [](compact_binary const& a, compact_binary const& b) {
                return a.lit2 < b.lit2;
            });

        return it != m_binaries.data() + end && it->lit2 == idx2;
    }

    //
    // Scan all irredundant ternary clauses. For each (a, b, c):
    //   If binary (-a, b) or (-a, c) exists => derive (b, c)
    //   If binary (-b, a) or (-b, c) exists => derive (a, c)
    //   If binary (-c, a) or (-c, b) exists => derive (a, b)
    //
    // Only the first matching resolution is applied per ternary clause
    // (CaDiCaL semantics). The derived binary is added if not already
    // present. Subsumption of the original ternary is NOT done here --
    // CaDiCaL leaves that to its general subsumption pass.
    //
    void ternary_strengthen::scan_ternaries() {
        unsigned derived = 0;
        unsigned already = 0;

        // We scan m_clauses (irredundant). Ternary learned clauses are
        // not worth strengthening -- they can be deleted by GC anyway.
        clause_vector const& clauses = m_solver.clauses();
        unsigned sz = clauses.size();

        for (unsigned i = 0; i < sz; ++i) {
            if (m_solver.inconsistent())
                break;

            clause const& c = *clauses[i];
            if (c.was_removed())
                continue;
            if (c.size() != 3)
                continue;

            literal a = c[0], b = c[1], cc = c[2];

            // Skip if any literal is already assigned (CaDiCaL check).
            if (m_solver.value(a) != l_undef)
                continue;
            if (m_solver.value(b) != l_undef)
                continue;
            if (m_solver.value(cc) != l_undef)
                continue;

            literal l = null_literal, k = null_literal;

            if (find_binary(~a, b) || find_binary(~a, cc)) {
                l = b; k = cc;
            }
            else if (find_binary(~b, a) || find_binary(~b, cc)) {
                l = a; k = cc;
            }
            else if (find_binary(~cc, a) || find_binary(~cc, b)) {
                l = a; k = b;
            }
            else {
                continue;
            }

            // Check if binary (l, k) already exists before adding.
            // The sorted table only has pre-existing binaries, so also
            // check the live watch lists to catch binaries derived
            // earlier in this same pass.
            if (!find_binary(l, k) &&
                !find_binary_watch(m_solver.get_bin_wlist(~l), k)) {
                m_solver.mk_clause(l, k, status::asserted());
                ++derived;
            }
            else {
                ++already;
            }
        }

        TRACE(sat_ternary_strengthen,
            tout << "ternary strengthen: derived=" << derived
                 << " already_present=" << already << "\n";);

        m_num_derived += derived;
    }

    unsigned ternary_strengthen::operator()() {
        if (m_solver.inconsistent())
            return 0;

        stopwatch sw;
        sw.start();

        unsigned old_derived = m_num_derived;

        // Phase 1: build sorted binary lookup table.
        collect_and_sort_binaries();

        // Phase 2: scan ternaries and derive new binaries.
        scan_ternaries();

        // Cleanup temporaries.
        m_binaries.reset();
        m_offset_table.reset();

        sw.stop();
        unsigned new_derived = m_num_derived - old_derived;
        IF_VERBOSE(2,
            if (new_derived > 0)
                verbose_stream() << " (sat-ternary-strengthen"
                                 << " :derived " << new_derived
                                 << sw << ")\n";);

        return new_derived;
    }

    void ternary_strengthen::collect_statistics(statistics& st) const {
        st.update("sat ternary derived", m_num_derived);
        st.update("sat ternary subsumed", m_num_subsumed);
    }

    void ternary_strengthen::reset_statistics() {
        m_num_derived = 0;
        m_num_subsumed = 0;
    }

}
