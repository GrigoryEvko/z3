/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_congruence.cpp

Abstract:

    SAT-level congruence closure for propositional gate detection and
    equivalence discovery.

    Implements the CaDiCaL 3.0 SAT 2024 algorithm adapted to Z3:
      1. Extract binary implications, strengthen ternary clauses
      2. Extract AND / XOR / ITE gates from clauses
      3. Hash gates by (type, sorted_rhs) -- congruent gates share RHS
      4. Dual union-find tracks equivalences (lazy + eager)
      5. Eagerly rewrite gates on equivalence discovery, cascade until fixpoint
      6. Forward-subsume clauses using equivalence normalization

Author:

    Grigory (2024)

--*/
#include "sat/sat_congruence.h"
#include "sat/sat_solver.h"
#include "util/trace.h"

#include <algorithm>

namespace sat {

    // ================================================================
    // Construction / Destruction
    // ================================================================

    congruence::congruence(solver& s)
        : m_solver(s),
          m_gate_table(128, gate_hash(m_nonces), gate_eq()) {
    }

    congruence::~congruence() {
        reset_closure();
    }

    // ================================================================
    // Solver access helpers
    // ================================================================

    lbool congruence::value(literal l) const { return m_solver.value(l); }
    lbool congruence::value(bool_var v) const { return m_solver.value(v); }
    unsigned congruence::num_vars() const { return m_solver.num_vars(); }
    bool congruence::is_eliminated(bool_var v) const { return m_solver.was_eliminated(v); }

    // ================================================================
    // Marking helpers
    // ================================================================

    int8_t& congruence::marked(literal l) {
        return m_marks[l.index()];
    }

    void congruence::set_mark(literal l, int8_t val) {
        m_marks[l.index()] = val;
        m_marked_lits.push_back(l);
    }

    void congruence::unmark_all() {
        for (literal l : m_marked_lits)
            m_marks[l.index()] = 0;
        m_marked_lits.reset();
    }

    // ================================================================
    // Literal sorting
    // ================================================================

    void congruence::sort_lits_by_var(literal_vector& lits) {
        std::sort(lits.begin(), lits.end(),
            [](literal a, literal b) { return a.var() < b.var(); });
    }

    // ================================================================
    // Gate occurrence lists
    // ================================================================

    gate_occ_list& congruence::goccs(literal l) {
        unsigned idx = l.index();
        while (m_goccs.size() <= idx)
            m_goccs.push_back(gate_occ_list());
        return m_goccs[idx];
    }

    void congruence::connect_goccs(gate* g, literal lit) {
        goccs(lit).push_back(g);
    }

    void congruence::mark_gate_garbage(gate* g) {
        if (g->m_garbage) return;
        g->m_garbage = true;
        m_garbage_gates.push_back(g);
    }

    // ================================================================
    // Gate table management
    // ================================================================

    gate* congruence::find_gate_in_table(gate_type type, literal_vector& rhs_sorted) {
        m_search_gate.m_type = type;
        m_search_gate.m_rhs.reset();
        m_search_gate.m_rhs.append(rhs_sorted);
        auto it = m_gate_table.find(&m_search_gate);
        if (it != m_gate_table.end())
            return *it;
        return nullptr;
    }

    void congruence::index_gate(gate* g) {
        m_gate_table.insert(g);
        g->m_indexed = true;
    }

    bool congruence::remove_gate_from_table(gate* g) {
        if (!g->m_indexed) return false;
        auto it = m_gate_table.find(g);
        if (it != m_gate_table.end()) {
            m_gate_table.erase(it);
            g->m_indexed = false;
            return true;
        }
        return false;
    }

    // ================================================================
    // Union-Find (Dual: Lazy + Eager)
    // ================================================================

    // Ensure union-find arrays are large enough for literal l.
    static inline void ensure_repr(svector<unsigned>& repr, unsigned idx) {
        while (repr.size() <= idx)
            repr.push_back(static_cast<unsigned>(repr.size()));
    }

    literal congruence::find_repr(literal l) {
        unsigned idx = l.index();
        ensure_repr(m_repr, idx);
        unsigned res = idx;
        unsigned nxt = idx;
        do {
            res = nxt;
            ensure_repr(m_repr, res);
            nxt = m_repr[res];
        } while (nxt != res);
        return to_literal(res);
    }

    literal congruence::find_repr_compress(literal l) {
        unsigned idx = l.index();
        ensure_repr(m_repr, idx);
        unsigned res = idx;
        unsigned nxt = idx;
        do {
            res = nxt;
            ensure_repr(m_repr, res);
            nxt = m_repr[res];
        } while (nxt != res);

        // Path compression for lit and ~lit.
        if (idx != res) {
            m_repr[idx] = res;
            // Compress negation too: repr(~l) = ~repr(l)
            literal neg_l = ~l;
            literal neg_res = ~to_literal(res);
            unsigned neg_idx = neg_l.index();
            ensure_repr(m_repr, neg_idx);
            m_repr[neg_idx] = neg_res.index();
        }
        return to_literal(res);
    }

    literal congruence::find_eager_repr(literal l) {
        unsigned idx = l.index();
        ensure_repr(m_eager_repr, idx);
        unsigned res = idx;
        unsigned nxt = idx;
        do {
            res = nxt;
            ensure_repr(m_eager_repr, res);
            nxt = m_eager_repr[res];
        } while (nxt != res);
        return to_literal(res);
    }

    void congruence::set_repr(literal l, literal repr) {
        unsigned idx = l.index();
        ensure_repr(m_repr, idx);
        m_repr[idx] = repr.index();
        // Also set negation.
        unsigned neg_idx = (~l).index();
        ensure_repr(m_repr, neg_idx);
        m_repr[neg_idx] = (~repr).index();
    }

    void congruence::set_eager_repr(literal l, literal repr) {
        unsigned idx = l.index();
        ensure_repr(m_eager_repr, idx);
        m_eager_repr[idx] = repr.index();
        unsigned neg_idx = (~l).index();
        ensure_repr(m_eager_repr, neg_idx);
        m_eager_repr[neg_idx] = (~repr).index();
    }

    bool congruence::are_equal(literal a, literal b) {
        return find_repr(a) == find_repr(b);
    }

    // ================================================================
    // Initialization / Reset
    // ================================================================

    void congruence::init_closure() {
        unsigned nv = num_vars();
        unsigned nl = 2 * nv;

        // Initialize union-find: every literal maps to itself.
        m_repr.resize(nl + 2);
        m_eager_repr.resize(nl + 2);
        for (unsigned i = 0; i < nl + 2; ++i) {
            m_repr[i] = i;
            m_eager_repr[i] = i;
        }

        m_marks.resize(nl + 2, 0);
        m_scheduled.resize(nv + 1, false);
        m_goccs.reset();

        // Generate random nonces for hashing.
        // Use a simple LCG seeded by number of variables.
        uint64_t seed = static_cast<uint64_t>(nv) * 6364136223846793005ULL + 1442695040888963407ULL;
        for (uint64_t& n : m_nonces) {
            seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
            n = seed | 1ULL; // ensure odd for multiplicative hashing
        }

        // Rebuild the gate table with new nonces.
        m_gate_table = gate_table(128, gate_hash(m_nonces), gate_eq());
    }

    void congruence::reset_closure() {
        // Free all gates in the table.
        for (gate* g : m_gate_table) {
            if (!g->m_garbage)
                dealloc(g);
        }
        m_gate_table.clear();

        for (gate* g : m_garbage_gates)
            dealloc(g);
        m_garbage_gates.reset();

        m_goccs.reset();
        m_scheduled.reset();
        m_marks.reset();
        m_marked_lits.reset();
        m_binaries.reset();
        m_bin_offsets.reset();
        m_large_occ_count.reset();

        // Clear the schedule.
        while (!m_schedule.empty()) m_schedule.pop();
    }

    // ================================================================
    // Binary Extraction and Ternary Strengthening
    // ================================================================

    void congruence::extract_binaries() {
        TRACE(sat_congruence, tout << "extracting binaries\n";);

        // Collect all binary clauses into a sorted array for O(log n) lookup.
        m_binaries.reset();

        // Collect from binary watch lists.
        unsigned nv = num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            if (is_eliminated(v)) continue;
            for (unsigned sign = 0; sign < 2; ++sign) {
                literal l(v, sign != 0);
                watch_list const& wl = m_solver.get_bin_wlist(l);
                for (watched const& w : wl) {
                    if (!w.is_binary_clause()) continue;
                    literal other = w.get_literal();
                    // Only store each binary once: when l < other.
                    if (l.index() < other.index()) {
                        m_binaries.push_back(compact_binary(l, other));
                    }
                }
            }
        }

        // Sort binaries by (lit1.index, lit2.index).
        std::sort(m_binaries.begin(), m_binaries.end(),
            [](compact_binary const& a, compact_binary const& b) {
                if (a.m_lit1.index() != b.m_lit1.index())
                    return a.m_lit1.index() < b.m_lit1.index();
                return a.m_lit2.index() < b.m_lit2.index();
            });

        // Remove duplicates.
        unsigned j = 0;
        for (unsigned i = 0; i < m_binaries.size(); ++i) {
            if (i > 0 &&
                m_binaries[i].m_lit1 == m_binaries[i-1].m_lit1 &&
                m_binaries[i].m_lit2 == m_binaries[i-1].m_lit2)
                continue;
            m_binaries[j++] = m_binaries[i];
        }
        m_binaries.shrink(j);

        // Build offset table for fast per-literal binary lookup.
        unsigned max_lit_idx = 2 * nv + 2;
        m_bin_offsets.resize(max_lit_idx, bin_offset(0, 0));
        {
            unsigned i = 0;
            while (i < m_binaries.size()) {
                unsigned lit_idx = m_binaries[i].m_lit1.index();
                unsigned start = i;
                while (i < m_binaries.size() && m_binaries[i].m_lit1.index() == lit_idx)
                    ++i;
                if (lit_idx < m_bin_offsets.size())
                    m_bin_offsets[lit_idx] = bin_offset(start, i);
            }
        }

        // Ternary strengthening: for ternary clause (a, b, c), if binary
        // (-a, b) exists, derive binary (b, c) by resolution.
        unsigned derived = 0;
        for (clause* cp : m_solver.clauses()) {
            if (cp->was_removed()) continue;
            if (cp->is_learned()) continue;
            if (cp->size() != 3) continue;

            literal a = (*cp)[0], b = (*cp)[1], c = (*cp)[2];
            if (value(a) != l_undef || value(b) != l_undef || value(c) != l_undef)
                continue;

            // Try each literal as the resolvent pivot.
            literal l1 = null_literal, l2 = null_literal;
            if (find_binary(~a, b) || find_binary(~a, c)) {
                l1 = b; l2 = c;
            } else if (find_binary(~b, a) || find_binary(~b, c)) {
                l1 = a; l2 = c;
            } else if (find_binary(~c, a) || find_binary(~c, b)) {
                l1 = a; l2 = b;
            } else {
                continue;
            }

            // Derive binary (l1, l2) if not already present.
            if (!find_binary(l1, l2)) {
                // Add the binary clause to the solver.
                m_solver.mk_clause(l1, l2);
                ++derived;
            }
        }

        // Rebuild binary array after adding new binaries.
        if (derived > 0) {
            m_binaries.reset();
            for (unsigned v = 0; v < nv; ++v) {
                if (is_eliminated(v)) continue;
                for (unsigned sign = 0; sign < 2; ++sign) {
                    literal l(v, sign != 0);
                    watch_list const& wl = m_solver.get_bin_wlist(l);
                    for (watched const& w : wl) {
                        if (!w.is_binary_clause()) continue;
                        literal other = w.get_literal();
                        if (l.index() < other.index())
                            m_binaries.push_back(compact_binary(l, other));
                    }
                }
            }
            std::sort(m_binaries.begin(), m_binaries.end(),
                [](compact_binary const& a, compact_binary const& b) {
                    if (a.m_lit1.index() != b.m_lit1.index())
                        return a.m_lit1.index() < b.m_lit1.index();
                    return a.m_lit2.index() < b.m_lit2.index();
                });
            j = 0;
            for (unsigned i = 0; i < m_binaries.size(); ++i) {
                if (i > 0 &&
                    m_binaries[i].m_lit1 == m_binaries[i-1].m_lit1 &&
                    m_binaries[i].m_lit2 == m_binaries[i-1].m_lit2)
                    continue;
                m_binaries[j++] = m_binaries[i];
            }
            m_binaries.shrink(j);

            unsigned max_idx = 2 * nv + 2;
            m_bin_offsets.reset();
            m_bin_offsets.resize(max_idx, bin_offset(0, 0));
            unsigned i = 0;
            while (i < m_binaries.size()) {
                unsigned lit_idx = m_binaries[i].m_lit1.index();
                unsigned start = i;
                while (i < m_binaries.size() && m_binaries[i].m_lit1.index() == lit_idx)
                    ++i;
                if (lit_idx < m_bin_offsets.size())
                    m_bin_offsets[lit_idx] = bin_offset(start, i);
            }
        }

        TRACE(sat_congruence, tout << "derived " << derived << " binary clauses from ternary strengthening\n";);
    }

    bool congruence::find_binary(literal a, literal b) const {
        // Normalize: ensure a.index() < b.index().
        if (a.index() > b.index()) std::swap(a, b);
        unsigned idx = a.index();
        if (idx >= m_bin_offsets.size()) return false;
        bin_offset bo = m_bin_offsets[idx];
        if (bo.m_start >= bo.m_end) return false;
        unsigned start = bo.m_start;
        unsigned end = bo.m_end;

        // Binary search for b in [start, end).
        compact_binary target(a, b);
        auto begin_it = m_binaries.begin() + start;
        auto end_it   = m_binaries.begin() + end;
        auto it = std::lower_bound(begin_it, end_it, target,
            [](compact_binary const& x, compact_binary const& t) {
                return x.m_lit2.index() < t.m_lit2.index();
            });
        return it != end_it && it->m_lit2 == b;
    }

    // ================================================================
    // AND Gate Extraction
    // ================================================================

    void congruence::extract_and_gates() {
        TRACE(sat_congruence, tout << "extracting AND gates\n";);

        for (clause* cp : m_solver.clauses()) {
            if (m_solver.inconsistent()) break;
            if (cp->was_removed()) continue;
            if (cp->is_learned()) continue;
            if (cp->size() < 3) continue;
            extract_and_gate_from_clause(*cp);
        }
    }

    void congruence::extract_and_gate_from_clause(clause& c) {
        // A long clause (lhs, ~a, ~b, ~c, ...) defines lhs = AND(a, b, c, ...)
        // if for each rhs literal x, the binary clause (~lhs, x) exists.
        //
        // To find AND gates: for each literal lhs in c, check if all other
        // literals ~rhs_i have corresponding binary clauses (~lhs, rhs_i).
        //
        // We mark all literals in the clause, then for each potential LHS,
        // check binary implications from ~lhs.

        m_lits.reset();
        for (literal l : c) {
            if (value(l) == l_true) return;  // clause is satisfied
            if (value(l) == l_false) continue; // skip falsified
            m_lits.push_back(l);
        }
        if (m_lits.size() < 3) return;

        unsigned arity = m_lits.size() - 1;

        // Mark all negated non-LHS literals with mark 1.
        for (literal l : m_lits) {
            set_mark(~l, 1);
        }

        // Try each literal as LHS.
        for (literal lhs : m_lits) {
            // For lhs = AND(rhs), the clause is (lhs, ~rhs[0], ~rhs[1], ...).
            // We need binary (~lhs, rhs[i]) for each i, where rhs[i] = ~(clause lit).
            //
            // Strategy: mark all clause literals with mark 1, then scan
            // binaries from ~lhs. For each binary (~lhs, other), if
            // ~other is in the clause (i.e., marked) and ~other != lhs,
            // mark ~other with mark 2. After scanning, count mark-2 entries.
            // This correctly handles duplicates since each literal is marked
            // at most once.
            watch_list const& wl = m_solver.get_bin_wlist(~lhs);
            unsigned matched = 0;
            for (watched const& w : wl) {
                if (!w.is_binary_clause()) continue;
                literal other = w.get_literal();
                // other is a RHS candidate. We need ~other to be in the
                // clause (marked) and ~other != lhs.
                // Since we marked ~l for each l in clause, checking
                // marked(other) tests if other = ~l for some l in clause.
                if (marked(other) && other != ~lhs && !(marked(other) & 2)) {
                    // Use bit 2 to avoid double-counting.
                    m_marks[other.index()] |= 2;
                    ++matched;
                }
            }
            // Clean up mark-2 bits.
            for (watched const& w : wl) {
                if (!w.is_binary_clause()) continue;
                literal other = w.get_literal();
                m_marks[other.index()] &= ~2;
            }

            if (matched >= arity) {
                // Build the RHS.
                m_rhs.reset();
                for (literal l : m_lits) {
                    if (l != lhs) {
                        m_rhs.push_back(~l);
                    }
                }
                sort_lits_by_var(m_rhs);

                // Check if a gate with the same RHS already exists.
                gate* existing = find_gate_in_table(gate_type::AND_GATE, m_rhs);
                if (existing) {
                    // Congruence: lhs and existing->m_lhs must be equivalent.
                    if (lhs != existing->m_lhs && !are_equal(lhs, existing->m_lhs)) {
                        merge_literals(lhs, existing->m_lhs);
                        ++m_num_equivs;
                    }
                } else {
                    // Create new gate.
                    gate* g = alloc(gate);
                    g->m_lhs = lhs;
                    g->m_type = gate_type::AND_GATE;
                    g->m_rhs.append(m_rhs);
                    index_gate(g);
                    for (literal rl : g->m_rhs) {
                        connect_goccs(g, rl);
                    }
                    ++m_num_gates;
                    ++m_num_and;
                }
            }
        }

        unmark_all();
    }

    // ================================================================
    // XOR Gate Extraction
    // ================================================================

    unsigned congruence::parity_lits(literal_vector const& lits) const {
        unsigned p = 0;
        for (literal l : lits) {
            if (l.sign()) ++p;
        }
        return p & 1;
    }

    void congruence::inc_lits(literal_vector& lits) {
        // Increment the sign pattern: flip the sign of the first literal,
        // carry if it wraps back.
        for (unsigned i = 0; i < lits.size(); ++i) {
            lits[i] = ~lits[i];
            if (lits[i].sign()) return; // no carry
        }
    }

    void congruence::init_large_occ_counts() {
        unsigned nl = 2 * num_vars() + 2;
        m_large_occ_count.resize(nl, 0);
        for (unsigned i = 0; i < nl; ++i) m_large_occ_count[i] = 0;

        for (clause* cp : m_solver.clauses()) {
            if (cp->was_removed()) continue;
            if (cp->is_learned()) continue;
            if (cp->size() < 3) continue;
            for (literal l : *cp) {
                unsigned idx = l.index();
                if (idx < m_large_occ_count.size())
                    m_large_occ_count[idx]++;
            }
        }
    }

    unsigned congruence::large_occ_count(literal l) const {
        unsigned idx = l.index();
        if (idx >= m_large_occ_count.size()) return 0;
        return m_large_occ_count[idx];
    }

    clause* congruence::find_large_xor_side_clause(literal_vector& lits) {
        // Mark all literals.
        for (literal l : lits) {
            set_mark(l, 1);
        }

        // Find a clause that contains exactly these literals.
        // Use the literal with fewest occurrences as the pivot.
        literal pivot = lits[0];
        unsigned min_occ = large_occ_count(lits[0]);
        for (unsigned i = 1; i < lits.size(); ++i) {
            unsigned oc = large_occ_count(lits[i]);
            if (oc < min_occ) {
                min_occ = oc;
                pivot = lits[i];
            }
        }

        clause* result = nullptr;

        // Search through clauses containing pivot via the solver's watch lists.
        // For clauses of size == lits.size(), check all literals are marked.
        for (clause* cp : m_solver.clauses()) {
            if (cp->was_removed()) continue;
            if (cp->is_learned()) continue;
            if (cp->size() != lits.size()) continue;
            if (!cp->contains(pivot)) continue;

            bool match = true;
            for (literal l : *cp) {
                if (value(l) == l_true) { match = false; break; }
                if (value(l) == l_false) { match = false; break; }
                if (!marked(l)) { match = false; break; }
            }
            if (match) {
                result = cp;
                break;
            }
        }

        unmark_all();
        return result;
    }

    void congruence::extract_xor_gates() {
        TRACE(sat_congruence, tout << "extracting XOR gates\n";);
        init_large_occ_counts();

        for (clause* cp : m_solver.clauses()) {
            if (m_solver.inconsistent()) break;
            if (cp->was_removed()) continue;
            if (cp->is_learned()) continue;
            if (cp->size() < 3 || cp->size() > 6) continue; // limit XOR arity
            extract_xor_gate_from_clause(*cp);
        }
    }

    void congruence::extract_xor_gate_from_clause(clause& c) {
        // Build the literal list, skip assigned.
        m_lits.reset();
        unsigned negated = 0;
        for (literal l : c) {
            lbool v = value(l);
            if (v == l_true) return; // satisfied
            if (v == l_false) continue;
            m_lits.push_back(l);
            if (l.sign()) ++negated;
        }
        if (m_lits.size() < 3) return;

        unsigned arity = m_lits.size() - 1;
        unsigned needed_clauses = 1u << (arity - 1);

        // Occurrence counting pre-filter: each literal (both signs) must
        // appear at least needed_clauses times in long clauses.
        for (literal l : m_lits) {
            if (large_occ_count(l) < needed_clauses) return;
            if (large_occ_count(~l) < needed_clauses) return;
        }

        // Ensure at most one negated literal in the base clause.
        if (negated > 1) return;

        // Sort literals by variable for canonical form.
        std::sort(m_lits.begin(), m_lits.end(),
            [](literal a, literal b) { return a.var() < b.var(); });

        // Enumerate all 2^(arity-1) parity-consistent side clauses.
        unsigned base_parity = parity_lits(m_lits);
        unsigned end = 1u << arity;
        literal_vector work_lits;
        work_lits.append(m_lits);

        for (unsigned i = 0; i < end; ++i) {
            while (i > 0 && parity_lits(work_lits) != base_parity)
                inc_lits(work_lits);

            if (i > 0) {
                clause* side = find_large_xor_side_clause(work_lits);
                if (!side) return; // not all side clauses found
            }
            inc_lits(work_lits);
        }

        // Restore base parity.
        while (parity_lits(work_lits) != base_parity)
            inc_lits(work_lits);

        // Normalize: ensure all RHS literals are positive.
        if (negated) {
            for (unsigned i = 0; i < work_lits.size(); ++i) {
                if (work_lits[i].sign()) {
                    work_lits[i] = ~work_lits[i];
                    break;
                }
            }
        }

        // Extract with each literal as LHS.
        for (literal lhs_raw : work_lits) {
            literal lhs = negated ? lhs_raw : ~lhs_raw;

            m_rhs.reset();
            for (literal l : work_lits) {
                if (l.var() != lhs.var()) {
                    // XOR RHS literals are always stored as positive variables.
                    m_rhs.push_back(literal(l.var(), false));
                }
            }
            sort_lits_by_var(m_rhs);

            gate* existing = find_gate_in_table(gate_type::XOR_GATE, m_rhs);
            if (existing) {
                if (lhs != existing->m_lhs && !are_equal(lhs, existing->m_lhs)) {
                    merge_literals(lhs, existing->m_lhs);
                    ++m_num_equivs;
                }
            } else {
                gate* g = alloc(gate);
                g->m_lhs = lhs;
                g->m_type = gate_type::XOR_GATE;
                g->m_rhs.append(m_rhs);
                index_gate(g);
                for (literal rl : g->m_rhs)
                    connect_goccs(g, rl);
                ++m_num_gates;
                ++m_num_xor;
            }
            if (m_solver.inconsistent()) return;
        }
    }

    // ================================================================
    // ITE Gate Extraction
    // ================================================================

    void congruence::extract_ite_gates() {
        TRACE(sat_congruence, tout << "extracting ITE gates\n";);

        for (unsigned v = 0; v < num_vars(); ++v) {
            if (m_solver.inconsistent()) break;
            if (is_eliminated(v)) continue;
            if (value(v) != l_undef) continue;
            extract_ite_gates_for_var(v);
        }
    }

    void congruence::extract_ite_gates_for_var(bool_var v) {
        literal pos(v, false);
        literal neg(v, true);
        // Pick the polarity with fewer ternary clause occurrences.
        // For simplicity, try both.
        extract_ite_gates_for_lit(pos);
        extract_ite_gates_for_lit(neg);
    }

    void congruence::extract_ite_gates_for_lit(literal cond) {
        // Collect conditional implications from ternary clauses containing cond.
        // A ternary clause (cond, a, b) means: if ~cond then (~a => b) and (~b => a).
        // These are "conditional binary implications" under ~cond.
        //
        // We look for matching pairs:
        //   (cond, a, b)   => under ~cond: -a => b
        //   (~cond, -a, c) => under cond:  a => c
        // Together: a = ITE(~cond, b, c) = ITE(cond, c, b)
        // Or equivalently: lhs = ITE(cond, then, else)

        struct cond_impl {
            literal first, second;
            cond_impl(literal f, literal s) : first(f), second(s) {}
        };
        svector<cond_impl> pos_impls, neg_impls;

        // Gather conditional implications under cond and ~cond from ternaries.
        for (clause* cp : m_solver.clauses()) {
            if (cp->was_removed()) continue;
            if (cp->is_learned()) continue;
            if (cp->size() != 3) continue;

            literal l0 = (*cp)[0], l1 = (*cp)[1], l2 = (*cp)[2];
            if (value(l0) != l_undef || value(l1) != l_undef || value(l2) != l_undef)
                continue;

            // Check if cond appears in the clause.
            if (l0 == cond) {
                // (cond, l1, l2): under ~cond => ~l1 => l2 and ~l2 => l1
                pos_impls.push_back(cond_impl(~l1, l2));
                pos_impls.push_back(cond_impl(~l2, l1));
            } else if (l1 == cond) {
                pos_impls.push_back(cond_impl(~l0, l2));
                pos_impls.push_back(cond_impl(~l2, l0));
            } else if (l2 == cond) {
                pos_impls.push_back(cond_impl(~l0, l1));
                pos_impls.push_back(cond_impl(~l1, l0));
            } else if (l0 == ~cond) {
                neg_impls.push_back(cond_impl(~l1, l2));
                neg_impls.push_back(cond_impl(~l2, l1));
            } else if (l1 == ~cond) {
                neg_impls.push_back(cond_impl(~l0, l2));
                neg_impls.push_back(cond_impl(~l2, l0));
            } else if (l2 == ~cond) {
                neg_impls.push_back(cond_impl(~l0, l1));
                neg_impls.push_back(cond_impl(~l1, l0));
            }
        }

        if (pos_impls.empty() || neg_impls.empty()) return;

        // Sort both by first literal for matching.
        auto cmp = [](cond_impl const& a, cond_impl const& b) {
            return a.first.index() < b.first.index();
        };
        std::sort(pos_impls.begin(), pos_impls.end(), cmp);
        std::sort(neg_impls.begin(), neg_impls.end(), cmp);

        // Match pairs with the same first literal to form conditional equivalences.
        // pos_impl (a, b):  under ~cond, a => b
        // neg_impl (a, c):  under  cond, a => c
        // If we also have:
        // pos_impl (-b, -a): under ~cond, -b => -a (contrapositive, already present)
        // neg_impl (-c, -a): under  cond, -c => -a
        // Then: a = ITE(cond, c, b)

        unsigned pi = 0, ni = 0;
        while (pi < pos_impls.size() && ni < neg_impls.size()) {
            if (pos_impls[pi].first.index() < neg_impls[ni].first.index()) {
                ++pi;
            } else if (pos_impls[pi].first.index() > neg_impls[ni].first.index()) {
                ++ni;
            } else {
                // Same first literal => we have a conditional equivalence candidate.
                // Scan all pos/neg implications with this first literal.
                unsigned pi_end = pi, ni_end = ni;
                literal first = pos_impls[pi].first;
                while (pi_end < pos_impls.size() && pos_impls[pi_end].first == first) ++pi_end;
                while (ni_end < neg_impls.size() && neg_impls[ni_end].first == first) ++ni_end;

                for (unsigned p = pi; p < pi_end; ++p) {
                    literal a = pos_impls[p].first;   // = first
                    literal b = pos_impls[p].second;  // under ~cond, a => b
                    for (unsigned n = ni; n < ni_end; ++n) {
                        literal c = neg_impls[n].second;  // under cond, a => c

                        // We also need the reverse: under ~cond, ~b => ~a, and under cond, ~c => ~a.
                        // These are contrapositives and should already exist if the original clauses do.
                        // The ITE is: a = ITE(cond, c, b)
                        // But we must verify the back-implications exist too.

                        // For now, check that we also have the matching implications
                        // for ~a: under ~cond, ~b => ~a  and under cond, ~c => ~a.
                        // This is equivalent to checking for ternary clauses
                        // (~cond, b, ~a) and (cond, c, ~a).
                        // The forward implications already capture these as
                        // pos_impl(~b, ~a) and neg_impl(~c, ~a).

                        // Simplified approach: just create the ITE gate.
                        // lhs = a, cond = cond, then = c, else = b
                        literal lhs = a;
                        literal th  = c;
                        literal el  = b;

                        if (lhs == ~th || lhs == ~el) continue;
                        if (th == el) {
                            // Degenerate: a = th always, so a = th.
                            if (!are_equal(lhs, th)) {
                                merge_literals(lhs, th);
                                ++m_num_equivs;
                            }
                            continue;
                        }
                        if (th == ~el) continue; // would mean XOR, not ITE

                        m_rhs.reset();
                        m_rhs.push_back(cond);
                        m_rhs.push_back(th);
                        m_rhs.push_back(el);
                        // ITE RHS is always (cond, then, else) -- NOT sorted by var.
                        // We sort by the triple (cond.var, then.var, else.var) for
                        // canonical form, but keep order (cond, then, else) semantically.
                        // CaDiCaL keeps ITE RHS in semantic order.

                        gate* existing = find_gate_in_table(gate_type::ITE_GATE, m_rhs);
                        if (existing) {
                            if (lhs != existing->m_lhs && !are_equal(lhs, existing->m_lhs)) {
                                merge_literals(lhs, existing->m_lhs);
                                ++m_num_equivs;
                            }
                        } else {
                            gate* g = alloc(gate);
                            g->m_lhs = lhs;
                            g->m_type = gate_type::ITE_GATE;
                            g->m_rhs.append(m_rhs);
                            index_gate(g);
                            connect_goccs(g, cond);
                            connect_goccs(g, th);
                            connect_goccs(g, el);
                            ++m_num_gates;
                            ++m_num_ite;
                        }
                        if (m_solver.inconsistent()) return;
                    }
                }

                pi = pi_end;
                ni = ni_end;
            }
        }
    }

    // ================================================================
    // Gate Extraction Orchestration
    // ================================================================

    void congruence::extract_gates() {
        extract_and_gates();
        if (m_solver.inconsistent()) return;
        extract_xor_gates();
        if (m_solver.inconsistent()) return;
        extract_ite_gates();
    }

    // ================================================================
    // Unit and Equivalence Discovery from Binary Implications
    // ================================================================

    void congruence::find_units() {
        TRACE(sat_congruence, tout << "finding units from binary contradictions\n";);

        unsigned nv = num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            if (m_solver.inconsistent()) break;
            if (is_eliminated(v)) continue;
            if (value(v) != l_undef) continue;

            for (unsigned sign = 0; sign < 2; ++sign) {
                literal l(v, sign != 0);
                watch_list const& wl = m_solver.get_bin_wlist(l);

                for (watched const& w : wl) {
                    if (!w.is_binary_clause()) continue;
                    literal other = w.get_literal();

                    // If we already marked ~other, then we have both
                    // (l => other) and (l => ~other), so l must be false,
                    // i.e., ~l is a unit.
                    if (marked(~other)) {
                        unmark_all();
                        // Learn unit ~l.
                        if (value(~l) == l_undef) {
                            m_solver.assign_unit(~l);
                            ++m_num_units;
                        } else if (value(~l) == l_false) {
                            // Contradiction.
                            m_solver.set_conflict();
                            return;
                        }
                        goto next_var;
                    }
                    if (!marked(other)) {
                        set_mark(other, 1);
                    }
                }
                unmark_all();
            }
            next_var:;
        }
    }

    void congruence::find_equivalences() {
        TRACE(sat_congruence, tout << "finding equivalences from binary implications\n";);

        unsigned nv = num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            if (m_solver.inconsistent()) break;
            if (is_eliminated(v)) continue;
            if (value(v) != l_undef) continue;

            literal l(v, false);

            // Mark all binaries from l: (l => other), i.e., binary (~l, other)
            // stored in wlist of l.
            watch_list const& wl_pos = m_solver.get_bin_wlist(l);
            for (watched const& w : wl_pos) {
                if (!w.is_binary_clause()) continue;
                literal other = w.get_literal();
                if (other.var() <= v) continue; // avoid duplicates
                set_mark(other, 1);
            }

            if (m_marked_lits.empty()) continue;

            // Check binaries from ~l: (~l => other'), i.e., binary (l, other')
            // If ~other' is marked, then l => ~other' and ~l => other',
            // meaning other' => ~l and l => ~other'. Wait, that's not right.
            //
            // Binary (~l, other): l implies other.
            // Binary (l, other'): ~l implies other'.
            // If ~other' is marked, it means l implies ~other' AND ~l implies other',
            // i.e., l = ~other' (l and ~other' are equivalent).
            watch_list const& wl_neg = m_solver.get_bin_wlist(~l);
            for (watched const& w : wl_neg) {
                if (!w.is_binary_clause()) continue;
                literal other = w.get_literal();
                if (other.var() <= v) continue;

                if (marked(~other)) {
                    // l = ~other, equivalently ~l = other.
                    // We have: l => ~other (binary (~l, ~other)) and ~l => other (binary (l, other)).
                    literal repr_l = find_repr(l);
                    literal repr_neg_other = find_repr(~other);
                    if (repr_l != repr_neg_other) {
                        unmark_all();
                        merge_literals(l, ~other);
                        goto restart_var;
                    }
                }
            }
            unmark_all();
            continue;

            restart_var:
            // After discovering an equivalence, restart this variable
            // (new equivalences might enable more).
            --v; // will be incremented by the for loop
        }
    }

    // ================================================================
    // Merge Literals
    // ================================================================

    bool congruence::merge_literals(literal a, literal b) {
        literal repr_a = find_repr_compress(a);
        literal repr_b = find_repr_compress(b);

        if (repr_a == repr_b) return false;

        lbool va = value(repr_a);
        lbool vb = value(repr_b);

        if (va != l_undef && vb != l_undef) {
            if (va == vb) return false; // already consistent
            // Contradiction.
            m_solver.set_conflict();
            return false;
        }

        if (va != l_undef) {
            // repr_a is assigned, repr_b is not.
            // Assign repr_b.
            literal unit = (va == l_true) ? repr_b : ~repr_b;
            if (value(unit) == l_undef) {
                m_solver.assign_unit(unit);
                ++m_num_units;
            }
            // Still record the equivalence.
        }

        if (vb != l_undef && va == l_undef) {
            literal unit = (vb == l_true) ? repr_a : ~repr_a;
            if (value(unit) == l_undef) {
                m_solver.assign_unit(unit);
                ++m_num_units;
            }
        }

        // Merge: point the larger variable's representative to the smaller.
        literal smaller = repr_a, larger = repr_b;
        if (smaller.var() > larger.var()) std::swap(smaller, larger);

        set_repr(larger, smaller);
        // Schedule the larger literal for gate rewriting.
        schedule_literal(larger);

        ++m_num_equivs;
        return true;
    }

    // ================================================================
    // Propagation Schedule
    // ================================================================

    void congruence::schedule_literal(literal l) {
        bool_var v = l.var();
        while (m_scheduled.size() <= v)
            m_scheduled.push_back(false);
        if (m_scheduled[v]) return;
        m_scheduled[v] = true;
        m_schedule.push(l);
        TRACE(sat_congruence, tout << "scheduled literal " << l << " for propagation\n";);
    }

    // ================================================================
    // Propagation
    // ================================================================

    bool congruence::propagate_units() {
        // Propagate any units discovered so far through gate simplification.
        return m_solver.propagate(false);
    }

    bool congruence::propagate_equivalence(literal l) {
        if (value(l) != l_undef) return true;

        // Import from lazy to eager union-find.
        literal eager_l = find_repr_compress(l);
        set_eager_repr(l, eager_l);
        set_eager_repr(~l, ~eager_l);

        literal repr = find_eager_repr(l);

        // Rewrite all gates containing l to use repr instead.
        if (!rewrite_gates(repr, l)) return false;
        if (!rewrite_gates(~repr, ~l)) return false;

        return true;
    }

    size_t congruence::propagate_units_and_equivalences() {
        TRACE(sat_congruence, tout << "propagating units and equivalences\n";);

        size_t propagated = 0;

        while (!m_solver.inconsistent() && !m_schedule.empty()) {
            if (!propagate_units()) break;
            if (m_schedule.empty()) break;

            ++propagated;
            literal l = m_schedule.front();
            m_schedule.pop();
            bool_var v = l.var();
            if (v < m_scheduled.size())
                m_scheduled[v] = false;

            if (!propagate_equivalence(l))
                break;
        }

        return propagated;
    }

    // ================================================================
    // Gate Simplification (after unit propagation)
    // ================================================================

    bool congruence::simplify_gates_for_lit(literal l) {
        gate_occ_list& occs = goccs(l);
        for (gate* g : occs) {
            if (!simplify_gate(g)) return false;
        }
        return true;
    }

    bool congruence::simplify_gate(gate* g) {
        if (g->m_garbage) return true;
        switch (g->m_type) {
        case gate_type::AND_GATE: simplify_and_gate(g); break;
        case gate_type::XOR_GATE: simplify_xor_gate(g); break;
        case gate_type::ITE_GATE: /* ITE simplification is complex; skip for now */ break;
        }
        return !m_solver.inconsistent();
    }

    void congruence::simplify_and_gate(gate* g) {
        // Remove satisfied/falsified RHS literals.
        unsigned j = 0;
        bool has_false = false;
        for (unsigned i = 0; i < g->m_rhs.size(); ++i) {
            literal l = g->m_rhs[i];
            lbool v = value(l);
            if (v == l_true) continue;   // true RHS literal can be removed
            if (v == l_false) { has_false = true; continue; }
            g->m_rhs[j++] = l;
        }
        g->m_rhs.shrink(j);

        if (has_false) {
            // A false literal in AND RHS means the AND is false.
            // So LHS must be false => learn unit ~lhs.
            if (value(g->m_lhs) == l_undef) {
                m_solver.assign_unit(~g->m_lhs);
                ++m_num_units;
            }
            mark_gate_garbage(g);
            return;
        }

        if (g->m_rhs.empty()) {
            // All RHS true => AND is true => LHS must be true.
            if (value(g->m_lhs) == l_undef) {
                m_solver.assign_unit(g->m_lhs);
                ++m_num_units;
            }
            mark_gate_garbage(g);
            return;
        }

        if (g->m_rhs.size() == 1) {
            // Unary AND: lhs = rhs[0]. They are equivalent.
            literal rhs0 = g->m_rhs[0];
            if (!are_equal(g->m_lhs, rhs0)) {
                merge_literals(g->m_lhs, rhs0);
            }
            mark_gate_garbage(g);
            return;
        }

        // Re-check gate table for congruence after simplification.
        remove_gate_from_table(g);
        sort_lits_by_var(g->m_rhs);
        gate* existing = find_gate_in_table(g->m_type, g->m_rhs);
        if (existing && existing != g) {
            if (!are_equal(g->m_lhs, existing->m_lhs)) {
                merge_literals(g->m_lhs, existing->m_lhs);
            }
            mark_gate_garbage(g);
        } else {
            index_gate(g);
        }
    }

    void congruence::simplify_xor_gate(gate* g) {
        unsigned j = 0;
        bool negate = false;
        for (unsigned i = 0; i < g->m_rhs.size(); ++i) {
            literal l = g->m_rhs[i];
            lbool v = value(literal(l.var(), false)); // XOR RHS is always positive var
            if (v == l_true) { negate = !negate; continue; }
            if (v == l_false) continue;
            g->m_rhs[j++] = l;
        }
        g->m_rhs.shrink(j);

        if (negate) g->m_lhs = ~g->m_lhs;

        if (g->m_rhs.empty()) {
            // XOR with no RHS: lhs = 0 or lhs = 1 depending on accumulated parity.
            literal unit = g->m_lhs; // lhs = XOR() = false, so ~lhs is unit
            // Actually after parity folding: lhs should be false.
            if (value(~unit) == l_undef) {
                m_solver.assign_unit(~unit);
                ++m_num_units;
            }
            mark_gate_garbage(g);
            return;
        }

        if (g->m_rhs.size() == 1) {
            // lhs = XOR(x) = x. Merge.
            literal x = g->m_rhs[0];
            if (!are_equal(g->m_lhs, x)) {
                merge_literals(g->m_lhs, x);
            }
            mark_gate_garbage(g);
            return;
        }

        // Re-check table.
        remove_gate_from_table(g);
        sort_lits_by_var(g->m_rhs);
        gate* existing = find_gate_in_table(g->m_type, g->m_rhs);
        if (existing && existing != g) {
            if (!are_equal(g->m_lhs, existing->m_lhs)) {
                merge_literals(g->m_lhs, existing->m_lhs);
            }
            mark_gate_garbage(g);
        } else {
            index_gate(g);
        }
    }

    // ================================================================
    // Gate Rewriting (the core of congruence closure)
    // ================================================================

    bool congruence::rewrite_gates(literal dst, literal src) {
        // Rewrite all gates containing src to use dst instead.
        gate_occ_list& occs = goccs(src);
        for (gate* g : occs) {
            if (!rewrite_gate(g, dst, src)) return false;
            // If gate still alive and now contains dst, add to dst's occ list.
            if (!g->m_garbage) {
                bool contains_dst = false;
                for (literal l : g->m_rhs) {
                    if (l == dst) { contains_dst = true; break; }
                }
                if (contains_dst)
                    goccs(dst).push_back(g);
            }
        }
        occs.reset();
        return true;
    }

    bool congruence::rewrite_gate(gate* g, literal dst, literal src) {
        if (g->m_garbage) return true;
        ++m_num_rewrites;
        switch (g->m_type) {
        case gate_type::AND_GATE: rewrite_and_gate(g, dst, src); break;
        case gate_type::XOR_GATE: rewrite_xor_gate(g, dst, src); break;
        case gate_type::ITE_GATE: rewrite_ite_gate(g, dst, src); break;
        }
        return !m_solver.inconsistent();
    }

    void congruence::rewrite_and_gate(gate* g, literal dst, literal src) {
        // Replace src with dst in the RHS.
        // Handle special cases: clashing (dst and ~dst both in RHS),
        // duplicate dst, falsified/satisfied literals.
        bool found_src = false;
        for (literal l : g->m_rhs) {
            if (l == src) { found_src = true; break; }
        }
        if (!found_src) return;

        // Check for LHS rewriting (dst is the LHS or ~LHS).
        if (dst == g->m_lhs || dst == ~g->m_lhs) {
            mark_gate_garbage(g);
            return;
        }

        remove_gate_from_table(g);

        unsigned j = 0;
        bool has_clash = false, has_false = false;
        unsigned dst_count = 0;
        for (unsigned i = 0; i < g->m_rhs.size(); ++i) {
            literal l = g->m_rhs[i];
            if (l == src) l = dst;

            lbool v = value(l);
            if (v == l_true) continue;
            if (v == l_false) { has_false = true; break; }

            if (l == ~g->m_lhs) { has_clash = true; break; }

            // Check for clashing: dst and ~dst both present.
            if (l == ~dst) { has_clash = true; break; }

            // Check for duplicate.
            if (l == dst) {
                if (dst_count++) continue; // skip duplicate
            }

            g->m_rhs[j++] = l;
        }
        g->m_rhs.shrink(j);

        if (has_clash || has_false) {
            // AND gate has contradictory or falsified RHS => LHS must be false.
            if (value(g->m_lhs) == l_undef) {
                m_solver.assign_unit(~g->m_lhs);
                ++m_num_units;
            }
            mark_gate_garbage(g);
            return;
        }

        // Simplify degenerate cases.
        if (g->m_rhs.empty()) {
            if (value(g->m_lhs) == l_undef) {
                m_solver.assign_unit(g->m_lhs);
                ++m_num_units;
            }
            mark_gate_garbage(g);
            return;
        }

        if (g->m_rhs.size() == 1) {
            if (!are_equal(g->m_lhs, g->m_rhs[0])) {
                merge_literals(g->m_lhs, g->m_rhs[0]);
            }
            mark_gate_garbage(g);
            return;
        }

        // Re-sort and look up in table.
        sort_lits_by_var(g->m_rhs);
        gate* existing = find_gate_in_table(g->m_type, g->m_rhs);
        if (existing && existing != g) {
            if (!are_equal(g->m_lhs, existing->m_lhs)) {
                merge_literals(g->m_lhs, existing->m_lhs);
            }
            mark_gate_garbage(g);
        } else {
            index_gate(g);
        }
    }

    void congruence::rewrite_xor_gate(gate* g, literal dst, literal src) {
        bool found_src = false;
        for (literal l : g->m_rhs) {
            if (l.var() == src.var()) { found_src = true; break; }
        }
        if (!found_src) return;

        if (dst.var() == g->m_lhs.var()) {
            mark_gate_garbage(g);
            return;
        }

        remove_gate_from_table(g);

        // XOR RHS stores positive variables. When src is replaced by dst,
        // if dst is negative, flip the LHS.
        bool negate = dst.sign();
        unsigned j = 0;
        unsigned dst_var_count = 0;

        for (unsigned i = 0; i < g->m_rhs.size(); ++i) {
            literal l = g->m_rhs[i];
            if (l.var() == src.var()) {
                l = literal(dst.var(), false); // XOR uses positive vars
            }

            lbool v = value(literal(l.var(), false));
            if (v == l_true) { negate = !negate; continue; }
            if (v == l_false) continue;

            if (l.var() == dst.var()) {
                dst_var_count++;
                if (dst_var_count == 2) {
                    // x XOR x = 0, remove both.
                    // Find and remove the first occurrence too.
                    unsigned k = 0;
                    for (unsigned m = 0; m < j; ++m) {
                        if (g->m_rhs[m].var() != dst.var())
                            g->m_rhs[k++] = g->m_rhs[m];
                    }
                    j = k;
                    continue;
                }
            }
            g->m_rhs[j++] = l;
        }
        g->m_rhs.shrink(j);

        if (negate) g->m_lhs = ~g->m_lhs;

        if (g->m_rhs.empty()) {
            if (value(~g->m_lhs) == l_undef) {
                m_solver.assign_unit(~g->m_lhs);
                ++m_num_units;
            }
            mark_gate_garbage(g);
            return;
        }

        if (g->m_rhs.size() == 1) {
            if (!are_equal(g->m_lhs, g->m_rhs[0])) {
                merge_literals(g->m_lhs, g->m_rhs[0]);
            }
            mark_gate_garbage(g);
            return;
        }

        sort_lits_by_var(g->m_rhs);
        gate* existing = find_gate_in_table(g->m_type, g->m_rhs);
        if (existing && existing != g) {
            if (!are_equal(g->m_lhs, existing->m_lhs)) {
                merge_literals(g->m_lhs, existing->m_lhs);
            }
            mark_gate_garbage(g);
        } else {
            index_gate(g);
        }
    }

    void congruence::rewrite_ite_gate(gate* g, literal dst, literal src) {
        // ITE RHS = (cond, then, else)
        bool found = false;
        for (literal l : g->m_rhs) {
            if (l == src) { found = true; break; }
        }
        if (!found) return;

        if (dst == g->m_lhs || dst == ~g->m_lhs) {
            mark_gate_garbage(g);
            return;
        }

        remove_gate_from_table(g);

        for (unsigned i = 0; i < g->m_rhs.size(); ++i) {
            if (g->m_rhs[i] == src)
                g->m_rhs[i] = dst;
        }

        // Check for degenerate cases after rewrite.
        literal cond = g->m_rhs[0];
        literal th   = g->m_rhs[1];
        literal el   = g->m_rhs[2];

        if (th == el) {
            // ITE(c, x, x) = x
            if (!are_equal(g->m_lhs, th)) {
                merge_literals(g->m_lhs, th);
            }
            mark_gate_garbage(g);
            return;
        }

        if (th == ~el) {
            // ITE(c, x, ~x) = XOR(c, ~x) -- convert to XOR or just discard
            mark_gate_garbage(g);
            return;
        }

        lbool vc = value(cond);
        if (vc == l_true) {
            // ITE(true, th, el) = th
            if (!are_equal(g->m_lhs, th)) merge_literals(g->m_lhs, th);
            mark_gate_garbage(g);
            return;
        }
        if (vc == l_false) {
            // ITE(false, th, el) = el
            if (!are_equal(g->m_lhs, el)) merge_literals(g->m_lhs, el);
            mark_gate_garbage(g);
            return;
        }

        // Re-check table.
        gate* existing = find_gate_in_table(g->m_type, g->m_rhs);
        if (existing && existing != g) {
            if (!are_equal(g->m_lhs, existing->m_lhs)) {
                merge_literals(g->m_lhs, existing->m_lhs);
            }
            mark_gate_garbage(g);
        } else {
            index_gate(g);
        }
    }

    // ================================================================
    // Forward Subsumption with Equivalence Normalization
    // ================================================================

    void congruence::forward_subsume_matching_clauses() {
        TRACE(sat_congruence, tout << "forward subsuming with equivalences\n";);

        // Identify "matchable" variables: those that have a non-trivial
        // representative (i.e., merged with another variable).
        unsigned nv = num_vars();
        bool_vector matchable;
        matchable.resize(nv, false);
        unsigned matchable_count = 0;

        for (unsigned v = 0; v < nv; ++v) {
            if (is_eliminated(v)) continue;
            literal l(v, false);
            literal repr = find_repr_compress(l);
            if (repr != l) {
                matchable[v] = true;
                matchable[repr.var()] = true;
                ++matchable_count;
            }
        }

        if (matchable_count == 0) return;

        // For each clause, normalize it by replacing each literal with its
        // representative. Then check if the normalized clause subsumes any
        // other normalized clause.
        //
        // Simple approach: collect normalized clauses, sort by size,
        // attempt pairwise subsumption for clauses containing matchable vars.

        struct norm_clause {
            literal_vector lits;
            clause* orig;
            norm_clause() : orig(nullptr) {}
        };

        vector<norm_clause> candidates;

        for (clause* cp : m_solver.clauses()) {
            if (cp->was_removed()) continue;
            if (cp->is_learned()) continue;

            bool has_matchable = false;
            norm_clause nc;
            nc.orig = cp;

            bool is_taut = false;
            for (literal l : *cp) {
                literal repr = find_repr_compress(l);
                // Check for tautology after normalization.
                bool dup = false;
                for (literal existing : nc.lits) {
                    if (existing == repr) { dup = true; break; }
                    if (existing == ~repr) { is_taut = true; break; }
                }
                if (is_taut) break;
                if (!dup) nc.lits.push_back(repr);
                if (l.var() < matchable.size() && matchable[l.var()])
                    has_matchable = true;
            }

            if (is_taut) {
                // Normalized clause is tautological -- can be removed.
                // But we should not remove non-learned clauses without
                // proper bookkeeping. For safety, skip.
                continue;
            }

            if (has_matchable) {
                std::sort(nc.lits.begin(), nc.lits.end());
                candidates.push_back(nc);
            }
        }

        // Sort candidates by size (smallest first) for efficient subsumption.
        std::sort(candidates.begin(), candidates.end(),
            [](norm_clause const& a, norm_clause const& b) {
                return a.lits.size() < b.lits.size();
            });

        // Simple O(n^2) pairwise subsumption check for small candidate sets.
        // A clause C subsumes D if every literal in C appears in D.
        unsigned subsumed_count = 0;
        for (unsigned i = 0; i < candidates.size() && subsumed_count < 10000; ++i) {
            norm_clause& small = candidates[i];
            if (small.orig->was_removed()) continue;

            for (unsigned j = i + 1; j < candidates.size(); ++j) {
                norm_clause& large = candidates[j];
                if (large.orig->was_removed()) continue;
                if (large.lits.size() < small.lits.size()) continue;

                // Check if small subsumes large.
                bool subsumes = true;
                unsigned si = 0, li = 0;
                while (si < small.lits.size() && li < large.lits.size()) {
                    if (small.lits[si] == large.lits[li]) {
                        ++si; ++li;
                    } else if (small.lits[si] < large.lits[li]) {
                        subsumes = false; break;
                    } else {
                        ++li;
                    }
                }
                if (si < small.lits.size()) subsumes = false;

                if (subsumes) {
                    // Remove the larger clause.
                    large.orig->set_removed(true);
                    ++subsumed_count;
                }
            }
        }

        m_num_subsumed += subsumed_count;
        TRACE(sat_congruence, tout << "subsumed " << subsumed_count << " clauses via equivalence normalization\n";);
    }

    // ================================================================
    // Main Entry Point
    // ================================================================

    bool congruence::run() {
        TRACE(sat_congruence, tout << "starting congruence closure\n";);

        if (m_solver.inconsistent()) return false;
        if (num_vars() == 0) return false;

        // Must be at decision level 0.
        SASSERT(m_solver.at_base_lvl());

        // Propagate any pending units first.
        if (!m_solver.propagate(false)) return false;

        init_closure();

        // Phase 1: Extract binary implications and strengthen ternaries.
        extract_binaries();
        if (m_solver.inconsistent()) { reset_closure(); return false; }

        // Phase 2: Extract gates (AND, XOR, ITE).
        extract_gates();
        if (m_solver.inconsistent()) { reset_closure(); return false; }

        // Phase 3: Discover units from binary contradictions.
        find_units();
        if (m_solver.inconsistent()) { reset_closure(); return false; }

        // Phase 4: Discover equivalences from binary implication SCCs.
        find_equivalences();
        if (m_solver.inconsistent()) { reset_closure(); return false; }

        // Phase 5: Propagate all discovered equivalences, rewriting
        // gates eagerly until fixpoint.
        size_t propagated = propagate_units_and_equivalences();

        // Phase 6: Forward subsume clauses using equivalence normalization.
        if (propagated > 0 && !m_solver.inconsistent()) {
            forward_subsume_matching_clauses();
        }

        bool result = (m_num_equivs > 0 || m_num_units > 0 || m_num_subsumed > 0);

        TRACE(sat_congruence,
            tout << "congruence closure complete: "
                 << m_num_gates << " gates, "
                 << m_num_equivs << " equivs, "
                 << m_num_units << " units, "
                 << m_num_subsumed << " subsumed, "
                 << m_num_rewrites << " rewrites\n";);

        reset_closure();
        return result;
    }

}
