    /**
       \brief Detect equivalence v <=> other.
       Looks for binary clauses (pos_l, ~other) and (neg_l, other) among the
       collected clause wrappers in m_pos_cls / m_neg_cls.
       If found, sets eq_lit to 'other', populates m_gate_marks, and returns true.
       Must be called after m_pos_cls / m_neg_cls are populated.
    */
    bool simplifier::find_equivalence(bool_var v, literal & eq_lit) {
        literal pos_l(v, false);
        literal neg_l(v, true);

        // Equivalence v <=> other requires:
        //   (pos_l | ~other)  in m_pos_cls  [encodes other => v]
        //   (neg_l |  other)  in m_neg_cls  [encodes v => other]

        if (m_visited.size() <= 2 * s.num_vars())
            m_visited.resize(2 * s.num_vars(), false);

        // For each binary (pos_l, x) in m_pos_cls, x = ~other, so candidate other = ~x.
        // Mark ~x so we can check for (neg_l, ~x) in m_neg_cls.
        literal_vector marked_lits;
        for (unsigned i = 0; i < m_pos_cls.size(); ++i) {
            clause_wrapper const & cw = m_pos_cls[i];
            if (cw.size() != 2) continue;
            literal x = (cw[0] == pos_l) ? cw[1] : cw[0];
            literal candidate = ~x;
            if (candidate.index() < m_visited.size()) {
                m_visited[candidate.index()] = true;
                marked_lits.push_back(candidate);
            }
        }

        eq_lit = null_literal;
        unsigned neg_idx = UINT_MAX;

        for (unsigned j = 0; j < m_neg_cls.size(); ++j) {
            clause_wrapper const & cw = m_neg_cls[j];
            if (cw.size() != 2) continue;
            literal y = (cw[0] == neg_l) ? cw[1] : cw[0];
            if (y.index() < m_visited.size() && m_visited[y.index()]) {
                eq_lit = y;
                neg_idx = j;
                break;
            }
        }

        for (literal lit : marked_lits)
            m_visited[lit.index()] = false;

        if (eq_lit == null_literal)
            return false;

        // Find the matching positive clause index: need (pos_l, ~eq_lit).
        literal target = ~eq_lit;
        unsigned pos_idx = UINT_MAX;
        for (unsigned i = 0; i < m_pos_cls.size(); ++i) {
            clause_wrapper const & cw = m_pos_cls[i];
            if (cw.size() != 2) continue;
            literal x = (cw[0] == pos_l) ? cw[1] : cw[0];
            if (x == target) {
                pos_idx = i;
                break;
            }
        }

        if (pos_idx == UINT_MAX)
            return false;

        // Mark these two binary clauses as gate clauses.
        m_gate_marks.reset();
        m_gate_marks.resize(m_pos_cls.size() + m_neg_cls.size(), false);
        m_gate_marks[pos_idx] = true;
        m_gate_marks[m_pos_cls.size() + neg_idx] = true;

        TRACE(sat_simplifier, tout << "found equivalence: " << pos_l << " <=> " << eq_lit
              << "  gate clauses: pos[" << pos_idx << "] neg[" << neg_idx << "]\n";);
        return true;
    }

    /**
       \brief Detect AND gate: v = a1 & a2 & ... & ak.
       Requirements (in m_pos_cls / m_neg_cls):
         - Binary clauses (pos_l, ~a1), ..., (pos_l, ~ak) in m_pos_cls
         - A long clause (neg_l, a1, ..., ak) in m_neg_cls
       Returns true if found; populates m_gate_marks.
    */
    bool simplifier::find_and_gate(bool_var v) {
        literal pos_l(v, false);
        literal neg_l(v, true);

        if (m_visited.size() <= 2 * s.num_vars())
            m_visited.resize(2 * s.num_vars(), false);

        // Collect binary clauses (pos_l, ~ai); mark each ai.
        struct bin_info { literal ai; unsigned idx; };
        svector<bin_info> bin_clauses;

        for (unsigned i = 0; i < m_pos_cls.size(); ++i) {
            clause_wrapper const & cw = m_pos_cls[i];
            if (cw.size() == 2) {
                literal x = (cw[0] == pos_l) ? cw[1] : cw[0];
                literal ai = ~x;
                m_visited[ai.index()] = true;
                bin_clauses.push_back({ai, i});
            }
        }

        if (bin_clauses.size() < 2) {
            for (auto const & b : bin_clauses)
                m_visited[b.ai.index()] = false;
            return false;
        }

        // Scan m_neg_cls for (~v, a1, ..., ak) where all ai are marked.
        bool found = false;
        unsigned neg_long_idx = UINT_MAX;

        for (unsigned j = 0; j < m_neg_cls.size(); ++j) {
            clause_wrapper const & cw = m_neg_cls[j];
            if (cw.size() < 3) continue;
            bool all_marked = true;
            unsigned arity = 0;
            for (unsigned k = 0; k < cw.size(); ++k) {
                literal lit = cw[k];
                if (lit == neg_l) continue;
                if (lit.index() >= m_visited.size() || !m_visited[lit.index()]) {
                    all_marked = false;
                    break;
                }
                arity++;
            }
            if (all_marked && arity >= 2) {
                neg_long_idx = j;
                found = true;
                break;
            }
        }

        if (!found) {
            for (auto const & b : bin_clauses)
                m_visited[b.ai.index()] = false;
            return false;
        }

        // Re-mark with only literals from the long clause.
        for (auto const & b : bin_clauses)
            m_visited[b.ai.index()] = false;

        clause_wrapper const & long_cw = m_neg_cls[neg_long_idx];
        for (unsigned k = 0; k < long_cw.size(); ++k) {
            literal lit = long_cw[k];
            if (lit != neg_l)
                m_visited[lit.index()] = true;
        }

        // Build m_gate_marks: mark the matching binary clauses and the long clause.
        m_gate_marks.reset();
        m_gate_marks.resize(m_pos_cls.size() + m_neg_cls.size(), false);

        for (auto const & b : bin_clauses) {
            if (m_visited[b.ai.index()])
                m_gate_marks[b.idx] = true;
        }
        m_gate_marks[m_pos_cls.size() + neg_long_idx] = true;

        // Clean up visited marks.
        for (unsigned k = 0; k < long_cw.size(); ++k) {
            literal lit = long_cw[k];
            if (lit != neg_l)
                m_visited[lit.index()] = false;
        }

        TRACE(sat_simplifier, {
            tout << "found AND gate: " << pos_l << " = ";
            bool first = true;
            for (unsigned k = 0; k < long_cw.size(); ++k) {
                literal lit = long_cw[k];
                if (lit == neg_l) continue;
                if (!first) tout << " & ";
                tout << lit;
                first = false;
            }
            tout << "\n";
        });
        return true;
    }

    /**
       \brief Detect ITE gate: pivot = ITE(cond, a, b).

       The encoding uses four ternary clauses:
         (pivot,  cond, x)    -- clause A   [in m_pos_cls]
         (pivot, ~cond, y)    -- clause B   [in m_pos_cls]
         (~pivot, cond, ~x)   -- clause C   [in m_neg_cls]
         (~pivot,~cond, ~y)   -- clause D   [in m_neg_cls]

       This encodes: pivot <=> ITE(~cond, ~x, ~y).

       Algorithm (from CaDiCaL find_if_then_else):
       For each pair of ternary clauses (A, B) in m_pos_cls containing pos_l:
         - Extract the condition literal (appears with opposite sign in A vs B)
         - Look up the two complementary ternary clauses in m_neg_cls
         - If all four exist, mark them as gate clauses in m_gate_marks
    */
    bool simplifier::find_ite_gate(bool_var v) {
        literal pos_l(v, false);
        literal neg_l(v, true);
        unsigned pos_sz = m_pos_cls.size();
        unsigned neg_sz = m_neg_cls.size();

        for (unsigned i = 0; i < pos_sz; ++i) {
            clause_wrapper & ci = m_pos_cls[i];
            if (ci.size() != 3) continue;

            // Extract the two non-pivot literals from ci: (pos_l, bi, xi).
            literal bi = null_literal, xi = null_literal;
            for (unsigned k = 0; k < 3; ++k) {
                literal l = ci[k];
                if (l == pos_l) continue;
                if (bi == null_literal) bi = l; else xi = l;
            }
            if (bi == null_literal || xi == null_literal) continue;

            for (unsigned j = i + 1; j < pos_sz; ++j) {
                clause_wrapper & cj = m_pos_cls[j];
                if (cj.size() != 3) continue;

                // Extract (pos_l, bj, xj).
                literal bj = null_literal, xj = null_literal;
                for (unsigned k = 0; k < 3; ++k) {
                    literal l = cj[k];
                    if (l == pos_l) continue;
                    if (bj == null_literal) bj = l; else xj = l;
                }
                if (bj == null_literal || xj == null_literal) continue;

                // Find a complementary pair to identify the condition.
                // One of {bi,xi} must equal the negation of one of {bj,xj}.
                literal cond, then_l, else_l;
                bool found_pattern = false;

                if (bi == ~bj && xi.var() != xj.var()) {
                    cond = bi; then_l = xi; else_l = xj;
                    found_pattern = true;
                } else if (bi == ~xj && xi.var() != bj.var()) {
                    cond = bi; then_l = xi; else_l = bj;
                    found_pattern = true;
                } else if (xi == ~bj && bi.var() != xj.var()) {
                    cond = xi; then_l = bi; else_l = xj;
                    found_pattern = true;
                } else if (xi == ~xj && bi.var() != bj.var()) {
                    cond = xi; then_l = bi; else_l = bj;
                    found_pattern = true;
                }

                if (!found_pattern) continue;

                // Look for the two complementary clauses in m_neg_cls:
                //   C = (~pivot, cond, ~then_l)
                //   D = (~pivot, ~cond, ~else_l)
                unsigned c_idx = UINT_MAX, d_idx = UINT_MAX;
                for (unsigned k = 0; k < neg_sz; ++k) {
                    clause_wrapper & ck = m_neg_cls[k];
                    if (ck.size() != 3) continue;
                    bool has_neg_l = false;
                    bool has_cond = false, has_neg_then = false;
                    bool has_neg_cond = false, has_neg_else = false;
                    for (unsigned m = 0; m < 3; ++m) {
                        literal l = ck[m];
                        if (l == neg_l) { has_neg_l = true; continue; }
                        if (l == cond)     has_cond = true;
                        if (l == ~then_l)  has_neg_then = true;
                        if (l == ~cond)    has_neg_cond = true;
                        if (l == ~else_l)  has_neg_else = true;
                    }
                    if (has_neg_l && has_cond && has_neg_then && c_idx == UINT_MAX)
                        c_idx = k;
                    if (has_neg_l && has_neg_cond && has_neg_else && d_idx == UINT_MAX)
                        d_idx = k;
                    if (c_idx != UINT_MAX && d_idx != UINT_MAX) break;
                }

                if (c_idx == UINT_MAX || d_idx == UINT_MAX) continue;

                // Found ITE gate. Populate m_gate_marks.
                m_gate_marks.reset();
                m_gate_marks.resize(pos_sz + neg_sz, false);
                m_gate_marks[i] = true;              // clause A
                m_gate_marks[j] = true;              // clause B
                m_gate_marks[pos_sz + c_idx] = true; // clause C
                m_gate_marks[pos_sz + d_idx] = true; // clause D

                TRACE(sat_simplifier, tout << "found ITE gate: " << pos_l
                      << " = ITE(" << ~cond << ", " << ~then_l << ", " << ~else_l << ")\n";);
                return true;
            }
        }
        return false;
    }

    /**
       \brief Detect XOR gate: pivot = a1 ^ a2 ^ ... ^ ak.

       A k-ary XOR on variables {v, a1, ..., ak} is encoded as 2^k
       clauses of size k+1, all over the same variable set.  Each clause
       has an even number of negated literals (even parity).

       Half (2^(k-1)) contain pos_l, the other half contain neg_l.

       Algorithm adapted from CaDiCaL find_xor_gate:
       For each clause of size >= 3 containing pos_l, extract the variable
       set, then enumerate all 2^k - 1 remaining even-parity sign patterns
       and verify that each corresponding clause exists.
    */
    bool simplifier::find_xor_gate(bool_var v) {
        literal pos_l(v, false);
        literal neg_l(v, true);
        unsigned pos_sz = m_pos_cls.size();
        unsigned neg_sz = m_neg_cls.size();
        literal_vector lits;

        for (unsigned i = 0; i < pos_sz; ++i) {
            clause_wrapper & ci = m_pos_cls[i];
            unsigned clause_sz = ci.size();
            if (clause_sz < 3) continue;
            unsigned arity = clause_sz - 1;
            if (arity > m_xor_lim) continue;

            // Extract seed clause with pivot at index 0.
            lits.reset();
            lits.push_back(pos_l);
            for (unsigned k = 0; k < clause_sz; ++k) {
                literal l = ci[k];
                if (l != pos_l) lits.push_back(l);
            }
            SASSERT(lits.size() == clause_sz);

            // Need 2^arity - 1 additional clauses (total 2^arity).
            unsigned total_needed = (1u << arity) - 1;
            unsigned signs = 0;
            unsigned found_count = 0;
            bool failed = false;

            svector<unsigned> gate_pos_indices;
            svector<unsigned> gate_neg_indices;
            gate_pos_indices.push_back(i);

            while (found_count < total_needed) {
                unsigned prev = signs;
                // Advance to next even-parity sign pattern.
                ++signs;
                while (signs < (1u << clause_sz)) {
                    unsigned bc = 0;
                    for (unsigned tmp = signs; tmp; tmp &= tmp - 1) ++bc;
                    if ((bc & 1) == 0) break; // even parity
                    ++signs;
                }
                if (signs >= (1u << clause_sz)) { failed = true; break; }

                // Flip changed literals.
                for (unsigned jj = 0; jj < clause_sz; ++jj) {
                    unsigned bit = 1u << jj;
                    if ((prev & bit) != (signs & bit))
                        lits[jj] = ~lits[jj];
                }

                bool pivot_negated = (signs & 1u) != 0;

                // Search for matching clause.
                auto match_clause = [&](clause_wrapper & ck) -> bool {
                    if (ck.size() != clause_sz) return false;
                    // Check all literals in lits appear in ck.
                    for (unsigned m = 0; m < clause_sz; ++m) {
                        bool found_lit = false;
                        for (unsigned n = 0; n < clause_sz; ++n) {
                            if (ck[n] == lits[m]) { found_lit = true; break; }
                        }
                        if (!found_lit) return false;
                    }
                    return true;
                };

                if (!pivot_negated) {
                    bool found_here = false;
                    for (unsigned k = 0; k < pos_sz; ++k) {
                        if (match_clause(m_pos_cls[k])) {
                            gate_pos_indices.push_back(k);
                            found_here = true;
                            break;
                        }
                    }
                    if (!found_here) { failed = true; break; }
                } else {
                    SASSERT(lits[0] == neg_l);
                    bool found_here = false;
                    for (unsigned k = 0; k < neg_sz; ++k) {
                        if (match_clause(m_neg_cls[k])) {
                            gate_neg_indices.push_back(k);
                            found_here = true;
                            break;
                        }
                    }
                    if (!found_here) { failed = true; break; }
                }
                ++found_count;
            }

            if (failed || found_count < total_needed) continue;

            SASSERT(gate_pos_indices.size() + gate_neg_indices.size() == (1u << arity));

            // Populate m_gate_marks.
            m_gate_marks.reset();
            m_gate_marks.resize(pos_sz + neg_sz, false);
            for (unsigned idx : gate_pos_indices)
                m_gate_marks[idx] = true;
            for (unsigned idx : gate_neg_indices)
                m_gate_marks[pos_sz + idx] = true;

            TRACE(sat_simplifier, {
                tout << "found XOR gate: " << neg_l << " = ";
                bool first = true;
                for (unsigned k = 1; k < ci.size(); ++k) {
                    if (!first) tout << " ^ ";
                    tout << ci[k];
                    first = false;
                }
                tout << " (arity " << arity << ", " << (1u << arity) << " clauses)\n";
            });
            return true;
        }
        return false;
    }

    /**
       \brief Find a non-learned, non-removed clause in occurrence lists
       that contains exactly the given set of literals.
       Searches the occurrence list of the literal with fewest occurrences.
    */
    clause * simplifier::find_clause_with_lits(literal_vector const & lits) {
        if (lits.empty()) return nullptr;
        literal best = lits[0];
        unsigned best_sz = m_use_list.get(best).size();
        for (unsigned i = 1; i < lits.size(); ++i) {
            unsigned sz = m_use_list.get(lits[i]).size();
            if (sz < best_sz) {
                best = lits[i];
                best_sz = sz;
            }
        }
        unsigned target_size = lits.size();
        clause_use_list & cul = m_use_list.get(best);
        for (auto it = cul.mk_iterator(); !it.at_end(); it.next()) {
            clause & c = it.curr();
            if (c.is_learned() || c.was_removed()) continue;
            unsigned found = 0;
            bool ok = true;
            for (literal l : c) {
                lbool val = value(l);
                if (val == l_false) continue;
                if (val == l_true) { ok = false; break; }
                bool in_lits = false;
                for (unsigned k = 0; k < target_size; ++k) {
                    if (lits[k] == l) { in_lits = true; break; }
                }
                if (!in_lits) { ok = false; break; }
                if (++found > target_size) { ok = false; break; }
            }
            if (ok && found == target_size)
                return &c;
        }
        return nullptr;
    }
