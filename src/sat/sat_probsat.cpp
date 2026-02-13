/*++
  Copyright (c) 2025 Microsoft Corporation

  Module Name:

    sat_probsat.cpp

  Abstract:

    Lightweight in-place ProbSAT random walker for SAT solver phase improvement.
    Based on CaDiCaL's walk.cpp. Operates directly on solver's clause storage.

  Author:

    Grigory (2025)

--*/

#include "sat/sat_probsat.h"
#include "sat/sat_solver.h"
#include <cmath>

namespace sat {

    // CB interpolation table from CaDiCaL (Adrian Balint's thesis).
    // Format: {clause_size, CB_value}
    static const double cbvals[][2] = {
        {0.0, 2.00}, {3.0, 2.50}, {4.0, 2.85}, {5.0, 3.70},
        {6.0, 5.10}, {7.0, 7.40},
    };
    static const int ncbvals = sizeof(cbvals) / sizeof(cbvals[0]);

    double probsat::fit_cb(double size) {
        int i = 0;
        while (i + 2 < ncbvals &&
               (cbvals[i][0] > size || cbvals[i + 1][0] < size))
            i++;
        double x1 = cbvals[i][0],     y1 = cbvals[i][1];
        double x2 = cbvals[i + 1][0], y2 = cbvals[i + 1][1];
        double dx = x2 - x1;
        SASSERT(dx > 0);
        return (y2 - y1) * (size - x1) / dx + y1;
    }

    double probsat::compute_avg_clause_size() const {
        if (m_clauses.empty()) return 3.0;
        uint64_t total = 0;
        for (auto const& cr : m_clauses)
            total += cr.size();
        return static_cast<double>(total) / m_clauses.size();
    }

    void probsat::populate_score_table() {
        double avg_size = compute_avg_clause_size();

        // CaDiCaL alternates: every second invocation uses CB=2.0 for diversity
        bool use_size_cb = (m_walk_count & 1) != 0;
        double cb = use_size_cb ? fit_cb(avg_size) : 2.0;
        SASSERT(cb > 0);
        double base = 1.0 / cb;

        m_score_table.reset();
        double val = 1.0;
        m_epsilon = val;
        // Build table until values underflow to zero
        while (val > 0) {
            m_score_table.push_back(val);
            m_epsilon = val;
            val *= base;
        }
    }

    // Build occurrence lists from solver's clause database.
    // This is the ONLY O(total_literals) operation -- no clause copying.
    void probsat::build_occurrences(solver& s) {
        m_clauses.reset();
        m_occs.reset();

        unsigned num_lit_indices = 2 * m_num_vars;
        m_occs.reserve(num_lit_indices);
        for (unsigned i = 0; i < num_lit_indices; ++i) {
            if (i < m_occs.size())
                m_occs[i].reset();
        }
        m_occs.resize(num_lit_indices);

        // Binary clauses from watch lists.
        // Each binary clause appears in both literals' watch lists,
        // so we only add it once (when l1.index() < l2.index()).
        unsigned sz = s.m_bin_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l1 = ~to_literal(l_idx);
            if (l1.var() >= m_num_vars) continue;
            for (watched const& w : s.m_bin_watches[l_idx]) {
                if (!w.is_binary_non_learned_clause()) continue;
                literal l2 = w.get_literal();
                if (l2.var() >= m_num_vars) continue;
                if (l1.index() > l2.index()) continue; // avoid duplicates
                unsigned cidx = m_clauses.size();
                m_clauses.push_back(clause_ref(l1, l2));
                m_occs[l1.index()].push_back(cidx);
                m_occs[l2.index()].push_back(cidx);
            }
        }

        // Long clauses (irredundant only -- same as CaDiCaL's default)
        for (clause* cp : s.m_clauses) {
            if (cp->was_removed()) continue;
            unsigned cidx = m_clauses.size();
            m_clauses.push_back(clause_ref(cp));
            for (literal lit : *cp) {
                if (lit.var() < m_num_vars) {
                    m_occs[lit.index()].push_back(cidx);
                }
            }
        }
    }

    void probsat::init_assignment(solver& s) {
        m_values.resize(m_num_vars, false);
        for (unsigned v = 0; v < m_num_vars; ++v) {
            // Use current CDCL phases as the starting assignment.
            // CaDiCaL alternates between prev (walk continuity) and current phases;
            // we use current phases since they incorporate the latest CDCL progress.
            if (v < s.m_phase.size()) {
                m_values[v] = s.m_phase[v];
            }
            else {
                m_values[v] = (m_rand() % 2) == 0;
            }
        }
    }

    void probsat::init_clause_info() {
        unsigned nc = m_clauses.size();
        m_clause_info.reset();
        m_clause_info.resize(nc);
        m_unsat.reset();
        m_break_count.reset();
        m_break_count.resize(m_num_vars, 0);

        for (unsigned ci = 0; ci < nc; ++ci) {
            clause_info& info = m_clause_info[ci];
            info.m_num_true = 0;
            info.m_true_sum = 0;

            auto const& cr = m_clauses[ci];
            if (cr.is_binary()) {
                if (is_true(cr.m_l0)) info.add(cr.m_l0);
                if (is_true(cr.m_l1)) info.add(cr.m_l1);
            }
            else {
                for (literal lit : *cr.m_clause) {
                    if (lit.var() < m_num_vars && is_true(lit))
                        info.add(lit);
                }
            }

            if (info.m_num_true == 0) {
                m_unsat.insert_fresh(ci);
            }
            else if (info.m_num_true == 1) {
                // The sole satisfier gets a break-count increment
                literal sole = to_literal(info.m_true_sum);
                m_break_count[sole.var()]++;
            }
        }
    }

    void probsat::init(solver& s) {
        m_solver = &s;
        m_num_vars = s.num_vars();
        m_rand.set_seed(s.m_rand());

        build_occurrences(s);
        init_assignment(s);
        init_clause_info();
        populate_score_table();

        // Initialize best-model tracking
        m_best_values.resize(m_num_vars);
        for (unsigned v = 0; v < m_num_vars; ++v)
            m_best_values[v] = m_values[v];
        m_best_trail_pos = 0;
        m_flip_trail.reset();
        m_best_unsat = m_unsat.size();
    }

    bool_var probsat::pick_var() {
        SASSERT(!m_unsat.empty());

        // Pick random unsatisfied clause
        unsigned cidx = m_unsat.elem_at(m_rand() % m_unsat.size());
        auto const& cr = m_clauses[cidx];

        // Compute scores for each literal in the clause
        m_lit_scores.reset();
        double sum = 0;

        if (cr.is_binary()) {
            double s0 = score(m_break_count[cr.m_l0.var()]);
            double s1 = score(m_break_count[cr.m_l1.var()]);
            m_lit_scores.push_back(s0);
            m_lit_scores.push_back(s1);
            sum = s0 + s1;
        }
        else {
            for (literal lit : *cr.m_clause) {
                if (lit.var() >= m_num_vars) continue;
                double sc = score(m_break_count[lit.var()]);
                m_lit_scores.push_back(sc);
                sum += sc;
            }
        }

        SASSERT(!m_lit_scores.empty());
        SASSERT(sum > 0);

        // Probabilistic selection weighted by scores
        double lim = sum * (static_cast<double>(m_rand()) / random_gen::max_value());

        // Walk through scores to find the selected literal
        if (cr.is_binary()) {
            if (lim < m_lit_scores[0])
                return cr.m_l0.var();
            return cr.m_l1.var();
        }

        unsigned j = 0;
        double accum = 0;
        for (literal lit : *cr.m_clause) {
            if (lit.var() >= m_num_vars) continue;
            accum += m_lit_scores[j++];
            if (accum > lim)
                return lit.var();
        }
        // Fallback: return last variable (rounding edge case)
        if (cr.m_clause->size() > 0) {
            for (int k = static_cast<int>(cr.m_clause->size()) - 1; k >= 0; --k) {
                literal lit = (*cr.m_clause)[k];
                if (lit.var() < m_num_vars)
                    return lit.var();
            }
        }
        UNREACHABLE();
        return 0;
    }

    void probsat::flip(bool_var v) {
        SASSERT(v < m_num_vars);

        // literal(v, sign): sign=false is positive lit, sign=true is negative lit.
        // is_true(literal(v, false)) iff m_values[v] == true
        // is_true(literal(v, true))  iff m_values[v] == false
        // was_true: the literal that IS currently true (will become false after flip)
        // was_false: the literal that IS currently false (will become true after flip)
        literal was_true  = literal(v, !m_values[v]);
        literal was_false = literal(v,  m_values[v]);

        // Process clauses where was_true appears: it was satisfying, now it's not
        for (unsigned cidx : m_occs[was_true.index()]) {
            clause_info& ci = m_clause_info[cidx];
            ci.del(was_true);
            switch (ci.m_num_true) {
            case 0:
                // Clause just became unsatisfied
                m_unsat.insert_fresh(cidx);
                // was_true was the sole satisfier, its break_count was already counted
                // Now no one satisfies it, so remove the break_count that was_true contributed
                // Actually: we already decremented m_num_true. The sole satisfier WAS was_true.
                // Its break_count contribution was already in m_break_count[v].
                // We need to decrement it since the clause is now unsat (no sole satisfier).
                m_break_count[v]--;
                break;
            case 1: {
                // Clause went from 2+ satisfiers to exactly 1.
                // The remaining sole satisfier now gets a break_count increment.
                literal sole = to_literal(ci.m_true_sum);
                m_break_count[sole.var()]++;
                break;
            }
            default:
                // Still multiply satisfied, no break_count changes
                break;
            }
        }

        // Process clauses where was_false appears: it was false, now becomes true
        for (unsigned cidx : m_occs[was_false.index()]) {
            clause_info& ci = m_clause_info[cidx];
            switch (ci.m_num_true) {
            case 0:
                // Clause was unsat, now becomes satisfied by was_false -> now ~was_false (i.e., the var flip)
                m_unsat.remove(cidx);
                // The new sole satisfier is was_false (which is now true)
                m_break_count[v]++;
                break;
            case 1: {
                // Clause goes from 1 satisfier to 2. Remove break_count from the old sole satisfier.
                literal sole = to_literal(ci.m_true_sum);
                m_break_count[sole.var()]--;
                break;
            }
            default:
                // Already multiply satisfied
                break;
            }
            ci.add(was_false);
        }

        // Actually flip the value
        m_values[v] = !m_values[v];
    }

    void probsat::push_flip(bool_var v) {
        if (m_best_trail_pos < 0) return; // trail invalidated

        unsigned limit = m_num_vars / 4 + 1;
        if (m_flip_trail.size() < limit) {
            m_flip_trail.push_back(v);
            return;
        }

        // Trail overflow: flush prefix up to best_trail_pos into best_values
        if (m_best_trail_pos > 0) {
            flush_trail();
            m_flip_trail.push_back(v);
        }
        else {
            // best_trail_pos == 0 and trail is full: invalidate trail, save full snapshot
            m_flip_trail.reset();
            m_best_trail_pos = -1;
        }
    }

    void probsat::flush_trail() {
        SASSERT(m_best_trail_pos >= 0);
        SASSERT(static_cast<unsigned>(m_best_trail_pos) <= m_flip_trail.size());

        // Apply flips [0, best_trail_pos) to best_values
        for (int i = 0; i < m_best_trail_pos; ++i) {
            bool_var v = m_flip_trail[i];
            m_best_values[v] = !m_best_values[v];
        }

        // Shift remaining flips to front
        unsigned kept = m_flip_trail.size() - m_best_trail_pos;
        for (unsigned i = 0; i < kept; ++i) {
            m_flip_trail[i] = m_flip_trail[m_best_trail_pos + i];
        }
        m_flip_trail.resize(kept);
        m_best_trail_pos = 0;
    }

    void probsat::save_best_if_improved() {
        unsigned current_unsat = m_unsat.size();
        if (current_unsat >= m_best_unsat) return;

        m_best_unsat = current_unsat;

        if (m_best_trail_pos < 0) {
            // Trail was invalidated: full snapshot
            for (unsigned v = 0; v < m_num_vars; ++v)
                m_best_values[v] = m_values[v];
            m_best_trail_pos = 0;
            m_flip_trail.reset();
        }
        else {
            // Just record position in trail
            m_best_trail_pos = m_flip_trail.size();
        }
    }

    void probsat::export_best(solver& s) {
        // Reconstruct best_values from trail if needed
        if (m_best_trail_pos > 0) {
            flush_trail();
        }
        // else: trail invalidated (-1) means best_values already has the full snapshot
        //       trail at pos 0 means best_values is up to date

        // Write to solver's phase vectors
        for (unsigned v = 0; v < m_num_vars; ++v) {
            if (v < s.m_best_phase.size())
                s.m_best_phase[v] = m_best_values[v];
            if (v < s.m_phase.size())
                s.m_phase[v] = m_best_values[v];
        }
        // Also save to prev_phase for walk continuity (CaDiCaL phases.prev)
        for (unsigned v = 0; v < m_num_vars && v < s.m_prev_phase.size(); ++v) {
            s.m_prev_phase[v] = m_best_values[v];
        }
    }

    bool probsat::operator()(solver& s, unsigned max_flips) {
        // Use solver's rephase count for CB alternation (persists across calls)
        m_walk_count = s.m_rephase.count;

        if (s.num_vars() == 0) return false;
        if (s.m_clauses.empty() && s.m_bin_watches.empty()) return false;

        init(s);

        if (m_clauses.empty()) return false;

        // Auto-compute budget if not specified
        if (max_flips == 0) {
            // Scale with problem size: at least 10*num_vars, at most 100*num_vars
            uint64_t budget = static_cast<uint64_t>(m_num_vars) * 50;
            if (budget < 10000) budget = 10000;
            if (budget > 5000000) budget = 5000000;
            max_flips = static_cast<unsigned>(budget);
        }

        unsigned flips = 0;
        while (flips < max_flips && !m_unsat.empty()) {
            bool_var v = pick_var();
            flip(v);
            push_flip(v);
            save_best_if_improved();
            ++flips;

            if (m_best_unsat == 0) break;
        }

        export_best(s);
        return m_best_unsat == 0;
    }

}
