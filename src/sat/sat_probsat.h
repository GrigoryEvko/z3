/*++
  Copyright (c) 2025 Microsoft Corporation

  Module Name:

    sat_probsat.h

  Abstract:

    Lightweight in-place ProbSAT random walker for SAT solver phase improvement.

    Based on CaDiCaL's walk.cpp implementation of ProbSAT (Adrian Balint's thesis).
    Operates directly on the solver's clause storage -- NO clause copying.

    Algorithm:
      1. Build occurrence lists from solver's clauses/binaries (one-time O(total_lits))
      2. Initialize assignment from current phases
      3. Flip loop: pick random unsatisfied clause, select literal probabilistically
         by break-count score (base^break_count where base = 1/CB), flip it
      4. Track best assignment via incremental flip trail
      5. Save best assignment back to solver phases

  Author:

    Grigory (2025)

  Notes:

    CB interpolation table from CaDiCaL (Adrian Balint):
      size=0 -> CB=2.00, size=3 -> CB=2.50, size=4 -> CB=2.85,
      size=5 -> CB=3.70, size=6 -> CB=5.10, size=7 -> CB=7.40
    Every second invocation uses CB=2.0 for diversity.

--*/
#pragma once

#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "util/vector.h"

namespace sat {

    class solver;

    class probsat {
    public:
        // Run ProbSAT walk on solver s.
        // max_flips: budget (0 = auto-compute from conflicts).
        // Returns true if all clauses satisfied (unlikely but possible).
        bool operator()(solver& s, unsigned max_flips = 0);

    private:
        // Clause reference: either a pointer to a long clause or a binary encoded inline.
        // Binary clauses don't have clause objects in Z3, so we store both literals directly.
        struct clause_ref {
            // For long clauses: pointer to clause object (non-owning).
            // For binary clauses: nullptr, with literals stored in l0, l1.
            clause*  m_clause;
            literal  m_l0;
            literal  m_l1;

            // Long clause constructor
            explicit clause_ref(clause* c) : m_clause(c), m_l0(null_literal), m_l1(null_literal) {}
            // Binary clause constructor
            clause_ref(literal a, literal b) : m_clause(nullptr), m_l0(a), m_l1(b) {}

            bool is_binary() const { return m_clause == nullptr; }
            unsigned size() const { return is_binary() ? 2 : m_clause->size(); }
        };

        // Occurrence list entry: index into m_clauses
        using occ_list = unsigned_vector;

        // Per-clause tracking
        struct clause_info {
            unsigned m_num_true;   // count of currently-true literals
            unsigned m_true_sum;   // sum of true literal indices (for break-count: when num_true==1, identifies the sole satisfier)

            clause_info() : m_num_true(0), m_true_sum(0) {}

            bool is_sat() const { return m_num_true > 0; }

            void add(literal lit) {
                ++m_num_true;
                m_true_sum += lit.index();
            }

            void del(literal lit) {
                SASSERT(m_num_true > 0);
                --m_num_true;
                m_true_sum -= lit.index();
            }
        };

        // --- State ---
        solver*                     m_solver;
        svector<clause_ref>         m_clauses;          // all clauses (binary + long)
        svector<clause_info>        m_clause_info;      // per-clause sat tracking
        vector<occ_list>            m_occs;             // occurrence lists indexed by literal.index()
        bool_vector                 m_values;           // current assignment (indexed by bool_var)
        unsigned_vector             m_break_count;      // break count per variable
        indexed_uint_set            m_unsat;            // set of unsatisfied clause indices
        svector<double>             m_score_table;      // pre-computed scores: score_table[i] = base^i
        double                      m_epsilon = 0;      // smallest score (for break counts beyond table)
        random_gen                  m_rand;
        unsigned                    m_num_vars = 0;
        unsigned                    m_walk_count = 0;   // how many times we've been called (for CB alternation)

        // Best-model tracking via flip trail (CaDiCaL-style)
        bool_vector                 m_best_values;      // best assignment seen
        int                         m_best_trail_pos = 0; // position in flip trail of best model (-1 = invalid)
        unsigned_vector             m_flip_trail;       // trail of flipped variables
        unsigned                    m_best_unsat = 0;   // number of unsat clauses at best

        // Temporary buffer for scoring (reused across picks)
        svector<double>             m_lit_scores;

        // --- Methods ---
        void init(solver& s);
        void build_occurrences(solver& s);
        void init_assignment(solver& s);
        void init_clause_info();
        void populate_score_table();
        double compute_avg_clause_size() const;

        // CB interpolation (piecewise linear, CaDiCaL-style)
        static double fit_cb(double avg_size);

        // Score lookup
        double score(unsigned break_val) const {
            return break_val < m_score_table.size() ? m_score_table[break_val] : m_epsilon;
        }

        // Pick a random unsatisfied clause, then probabilistically select a literal to flip
        bool_var pick_var();

        // Flip variable: update assignment, break-counts, unsat set
        void flip(bool_var v);

        // Save current assignment as best if improved
        void save_best_if_improved();

        // Flip trail management
        void push_flip(bool_var v);
        void flush_trail();

        // Export best assignment back to solver phases
        void export_best(solver& s);

        // Check if literal is true under current assignment
        bool is_true(literal lit) const {
            return m_values[lit.var()] != lit.sign();
        }
    };

}
