/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_asymm_branch.h

Abstract:

    SAT solver asymmetric branching

Author:

    Leonardo de Moura (leonardo) 2011-05-30.

Revision History:

--*/
#pragma once

#include "sat/sat_types.h"
#include "sat/sat_big.h"
#include "util/statistics.h"
#include "util/params.h"

namespace sat {
    class solver;
    class scoped_detach;

    class asymm_branch {
        friend class solver;
        struct report;

        solver &   s;
        params_ref m_params;
        int64_t    m_counter;
        random_gen m_rand;
        unsigned   m_calls;
        unsigned   m_touch_index;
        
        // config
        bool       m_asymm_branch;
        unsigned   m_asymm_branch_rounds;
        unsigned   m_asymm_branch_delay;
        bool       m_asymm_branch_sampled;
        bool       m_asymm_branch_all;
        int64_t    m_asymm_branch_limit;

        // stats
        unsigned   m_elim_literals;
        unsigned   m_elim_learned_literals;
        unsigned   m_tr;
        unsigned   m_prefix_subsumed;
        unsigned   m_vivify_retries;   // number of retry passes that succeeded

        // vivification retry & once-only (CaDiCaL-style)
        clause_vector m_retry_queue;   // clauses strengthened this pass, eligible for retry
        uint_set      m_vivified;      // clause IDs attempted without change (skip in future rounds)

        literal_vector m_pos, m_neg; // literals (complements of literals) in clauses sorted by discovery time (m_left in BIG).
        svector<std::pair<literal, unsigned>> m_pos1, m_neg1;
        literal_vector m_to_delete;
        literal_vector m_tmp;
        svector<int64_t> m_jw_occ;  // Jeroslow-Wang per-literal occurrence scores
       
        struct compare_left;

        bool is_touched(bool_var v) const;

        void sort(big& big, literal const* begin, literal const* end);
        void sort(big & big, clause const& c);

        bool uhle(scoped_detach& scoped_d, big & big, clause & c);

        void uhle(big & big);

        bool uhte(big & big, clause & c);

        bool re_attach(scoped_detach& scoped_d, clause& c, unsigned new_sz);

        bool process(bool learned);

        bool process(big& big, bool learned);

        bool process(clause & c);

        bool process_sampled(big& big, clause & c);

        void process(big* big, clause_vector & c);
        
        bool process_all(clause & c);

        void process_bin(big& big);
        
        bool flip_literal_at(clause const& c, unsigned flip_index, unsigned& new_sz);

        bool cleanup(scoped_detach& scoped_d, clause& c, unsigned skip_index, unsigned new_sz);

        bool propagate_literal(clause const& c, literal l);

        // CaDiCaL-style vivification with full conflict analysis.
        // Assigns each negated clause literal at its own scope level,
        // performs conflict analysis on conflict to derive a decision-only
        // strengthened clause, and tries instantiation as fallback.
        bool vivify_clause(clause& c);

        // Analyze conflict during vivification: walk implication graph
        // backward, collect the set of decision literals that contributed
        // to the conflict. Returns the strengthened clause as m_tmp.
        void vivify_analyze(clause const& c, unsigned num_levels);

        // CaDiCaL-style vivification with decision reuse between clauses.
        // Sorts clause literals by JW occurrence, sorts clauses lexicographically,
        // then processes them incrementally -- reusing decisions on the trail
        // when consecutive clauses share a common literal prefix.
        void process_with_reuse(clause_vector& clauses, int64_t limit);

        // Decision-reuse state: tracks which negated literals are currently
        // decided on the trail (one per scope level, starting at level 1).
        literal_vector m_decisions;  // m_decisions[i] = literal decided at level i+1
        unsigned       m_reused_decisions;  // stat counter

        void prefix_subsume(clause_vector& clauses);

    public:
        asymm_branch(solver & s, params_ref const & p);

        void operator()(bool force);

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void collect_statistics(statistics & st) const;
        void reset_statistics();

        void init_search() { m_calls = 0; m_vivified.reset(); m_reused_decisions = 0; }

        // Scale budget proportional to propagation work (CaDiCaL SET_EFFORT_LIMIT).
        // Adds delta to the current limit, so early calls use the parameter default
        // and later calls grow with search effort.
        void add_effort_budget(int64_t delta) {
            if (delta > 0) {
                m_asymm_branch_limit += delta;
                if (m_asymm_branch_limit > static_cast<int64_t>(UINT_MAX))
                    m_asymm_branch_limit = UINT_MAX;
            }
        }

        inline void dec(unsigned c) { m_counter -= c; }
    };

};

