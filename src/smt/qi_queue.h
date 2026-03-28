/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    qi_queue.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-15.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/quantifier_stat.h"
#include "ast/rewriter/cached_var_subst.h"
#include "parsers/util/cost_parser.h"
#include "smt/smt_checker.h"
#include "smt/smt_quantifier.h"
#include "smt/fingerprints.h"
#include "params/qi_params.h"
#include "ast/cost_evaluator.h"
#include "util/statistics.h"
#include "tactic/user_propagator_base.h"
#include "smt/negative_knowledge.h"
#include <algorithm>
#include <cstring>

namespace smt {
    class context;

    /**
     * Dual-half Bloom filter for binding-level feedback.
     *
     * Tracks which binding structure hashes have appeared in conflict
     * antecedent chains.  Two 64KB halves (active/shadow) implement
     * epoch-based aging: every EPOCH_INSERTIONS marks, active is
     * replaced by shadow and shadow is cleared.  This gives a sliding
     * window of "useful" binding patterns without unbounded growth.
     *
     * k=3 independent hash functions from golden-ratio multiplicative
     * constants.  False positive rate ~1-5% at typical load.
     */
    struct qi_bloom_filter {
        static constexpr unsigned FILTER_SIZE      = 65536;  // 64KB per half
        static constexpr unsigned EPOCH_INSERTIONS = 20000;
        static constexpr uint64_t K1 = 0x9E3779B97F4A7C15ULL; // golden ratio
        static constexpr uint64_t K2 = 0x517CC1B727220A95ULL; // sqrt(3) frac
        static constexpr uint64_t K3 = 0x6C62272E07BB0142ULL; // sqrt(5) frac

        uint8_t  m_active[FILTER_SIZE];
        uint8_t  m_shadow[FILTER_SIZE];
        unsigned m_insert_count;
        unsigned m_total_marks;

        void init() {
            memset(m_active, 0, sizeof(m_active));
            memset(m_shadow, 0, sizeof(m_shadow));
            m_insert_count = 0;
            m_total_marks  = 0;
        }

        void indices(uint64_t h, unsigned & i1, unsigned & i2, unsigned & i3) const {
            i1 = static_cast<unsigned>((h * K1) >> 48) & (FILTER_SIZE - 1);
            i2 = static_cast<unsigned>((h * K2) >> 48) & (FILTER_SIZE - 1);
            i3 = static_cast<unsigned>((h * K3) >> 48) & (FILTER_SIZE - 1);
        }

        void mark_useful(uint64_t h) {
            unsigned i1, i2, i3;
            indices(h, i1, i2, i3);
            m_active[i1] = 1; m_active[i2] = 1; m_active[i3] = 1;
            m_shadow[i1] = 1; m_shadow[i2] = 1; m_shadow[i3] = 1;
            m_total_marks++;
            if (++m_insert_count >= EPOCH_INSERTIONS) {
                memcpy(m_active, m_shadow, FILTER_SIZE);
                memset(m_shadow, 0, FILTER_SIZE);
                m_insert_count = 0;
            }
        }

        bool probably_useful(uint64_t h) const {
            unsigned i1, i2, i3;
            indices(h, i1, i2, i3);
            return m_active[i1] && m_active[i2] && m_active[i3];
        }

        bool is_empty() const { return m_total_marks == 0; }
    };

    struct qi_queue_stats {
        unsigned m_num_instances, m_num_lazy_instances;
        unsigned m_num_qi_conflicts;  // global count of conflicts with QI participation
        unsigned m_num_fast_rejected; // insert() surprisal early-exit rejects
        unsigned m_num_qi_bankruptcies; // number of times QI velocity gate triggered
        void reset() { memset(this, 0, sizeof(qi_queue_stats)); }
        qi_queue_stats() { reset(); }
    };

    /**
     * E-graph metrics for adaptive QI throttling.
     * Tracks growth rate, binding depth, and equivalence class connectivity
     * across QI batches to modulate instantiation thresholds.
     */
    struct egraph_qi_metrics {
        unsigned m_enodes_before_qi;        // enode count snapshot before instantiate()
        float    m_growth_rate_ema;          // EMA of (enodes_after - enodes_before) / enodes_before
        float    m_avg_binding_depth_ema;    // EMA of max binding depth per insert()
        float    m_avg_connectivity_ema;     // EMA of distinct_roots / num_bindings
        unsigned m_add_eq_at_last_qi;        // m_num_add_eq snapshot before instantiate()
        unsigned m_instances_at_last_qi;     // m_num_instances snapshot before instantiate()
        float    m_qi_merge_ratio_ema;       // EMA of add_eq_delta / instances_delta
        unsigned m_deep_instance_count;      // instances with max_binding_depth >= 6
        void reset() { memset(this, 0, sizeof(egraph_qi_metrics)); }
        egraph_qi_metrics() { reset(); }
    };

    class qi_queue {
        quantifier_manager &          m_qm;
        context &                     m_context;
        ast_manager &                 m;
        qi_params &                   m_params;
        qi_queue_stats                m_stats;
        qi_bloom_filter               m_binding_filter;
        binding_failure_filter        m_failure_filter;
        egraph_qi_metrics             m_egraph_metrics;
        checker                       m_checker;
        expr_ref                      m_cost_function;
        expr_ref                      m_new_gen_function;
        cost_parser                   m_parser;
        cost_evaluator                m_evaluator;
        cached_var_subst              m_subst;
        svector<float>                m_vals;
        double                        m_eager_cost_threshold = 0;
        double                        m_surprisal_coeff = 2.0;
        std::function<bool(quantifier*,expr*)> m_on_binding;
        struct entry {
            fingerprint * m_qb;
            float         m_cost;
            float         m_heat_score;   //!< E7: sum of func_decl heat for binding enodes
            unsigned      m_generation:31;
            unsigned      m_instantiated:1;
            entry(fingerprint * f, float c, float h, unsigned g):m_qb(f), m_cost(c), m_heat_score(h), m_generation(g), m_instantiated(false) {}
        };
        svector<entry>                m_new_entries;
        svector<entry>                m_delayed_entries;
        expr_ref_vector               m_instances;
        unsigned_vector               m_instantiated_trail;
        struct scope {
            unsigned   m_delayed_entries_lim;
            unsigned   m_instances_lim;
            unsigned   m_instantiated_trail_lim;
            // NOTE: m_qi_velocity_inserts, m_qi_bankrupt, m_eager_cost_threshold,
            // m_surprisal_coeff are scoped at the BASE level (check-sat boundary)
            // by solver_driver::push/pop + apply_params, NOT at every decision
            // scope. They're constant within a single check-sat, and saving them
            // here (120K+ times per search) causes 18% CPU overhead.
        };
        svector<scope>                m_scopes;
        unsigned                      m_final_check_no_conflict_streak = 0;
        unsigned                      m_last_conflict_count = 0;

        // QI velocity gate: global insert/conflict ratio tracking.
        // When QI floods in without producing conflicts, the velocity
        // ratio (inserts / max(conflicts, 1)) spikes.  After a 50K-insert
        // warmup, ratio > 5000 doubles the effective eager threshold (BFS mode),
        // and ratio > 20000 blocks ALL new QI until the next search.
        unsigned                      m_qi_velocity_inserts = 0;
        unsigned                      m_qi_velocity_conflicts_base = 0; // qi_conflicts at search start
        bool                          m_qi_bankrupt = false;

        void init_parser_vars();
        q::quantifier_stat * set_values(quantifier * q, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation, float cost);
        unsigned pattern_ground_terms(app * pat);
        float get_cost(quantifier * q, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation);
        unsigned get_new_gen(quantifier * q, unsigned generation, float cost);
        void instantiate(entry & ent, bool skip_sat_check = false);
        void get_min_max_costs(float & min, float & max) const;
        void display_instance_profile(fingerprint * f, quantifier * q, unsigned num_bindings, enode * const * bindings, unsigned proof_id, unsigned generation);
        double compute_binding_relevancy(unsigned num_bindings, enode * const * bindings);
        float compute_binding_heat(quantifier * q, unsigned num_bindings, enode * const * bindings);

    public:
        qi_queue(quantifier_manager & qm, context & ctx, qi_params & params);
        void setup();
        /**
           \brief Insert a new quantifier in the queue, f contains the quantifier and bindings.
           f->get_data() is the quantifier.
        */
        void insert(fingerprint * f, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation);
        void instantiate();
        bool has_work() const { return !m_new_entries.empty(); }
        void init_search_eh();
        bool final_check_eh();
        void push_scope();
        void pop_scope(unsigned num_scopes);
        void reset();
        void display_delayed_instances_stats(std::ostream & out) const;
        void collect_statistics(::statistics & st) const;
        void register_on_binding(std::function<bool(quantifier* q, expr* e)> & on_binding) {
            m_on_binding = on_binding;
        }
        void inc_global_qi_conflicts() { m_stats.m_num_qi_conflicts++; }
        unsigned get_qi_conflicts() const { return m_stats.m_num_qi_conflicts; }
        void mark_binding_useful(uint64_t h) { m_binding_filter.mark_useful(h); }
        void record_binding_failure(uint64_t h) { m_failure_filter.record_failure(h); }
        void record_binding_success(uint64_t h) { m_failure_filter.record_success(h); }
        void on_conflict_failure_decay() { m_failure_filter.on_conflict(); }
        void inc_fast_rejected() { m_stats.m_num_fast_rejected++; }
        // SPSA causal signal accessors
        unsigned get_qi_velocity_inserts() const { return m_qi_velocity_inserts; }
        float    get_egraph_growth_rate_ema() const { return m_egraph_metrics.m_growth_rate_ema; }
        bool     is_qi_bankrupt() const { return m_qi_bankrupt; }

        // Solver driver: direct write to the cached eager threshold.
        // qi_queue::setup() copies m_params.m_qi_eager_threshold once;
        // subsequent runtime changes must go through this setter.
        void set_eager_threshold(double t) { m_eager_cost_threshold = t; }
        double get_eager_threshold() const { return m_eager_cost_threshold; }

        // Solver driver: scale the Bayesian surprisal coefficient.
        // Base coefficient is 2.0; the driver multiplies by qi_surprisal_scale.
        void set_surprisal_coeff(double c) { m_surprisal_coeff = c; }
        double get_surprisal_coeff() const { return m_surprisal_coeff; }
    };
};


