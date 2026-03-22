/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    quantifier_stat.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/approx_nat.h"
#include "util/region.h"

namespace q {
    
    /**
       \brief Store statistics for quantifiers. This information is
       used to implement heuristics for quantifier instantiation.
    */
    class quantifier_stat {
        unsigned m_size;
        unsigned m_depth;
        unsigned m_generation;
        unsigned m_case_split_factor; //!< the product of the size of the clauses created by this quantifier.
        unsigned m_num_nested_quantifiers;
        unsigned m_num_instances;
        unsigned m_num_instances_checker_sat;
        unsigned m_num_instances_simplify_true;
        unsigned m_num_instances_curr_search;
        unsigned m_num_instances_curr_branch; //!< only updated if QI_TRACK_INSTANCES is true
        unsigned m_max_generation; //!< max. generation of an instance
        float    m_max_cost;
        bool     m_had_unary_instance; //!< single-trigger produced instance this search
        unsigned m_num_conflicts;       //!< number of conflicts where a clause from this quantifier appeared in the antecedent chain
        unsigned m_num_conflicts_curr_search; //!< conflicts in current search
        unsigned m_instances_total;     //!< total instances ever created (never reset)
        double   m_reward;              //!< EMA of conflict participation rate (instances_in_conflict / total_instances)

        // Ring buffer of recent binding structure hashes (E2.3).
        // Used by attribute_qi_conflict to mark useful patterns in the
        // Bloom filter.  4 entries keeps overhead to 36 bytes per
        // quantifier while providing recent binding lookback.
        static constexpr unsigned BINDING_RING_SIZE = 4;
        uint64_t m_binding_hash_ring[BINDING_RING_SIZE];
        unsigned m_binding_hash_ring_pos;

        friend class quantifier_stat_gen;

        quantifier_stat(unsigned generation);
    public:

        unsigned get_size() const { 
            return m_size; 
        }
        
        unsigned get_depth() const { 
            return m_depth; 
        }
        
        unsigned get_generation() const {
            return m_generation; 
        }
        
        unsigned get_case_split_factor() const {
            return m_case_split_factor;
        }

        unsigned get_num_nested_quantifiers() const {
            return m_num_nested_quantifiers;
        }

        unsigned get_num_instances() const {
            return m_num_instances;
        }
        unsigned get_num_instances_simplify_true() const {
            return m_num_instances_simplify_true;
        }
        unsigned get_num_instances_checker_sat() const {
            return m_num_instances_checker_sat;
        }

        unsigned get_num_instances_curr_search() const {
            return m_num_instances_curr_search;
        }

        unsigned & get_num_instances_curr_branch() {
            return m_num_instances_curr_branch;
        }

        void inc_num_instances_simplify_true() {
            m_num_instances_simplify_true++;
        }

        void inc_num_instances_checker_sat() {
            m_num_instances_checker_sat++;
        }
        
        void inc_num_instances() {
            m_num_instances++;
            m_num_instances_curr_search++;
        }

        void inc_num_instances_curr_branch() {
            m_num_instances_curr_branch++;
        }

        void reset_num_instances_curr_search() {
            m_num_instances_curr_search = 0;
            m_had_unary_instance = false;
            m_num_conflicts_curr_search = 0;
        }

        void set_had_unary_instance() { m_had_unary_instance = true; }
        bool had_unary_instance() const { return m_had_unary_instance; }

        void inc_num_conflicts() {
            inc_num_conflicts_weighted(1.0);
        }

        /**
         * Increment conflict count with a depth-weighted EMA alpha.
         * weight < 1 reduces the learning rate for quantifiers that
         * appeared far from the conflict in the antecedent chain.
         */
        void inc_num_conflicts_weighted(double weight) {
            m_num_conflicts++;
            m_num_conflicts_curr_search++;
            double sample = static_cast<double>(m_num_conflicts) / (m_instances_total > 0 ? m_instances_total : 1u);
            double alpha  = 0.05 * weight;
            m_reward = (1.0 - alpha) * m_reward + alpha * sample;
            if (m_reward < 0.01) m_reward = 0.01;
        }
        unsigned get_num_conflicts() const { return m_num_conflicts; }
        unsigned get_num_conflicts_curr_search() const { return m_num_conflicts_curr_search; }
        void reset_num_conflicts_curr_search() { m_num_conflicts_curr_search = 0; }

        void inc_instances_total() { m_instances_total++; }
        unsigned get_instances_total() const { return m_instances_total; }
        double get_reward() const { return m_reward; }
        void set_reward(double r) { m_reward = r; }

        void update_max_generation(unsigned g) {
            if (m_max_generation < g)
                m_max_generation = g;
        }

        unsigned get_max_generation() const {
            return m_max_generation;
        }

        void update_max_cost(float c) {
            if (m_max_cost < c)
                m_max_cost = c;
        }

        float get_max_cost() const {
            return m_max_cost;
        }

        /**
         * Record a binding structure hash in the per-quantifier ring buffer.
         * Called after each successful instantiation so that
         * attribute_qi_conflict can mark recent bindings as useful.
         */
        void record_binding_hash(uint64_t h) {
            m_binding_hash_ring[m_binding_hash_ring_pos & (BINDING_RING_SIZE - 1)] = h;
            m_binding_hash_ring_pos++;
        }

        /**
         * Iterate over recent binding hashes in the ring buffer.
         * Calls fn(hash) for each non-zero entry.  At most
         * BINDING_RING_SIZE entries are visited.
         */
        template<typename Fn>
        void for_each_recent_binding_hash(Fn && fn) const {
            unsigned n = m_binding_hash_ring_pos < BINDING_RING_SIZE
                       ? m_binding_hash_ring_pos : BINDING_RING_SIZE;
            for (unsigned i = 0; i < n; ++i) {
                uint64_t h = m_binding_hash_ring[i];
                if (h != 0)
                    fn(h);
            }
        }
    };

    /**
       \brief Functor used to generate quantifier statistics.
    */
    class quantifier_stat_gen {
        struct entry {
            expr *    m_expr;
            unsigned  m_depth:31;
            bool      m_depth_only:1; //!< track only the depth of this entry.
            entry():m_expr(nullptr), m_depth(0), m_depth_only(false) {}
            entry(expr * n, unsigned depth = 0, bool depth_only = false):m_expr(n), m_depth(depth), m_depth_only(depth_only) {}
        };
        ast_manager &           m_manager;
        region &                m_region;
        unsigned                m_gen;           // generation counter for O(1) reset
        svector<unsigned>       m_visited_gen;   // generation stamps indexed by expr->get_id()
        svector<unsigned>       m_visited_depth; // cached depth values
        svector<entry>          m_todo;
        approx_nat              m_case_split_factor;
        void reset();
        
    public:
        quantifier_stat_gen(ast_manager & m, region & r);
        quantifier_stat * operator()(quantifier * q, unsigned generation);
    };

};


