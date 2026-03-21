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
            m_num_conflicts++;
            m_num_conflicts_curr_search++;
            // Update reward EMA: binary sample = 1.0 (conflict just happened).
            // Combined with decay in inc_instances_total(), this tracks the
            // conflict participation rate with proper temporal weighting.
            m_reward = 0.95 * m_reward + 0.05;
        }
        unsigned get_num_conflicts() const { return m_num_conflicts; }
        unsigned get_num_conflicts_curr_search() const { return m_num_conflicts_curr_search; }
        void reset_num_conflicts_curr_search() { m_num_conflicts_curr_search = 0; }

        void inc_instances_total() {
            m_instances_total++;
            // Decay reward EMA: sample = 0.0 (instance created without conflict).
            // This ensures the reward decays when instances are created without
            // contributing to conflicts, preventing stale high rewards.
            m_reward *= 0.999;
        }
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


