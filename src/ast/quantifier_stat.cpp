/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_quantifier_stat.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#include "ast/quantifier_stat.h"
#include <cstring>

namespace q {

    quantifier_stat::quantifier_stat(unsigned generation):
        m_size(0),
        m_depth(0),
        m_generation(generation),
        m_case_split_factor(1),
        m_num_nested_quantifiers(0),
        m_num_instances(0),
        m_num_instances_checker_sat(0),
        m_num_instances_simplify_true(0),
        m_num_instances_curr_search(0),
        m_num_instances_curr_branch(0),
        m_max_generation(0),
        m_max_cost(0.0f),
        m_had_unary_instance(false),
        m_num_conflicts(0),
        m_num_conflicts_curr_search(0),
        m_instances_total(0),
        m_inserts_total(0),
        m_reward(0.1),
        m_body_heat(0.0),
        m_body_heat_conflict(0),
        m_binding_hash_ring_pos(0) {
        memset(m_binding_hash_ring, 0, sizeof(m_binding_hash_ring));
    }

    quantifier_stat_gen::quantifier_stat_gen(ast_manager & m, region & r):
        m_manager(m),
        m_region(r),
        m_gen(1) {
    }

    void quantifier_stat_gen::reset() {
        m_gen++;
        m_todo.reset();
        m_case_split_factor = 1;
    }

    quantifier_stat * quantifier_stat_gen::operator()(quantifier * q, unsigned generation) {
        reset();
        quantifier_stat * r = new (m_region) quantifier_stat(generation);
        m_todo.push_back(entry(q->get_expr()));
        while (!m_todo.empty()) {
            entry & e       = m_todo.back();
            expr * n        = e.m_expr;
            unsigned depth  = e.m_depth;
            bool depth_only = e.m_depth_only;
            m_todo.pop_back();
            unsigned id = n->get_id();
            if (id < m_visited_gen.size() && m_visited_gen[id] == m_gen) {
                if (m_visited_depth[id] >= depth)
                    continue;
                depth_only = true;
            }
            m_visited_gen.reserve(id + 1, 0);
            m_visited_depth.reserve(id + 1, 0);
            m_visited_gen[id] = m_gen;
            m_visited_depth[id] = depth;
            if (depth >= r->m_depth) 
                r->m_depth = depth;
            if (!depth_only) {
                r->m_size++;
                if (is_quantifier(n))
                    r->m_num_nested_quantifiers ++;
                if (is_app(n) && to_app(n)->get_family_id() == m_manager.get_basic_family_id()) {
                    unsigned num_args = to_app(n)->get_num_args();
                    // Remark: I'm approximating the case_split factor.
                    // I'm also ignoring the case split factor due to theories.
                    switch (to_app(n)->get_decl_kind()) {
                    case OP_OR:
                        if (depth == 0)
                            m_case_split_factor *= num_args;
                        else
                            m_case_split_factor *= (num_args + 1);
                        break;
                    case OP_AND:
                        if (depth > 0)
                            m_case_split_factor *= (num_args + 1);
                        break;
                    case OP_EQ:
                        if (m_manager.is_iff(n)) {
                            if (depth == 0)
                                m_case_split_factor *= 4;
                            else
                                m_case_split_factor *= 9;
                        }
                        break;
                    case OP_ITE:
                        if (depth == 0)
                            m_case_split_factor *= 4;
                        else
                            m_case_split_factor *= 9;
                        break;
                    default:
                        break;
                    }
                }
            }
            if (is_app(n)) {
                unsigned j = to_app(n)->get_num_args();
                while (j > 0) {
                    --j;
                    m_todo.push_back(entry(to_app(n)->get_arg(j), depth + 1, depth_only));
                }
            }
        }
        r->m_case_split_factor = m_case_split_factor.get_value();
        return r;
    }

};

