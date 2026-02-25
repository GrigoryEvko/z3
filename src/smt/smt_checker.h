/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_checker.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-20.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/uint_set.h"

namespace smt {

    class context;

    class checker {

        context &              m_context;
        ast_manager &          m_manager;

        // Split generation-stamped caches indexed by expr->get_id().
        // Bool cache: reset between is_unsat/all_terms_exist/is_sat calls.
        // Enode cache: kept across calls with the same bindings (avoids redundant CG lookups).
        unsigned               m_bool_cache_gen;
        unsigned               m_enode_cache_gen;
        svector<unsigned>      m_bool_gen[2];   // generation stamps per polarity
        svector<char>          m_bool_val[2];   // cached bool results per polarity
        svector<unsigned>      m_enode_gen;      // generation stamps for enode cache
        svector<enode*>        m_enode_val;      // cached enode* results

        unsigned               m_num_bindings;
        enode * const *        m_bindings;

        // Track previous bindings to detect changes and reset enode cache.
        unsigned               m_prev_num_bindings;
        enode * const *        m_prev_bindings;

        // Cached relevancy state — avoids repeated pointer chases through
        // m_context.relevancy() → relevancy_lvl() → std::min(...) and
        // m_relevancy_propagator->get_relevant_set() on every is_relevant call.
        bool                   m_relevancy_enabled;
        uint_set const *       m_relevant_set;

        bool all_args(app * a, bool is_true);
        bool any_arg(app * a, bool is_true);
        bool check_core(expr * n, bool is_true);
        bool check(expr * n, bool is_true);
        enode * get_enode_eq_to_core(app * n);
        enode * get_enode_eq_to(expr * n);

        bool all_terms_exist_core(expr * n);

        void cache_reset_bool() { m_bool_cache_gen++; }
        void cache_reset_all()  { m_bool_cache_gen++; m_enode_cache_gen++; }

        // Reset enode cache only if bindings changed; always reset bool cache.
        void begin_check(unsigned num_bindings, enode * const * bindings) {
            if (num_bindings != m_prev_num_bindings || bindings != m_prev_bindings) {
                m_enode_cache_gen++;
                m_prev_num_bindings = num_bindings;
                m_prev_bindings = bindings;
            }
        }

        // Fast relevancy check using cached state.
        // Avoids 2 pointer indirections per call vs m_context.is_relevant().
        bool is_relevant(expr * n) const {
            if (!m_relevancy_enabled) return true;
            return m_relevant_set && m_relevant_set->contains(n->get_id());
        }
        bool is_relevant(enode * n) const;

        void init_relevancy_cache();

    public:
        checker(context & c);
        bool is_sat(expr * n, unsigned num_bindings = 0, enode * const * bindings = nullptr);
        bool is_unsat(expr * n, unsigned num_bindings = 0, enode * const * bindings = nullptr);
        // Returns true if all non-boolean subterms of n (with current bindings)
        // already exist in the E-graph. Such instances create no new E-graph
        // nodes and should be processed immediately.
        bool all_terms_exist(expr * n, unsigned num_bindings, enode * const * bindings);
    };

};

