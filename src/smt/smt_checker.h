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
#include "util/obj_hashtable.h"

namespace smt {

    class context;

    class checker {

        typedef obj_map<expr, bool>    expr2bool;
        typedef obj_map<expr, enode *> expr2enode;

        context &              m_context;
        ast_manager &          m_manager;
        expr2bool              m_is_true_cache[2];
        expr2enode             m_to_enode_cache;
        // Track inserted entries for O(entries) cache reset instead of O(capacity).
        ptr_vector<expr>       m_is_true_inserted[2];
        ptr_vector<expr>       m_to_enode_inserted;
        unsigned               m_num_bindings;
        enode * const *        m_bindings;

        bool all_args(app * a, bool is_true);
        bool any_arg(app * a, bool is_true);
        bool check_core(expr * n, bool is_true);
        bool check(expr * n, bool is_true);
        enode * get_enode_eq_to_core(app * n);
        enode * get_enode_eq_to(expr * n);

        bool all_terms_exist_core(expr * n);

        void cache_reset();

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

