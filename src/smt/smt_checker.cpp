/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_checker.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-20.

Revision History:

--*/
#include "smt/smt_context.h"
#include "smt/smt_checker.h"
#include "ast/ast_ll_pp.h"

namespace smt {

    bool checker::all_args(app * a, bool is_true) {
        for (expr* arg : *a) {
            if (!check(arg, is_true))
                return false;
        }
        return true;
    }

    bool checker::any_arg(app * a, bool is_true) {
        for (expr* arg : *a) {
            if (check(arg, is_true))
                return true;
        }
        return false;
    }

    bool checker::check_core(expr * n, bool is_true) {
        SASSERT(m_manager.is_bool(n));
        // Fast path: if n is already internalized and relevant, check its assignment.
        // Combined b_internalized + get_assignment to avoid double ID lookup.
        {
            bool_var v = m_context.get_bool_var_of_id_option(n->get_id());
            if (v != null_bool_var && is_relevant(n)) {
                lbool val = m_context.get_assignment(v);
                return val != l_undef && is_true == (val == l_true);
            }
        }
        if (!is_app(n))
            return false;
        app * a = to_app(n);
        if (a->get_family_id() == m_manager.get_basic_family_id()) {
            switch (a->get_decl_kind()) {
            case OP_TRUE:
                return is_true;
            case OP_FALSE:
                return !is_true;
            case OP_NOT:
                return check(a->get_arg(0), !is_true);
            case OP_OR:
                return is_true ? any_arg(a, true) : all_args(a, false);
            case OP_AND:
                return is_true ? all_args(a, true) : any_arg(a, false);
            case OP_EQ:
                if (!m_manager.is_iff(a)) {
                    enode * lhs = get_enode_eq_to(a->get_arg(0));
                    enode * rhs = get_enode_eq_to(a->get_arg(1));
                    if (lhs && rhs && is_relevant(lhs) && is_relevant(rhs)) {
                        if (is_true && lhs->get_root() == rhs->get_root())
                            return true;
                        if (!is_true && m_context.is_diseq(lhs, rhs))
                            return true;
                    }
                    return false;
                }
                else if (is_true) {
                    return
                        (check(a->get_arg(0), true) &&
                         check(a->get_arg(1), true)) ||
                        (check(a->get_arg(0), false) &&
                         check(a->get_arg(1), false));
                }
                else {
                    return
                        (check(a->get_arg(0), true) &&
                         check(a->get_arg(1), false)) ||
                        (check(a->get_arg(0), false) &&
                         check(a->get_arg(1), true));
                }
            case OP_ITE: {
                if (m_context.lit_internalized(a->get_arg(0)) && is_relevant(a->get_arg(0))) {
                    switch (m_context.get_assignment(a->get_arg(0))) {
                    case l_false: return check(a->get_arg(2), is_true);
                    case l_undef: return false;
                    case l_true:  return check(a->get_arg(1), is_true);
                    }
                }
                return check(a->get_arg(1), is_true) && check(a->get_arg(2), is_true);
            }
            default:
                break;
            }
        }
        enode * e = get_enode_eq_to(a);
        if (e && e->is_bool() && is_relevant(e)) {
            lbool val = m_context.get_assignment(e->get_expr());
            return val != l_undef && is_true == (val == l_true);
        }
        return false;
    }

    bool checker::check(expr * n, bool is_true) {
        if (n->get_ref_count() > 1) {
            unsigned id = n->get_id();
            unsigned pol = static_cast<unsigned>(is_true);
            if (id < m_bool_gen[pol].size() && m_bool_gen[pol][id] == m_bool_cache_gen)
                return m_bool_val[pol][id] != 0;
            bool r = check_core(n, is_true);
            m_bool_gen[pol].reserve(id + 1, 0);
            m_bool_val[pol].reserve(id + 1, 0);
            m_bool_gen[pol][id] = m_bool_cache_gen;
            m_bool_val[pol][id] = r ? 1 : 0;
            return r;
        }
        return check_core(n, is_true);
    }

    enode * checker::get_enode_eq_to_core(app * n) {
        unsigned num = n->get_num_args();
        // Specialize for binary (most common) and unary to avoid ptr_buffer overhead
        if (num == 2) {
            enode * a0 = get_enode_eq_to(n->get_arg(0));
            if (!a0) return nullptr;
            // Prefetch a0's cache line — CG table hash will read a0->m_root_hash
            // and equality will read a0->m_root. The recursive call to resolve arg1
            // provides enough time for the prefetch to complete.
            __builtin_prefetch(a0, 0, 1);
            enode * a1 = get_enode_eq_to(n->get_arg(1));
            if (!a1) return nullptr;
            enode * args[2] = { a0, a1 };
            enode * e = m_context.get_enode_eq_to(n->get_decl(), 2, args);
            return (e && is_relevant(e)) ? e : nullptr;
        }
        if (num == 1) {
            enode * a0 = get_enode_eq_to(n->get_arg(0));
            if (!a0) return nullptr;
            enode * e = m_context.get_enode_eq_to(n->get_decl(), 1, &a0);
            return (e && is_relevant(e)) ? e : nullptr;
        }
        ptr_buffer<enode> buffer;
        for (unsigned i = 0; i < num; ++i) {
            enode * arg = get_enode_eq_to(n->get_arg(i));
            if (arg == nullptr)
                return nullptr;
            buffer.push_back(arg);
        }
        enode * e = m_context.get_enode_eq_to(n->get_decl(), num, buffer.data());
        if (e == nullptr)
            return nullptr;
        return is_relevant(e) ? e : nullptr;
    }

    enode * checker::get_enode_eq_to(expr * n) {
        if (is_var(n)) {
            unsigned idx = to_var(n)->get_idx();
            if (idx >= m_num_bindings)
                return nullptr;
            return m_bindings[m_num_bindings - idx - 1];
        }
        enode * e = m_context.get_enode_or_null(n);
        if (e && is_relevant(n))
            return e;
        if (!is_app(n) || to_app(n)->get_num_args() == 0)
            return nullptr;
        if (n->get_ref_count() > 1) {
            unsigned id = n->get_id();
            if (id < m_enode_gen.size() && m_enode_gen[id] == m_enode_cache_gen)
                return m_enode_val[id];
            enode * r = get_enode_eq_to_core(to_app(n));
            m_enode_gen.reserve(id + 1, 0);
            m_enode_val.reserve(id + 1, nullptr);
            m_enode_gen[id] = m_enode_cache_gen;
            m_enode_val[id] = r;
            return r;
        }
        return get_enode_eq_to_core(to_app(n));
    }

    void checker::init_relevancy_cache() {
        m_relevancy_enabled = m_context.relevancy();
        if (m_relevancy_enabled)
            m_relevant_set = m_context.get_relevancy_propagator().get_relevant_set();
        else
            m_relevant_set = nullptr;
    }

    bool checker::is_relevant(enode * n) const {
        if (!m_relevancy_enabled) return true;
        return m_relevant_set && m_relevant_set->contains(n->get_expr()->get_id());
    }

    bool checker::is_sat(expr * n, unsigned num_bindings, enode * const * bindings) {
        flet<unsigned>        l1(m_num_bindings, num_bindings);
        flet<enode * const *> l2(m_bindings, bindings);
        begin_check(num_bindings, bindings);
        init_relevancy_cache();
        bool r = check(n, true);
        cache_reset_bool();
        return r;
    }

    bool checker::is_unsat(expr * n, unsigned num_bindings, enode * const * bindings) {
        flet<unsigned>        l1(m_num_bindings, num_bindings);
        flet<enode * const *> l2(m_bindings, bindings);
        begin_check(num_bindings, bindings);
        init_relevancy_cache();
        bool r = check(n, false);
        cache_reset_bool();
        return r;
    }

    bool checker::all_terms_exist_core(expr * n) {
        if (is_var(n))
            return to_var(n)->get_idx() < m_num_bindings;
        if (!is_app(n))
            return false;

        if (n->get_ref_count() > 1) {
            unsigned id = n->get_id();
            if (id < m_bool_gen[0].size() && m_bool_gen[0][id] == m_bool_cache_gen)
                return m_bool_val[0][id] != 0;
        }

        app * a = to_app(n);
        bool r;
        if (a->get_family_id() == m_manager.get_basic_family_id()) {
            switch (a->get_decl_kind()) {
            case OP_TRUE:
            case OP_FALSE:
                r = true;
                break;
            case OP_NOT:
                r = all_terms_exist_core(a->get_arg(0));
                break;
            case OP_AND:
            case OP_OR:
                r = true;
                for (expr * arg : *a) {
                    if (!all_terms_exist_core(arg)) {
                        r = false;
                        break;
                    }
                }
                break;
            case OP_IMPLIES:
            case OP_XOR:
            case OP_OEQ:
                r = all_terms_exist_core(a->get_arg(0)) &&
                    all_terms_exist_core(a->get_arg(1));
                break;
            case OP_EQ:
                if (m_manager.is_bool(a->get_arg(0)))
                    r = all_terms_exist_core(a->get_arg(0)) &&
                        all_terms_exist_core(a->get_arg(1));
                else
                    r = get_enode_eq_to(a->get_arg(0)) != nullptr &&
                        get_enode_eq_to(a->get_arg(1)) != nullptr;
                break;
            case OP_DISTINCT:
                r = true;
                for (expr * arg : *a) {
                    if (get_enode_eq_to(arg) == nullptr) {
                        r = false;
                        break;
                    }
                }
                break;
            case OP_ITE:
                if (m_manager.is_bool(a))
                    r = all_terms_exist_core(a->get_arg(0)) &&
                        all_terms_exist_core(a->get_arg(1)) &&
                        all_terms_exist_core(a->get_arg(2));
                else
                    r = get_enode_eq_to(a) != nullptr;
                break;
            default:
                r = get_enode_eq_to(a) != nullptr;
                break;
            }
        }
        else {
            r = get_enode_eq_to(a) != nullptr;
        }

        if (n->get_ref_count() > 1) {
            unsigned id = n->get_id();
            m_bool_gen[0].reserve(id + 1, 0);
            m_bool_val[0].reserve(id + 1, 0);
            m_bool_gen[0][id] = m_bool_cache_gen;
            m_bool_val[0][id] = r ? 1 : 0;
        }
        return r;
    }

    bool checker::all_terms_exist(expr * n, unsigned num_bindings, enode * const * bindings) {
        flet<unsigned>        l1(m_num_bindings, num_bindings);
        flet<enode * const *> l2(m_bindings, bindings);
        begin_check(num_bindings, bindings);
        init_relevancy_cache();
        bool r = all_terms_exist_core(n);
        cache_reset_bool();
        return r;
    }

    checker::checker(context & c):
        m_context(c),
        m_manager(c.get_manager()),
        m_bool_cache_gen(1),
        m_enode_cache_gen(1),
        m_num_bindings(0),
        m_bindings(nullptr),
        m_prev_num_bindings(UINT_MAX),
        m_prev_bindings(nullptr),
        m_relevancy_enabled(false),
        m_relevant_set(nullptr) {
    }

};
