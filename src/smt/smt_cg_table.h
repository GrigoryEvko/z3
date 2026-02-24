/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_cg_table.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#pragma once

#include "smt/smt_enode.h"
#include "util/hashtable.h"
#include "util/chashtable.h"

namespace smt {

    typedef std::pair<enode *, bool> enode_bool_pair;
    
    // one table per function symbol

    /**
       \brief Congruence table.
    */
    class cg_table {
        struct cg_unary_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->get_num_args() == 1);
                return n->get_arg(0)->get_root_hash();
            }
        };

        struct cg_unary_eq {
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->get_num_args() == 1);
                SASSERT(n2->get_num_args() == 1);
                SASSERT(n1->get_decl() == n2->get_decl());
                return n1->get_arg(0)->get_root() == n2->get_arg(0)->get_root();
            }
        };

        typedef chashtable<enode *, cg_unary_hash, cg_unary_eq> unary_table;
        
        struct cg_binary_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->get_num_args() == 2);
                enode * a0 = n->get_arg(0);
                enode * a1 = n->get_arg(1);
                __builtin_prefetch(a1, 0, 1);
                return combine_hash(a0->get_root_hash(), a1->get_root_hash());
            }
        };

        struct cg_binary_eq {
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->get_num_args() == 2);
                SASSERT(n2->get_num_args() == 2);
                SASSERT(n1->get_decl() == n2->get_decl());
                enode * a1_1 = n1->get_arg(1);
                enode * a2_1 = n2->get_arg(1);
                __builtin_prefetch(a1_1, 0, 1);
                __builtin_prefetch(a2_1, 0, 1);
                if (n1->get_arg(0)->get_root() != n2->get_arg(0)->get_root())
                    return false;
                return a1_1->get_root() == a2_1->get_root();
            }
        };

        typedef chashtable<enode*, cg_binary_hash, cg_binary_eq> binary_table;
        
        struct cg_comm_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->get_num_args() == 2);
                enode * a0 = n->get_arg(0);
                enode * a1 = n->get_arg(1);
                __builtin_prefetch(a1, 0, 1);
                unsigned h1 = a0->get_root_hash();
                unsigned h2 = a1->get_root_hash();
                if (h1 > h2)
                    std::swap(h1, h2);
                return hash_u(h1 + h2);
            }
        };
        
        struct cg_comm_eq {
            bool & m_commutativity;
            cg_comm_eq(bool & c):m_commutativity(c) {}
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->get_num_args() == 2);
                SASSERT(n2->get_num_args() == 2);
                SASSERT(n1->get_decl() == n2->get_decl());
                enode * a1_0 = n1->get_arg(0);
                enode * a1_1 = n1->get_arg(1);
                enode * a2_0 = n2->get_arg(0);
                enode * a2_1 = n2->get_arg(1);
                __builtin_prefetch(a1_1, 0, 1);
                __builtin_prefetch(a2_1, 0, 1);
                enode * c1_1 = a1_0->get_root();
                enode * c1_2 = a1_1->get_root();
                enode * c2_1 = a2_0->get_root();
                enode * c2_2 = a2_1->get_root();
                if (c1_1 == c2_1 && c1_2 == c2_2) {
                    return true;
                }
                if (c1_1 == c2_2 && c1_2 == c2_1) {
                    m_commutativity = true;
                    return true;
                }
                return false;
            }
        };

        typedef chashtable<enode*, cg_comm_hash, cg_comm_eq> comm_table;

        struct cg_hash {
            unsigned operator()(enode * n) const {
                unsigned a, b, c;
                a = b = 0x9e3779b9;
                c = 11;
                unsigned i = n->get_num_args();
                while (i >= 3) {
                    i--;
                    a += n->get_arg(i)->get_root_hash();
                    i--;
                    b += n->get_arg(i)->get_root_hash();
                    i--;
                    c += n->get_arg(i)->get_root_hash();
                    mix(a, b, c);
                }
                switch (i) {
                case 2:
                    b += n->get_arg(1)->get_root_hash();
                    Z3_fallthrough;
                case 1:
                    c += n->get_arg(0)->get_root_hash();
                }
                mix(a, b, c);
                return c;
            }
        };

        struct cg_eq {
            bool operator()(enode * n1, enode * n2) const {
                unsigned num = n1->get_num_args();
                if (num != n2->get_num_args())
                    return false;
                for (unsigned i = 0; i < num; ++i)
                    if (n1->get_arg(i)->get_root() != n2->get_arg(i)->get_root())
                        return false;
                return true;
            }
        };

        typedef chashtable<enode*, cg_hash, cg_eq> table;

        ast_manager &                 m_manager;
        bool                          m_commutativity; //!< true if the last found congruence used commutativity
        ptr_vector<void>              m_tables;
        obj_map<func_decl, unsigned>  m_func_decl2id;

        // Direct-mapped cache to accelerate set_func_decl_id lookups.
        // Avoids hash table probing for repeated func_decl → table_id queries.
        static constexpr unsigned     DCACHE_BITS = 8;
        static constexpr unsigned     DCACHE_SIZE = 1u << DCACHE_BITS;
        static constexpr unsigned     DCACHE_MASK = DCACHE_SIZE - 1;
        struct dcache_entry { func_decl * m_decl; unsigned m_tid; };
        dcache_entry                  m_dcache[DCACHE_SIZE];

        enum table_kind {
            UNARY,
            BINARY,
            BINARY_COMM,
            NARY
        };

        void * mk_table_for(func_decl * d);
        unsigned set_func_decl_id(enode * n);
        
        void * get_table(enode * n) {
            unsigned tid = n->get_func_decl_id();
            if (tid == UINT_MAX)
                tid = set_func_decl_id(n);
            SASSERT(tid < m_tables.size());
            return m_tables[tid];
        }

    public:
        cg_table(ast_manager & m);
        ~cg_table();

        /**
           \brief Try to insert n into the table. If the table already
           contains an element n' congruent to n, then do nothing and
           return n' and a boolean indicating whether n and n' are congruence
           modulo commutativity, otherwise insert n and return (n,false).
        */
        enode_bool_pair insert(enode * n);

        void erase(enode * n);

        bool contains(enode * n) const {
            SASSERT(n->get_num_args() > 0);
            void * t = const_cast<cg_table*>(this)->get_table(n); 
            switch (static_cast<table_kind>(GET_TAG(t))) {
            case UNARY:
                return UNTAG(unary_table*, t)->contains(n);
            case BINARY:
                return UNTAG(binary_table*, t)->contains(n);
            case BINARY_COMM:
                return UNTAG(comm_table*, t)->contains(n);
            default:
                return UNTAG(table*, t)->contains(n);
            }
        }

        enode * find(enode * n) const {
            SASSERT(n->get_num_args() > 0);
            enode * r = nullptr;
            void * t = const_cast<cg_table*>(this)->get_table(n); 
            switch (static_cast<table_kind>(GET_TAG(t))) {
            case UNARY:
                return UNTAG(unary_table*, t)->find(n, r) ? r : nullptr;
            case BINARY:
                return UNTAG(binary_table*, t)->find(n, r) ? r : nullptr;
            case BINARY_COMM:
                return UNTAG(comm_table*, t)->find(n, r) ? r : nullptr;
            default:
                return UNTAG(table*, t)->find(n, r) ? r : nullptr;
            }
        }

        bool contains_ptr(enode * n) const {
            enode * r;
            SASSERT(n->get_num_args() > 0);
            void * t = const_cast<cg_table*>(this)->get_table(n); 
            switch (static_cast<table_kind>(GET_TAG(t))) {
            case UNARY:
                return UNTAG(unary_table*, t)->find(n, r) && n == r;
            case BINARY:
                return UNTAG(binary_table*, t)->find(n, r) && n == r;
            case BINARY_COMM:
                return UNTAG(comm_table*, t)->find(n, r) && n == r;
            default:
                return UNTAG(table*, t)->find(n, r) && n == r;
            }
        }

        void reset();

        void display(std::ostream & out) const;

        void display_binary(std::ostream& out, void* t) const;

        void display_binary_comm(std::ostream& out, void* t) const;

        void display_unary(std::ostream& out, void* t) const;

        void display_nary(std::ostream& out, void* t) const;

        void display_compact(std::ostream & out) const;

        bool check_invariant() const;
    };

};


