/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_congruence.h

Abstract:

    SAT-level congruence closure for propositional gate detection and
    equivalence discovery. Implements the algorithm from SAT 2024
    (CaDiCaL 3.0) adapted to Z3's SAT solver infrastructure.

    The algorithm:
    1. Extracts AND, XOR, ITE gates from the clause database
    2. Stores gates in a hash table keyed by (gate_type, sorted_rhs)
    3. When two gates share the same type and RHS, their LHS literals
       are equivalent (congruence)
    4. Uses dual union-find (lazy + eager) to track equivalences
    5. Eagerly rewrites all gates with discovered equivalences,
       triggering cascading merges until fixpoint
    6. Forward-subsumes clauses using the discovered equivalences

Author:

    Grigory (2024)

Notes:

    Reference: CaDiCaL 3.0 congruence.hpp / congruence.cpp

--*/
#pragma once

#include "sat/sat_types.h"
#include "sat/sat_clause.h"
#include "sat/sat_watched.h"
#include "util/trace.h"
#include "util/vector.h"

#include <unordered_set>
#include <array>
#include <queue>

namespace sat {

    class solver;

    // ---------------------------------------------------------------
    // Gate type enumeration
    // ---------------------------------------------------------------
    enum class gate_type : uint8_t {
        AND_GATE,
        XOR_GATE,
        ITE_GATE
    };

    // ---------------------------------------------------------------
    // Gate structure: lhs = f(rhs[0], rhs[1], ...)
    //
    // For AND: lhs = AND(rhs[0], rhs[1], ...)
    //   Encoded as: long clause (lhs, ~rhs[0], ~rhs[1], ...)
    //               plus binary clauses (~lhs, rhs[i]) for each i
    //
    // For XOR: lhs = XOR(rhs[0], rhs[1], ...)
    //   Encoded as 2^(arity-1) clauses with all sign combinations
    //
    // For ITE: lhs = ITE(rhs[0], rhs[1], rhs[2])
    //   rhs[0] = condition, rhs[1] = then, rhs[2] = else
    // ---------------------------------------------------------------
    struct gate {
        literal          m_lhs;
        gate_type        m_type;
        bool             m_garbage  = false;
        bool             m_indexed  = false;
        bool             m_shrunken = false;
        literal_vector   m_rhs;

        unsigned arity() const { return m_rhs.size(); }
    };

    // ---------------------------------------------------------------
    // Gate occurrence list: gates containing a particular literal
    // ---------------------------------------------------------------
    typedef ptr_vector<gate> gate_occ_list;

    // ---------------------------------------------------------------
    // Gate hash and equality for the hash table
    // ---------------------------------------------------------------
    struct gate_hash {
        std::array<uint64_t, 16> const& m_nonces;
        gate_hash(std::array<uint64_t, 16> const& n) : m_nonces(n) {}

        size_t operator()(gate const* g) const {
            uint64_t h = (static_cast<uint64_t>(g->m_type) << 4) |
                         (static_cast<uint64_t>(g->m_type) >> 50);
            auto n_it = m_nonces.begin() + static_cast<unsigned>(g->m_type);
            for (literal l : g->m_rhs) {
                h += l.to_uint();
                h *= *n_it++;
                h = (h << 4) | (h >> 60);
                if (n_it == m_nonces.end()) n_it = m_nonces.begin();
            }
            h ^= h >> 32;
            return static_cast<size_t>(h);
        }
    };

    struct gate_eq {
        bool operator()(gate const* a, gate const* b) const {
            return a->m_type == b->m_type && a->m_rhs == b->m_rhs;
        }
    };

    // ---------------------------------------------------------------
    // Congruence closure engine
    //
    // Operates on a solver's clause database at decision level 0.
    // Discovers equivalences between literals via gate matching and
    // propagates them to fixpoint.
    //
    // Usage:
    //   congruence cc(s);
    //   cc.run();
    //   // Results available via cc.get_units(), cc.get_equivs(), etc.
    // ---------------------------------------------------------------
    class congruence {
    public:
        congruence(solver& s);
        ~congruence();

        // Main entry point. Returns true if any equivalences or units
        // were discovered.
        bool run();

        // Results for the caller (sat_simplifier).
        unsigned num_units()  const { return m_num_units; }
        unsigned num_equivs() const { return m_num_equivs; }
        unsigned num_subsumed() const { return m_num_subsumed; }
        unsigned num_gates() const { return m_num_gates; }

    private:
        solver& m_solver;

        // Hash table of extracted gates, keyed by (type, sorted_rhs).
        typedef std::unordered_set<gate*, gate_hash, gate_eq> gate_table;
        std::array<uint64_t, 16> m_nonces;
        gate_table               m_gate_table;

        // Dummy gate used for hash table lookups without allocation.
        gate m_search_gate;

        // Gate occurrence lists: indexed by literal index.
        // goccs(lit) = list of gates containing lit in their RHS.
        vector<gate_occ_list>    m_goccs;

        // Collected garbage gates to free at cleanup.
        ptr_vector<gate>         m_garbage_gates;

        // --- Dual union-find ---
        // Lazy: records ALL discovered equivalences.
        // representant[lit.index()] -> representative literal index.
        svector<unsigned>        m_repr;
        // Eager: only contains equivalences that have been fully propagated.
        svector<unsigned>        m_eager_repr;

        // --- Propagation schedule ---
        // Literals whose equivalence has been discovered but not yet
        // propagated (gates not yet rewritten).
        std::queue<literal>      m_schedule;
        bool_vector              m_scheduled;  // indexed by bool_var

        // --- Marking structure (for AND gate extraction) ---
        // Per-literal marks (indexed by literal index).
        svector<int8_t>          m_marks;

        // Literals that have been marked (for bulk cleanup).
        literal_vector           m_marked_lits;

        // --- Binary clause lookup (sorted for O(log n) search) ---
        struct compact_binary {
            literal m_lit1, m_lit2;
            compact_binary() {}
            compact_binary(literal l1, literal l2) : m_lit1(l1), m_lit2(l2) {}
        };
        svector<compact_binary>  m_binaries;
        // Offset table for binary lookup: indexed by literal index.
        // [offset, end) in m_binaries for binaries with that literal as first.
        struct bin_offset {
            unsigned m_start = 0;
            unsigned m_end = 0;
            bin_offset() {}
            bin_offset(unsigned s, unsigned e) : m_start(s), m_end(e) {}
        };
        svector<bin_offset>      m_bin_offsets;

        // --- Temporary buffers ---
        literal_vector           m_lits;   // clause literals during extraction
        literal_vector           m_rhs;    // RHS of gate being built
        literal_vector           m_clause_buf; // for subsumption

        // --- Statistics ---
        unsigned m_num_units    = 0;
        unsigned m_num_equivs   = 0;
        unsigned m_num_subsumed = 0;
        unsigned m_num_gates    = 0;
        unsigned m_num_and      = 0;
        unsigned m_num_xor      = 0;
        unsigned m_num_ite      = 0;
        unsigned m_num_rewrites = 0;

        // --- Phase methods ---
        void init_closure();
        void reset_closure();

        // Binary extraction and ternary strengthening.
        void extract_binaries();
        bool find_binary(literal a, literal b) const;

        // Gate extraction.
        void extract_gates();
        void extract_and_gates();
        void extract_and_gate_from_clause(clause& c);
        gate* try_and_gate(clause& c, literal lhs);
        void extract_xor_gates();
        void extract_xor_gate_from_clause(clause& c);
        void extract_ite_gates();
        void extract_ite_gates_for_var(bool_var v);
        void extract_ite_gates_for_lit(literal cond);

        // Gate creation and table management.
        gate* new_and_gate(literal lhs, literal_vector& rhs_lits);
        gate* new_xor_gate(literal lhs, literal_vector& rhs_lits);
        gate* new_ite_gate(literal lhs, literal cond, literal th, literal el);
        gate* find_gate_in_table(gate_type type, literal_vector& rhs_sorted);
        void  index_gate(gate* g);
        bool  remove_gate_from_table(gate* g);
        void  connect_goccs(gate* g, literal lit);
        void  mark_gate_garbage(gate* g);
        gate_occ_list& goccs(literal l);

        // Union-find operations.
        literal find_repr(literal l);
        literal find_repr_compress(literal l);
        literal find_eager_repr(literal l);
        void    set_repr(literal l, literal repr);
        void    set_eager_repr(literal l, literal repr);
        bool    are_equal(literal a, literal b);

        // Merge and propagation.
        bool merge_literals(literal a, literal b);
        void schedule_literal(literal l);
        bool propagate_units();
        bool propagate_equivalence(literal l);
        size_t propagate_units_and_equivalences();
        bool simplify_gates_for_lit(literal l);
        bool simplify_gate(gate* g);
        void simplify_and_gate(gate* g);
        void simplify_xor_gate(gate* g);

        // Gate rewriting.
        bool rewrite_gates(literal dst, literal src);
        bool rewrite_gate(gate* g, literal dst, literal src);
        void rewrite_and_gate(gate* g, literal dst, literal src);
        void rewrite_xor_gate(gate* g, literal dst, literal src);
        void rewrite_ite_gate(gate* g, literal dst, literal src);

        // Unit/equivalence discovery from binary implications.
        void find_units();
        void find_equivalences();

        // Forward subsumption with equivalence normalization.
        void forward_subsume_matching_clauses();
        bool find_subsuming_clause(clause& c);

        // Marking helpers.
        int8_t& marked(literal l);
        void    set_mark(literal l, int8_t val);
        void    unmark_all();

        // Literal sorting by variable index (for canonical RHS ordering).
        void sort_lits_by_var(literal_vector& lits);

        // Solver access helpers.
        lbool    value(literal l) const;
        lbool    value(bool_var v) const;
        unsigned num_vars() const;
        bool     is_eliminated(bool_var v) const;

        // XOR helpers.
        unsigned parity_lits(literal_vector const& lits) const;
        void     inc_lits(literal_vector& lits);
        clause*  find_large_xor_side_clause(literal_vector& lits);

        // Occurrence counting for XOR pre-filter.
        svector<unsigned> m_large_occ_count; // indexed by literal index
        void init_large_occ_counts();
        unsigned large_occ_count(literal l) const;
    };

}
