/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    smt_landscape.h

Abstract:

    Landscape map — a sparse, integrated data structure that records what the
    solver has explored and what it found.  Gives the solver "spatial awareness"
    of the problem space.

    Four layers:
      1. Literal stress    — per-literal EMA of conflict participation (uint8_t)
      2. Variable coverage — per-bool_var decision counts (true/false, uint16_t)
      3. Region fingerprints — bounded hash map of phase-vector hashes + health
      4. Conflict variable pairs — Bloom filter of co-occurring variable pairs

    This is PURELY OBSERVATIONAL in v1: it collects data but does not influence
    solver decisions.  Integration with the explorer comes later.

    Memory budget: <1MB for a 50K-var / 200K-clause problem.

Author:

    Z3 contributors

--*/
#pragma once

#include "util/vector.h"
#include "util/hash.h"
#include <cstdint>
#include <cinttypes>
#include <cstring>
#include <ostream>
#include <cstdio>
#include <algorithm>
#include <cmath>

namespace smt {

class landscape_map {
public:
    landscape_map();

    // ---------------------------------------------------------------
    // Layer 1: Literal stress
    //   Indexed by literal::index().  EMA of conflict participation.
    //   Stored as uint8_t (0..255) for memory efficiency.
    // ---------------------------------------------------------------

    void ensure_literal(unsigned lit_idx);
    void on_conflict_antecedent(unsigned lit_idx);
    void decay_stress();
    uint8_t  get_stress(unsigned lit_idx) const;
    double   avg_stress() const;
    double   stress_concentration() const;  // Gini coefficient

    // ---------------------------------------------------------------
    // Layer 2: Variable coverage
    //   Per bool_var: how many times decided TRUE / FALSE.
    // ---------------------------------------------------------------

    void ensure_var(unsigned var);
    void on_decision(unsigned var, bool is_true);
    uint16_t get_decisions_true(unsigned var) const;
    uint16_t get_decisions_false(unsigned var) const;
    double   coverage_fraction() const;
    unsigned most_unexplored_var(unsigned num_vars) const;

    // ---------------------------------------------------------------
    // Layer 3: Region fingerprints
    //   Bounded open-addressing hash map (1024 entries, LRU eviction).
    //   Key = hash of the phase/polarity vector, Value = visit stats.
    // ---------------------------------------------------------------

    void     on_restart(uint64_t phase_hash, float health);
    unsigned region_visit_count(uint64_t phase_hash) const;
    float    region_best_health(uint64_t phase_hash) const;
    unsigned num_unique_regions() const { return m_unique_regions; }
    double   region_diversity() const;

    // ---------------------------------------------------------------
    // Layer 4: Conflict variable pairs (Bloom filter)
    //   Records which PAIRS of bool_vars co-occur in learned clauses.
    //   64KB Bloom filter (512K bits), 3 hash functions.
    // ---------------------------------------------------------------

    void   on_learned_clause(unsigned num_vars, unsigned const* vars);
    double conflict_affinity(unsigned var, unsigned const* assigned_vars, unsigned num_assigned) const;

    // ---------------------------------------------------------------
    // Aggregate snapshot
    // ---------------------------------------------------------------

    struct health_snapshot {
        double   avg_stress;
        double   stress_concentration;
        double   coverage;
        unsigned unique_regions;
        double   region_diversity;
        unsigned total_conflicts;
        unsigned total_decisions;
    };

    health_snapshot snapshot(unsigned num_vars) const;

    // ---------------------------------------------------------------
    // Debug / trace
    // ---------------------------------------------------------------

    void dump_to_stream(std::ostream& out, unsigned num_vars) const;
    void dump_to_alog(FILE* alog, unsigned num_conflicts, unsigned num_vars) const;

    // ---------------------------------------------------------------
    // Lifecycle
    // ---------------------------------------------------------------

    void init_search();  // reset per-search counters (map persists!)
    void reset();        // full reset

    unsigned total_conflicts() const { return m_total_conflicts; }
    unsigned total_decisions() const { return m_total_decisions; }

private:
    // -- Layer 1 --
    svector<uint8_t>  m_lit_stress;
    unsigned          m_conflicts_since_decay = 0;
    unsigned          m_total_conflicts       = 0;

    // -- Layer 2 --
    svector<uint16_t> m_decisions_true;
    svector<uint16_t> m_decisions_false;
    unsigned          m_total_decisions       = 0;
    unsigned          m_vars_explored         = 0;  // cached count

    // -- Layer 3 --
    struct region_record {
        uint16_t visits;
        float    avg_health;
        float    best_health;
        uint32_t last_visit;
    };
    static constexpr unsigned REGION_MAP_SIZE = 1024;
    uint64_t      m_region_keys[REGION_MAP_SIZE];
    region_record m_region_vals[REGION_MAP_SIZE];
    bool          m_region_occupied[REGION_MAP_SIZE];
    unsigned      m_total_restarts  = 0;
    unsigned      m_unique_regions  = 0;

    // -- Layer 4 --
    static constexpr unsigned BLOOM_BITS  = 512 * 1024;  // 512K bits = 64KB
    static constexpr unsigned BLOOM_BYTES = BLOOM_BITS / 8;
    uint8_t m_conflict_pairs[BLOOM_BYTES];

    // Bloom filter helpers
    void bloom_set(unsigned v1, unsigned v2);
    bool bloom_test(unsigned v1, unsigned v2) const;
    static void bloom_hashes(unsigned v1, unsigned v2, unsigned& h0, unsigned& h1, unsigned& h2);

    // Region map helpers
    unsigned region_slot(uint64_t key) const;
    unsigned region_find(uint64_t key) const;          // returns slot or REGION_MAP_SIZE if not found
    unsigned region_insert_or_update(uint64_t key, float health);
};

} // namespace smt
