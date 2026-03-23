/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    smt_landscape.h

Abstract:

    Deep landscape map — a multi-tier data structure that records what the
    solver has explored and what it found.  Gives the solver "spatial awareness"
    of the problem space.

    Three tiers of data:

    TIER 0 (original, ~500KB):
      L1. Literal stress    — per-literal EMA of conflict participation (uint8_t)
      L2. Variable coverage — per-bool_var decision counts (uint16_t, kept for compat)
      L3. Region fingerprints — bounded hash map of phase-vector hashes + health
      L4. Conflict variable pairs — Bloom filter of co-occurring variable pairs

    TIER 1 (~12MB for 200K vars/clauses):
      T1a. Clause saving-literal profiles — which literal most often saves each clause
      T1b. Variable propagation fan-out profiles — decision impact per variable
      T1c. QI binding pattern success map — per-quantifier binding pattern tracking

    TIER 2 (~32MB):
      T2a. Variable conflict co-occurrence graph — top-16 partners per variable
      T2b. Conflict history buffer — ring buffer of last 200K conflicts
      T2c. Expanded region map — 100K slots with transition tracking

    This is PURELY OBSERVATIONAL: it collects data but does not influence
    solver decisions.  Integration with the explorer that USES this data
    comes in a separate step.

    Memory budget: ~60MB for a 200K-var / 200K-clause problem.
    Tier 1/2 structures are heap-allocated lazily on first use.

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

#ifdef __x86_64__
#include <x86intrin.h>
#endif

namespace smt {

// Lightweight cycle counter: ~1ns on x86, 0 (disabled) elsewhere.
inline uint64_t landscape_rdtsc() {
#ifdef __x86_64__
    return __rdtsc();
#else
    return 0;
#endif
}

class landscape_map {
public:
    landscape_map();
    ~landscape_map();

    // ===================================================================
    // TIER 0 — Original layers (unchanged public API)
    // ===================================================================

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
    // Layer 2: Variable coverage (legacy uint16 interface kept)
    // ---------------------------------------------------------------

    void ensure_var(unsigned var);
    void on_decision(unsigned var, bool is_true, unsigned scope_lvl,
                     unsigned trail_size);
    // Legacy overload for callers that don't pass scope/trail info
    void on_decision(unsigned var, bool is_true) {
        on_decision(var, is_true, 0, 0);
    }
    uint16_t get_decisions_true(unsigned var) const;
    uint16_t get_decisions_false(unsigned var) const;
    double   coverage_fraction() const;
    unsigned most_unexplored_var(unsigned num_vars) const;

    // ---------------------------------------------------------------
    // Layer 3: Region fingerprints (now uses expanded Tier 2 map)
    // ---------------------------------------------------------------

    void     on_restart(uint64_t phase_hash, float health);
    unsigned region_visit_count(uint64_t phase_hash) const;
    float    region_best_health(uint64_t phase_hash) const;
    unsigned num_unique_regions() const { return m_unique_regions; }
    double   region_diversity() const;

    // ---------------------------------------------------------------
    // Layer 4: Conflict variable pairs (Bloom filter)
    // ---------------------------------------------------------------

    void   on_learned_clause(unsigned num_vars, unsigned const* vars);
    double conflict_affinity(unsigned var, unsigned const* assigned_vars, unsigned num_assigned) const;

    // ===================================================================
    // TIER 1 — Clause Saving-Literal Profiles
    // ===================================================================

    struct clause_profile {
        uint32_t m_saving_literal;     // literal index that most often saves
        uint32_t m_last_stress;        // conflict number when last stressed
        uint16_t m_violation_count;    // times clause was stressed (all but 1 lit false)
        uint16_t m_propagation_count;  // times clause propagated via BCP
        uint16_t m_antecedent_count;   // times clause appeared as reason in conflict derivation
                                       // (bumped via clause_ptr reverse map during FUIP walk)
        uint8_t  m_saving_fraction;    // 0-255: how often saving_literal was sole survivor
        uint8_t  m_pad;
    };
    static_assert(sizeof(clause_profile) == 16, "clause_profile must be 16 bytes");

    void     ensure_clause_profiles(unsigned num_clauses);
    void     on_clause_propagation(unsigned clause_idx, unsigned saving_lit_idx);
    void     on_clause_antecedent(unsigned clause_idx);
    void     periodic_clause_scan(unsigned num_clauses,
                                  unsigned num_lits_fn(unsigned clause_idx, void* ctx),
                                  unsigned get_lit_value_fn(unsigned clause_idx, unsigned lit_pos, void* ctx),
                                  void* ctx);
    clause_profile const* get_clause_profile(unsigned clause_idx) const;
    unsigned get_saving_literal(unsigned clause_idx) const;

    // Clause pointer → index reverse map (for on_clause_antecedent wiring).
    // Callers register clause pointers during init_search, then look up
    // indices during conflict resolution.
    void     ensure_clause_ptr_map(unsigned num_clauses);
    void     register_clause_ptr(unsigned clause_idx, uintptr_t ptr);
    unsigned find_clause_idx(uintptr_t ptr) const;  // returns UINT32_MAX if not found

    // ===================================================================
    // TIER 1 — Variable Propagation Fan-Out Profiles
    // ===================================================================

    struct var_profile {
        uint32_t decisions_true;          // total decisions as true
        uint32_t decisions_false;         // total decisions as false
        uint32_t polarity_history;        // bitfield: last 32 restart polarities
        uint16_t avg_fanout_true;         // EMA: vars forced when decided true
        uint16_t avg_fanout_false;        // EMA: vars forced when decided false
        uint16_t max_fanout;              // max observed fanout
        uint16_t conflict_count;          // conflicts involving this variable
        uint16_t decision_conflict_count; // conflicts where var was DECISION
        uint8_t  avg_decision_depth;      // EMA of scope level when decided (0-255)
        uint8_t  clause_occurrence;       // number of input clauses containing var (capped 255)
    };
    static_assert(sizeof(var_profile) == 24, "var_profile must be 24 bytes");

    void     ensure_var_profiles(unsigned num_vars);
    var_profile const* get_var_profile(unsigned var) const;
    void     on_decision_fanout(unsigned var, unsigned fanout);
    void     on_var_in_conflict(unsigned var, bool was_decision);
    void     update_polarity_history(unsigned var, bool polarity);
    void     compute_clause_occurrences(unsigned num_vars, unsigned num_clauses,
                                        unsigned clause_num_lits_fn(unsigned, void*),
                                        unsigned clause_get_var_fn(unsigned, unsigned, void*),
                                        void* ctx);
    double   get_polarity_safety_score(unsigned var, bool is_true) const;
    double   get_impact_score(unsigned var) const;

    // ---------------------------------------------------------------
    // Saving-literal polarity safety: how many clauses prefer this
    // variable's TRUE vs FALSE literal as their saving literal.
    // Recomputed every periodic_clause_scan (1000 conflicts).
    // ---------------------------------------------------------------

    // Recompute polarity safety counters from clause profile saving literals.
    // Call this right after the periodic clause scan completes.
    void     compute_polarity_safety();

    // Returns: +1 if true is safer, -1 if false is safer, 0 if no strong signal.
    // The margin parameter controls the required difference (default 2).
    int      polarity_safety(unsigned var, unsigned margin = 2) const;

    // Returns the max of avg_fanout_true and avg_fanout_false for a variable.
    unsigned get_var_fanout(unsigned var) const;

    // Returns true if var profiles are allocated and populated.
    bool     has_var_profiles() const { return m_var_profiles != nullptr; }

    // Top-K high-fanout variable cache (rebuilt on each on_decision_fanout call).
    // Avoids iterating all variables on every restart.
    static constexpr unsigned TOP_FANOUT_K = 32;
    void     get_top_fanout_vars(unsigned const*& vars, unsigned& count) const {
        vars = m_top_fanout_vars;
        count = m_top_fanout_count;
    }

    // Fanout tracking state (called from context)
    void     save_trail_pos(unsigned trail_size) { m_last_decision_trail_pos = trail_size; }
    unsigned get_last_trail_pos() const { return m_last_decision_trail_pos; }
    void     set_last_decision_var(unsigned var) { m_last_decision_var = var; }
    unsigned get_last_decision_var() const { return m_last_decision_var; }
    void     set_last_decision_polarity(bool is_true) { m_last_decision_polarity = is_true; }
    bool     get_last_decision_polarity() const { return m_last_decision_polarity; }

    // ===================================================================
    // TIER 1 — QI Binding Pattern Success Map
    // ===================================================================

    struct binding_pattern_record {
        uint32_t pattern_hash;
        uint32_t total_instances;
        uint16_t useful_instances;
        uint16_t pad;
    };
    static_assert(sizeof(binding_pattern_record) == 12, "binding_pattern_record must be 12 bytes");

    static constexpr unsigned QI_PATTERN_SLOTS = 256;

    struct quantifier_pattern_map {
        binding_pattern_record slots[QI_PATTERN_SLOTS];
        unsigned num_entries;
    };

    void     ensure_qi_patterns(unsigned num_quantifiers);
    void     update_qi_pattern(unsigned quant_id, uint32_t pattern_hash, bool useful);
    float    get_qi_pattern_success(unsigned quant_id, uint32_t pattern_hash) const;

    // ===================================================================
    // TIER 2 — Variable Conflict Co-occurrence Graph
    // ===================================================================

    struct var_conflict_graph_entry {
        uint32_t partner_ids[16];
        uint16_t partner_counts[16];
        uint16_t total_degree;
        uint16_t pad;
    };
    static_assert(sizeof(var_conflict_graph_entry) == 100, "var_conflict_graph_entry must be 100 bytes");

    void     ensure_conflict_graph(unsigned num_vars);
    void     on_conflict_cooccurrence(unsigned num_vars, unsigned const* vars);
    var_conflict_graph_entry const* get_conflict_graph_entry(unsigned var) const;

    // ===================================================================
    // TIER 2 — Conflict History Buffer
    // ===================================================================

    struct conflict_record {
        uint64_t learned_clause_hash;
        uint32_t top_vars[5];
        uint32_t timestamp;
        uint16_t glue;
        uint16_t backjump_distance;
        uint16_t trail_size_lo;      // low 16 bits of trail size
        uint8_t  theory_flags;
        uint8_t  clause_size;        // capped 255
    };
    static_assert(sizeof(conflict_record) == 40, "conflict_record must be 40 bytes");

    static constexpr unsigned CONFLICT_HISTORY_SIZE = 200000;

    void     on_conflict_full(uint64_t clause_hash, unsigned const* top_vars,
                              unsigned num_top_vars, unsigned glue,
                              unsigned backjump, unsigned trail_size,
                              uint8_t theory_flags, unsigned clause_size);
    conflict_record const* get_conflict_record(unsigned idx) const;
    unsigned conflict_history_count() const;
    double   conflict_recurrence_rate(unsigned window) const;

    // ===================================================================
    // TIER 2 — Expanded Region Map
    // ===================================================================

    // The expanded region map replaces the original 1024-slot map.
    // 100K slots with transition tracking.
    struct expanded_region_record {
        uint64_t hash;
        float    avg_health;
        float    best_health;
        uint32_t visit_count;
        uint32_t last_visit;
        uint64_t prev_region_hash;
        float    entry_health;
        float    exit_health;
    };
    static_assert(sizeof(expanded_region_record) == 40,
                  "expanded_region_record must be 40 bytes");

    static constexpr unsigned EXPANDED_REGION_MAP_SIZE = 100000;

    // ===================================================================
    // TIER 3 — Solver Dynamics (20 lightweight datapoints)
    //
    // Cheap-to-collect signals about solver behavior:
    //   1-5:   Phase time breakdown (rdtsc-based cycle counters)
    //   6:     BCP propagation chain length (EMA)
    //   7:     Decision reversal rate
    //   8:     Assignment density at conflict (EMA)
    //   9:     Decision level at conflict (EMA)
    //   10:    Learned clause size trend (EMA)
    //   11:    LBD/glue trend (EMA)
    //   12:    Clause early-use rate (EMA, proxy: used-at-GC fraction)
    //   13:    GC survival rate
    //   14:    Backjump distance fraction (EMA)
    //   15:    Restart interval length (EMA)
    //   16:    Effective branching factor (EMA)
    //   17:    Theory conflict fraction (EMA)
    //   18:    Theory propagation density (EMA)
    //   19:    Binary clause ratio
    //   20:    Conflict temporal clustering / burstiness (EMA)
    //
    // Total memory: ~160 bytes.  Per-event overhead: < 50ns.
    // ===================================================================

    struct solver_dynamics {
        // Phase time breakdown (rdtsc cycles)
        uint64_t cycles_bcp;
        uint64_t cycles_decide;
        uint64_t cycles_conflict;
        uint64_t cycles_theory;
        uint64_t cycles_qi;
        uint64_t cycles_total;
        uint64_t phase_start_tsc;

        // BCP quality
        float    avg_prop_chain_length;  // EMA: propagated_lits between decisions

        // Decision quality
        uint32_t total_reversals;
        uint32_t reversal_window;
        float    avg_conflict_density;   // EMA: assigned/total at conflict
        float    avg_conflict_level;     // EMA: scope_lvl at conflict

        // Learning quality
        float    avg_learned_size;       // EMA: literals in learned clauses
        float    avg_glue;               // EMA: LBD of learned clauses
        float    clause_early_use_rate;  // EMA: fraction used at GC time
        float    gc_survival_rate;       // last GC: survived / candidates

        // Search structure
        float    avg_backjump_frac;      // EMA: backjump_dist / conflict_level
        float    avg_restart_interval;   // EMA: conflicts between restarts
        float    avg_branching_factor;   // EMA: trail_size / scope_level at conflict

        // Theory engagement
        float    theory_conflict_frac;   // EMA: theory / total conflicts
        float    theory_prop_density;    // EMA: theory_props / bcp_props per round

        // Problem structure
        float    binary_clause_ratio;    // binary / total clauses
        float    conflict_burstiness;    // normalized variance of inter-conflict gap
        float    ema_gap;                // EMA of decisions between conflicts
        float    ema_gap_sq;             // EMA of gap^2 (for variance)
        uint32_t last_conflict_decisions; // decisions at last conflict

        // Scratch counters for per-round aggregation
        uint32_t props_this_round;       // BCP propagations in current round
        uint32_t theory_props_this_round; // theory propagations in current round
        uint32_t binary_clauses;         // count of binary clauses
        uint32_t total_clauses;          // total clauses

        // ---------------------------------------------------------------
        // Efficiency signals (E1-E4)
        // Measure HOW WELL the solver works, not just WHAT it does.
        // ---------------------------------------------------------------
        float    wasted_work_rate;       // E1: EMA of (conflict_lvl - backjump_lvl)
        float    learned_clause_velocity;// E2: fraction of conflict antecedents that are learned
        float    prop_phase_alignment;   // E3: fraction of propagations matching phase cache
        float    conflict_novelty;       // E4: Jaccard novelty between consecutive conflict sigs
        uint64_t prev_conflict_sig;      // E4: 64-bit variable signature of previous conflict
        unsigned velocity_learned_num;   // E2: learned antecedents in current interval
        unsigned velocity_total_num;     // E2: total antecedents in current interval
        unsigned alignment_match_count;  // E3: sampled propagations matching phase cache
        unsigned alignment_total_count;  // E3: total sampled propagations

        // ---------------------------------------------------------------
        // Causal response signals (for SPSA gradient estimation)
        // Group A: Direct causal pairs with tunable parameters
        // ---------------------------------------------------------------
        float    qi_instance_rate;       // A1: QI instances per 1000 decisions
        float    actual_restart_interval;// A2: EMA of conflicts between restarts (fast alpha=0.2)
        float    phase_flip_rate;        // A3: fraction of decisions where polarity != phase cache
        float    activity_concentration; // A4: Gini of VSIDS activity distribution

        // Group B: Replacement signals (fix phantom/broken metrics)
        float    fp_hit_rate;            // B1: fingerprint dedup hit rate EMA
        float    new_variable_rate;      // B2: first-time decisions / total decisions per interval
        uint32_t high_stress_count;      // B3: count of literals with stress > 128
        float    stress_gini_trend;      // B4: rate of change of stress Gini

        // Group C: Theory and model signals
        float    trail_stability;        // C1: assignment survival rate across restarts
        float    theory_lemma_rate;      // C2: theory lemmas per 1000 decisions
        float    qi_egraph_growth;       // C3: EMA of enodes created per QI instance
        float    agility;                // C4: Z3 agility metric (polarity flip EMA)

        // Helper delta counters (reset at each LANDSCAPE dump / restart)
        uint32_t prev_qi_inserts;        // A1: qi_velocity_inserts snapshot
        uint32_t prev_decisions;         // A1/B2/C2: decisions snapshot
        uint32_t prev_fp_hits;           // B1: fp_hit_total snapshot
        uint32_t prev_fp_misses;         // B1: fp_miss_total snapshot
        uint32_t prev_theory_lemmas;     // C2: theory lemma count snapshot
        float    prev_stress_gini;       // B4: stress Gini at last dump
        uint32_t phase_flip_count;       // A3: phase flips this interval (reset each dump)
        uint32_t decisions_this_interval;// A3: decisions this interval (reset each dump)
        uint32_t first_time_decisions;   // B2: first-time var decisions this interval
        uint32_t theory_lemma_count;     // C2: running theory lemma counter

        void reset() { memset(this, 0, sizeof(*this)); }
    };
    static_assert(sizeof(solver_dynamics) <= 448, "solver_dynamics should be compact");

    // Dynamics public accessors
    solver_dynamics const& dynamics() const { return m_dynamics; }
    solver_dynamics&       dynamics()       { return m_dynamics; }
    svector<uint8_t>&      last_decided_polarity() { return m_last_decided_polarity; }

    // Phase timing helpers (call from context at phase boundaries)
    void     dynamics_phase_begin();
    void     dynamics_phase_end_bcp();
    void     dynamics_phase_end_theory();
    void     dynamics_phase_end_qi();
    void     dynamics_phase_end_decide();
    void     dynamics_phase_end_conflict();

    // Event hooks (call from context at specific events)
    void     dynamics_on_decision(unsigned trail_size);
    void     dynamics_on_conflict(unsigned scope_lvl, unsigned trail_size,
                                  unsigned num_vars_total, unsigned num_lits,
                                  unsigned glue, unsigned conflict_lvl,
                                  unsigned backjump_lvl, bool theory_conflict);
    void     dynamics_on_theory_prop();
    void     dynamics_on_bcp_prop();
    void     dynamics_on_gc(unsigned survived, unsigned candidates, unsigned used);
    void     dynamics_on_restart(unsigned conflicts_since_restart);
    void     dynamics_on_reversal();
    void     dynamics_update_binary_ratio(unsigned binary, unsigned total);

    // Causal signal hooks (SPSA gradient estimation)
    // A3: phase flip detection — call on each decision with actual vs cached polarity
    void     dynamics_on_phase_flip(bool flipped);
    // A4: activity Gini — compute from activity array at restart time
    void     dynamics_compute_activity_gini(double const* activity, unsigned num_vars);
    // B1: fingerprint hit rate — call at LANDSCAPE dump with current fp counters
    void     dynamics_update_fp_hit_rate(unsigned fp_hits, unsigned fp_misses);
    // B2: new variable detection — call on decision if variable is first-time
    void     dynamics_on_first_decision();
    // B3: high stress count — incremental maintenance
    void     dynamics_stress_crossed_up();   // stress crossed 128 from below
    void     dynamics_stress_crossed_down(); // stress crossed 128 from above
    // C1: trail stability — call at restart with # vars that kept polarity
    void     dynamics_update_trail_stability(float stability);
    // C2: theory lemma counter — call on each theory lemma creation
    void     dynamics_on_theory_lemma();
    // Batch update for rate signals at LANDSCAPE dump time
    void     dynamics_update_rates(unsigned qi_inserts, unsigned decisions,
                                   unsigned theory_lemmas, double stress_gini);
    // C3: qi egraph growth — call with existing egraph_metrics growth_rate_ema
    void     dynamics_update_qi_egraph_growth(float growth_rate_ema);
    // C4: agility — snapshot from solver
    void     dynamics_update_agility(float agility);

    // Efficiency signals (E1-E4): measure solver productivity
    // E1: wasted work — decisions undone per conflict (call after backjump level known)
    void     dynamics_on_wasted_work(unsigned conflict_level, unsigned backjump_level);
    // E2: learned clause velocity — call for each antecedent clause during FUIP walk
    void     dynamics_on_antecedent_clause(bool is_learned);
    // E3: propagation-phase alignment — call on sampled propagations
    void     dynamics_on_prop_alignment(bool matched);
    // E4: conflict clause novelty — call with learned clause literals after conflict
    void     dynamics_on_conflict_novelty(unsigned num_lits, unsigned const* lit_vars);

    // ===================================================================
    // Aggregate snapshot (extended)
    // ===================================================================

    struct health_snapshot {
        double   avg_stress;
        double   stress_concentration;
        double   coverage;
        unsigned unique_regions;
        double   region_diversity;
        unsigned total_conflicts;
        unsigned total_decisions;
        // New fields
        unsigned max_fanout_var;
        double   avg_fanout;
        double   conflict_recurrence;
    };

    health_snapshot snapshot(unsigned num_vars) const;

    // ===================================================================
    // Debug / trace
    // ===================================================================

    void dump_to_stream(std::ostream& out, unsigned num_vars) const;
    void dump_to_alog(FILE* alog, unsigned num_conflicts, unsigned num_vars) const;

    // ===================================================================
    // Lifecycle
    // ===================================================================

    void init_search();  // reset per-search counters (map persists!)
    void reset();        // full reset

    unsigned total_conflicts() const { return m_total_conflicts; }
    unsigned total_decisions() const { return m_total_decisions; }

private:
    // -- Tier 0 Layer 1: Literal stress --
    svector<uint8_t>  m_lit_stress;
    unsigned          m_conflicts_since_decay = 0;
    unsigned          m_total_conflicts       = 0;

    // -- Tier 0 Layer 2: Variable coverage (legacy) --
    svector<uint16_t> m_decisions_true;
    svector<uint16_t> m_decisions_false;
    unsigned          m_total_decisions       = 0;
    unsigned          m_vars_explored         = 0;

    // -- Tier 0 Layer 3: Region fingerprints --
    //    Now backed by expanded region map (Tier 2c).
    //    We keep the old inline arrays for backward compat during transition.
    //    The expanded map is allocated lazily.
    static constexpr unsigned REGION_MAP_SIZE = 1024;
    uint64_t      m_region_keys[REGION_MAP_SIZE];
    struct old_region_record {
        uint16_t visits;
        float    avg_health;
        float    best_health;
        uint32_t last_visit;
    };
    old_region_record m_region_vals[REGION_MAP_SIZE];
    bool          m_region_occupied[REGION_MAP_SIZE];
    unsigned      m_total_restarts  = 0;
    unsigned      m_unique_regions  = 0;

    // -- Tier 0 Layer 4: Bloom filter --
    static constexpr unsigned BLOOM_BITS  = 512 * 1024;
    static constexpr unsigned BLOOM_BYTES = BLOOM_BITS / 8;
    uint8_t m_conflict_pairs[BLOOM_BYTES];

    // Bloom filter helpers
    void bloom_set(unsigned v1, unsigned v2);
    bool bloom_test(unsigned v1, unsigned v2) const;
    static void bloom_hashes(unsigned v1, unsigned v2, unsigned& h0, unsigned& h1, unsigned& h2);

    // Region map helpers (legacy 1024-slot)
    unsigned region_slot(uint64_t key) const;
    unsigned region_find(uint64_t key) const;
    unsigned region_insert_or_update(uint64_t key, float health);

    // -- Tier 1a: Clause profiles (lazy) --
    clause_profile*   m_clause_profiles     = nullptr;
    unsigned          m_clause_profiles_cap = 0;

    // Clause pointer → index reverse map (open-addressing hash table).
    // Stores (ptr, idx) pairs for O(1) lookup during conflict resolution.
    struct clause_ptr_entry {
        uintptr_t ptr;   // 0 = empty slot
        unsigned  idx;
    };
    clause_ptr_entry* m_clause_ptr_map     = nullptr;
    unsigned          m_clause_ptr_map_cap = 0;  // always a power of 2

    // -- Tier 1b: Variable profiles (lazy) --
    var_profile*      m_var_profiles        = nullptr;
    unsigned          m_var_profiles_cap    = 0;

    // Fanout tracking state
    unsigned          m_last_decision_trail_pos = 0;
    unsigned          m_last_decision_var       = UINT32_MAX;
    bool              m_last_decision_polarity  = false;

    // -- Top-K fanout cache (rebuilt on each on_decision_fanout call) --
    unsigned          m_top_fanout_vars[TOP_FANOUT_K] = {};
    unsigned          m_top_fanout_count = 0;

    // -- Polarity safety counters (recomputed each periodic clause scan) --
    svector<uint16_t> m_safety_true;   // per-var: clauses where TRUE literal is saver
    svector<uint16_t> m_safety_false;  // per-var: clauses where FALSE literal is saver

    // -- Tier 1c: QI pattern maps (lazy) --
    quantifier_pattern_map* m_qi_patterns     = nullptr;
    unsigned                m_qi_patterns_cap = 0;

    // -- Tier 2a: Conflict co-occurrence graph (lazy) --
    var_conflict_graph_entry* m_conflict_graph     = nullptr;
    unsigned                  m_conflict_graph_cap = 0;

    // -- Tier 2b: Conflict history buffer (lazy) --
    conflict_record*  m_conflict_history     = nullptr;
    unsigned          m_conflict_history_pos = 0;
    unsigned          m_conflict_history_count = 0;

    // -- Tier 2c: Expanded region map (lazy) --
    expanded_region_record* m_expanded_regions      = nullptr;
    uint64_t*               m_expanded_region_keys  = nullptr;
    bool*                   m_expanded_region_occ   = nullptr;
    unsigned                m_expanded_unique        = 0;
    uint64_t                m_prev_region_hash       = 0;
    float                   m_prev_region_health     = 0.0f;

    // Expanded region map helpers
    void     ensure_expanded_regions();
    unsigned expanded_region_slot(uint64_t key) const;
    unsigned expanded_region_find(uint64_t key) const;
    unsigned expanded_region_insert_or_update(uint64_t key, float health);

    // Tier 1a helpers
    void ensure_clause_profiles_internal(unsigned cap);
    // Tier 1b helpers
    void ensure_var_profiles_internal(unsigned cap);
    // Tier 1c helpers
    void ensure_qi_patterns_internal(unsigned cap);
    // Tier 2a helpers
    void ensure_conflict_graph_internal(unsigned cap);
    // Tier 2b helpers
    void ensure_conflict_history();

    // -- Tier 3: Solver dynamics --
    solver_dynamics     m_dynamics;
    // Per-variable last-decided-polarity for reversal detection.
    // Lazily allocated (1 byte per var, could be bits but vars are few).
    svector<uint8_t>    m_last_decided_polarity;  // 0=unset, 1=false, 2=true
    // Scratch: trail size at start of current decision for prop chain length
    unsigned            m_decision_trail_start = 0;
};

} // namespace smt
