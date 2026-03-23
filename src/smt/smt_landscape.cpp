/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    smt_landscape.cpp

Abstract:

    Deep landscape map implementation.  See smt_landscape.h for design overview.

    Three tiers:
      Tier 0: literal stress, variable coverage, region fingerprints, Bloom filter
      Tier 1: clause profiles, variable profiles, QI pattern maps
      Tier 2: conflict co-occurrence graph, conflict history, expanded regions

    All Tier 1/2 structures are heap-allocated lazily on first use.

Author:

    Z3 contributors

--*/

#include "smt/smt_landscape.h"
#include "smt/adaptive_log.h"

namespace smt {

// -----------------------------------------------------------------------
// Construction / lifecycle
// -----------------------------------------------------------------------

landscape_map::landscape_map() {
    memset(m_region_keys, 0, sizeof(m_region_keys));
    memset(m_region_vals, 0, sizeof(m_region_vals));
    memset(m_region_occupied, 0, sizeof(m_region_occupied));
    memset(m_conflict_pairs, 0, sizeof(m_conflict_pairs));
}

landscape_map::~landscape_map() {
    delete[] m_clause_profiles;
    delete[] m_clause_ptr_map;
    delete[] m_var_profiles;
    delete[] m_qi_patterns;
    delete[] m_conflict_graph;
    delete[] m_conflict_history;
    delete[] m_expanded_regions;
    delete[] m_expanded_region_keys;
    delete[] m_expanded_region_occ;
}

void landscape_map::init_search() {
    // Per-search counters reset.  The map itself persists across searches
    // so that cross-search spatial awareness is maintained.
    m_total_conflicts       = 0;
    m_total_decisions       = 0;
    m_conflicts_since_decay = 0;
    m_total_restarts        = 0;
    // Fanout tracking
    m_last_decision_trail_pos = 0;
    m_last_decision_var       = UINT32_MAX;
    m_last_decision_polarity  = false;
    // Reset top-K fanout cache
    m_top_fanout_count = 0;
    memset(m_top_fanout_vars, 0, sizeof(m_top_fanout_vars));
    // Conflict history position resets (ring buffer wraps, data persists)
    m_conflict_history_pos   = 0;
    m_conflict_history_count = 0;
    // Region transition state
    m_prev_region_hash   = 0;
    m_prev_region_health = 0.0f;
    // NOTE: Tier 0 stress/coverage/regions/bloom, Tier 1/2 data all persist
    // across check-sat calls for cross-search spatial awareness.

    // Polarity safety counters — reset per search
    m_safety_true.reset();
    m_safety_false.reset();

    // Tier 3: Solver dynamics — reset per search
    m_dynamics.reset();
    m_last_decided_polarity.reset();
    m_decision_trail_start = 0;
}

void landscape_map::reset() {
    // Tier 0
    m_lit_stress.reset();
    m_conflicts_since_decay = 0;
    m_total_conflicts       = 0;

    m_decisions_true.reset();
    m_decisions_false.reset();
    m_total_decisions       = 0;
    m_vars_explored         = 0;

    memset(m_region_keys, 0, sizeof(m_region_keys));
    memset(m_region_vals, 0, sizeof(m_region_vals));
    memset(m_region_occupied, 0, sizeof(m_region_occupied));
    m_total_restarts  = 0;
    m_unique_regions  = 0;

    memset(m_conflict_pairs, 0, sizeof(m_conflict_pairs));

    // Tier 1a: clause profiles
    delete[] m_clause_profiles;
    m_clause_profiles     = nullptr;
    m_clause_profiles_cap = 0;
    delete[] m_clause_ptr_map;
    m_clause_ptr_map     = nullptr;
    m_clause_ptr_map_cap = 0;

    // Tier 1b: var profiles
    delete[] m_var_profiles;
    m_var_profiles     = nullptr;
    m_var_profiles_cap = 0;

    m_last_decision_trail_pos = 0;
    m_last_decision_var       = UINT32_MAX;
    m_last_decision_polarity  = false;

    // Polarity safety counters
    m_safety_true.reset();
    m_safety_false.reset();

    // Tier 1c: QI patterns
    delete[] m_qi_patterns;
    m_qi_patterns     = nullptr;
    m_qi_patterns_cap = 0;

    // Tier 2a: conflict graph
    delete[] m_conflict_graph;
    m_conflict_graph     = nullptr;
    m_conflict_graph_cap = 0;

    // Tier 2b: conflict history
    delete[] m_conflict_history;
    m_conflict_history       = nullptr;
    m_conflict_history_pos   = 0;
    m_conflict_history_count = 0;

    // Tier 2c: expanded regions
    delete[] m_expanded_regions;
    delete[] m_expanded_region_keys;
    delete[] m_expanded_region_occ;
    m_expanded_regions     = nullptr;
    m_expanded_region_keys = nullptr;
    m_expanded_region_occ  = nullptr;
    m_expanded_unique      = 0;
    m_prev_region_hash     = 0;
    m_prev_region_health   = 0.0f;

    // Tier 3: solver dynamics
    m_dynamics.reset();
    m_last_decided_polarity.reset();
    m_decision_trail_start = 0;
}

// -----------------------------------------------------------------------
// Tier 0 Layer 1: Literal stress
// -----------------------------------------------------------------------

void landscape_map::ensure_literal(unsigned lit_idx) {
    if (lit_idx >= m_lit_stress.size())
        m_lit_stress.resize(lit_idx + 1, 0);
}

void landscape_map::on_conflict_antecedent(unsigned lit_idx) {
    ensure_literal(lit_idx);
    unsigned old = m_lit_stress[lit_idx];
    unsigned bumped = old - (old >> 4) + 16;
    uint8_t new_val = static_cast<uint8_t>(bumped > 255 ? 255 : bumped);
    // B3: Incremental high_stress_count tracking — detect threshold crossing.
    if (old <= 128 && new_val > 128)
        m_dynamics.high_stress_count++;
    m_lit_stress[lit_idx] = new_val;
}

void landscape_map::decay_stress() {
    unsigned sz = m_lit_stress.size();
    uint8_t* p = m_lit_stress.data();
    for (unsigned i = 0; i < sz; ++i) {
        unsigned v = p[i];
        uint8_t nv = static_cast<uint8_t>(v - (v >> 7));
        // B3: Detect downward threshold crossing at 128.
        if (v > 128 && nv <= 128 && m_dynamics.high_stress_count > 0)
            m_dynamics.high_stress_count--;
        p[i] = nv;
    }
}

uint8_t landscape_map::get_stress(unsigned lit_idx) const {
    return lit_idx < m_lit_stress.size() ? m_lit_stress[lit_idx] : 0;
}

double landscape_map::avg_stress() const {
    unsigned sz = m_lit_stress.size();
    if (sz == 0) return 0.0;
    uint64_t sum = 0;
    const uint8_t* p = m_lit_stress.data();
    for (unsigned i = 0; i < sz; ++i)
        sum += p[i];
    return static_cast<double>(sum) / (255.0 * sz);
}

double landscape_map::stress_concentration() const {
    unsigned sz = m_lit_stress.size();
    if (sz < 2) return 0.0;

    unsigned step = 1;
    if (sz > 4096) step = sz / 4096;

    unsigned hist[256];
    memset(hist, 0, sizeof(hist));
    const uint8_t* p = m_lit_stress.data();
    for (unsigned i = 0; i < sz; i += step)
        hist[p[i]]++;

    uint64_t total = 0;
    uint64_t weighted = 0;
    unsigned rank = 0;
    for (unsigned v = 0; v < 256; ++v) {
        unsigned cnt = hist[v];
        if (cnt == 0) continue;
        for (unsigned j = 0; j < cnt; ++j) {
            rank++;
            total += v;
            weighted += static_cast<uint64_t>(rank) * v;
        }
    }
    if (total == 0) return 0.0;
    double gini = (2.0 * weighted) / (rank * static_cast<double>(total)) - (rank + 1.0) / rank;
    return gini < 0.0 ? 0.0 : (gini > 1.0 ? 1.0 : gini);
}

// -----------------------------------------------------------------------
// Tier 0 Layer 2: Variable coverage (legacy interface)
// -----------------------------------------------------------------------

void landscape_map::ensure_var(unsigned var) {
    if (var >= m_decisions_true.size()) {
        m_decisions_true.resize(var + 1, 0);
        m_decisions_false.resize(var + 1, 0);
    }
}

void landscape_map::on_decision(unsigned var, bool is_true, unsigned scope_lvl,
                                unsigned trail_size) {
    ensure_var(var);
    m_total_decisions++;

    // Legacy uint16 coverage counters
    if (is_true) {
        uint16_t old = m_decisions_true[var];
        if (old == 0 && m_decisions_false[var] == 0) {
            m_vars_explored++;
            m_dynamics.first_time_decisions++;  // B2: first-time decision
        }
        if (old < 65535)
            m_decisions_true[var] = old + 1;
    } else {
        uint16_t old = m_decisions_false[var];
        if (old == 0 && m_decisions_true[var] == 0) {
            m_vars_explored++;
            m_dynamics.first_time_decisions++;  // B2: first-time decision
        }
        if (old < 65535)
            m_decisions_false[var] = old + 1;
    }

    // --- Tier 1b: var_profile updates ---
    if (m_var_profiles && var < m_var_profiles_cap) {
        var_profile& vp = m_var_profiles[var];
        if (is_true) {
            if (vp.decisions_true < UINT32_MAX) vp.decisions_true++;
        } else {
            if (vp.decisions_false < UINT32_MAX) vp.decisions_false++;
        }

        // EMA of decision depth (scope_lvl → 0-255)
        if (scope_lvl > 0) {
            unsigned depth_byte = scope_lvl > 255 ? 255 : scope_lvl;
            // EMA: new = 0.9375 * old + 0.0625 * sample
            unsigned old = vp.avg_decision_depth;
            vp.avg_decision_depth = static_cast<uint8_t>(
                old - (old >> 4) + (depth_byte >> 4));
        }
    }

    // --- Fanout tracking: compute fanout for PREVIOUS decision ---
    if (m_last_decision_var != UINT32_MAX && trail_size > 0) {
        unsigned fanout = (trail_size > m_last_decision_trail_pos)
                        ? (trail_size - m_last_decision_trail_pos - 1)  // subtract 1 for the decision itself
                        : 0;
        on_decision_fanout(m_last_decision_var, fanout);
    }

    // Save state for next fanout computation
    m_last_decision_trail_pos = trail_size;
    m_last_decision_var       = var;
    m_last_decision_polarity  = is_true;
}

uint16_t landscape_map::get_decisions_true(unsigned var) const {
    return var < m_decisions_true.size() ? m_decisions_true[var] : 0;
}

uint16_t landscape_map::get_decisions_false(unsigned var) const {
    return var < m_decisions_false.size() ? m_decisions_false[var] : 0;
}

double landscape_map::coverage_fraction() const {
    unsigned total = m_decisions_true.size();
    if (total == 0) return 0.0;
    return static_cast<double>(m_vars_explored) / total;
}

unsigned landscape_map::most_unexplored_var(unsigned num_vars) const {
    unsigned best_var = 0;
    unsigned best_total = UINT32_MAX;
    unsigned limit = std::min(num_vars, static_cast<unsigned>(m_decisions_true.size()));
    for (unsigned v = 0; v < limit; ++v) {
        unsigned t = static_cast<unsigned>(m_decisions_true[v]) + m_decisions_false[v];
        if (t < best_total) {
            best_total = t;
            best_var = v;
            if (t == 0) break;
        }
    }
    if (limit < num_vars && best_total > 0)
        best_var = limit;
    return best_var;
}

// -----------------------------------------------------------------------
// Tier 0 Layer 3: Region fingerprints (1024-slot legacy + expanded)
// -----------------------------------------------------------------------

unsigned landscape_map::region_slot(uint64_t key) const {
    return static_cast<unsigned>(fmix64(key) >> 54) & (REGION_MAP_SIZE - 1);
}

unsigned landscape_map::region_find(uint64_t key) const {
    unsigned slot = region_slot(key);
    for (unsigned probe = 0; probe < REGION_MAP_SIZE; ++probe) {
        unsigned idx = (slot + probe) & (REGION_MAP_SIZE - 1);
        if (!m_region_occupied[idx])
            return REGION_MAP_SIZE;
        if (m_region_keys[idx] == key)
            return idx;
    }
    return REGION_MAP_SIZE;
}

unsigned landscape_map::region_insert_or_update(uint64_t key, float health) {
    unsigned slot = region_slot(key);
    unsigned oldest_slot = slot;
    uint32_t oldest_visit = UINT32_MAX;

    for (unsigned probe = 0; probe < REGION_MAP_SIZE; ++probe) {
        unsigned idx = (slot + probe) & (REGION_MAP_SIZE - 1);

        if (!m_region_occupied[idx]) {
            m_region_occupied[idx] = true;
            m_region_keys[idx] = key;
            m_region_vals[idx].visits = 1;
            m_region_vals[idx].avg_health = health;
            m_region_vals[idx].best_health = health;
            m_region_vals[idx].last_visit = m_total_restarts;
            m_unique_regions++;
            return idx;
        }

        if (m_region_keys[idx] == key) {
            old_region_record& r = m_region_vals[idx];
            if (r.visits < 65535) r.visits++;
            r.avg_health = 0.8f * r.avg_health + 0.2f * health;
            if (health > r.best_health) r.best_health = health;
            r.last_visit = m_total_restarts;
            return idx;
        }

        if (m_region_vals[idx].last_visit < oldest_visit) {
            oldest_visit = m_region_vals[idx].last_visit;
            oldest_slot = idx;
        }
    }

    // Table full — evict LRU entry
    m_region_keys[oldest_slot] = key;
    m_region_vals[oldest_slot].visits = 1;
    m_region_vals[oldest_slot].avg_health = health;
    m_region_vals[oldest_slot].best_health = health;
    m_region_vals[oldest_slot].last_visit = m_total_restarts;
    return oldest_slot;
}

void landscape_map::on_restart(uint64_t phase_hash, float health) {
    m_total_restarts++;

    // Legacy 1024-slot map
    region_insert_or_update(phase_hash, health);

    // Expanded region map (Tier 2c) — update if allocated
    if (m_expanded_regions) {
        // Record transition from previous region
        unsigned slot = expanded_region_insert_or_update(phase_hash, health);
        if (slot < EXPANDED_REGION_MAP_SIZE) {
            expanded_region_record& rec = m_expanded_regions[slot];
            if (m_prev_region_hash != 0) {
                rec.prev_region_hash = m_prev_region_hash;
                rec.entry_health = health;
            }
            // Update exit_health of previous region
            if (m_prev_region_hash != 0) {
                unsigned prev_slot = expanded_region_find(m_prev_region_hash);
                if (prev_slot < EXPANDED_REGION_MAP_SIZE)
                    m_expanded_regions[prev_slot].exit_health = m_prev_region_health;
            }
        }
        m_prev_region_hash   = phase_hash;
        m_prev_region_health = health;
    }
}

unsigned landscape_map::region_visit_count(uint64_t phase_hash) const {
    // Check expanded map first if available
    if (m_expanded_regions) {
        unsigned idx = expanded_region_find(phase_hash);
        if (idx < EXPANDED_REGION_MAP_SIZE)
            return m_expanded_regions[idx].visit_count;
    }
    unsigned idx = region_find(phase_hash);
    return idx < REGION_MAP_SIZE ? m_region_vals[idx].visits : 0;
}

float landscape_map::region_best_health(uint64_t phase_hash) const {
    if (m_expanded_regions) {
        unsigned idx = expanded_region_find(phase_hash);
        if (idx < EXPANDED_REGION_MAP_SIZE)
            return m_expanded_regions[idx].best_health;
    }
    unsigned idx = region_find(phase_hash);
    return idx < REGION_MAP_SIZE ? m_region_vals[idx].best_health : 0.0f;
}

double landscape_map::region_diversity() const {
    if (m_total_restarts == 0) return 0.0;
    unsigned unique = m_expanded_regions ? m_expanded_unique : m_unique_regions;
    return static_cast<double>(unique) / m_total_restarts;
}

// -----------------------------------------------------------------------
// Tier 0 Layer 4: Conflict variable pairs (Bloom filter)
// -----------------------------------------------------------------------

void landscape_map::bloom_hashes(unsigned v1, unsigned v2, unsigned& h0, unsigned& h1, unsigned& h2) {
    unsigned lo = v1 < v2 ? v1 : v2;
    unsigned hi = v1 < v2 ? v2 : v1;
    uint64_t combined = (static_cast<uint64_t>(lo) << 32) | hi;
    uint64_t a = fmix64(combined);
    uint64_t b = fmix64(combined + 0x9E3779B97F4A7C15ULL);
    h0 = static_cast<unsigned>(a) % BLOOM_BITS;
    h1 = static_cast<unsigned>(a >> 32) % BLOOM_BITS;
    h2 = static_cast<unsigned>(b) % BLOOM_BITS;
}

void landscape_map::bloom_set(unsigned v1, unsigned v2) {
    unsigned h0, h1, h2;
    bloom_hashes(v1, v2, h0, h1, h2);
    m_conflict_pairs[h0 >> 3] |= (1u << (h0 & 7));
    m_conflict_pairs[h1 >> 3] |= (1u << (h1 & 7));
    m_conflict_pairs[h2 >> 3] |= (1u << (h2 & 7));
}

bool landscape_map::bloom_test(unsigned v1, unsigned v2) const {
    unsigned h0, h1, h2;
    bloom_hashes(v1, v2, h0, h1, h2);
    return (m_conflict_pairs[h0 >> 3] & (1u << (h0 & 7))) &&
           (m_conflict_pairs[h1 >> 3] & (1u << (h1 & 7))) &&
           (m_conflict_pairs[h2 >> 3] & (1u << (h2 & 7)));
}

void landscape_map::on_learned_clause(unsigned num_vars, unsigned const* vars) {
    m_total_conflicts++;
    unsigned top = num_vars < 8 ? num_vars : 8;
    for (unsigned i = 0; i < top; ++i) {
        for (unsigned j = i + 1; j < top; ++j) {
            bloom_set(vars[i], vars[j]);
        }
    }

    // --- Tier 2a: Update co-occurrence graph ---
    if (m_conflict_graph)
        on_conflict_cooccurrence(num_vars, vars);
}

double landscape_map::conflict_affinity(unsigned var, unsigned const* assigned_vars, unsigned num_assigned) const {
    if (num_assigned == 0) return 0.0;
    unsigned hits = 0;
    unsigned check = num_assigned < 32 ? num_assigned : 32;
    for (unsigned i = 0; i < check; ++i) {
        if (bloom_test(var, assigned_vars[i]))
            hits++;
    }
    return static_cast<double>(hits) / check;
}

// -----------------------------------------------------------------------
// Tier 1a: Clause Saving-Literal Profiles
// -----------------------------------------------------------------------

void landscape_map::ensure_clause_profiles_internal(unsigned cap) {
    if (cap <= m_clause_profiles_cap) return;
    unsigned new_cap = cap + (cap >> 2) + 64;  // grow 25% + slack
    auto* p = new clause_profile[new_cap];
    memset(p, 0, sizeof(clause_profile) * new_cap);
    if (m_clause_profiles) {
        memcpy(p, m_clause_profiles, sizeof(clause_profile) * m_clause_profiles_cap);
        delete[] m_clause_profiles;
    }
    m_clause_profiles     = p;
    m_clause_profiles_cap = new_cap;
}

void landscape_map::ensure_clause_profiles(unsigned num_clauses) {
    if (num_clauses > m_clause_profiles_cap)
        ensure_clause_profiles_internal(num_clauses);
}

void landscape_map::on_clause_propagation(unsigned clause_idx, unsigned saving_lit_idx) {
    if (!m_clause_profiles) return;
    if (clause_idx >= m_clause_profiles_cap) return;
    clause_profile& cp = m_clause_profiles[clause_idx];
    if (cp.m_propagation_count < UINT16_MAX)
        cp.m_propagation_count++;
    // Update saving literal with EMA logic:
    // If this is the same saving literal, bump the fraction.
    // If different, decay the fraction and possibly switch.
    if (cp.m_saving_literal == saving_lit_idx || cp.m_violation_count == 0) {
        cp.m_saving_literal = saving_lit_idx;
        unsigned frac = cp.m_saving_fraction;
        // EMA up: frac = 0.9375 * frac + 0.0625 * 255
        cp.m_saving_fraction = static_cast<uint8_t>(
            frac - (frac >> 4) + 16);
    } else {
        // EMA down
        unsigned frac = cp.m_saving_fraction;
        unsigned decayed = frac - (frac >> 3);  // *= 0.875
        if (decayed < 64) {
            // Switch saving literal
            cp.m_saving_literal = saving_lit_idx;
            cp.m_saving_fraction = 64;
        } else {
            cp.m_saving_fraction = static_cast<uint8_t>(decayed);
        }
    }
    if (cp.m_violation_count < UINT16_MAX)
        cp.m_violation_count++;
    cp.m_last_stress = m_total_conflicts;
}

void landscape_map::on_clause_antecedent(unsigned clause_idx) {
    if (!m_clause_profiles) return;
    if (clause_idx >= m_clause_profiles_cap) return;
    clause_profile& cp = m_clause_profiles[clause_idx];
    if (cp.m_antecedent_count < UINT16_MAX)
        cp.m_antecedent_count++;
}

// -----------------------------------------------------------------------
// Clause pointer → index reverse map
// -----------------------------------------------------------------------

void landscape_map::ensure_clause_ptr_map(unsigned num_clauses) {
    // Size the table to next power of 2 with ~50% load factor
    unsigned needed = num_clauses * 2;
    if (needed < 64) needed = 64;
    // Round up to power of 2
    unsigned cap = 1;
    while (cap < needed) cap <<= 1;
    if (cap <= m_clause_ptr_map_cap) return;
    delete[] m_clause_ptr_map;
    m_clause_ptr_map = new clause_ptr_entry[cap];
    memset(m_clause_ptr_map, 0, sizeof(clause_ptr_entry) * cap);
    m_clause_ptr_map_cap = cap;
}

void landscape_map::register_clause_ptr(unsigned clause_idx, uintptr_t ptr) {
    if (!m_clause_ptr_map || m_clause_ptr_map_cap == 0 || ptr == 0) return;
    unsigned mask = m_clause_ptr_map_cap - 1;
    unsigned slot = static_cast<unsigned>(fmix64(ptr)) & mask;
    for (unsigned probe = 0; probe < 64; ++probe) {
        unsigned idx = (slot + probe) & mask;
        if (m_clause_ptr_map[idx].ptr == 0) {
            m_clause_ptr_map[idx].ptr = ptr;
            m_clause_ptr_map[idx].idx = clause_idx;
            return;
        }
        if (m_clause_ptr_map[idx].ptr == ptr) {
            // Already registered (update index in case of reuse)
            m_clause_ptr_map[idx].idx = clause_idx;
            return;
        }
    }
    // Probe limit hit — silently drop (shouldn't happen with 50% load)
}

unsigned landscape_map::find_clause_idx(uintptr_t ptr) const {
    if (!m_clause_ptr_map || m_clause_ptr_map_cap == 0 || ptr == 0)
        return UINT32_MAX;
    unsigned mask = m_clause_ptr_map_cap - 1;
    unsigned slot = static_cast<unsigned>(fmix64(ptr)) & mask;
    for (unsigned probe = 0; probe < 64; ++probe) {
        unsigned idx = (slot + probe) & mask;
        if (m_clause_ptr_map[idx].ptr == 0)
            return UINT32_MAX;  // Empty slot — not found
        if (m_clause_ptr_map[idx].ptr == ptr)
            return m_clause_ptr_map[idx].idx;
    }
    return UINT32_MAX;
}

void landscape_map::periodic_clause_scan(unsigned num_clauses,
                                         unsigned num_lits_fn(unsigned, void*),
                                         unsigned get_lit_value_fn(unsigned, unsigned, void*),
                                         void* ctx) {
    // Called every 1000 conflicts. For each input clause, check current
    // assignment: count how many literals are false. If all but one are
    // false, the surviving literal is the current "saver."
    if (!m_clause_profiles) return;
    unsigned limit = num_clauses < m_clause_profiles_cap ? num_clauses : m_clause_profiles_cap;
    for (unsigned ci = 0; ci < limit; ++ci) {
        unsigned nlits = num_lits_fn(ci, ctx);
        if (nlits == 0) continue;
        unsigned false_count = 0;
        unsigned true_lit = UINT32_MAX;
        for (unsigned li = 0; li < nlits; ++li) {
            // get_lit_value_fn returns: 0=false, 1=true, 2=undef
            unsigned val = get_lit_value_fn(ci, li, ctx);
            if (val == 0) {
                false_count++;
            } else if (val == 1) {
                true_lit = li;
            }
        }
        if (false_count == nlits - 1 && true_lit != UINT32_MAX) {
            on_clause_propagation(ci, true_lit);
        }
    }
}

landscape_map::clause_profile const* landscape_map::get_clause_profile(unsigned clause_idx) const {
    if (!m_clause_profiles || clause_idx >= m_clause_profiles_cap) return nullptr;
    return &m_clause_profiles[clause_idx];
}

unsigned landscape_map::get_saving_literal(unsigned clause_idx) const {
    if (!m_clause_profiles || clause_idx >= m_clause_profiles_cap) return UINT32_MAX;
    return m_clause_profiles[clause_idx].m_saving_literal;
}

// -----------------------------------------------------------------------
// Tier 1b: Variable Propagation Fan-Out Profiles
// -----------------------------------------------------------------------

void landscape_map::ensure_var_profiles_internal(unsigned cap) {
    if (cap <= m_var_profiles_cap) return;
    unsigned new_cap = cap + (cap >> 2) + 64;
    auto* p = new var_profile[new_cap];
    memset(p, 0, sizeof(var_profile) * new_cap);
    if (m_var_profiles) {
        memcpy(p, m_var_profiles, sizeof(var_profile) * m_var_profiles_cap);
        delete[] m_var_profiles;
    }
    m_var_profiles     = p;
    m_var_profiles_cap = new_cap;
}

void landscape_map::ensure_var_profiles(unsigned num_vars) {
    if (num_vars > m_var_profiles_cap)
        ensure_var_profiles_internal(num_vars);
}

landscape_map::var_profile const* landscape_map::get_var_profile(unsigned var) const {
    if (!m_var_profiles || var >= m_var_profiles_cap) return nullptr;
    return &m_var_profiles[var];
}

void landscape_map::on_decision_fanout(unsigned var, unsigned fanout) {
    if (!m_var_profiles || var >= m_var_profiles_cap) return;
    var_profile& vp = m_var_profiles[var];
    if (fanout > vp.max_fanout) {
        vp.max_fanout = static_cast<uint16_t>(fanout > UINT16_MAX ? UINT16_MAX : fanout);
    }
    // Update EMA for the appropriate polarity
    // EMA: new = 0.9375 * old + 0.0625 * sample
    bool polarity = (vp.decisions_true > vp.decisions_false);
    // Use the actual polarity from the decision that produced this fanout
    // (the PREVIOUS decision's polarity, stored before we updated)
    // We approximate: check if the last increment was to decisions_true
    if (m_last_decision_polarity) {
        unsigned old = vp.avg_fanout_true;
        unsigned sample = fanout > UINT16_MAX ? UINT16_MAX : fanout;
        vp.avg_fanout_true = static_cast<uint16_t>(
            old - (old >> 4) + (sample >> 4));
    } else {
        unsigned old = vp.avg_fanout_false;
        unsigned sample = fanout > UINT16_MAX ? UINT16_MAX : fanout;
        vp.avg_fanout_false = static_cast<uint16_t>(
            old - (old >> 4) + (sample >> 4));
    }

    // Maintain top-K high-fanout variable cache.
    // Insert var into the cache if its fanout exceeds the minimum in the cache.
    unsigned max_fo = std::max(vp.avg_fanout_true, vp.avg_fanout_false);
    if (max_fo > 10) {
        // Check if already in cache
        for (unsigned i = 0; i < m_top_fanout_count; ++i) {
            if (m_top_fanout_vars[i] == var) return; // already tracked
        }
        if (m_top_fanout_count < TOP_FANOUT_K) {
            // Cache not full — just append
            m_top_fanout_vars[m_top_fanout_count++] = var;
        } else {
            // Cache full — evict the lowest-fanout entry
            unsigned min_idx = 0;
            unsigned min_fo = UINT_MAX;
            for (unsigned i = 0; i < TOP_FANOUT_K; ++i) {
                unsigned fo_i = get_var_fanout(m_top_fanout_vars[i]);
                if (fo_i < min_fo) { min_fo = fo_i; min_idx = i; }
            }
            if (max_fo > min_fo) {
                m_top_fanout_vars[min_idx] = var;
            }
        }
    }
}

void landscape_map::on_var_in_conflict(unsigned var, bool was_decision) {
    if (!m_var_profiles || var >= m_var_profiles_cap) return;
    var_profile& vp = m_var_profiles[var];
    if (vp.conflict_count < UINT16_MAX)
        vp.conflict_count++;
    if (was_decision && vp.decision_conflict_count < UINT16_MAX)
        vp.decision_conflict_count++;
}

void landscape_map::update_polarity_history(unsigned var, bool polarity) {
    if (!m_var_profiles || var >= m_var_profiles_cap) return;
    var_profile& vp = m_var_profiles[var];
    vp.polarity_history = (vp.polarity_history << 1) | (polarity ? 1u : 0u);
}

void landscape_map::compute_clause_occurrences(unsigned num_vars, unsigned num_clauses,
                                               unsigned clause_num_lits_fn(unsigned, void*),
                                               unsigned clause_get_var_fn(unsigned, unsigned, void*),
                                               void* ctx) {
    if (!m_var_profiles) return;
    // Clear existing counts
    for (unsigned v = 0; v < m_var_profiles_cap; ++v)
        m_var_profiles[v].clause_occurrence = 0;

    for (unsigned ci = 0; ci < num_clauses; ++ci) {
        unsigned nlits = clause_num_lits_fn(ci, ctx);
        for (unsigned li = 0; li < nlits; ++li) {
            unsigned v = clause_get_var_fn(ci, li, ctx);
            if (v < m_var_profiles_cap) {
                if (m_var_profiles[v].clause_occurrence < 255)
                    m_var_profiles[v].clause_occurrence++;
            }
        }
    }
}

double landscape_map::get_polarity_safety_score(unsigned var, bool is_true) const {
    if (!m_var_profiles || var >= m_var_profiles_cap) return 0.5;
    var_profile const& vp = m_var_profiles[var];
    uint32_t total = vp.decisions_true + vp.decisions_false;
    if (total == 0) return 0.5;
    // Safety = fraction of decisions in this polarity that didn't lead to conflict
    uint32_t decisions = is_true ? vp.decisions_true : vp.decisions_false;
    if (decisions == 0) return 0.5;
    // Approximate: higher fanout = more propagation = more useful
    uint16_t fanout = is_true ? vp.avg_fanout_true : vp.avg_fanout_false;
    // Normalize fanout to 0-1 range (assume max ~1000)
    double fanout_norm = std::min(1.0, static_cast<double>(fanout) / 1000.0);
    // Combine with conflict rate
    double conflict_rate = (vp.conflict_count > 0)
        ? static_cast<double>(vp.decision_conflict_count) / vp.conflict_count
        : 0.0;
    return 0.5 * (1.0 - conflict_rate) + 0.5 * fanout_norm;
}

double landscape_map::get_impact_score(unsigned var) const {
    if (!m_var_profiles || var >= m_var_profiles_cap) return 0.0;
    var_profile const& vp = m_var_profiles[var];
    // Impact = max of average fanouts * clause occurrence density
    double fanout = std::max(static_cast<double>(vp.avg_fanout_true),
                             static_cast<double>(vp.avg_fanout_false));
    double occ = static_cast<double>(vp.clause_occurrence) / 255.0;
    return fanout * (0.5 + 0.5 * occ);
}

// -----------------------------------------------------------------------
// Saving-literal polarity safety
// -----------------------------------------------------------------------

void landscape_map::compute_polarity_safety() {
    if (!m_clause_profiles) return;
    // Ensure vectors are sized
    unsigned var_cap = m_var_profiles_cap;
    if (var_cap == 0) return;
    if (m_safety_true.size() < var_cap) {
        m_safety_true.resize(var_cap, 0);
        m_safety_false.resize(var_cap, 0);
    }
    // Clear counters
    memset(m_safety_true.data(), 0, m_safety_true.size() * sizeof(uint16_t));
    memset(m_safety_false.data(), 0, m_safety_false.size() * sizeof(uint16_t));
    // Scan all clause profiles for reliable saving literals
    for (unsigned i = 0; i < m_clause_profiles_cap; ++i) {
        clause_profile const& cp = m_clause_profiles[i];
        // Only count clauses with a reasonably reliable saving literal
        // (m_saving_fraction > 128 means >50% of the time this literal saves)
        if (cp.m_saving_fraction > 128 && cp.m_propagation_count > 0) {
            unsigned lit_idx = cp.m_saving_literal;
            unsigned var = lit_idx >> 1;
            if (var < var_cap) {
                // In Z3, literal index: even = positive, odd = negative
                bool is_pos = (lit_idx & 1) == 0;
                if (is_pos) {
                    if (m_safety_true[var] < UINT16_MAX)
                        m_safety_true[var]++;
                } else {
                    if (m_safety_false[var] < UINT16_MAX)
                        m_safety_false[var]++;
                }
            }
        }
    }
}

int landscape_map::polarity_safety(unsigned var, unsigned margin) const {
    if (var >= m_safety_true.size()) return 0;
    int diff = static_cast<int>(m_safety_true[var])
             - static_cast<int>(m_safety_false[var]);
    if (diff > static_cast<int>(margin)) return 1;   // true is safer
    if (diff < -static_cast<int>(margin)) return -1;  // false is safer
    return 0;
}

unsigned landscape_map::get_var_fanout(unsigned var) const {
    if (!m_var_profiles || var >= m_var_profiles_cap) return 0;
    var_profile const& vp = m_var_profiles[var];
    return std::max(static_cast<unsigned>(vp.avg_fanout_true),
                    static_cast<unsigned>(vp.avg_fanout_false));
}

// -----------------------------------------------------------------------
// Tier 1c: QI Binding Pattern Success Map
// -----------------------------------------------------------------------

void landscape_map::ensure_qi_patterns_internal(unsigned cap) {
    if (cap <= m_qi_patterns_cap) return;
    unsigned new_cap = cap + (cap >> 2) + 16;
    auto* p = new quantifier_pattern_map[new_cap];
    memset(p, 0, sizeof(quantifier_pattern_map) * new_cap);
    if (m_qi_patterns) {
        memcpy(p, m_qi_patterns, sizeof(quantifier_pattern_map) * m_qi_patterns_cap);
        delete[] m_qi_patterns;
    }
    m_qi_patterns     = p;
    m_qi_patterns_cap = new_cap;
}

void landscape_map::ensure_qi_patterns(unsigned num_quantifiers) {
    if (num_quantifiers > m_qi_patterns_cap)
        ensure_qi_patterns_internal(num_quantifiers);
}

void landscape_map::update_qi_pattern(unsigned quant_id, uint32_t pattern_hash, bool useful) {
    if (!m_qi_patterns || quant_id >= m_qi_patterns_cap) return;
    quantifier_pattern_map& qpm = m_qi_patterns[quant_id];

    // Open-addressing lookup in the per-quantifier hash table
    unsigned slot = pattern_hash & (QI_PATTERN_SLOTS - 1);
    unsigned empty_slot = UINT32_MAX;
    for (unsigned probe = 0; probe < QI_PATTERN_SLOTS; ++probe) {
        unsigned idx = (slot + probe) & (QI_PATTERN_SLOTS - 1);
        if (qpm.slots[idx].total_instances == 0 && qpm.slots[idx].pattern_hash == 0) {
            // Empty slot
            if (empty_slot == UINT32_MAX) empty_slot = idx;
            break;  // pattern not in table
        }
        if (qpm.slots[idx].pattern_hash == pattern_hash) {
            // Found — update
            if (qpm.slots[idx].total_instances < UINT32_MAX)
                qpm.slots[idx].total_instances++;
            if (useful && qpm.slots[idx].useful_instances < UINT16_MAX)
                qpm.slots[idx].useful_instances++;
            return;
        }
    }

    // Not found — insert if we have an empty slot
    if (empty_slot != UINT32_MAX && qpm.num_entries < QI_PATTERN_SLOTS * 3 / 4) {
        qpm.slots[empty_slot].pattern_hash = pattern_hash;
        qpm.slots[empty_slot].total_instances = 1;
        qpm.slots[empty_slot].useful_instances = useful ? 1 : 0;
        qpm.num_entries++;
    }
}

float landscape_map::get_qi_pattern_success(unsigned quant_id, uint32_t pattern_hash) const {
    if (!m_qi_patterns || quant_id >= m_qi_patterns_cap) return 0.0f;
    quantifier_pattern_map const& qpm = m_qi_patterns[quant_id];
    unsigned slot = pattern_hash & (QI_PATTERN_SLOTS - 1);
    for (unsigned probe = 0; probe < QI_PATTERN_SLOTS; ++probe) {
        unsigned idx = (slot + probe) & (QI_PATTERN_SLOTS - 1);
        if (qpm.slots[idx].total_instances == 0 && qpm.slots[idx].pattern_hash == 0)
            return 0.0f;  // not found
        if (qpm.slots[idx].pattern_hash == pattern_hash) {
            if (qpm.slots[idx].total_instances == 0) return 0.0f;
            return static_cast<float>(qpm.slots[idx].useful_instances) /
                   static_cast<float>(qpm.slots[idx].total_instances);
        }
    }
    return 0.0f;
}

// -----------------------------------------------------------------------
// Tier 2a: Variable Conflict Co-occurrence Graph
// -----------------------------------------------------------------------

void landscape_map::ensure_conflict_graph_internal(unsigned cap) {
    if (cap <= m_conflict_graph_cap) return;
    unsigned new_cap = cap + (cap >> 2) + 64;
    auto* p = new var_conflict_graph_entry[new_cap];
    memset(p, 0, sizeof(var_conflict_graph_entry) * new_cap);
    if (m_conflict_graph) {
        memcpy(p, m_conflict_graph, sizeof(var_conflict_graph_entry) * m_conflict_graph_cap);
        delete[] m_conflict_graph;
    }
    m_conflict_graph     = p;
    m_conflict_graph_cap = new_cap;
}

void landscape_map::ensure_conflict_graph(unsigned num_vars) {
    if (num_vars > m_conflict_graph_cap)
        ensure_conflict_graph_internal(num_vars);
}

void landscape_map::on_conflict_cooccurrence(unsigned num_vars, unsigned const* vars) {
    // For each pair of top-8 variables, update the co-occurrence graph
    unsigned top = num_vars < 8 ? num_vars : 8;
    for (unsigned i = 0; i < top; ++i) {
        unsigned vi = vars[i];
        if (vi >= m_conflict_graph_cap) continue;
        var_conflict_graph_entry& entry = m_conflict_graph[vi];
        if (entry.total_degree < UINT16_MAX)
            entry.total_degree++;

        for (unsigned j = i + 1; j < top; ++j) {
            unsigned vj = vars[j];
            // Update vi's partner list with vj
            bool found = false;
            unsigned min_idx = 0;
            uint16_t min_count = UINT16_MAX;
            for (unsigned k = 0; k < 16; ++k) {
                if (entry.partner_ids[k] == vj && entry.partner_counts[k] > 0) {
                    if (entry.partner_counts[k] < UINT16_MAX)
                        entry.partner_counts[k]++;
                    found = true;
                    break;
                }
                if (entry.partner_counts[k] < min_count) {
                    min_count = entry.partner_counts[k];
                    min_idx = k;
                }
            }
            if (!found) {
                // Insert into the slot with minimum count (evict if needed)
                if (min_count == 0 || min_count < 2) {
                    entry.partner_ids[min_idx] = vj;
                    entry.partner_counts[min_idx] = 1;
                }
            }

            // Also update vj's partner list with vi (symmetric)
            if (vj >= m_conflict_graph_cap) continue;
            var_conflict_graph_entry& entry_j = m_conflict_graph[vj];
            found = false;
            min_idx = 0;
            min_count = UINT16_MAX;
            for (unsigned k = 0; k < 16; ++k) {
                if (entry_j.partner_ids[k] == vi && entry_j.partner_counts[k] > 0) {
                    if (entry_j.partner_counts[k] < UINT16_MAX)
                        entry_j.partner_counts[k]++;
                    found = true;
                    break;
                }
                if (entry_j.partner_counts[k] < min_count) {
                    min_count = entry_j.partner_counts[k];
                    min_idx = k;
                }
            }
            if (!found) {
                if (min_count == 0 || min_count < 2) {
                    entry_j.partner_ids[min_idx] = vi;
                    entry_j.partner_counts[min_idx] = 1;
                }
            }
        }
    }
}

landscape_map::var_conflict_graph_entry const* landscape_map::get_conflict_graph_entry(unsigned var) const {
    if (!m_conflict_graph || var >= m_conflict_graph_cap) return nullptr;
    return &m_conflict_graph[var];
}

// -----------------------------------------------------------------------
// Tier 2b: Conflict History Buffer
// -----------------------------------------------------------------------

void landscape_map::ensure_conflict_history() {
    if (m_conflict_history) return;
    m_conflict_history = new conflict_record[CONFLICT_HISTORY_SIZE];
    memset(m_conflict_history, 0, sizeof(conflict_record) * CONFLICT_HISTORY_SIZE);
    m_conflict_history_pos   = 0;
    m_conflict_history_count = 0;
}

void landscape_map::on_conflict_full(uint64_t clause_hash, unsigned const* top_vars,
                                     unsigned num_top_vars, unsigned glue,
                                     unsigned backjump, unsigned trail_size,
                                     uint8_t theory_flags, unsigned clause_size) {
    ensure_conflict_history();
    conflict_record& rec = m_conflict_history[m_conflict_history_pos];
    rec.learned_clause_hash = clause_hash;
    unsigned top = num_top_vars < 5 ? num_top_vars : 5;
    for (unsigned i = 0; i < top; ++i)
        rec.top_vars[i] = top_vars[i];
    for (unsigned i = top; i < 5; ++i)
        rec.top_vars[i] = 0;
    rec.timestamp         = m_total_conflicts;
    rec.glue              = static_cast<uint16_t>(glue > UINT16_MAX ? UINT16_MAX : glue);
    rec.backjump_distance = static_cast<uint16_t>(backjump > UINT16_MAX ? UINT16_MAX : backjump);
    rec.trail_size_lo     = static_cast<uint16_t>(trail_size & 0xFFFF);
    rec.theory_flags      = theory_flags;
    rec.clause_size       = static_cast<uint8_t>(clause_size > 255 ? 255 : clause_size);

    m_conflict_history_pos = (m_conflict_history_pos + 1) % CONFLICT_HISTORY_SIZE;
    if (m_conflict_history_count < CONFLICT_HISTORY_SIZE)
        m_conflict_history_count++;
}

landscape_map::conflict_record const* landscape_map::get_conflict_record(unsigned idx) const {
    if (!m_conflict_history || idx >= m_conflict_history_count) return nullptr;
    // Convert logical index (0 = oldest) to ring buffer position
    if (m_conflict_history_count < CONFLICT_HISTORY_SIZE) {
        return &m_conflict_history[idx];
    }
    unsigned pos = (m_conflict_history_pos + idx) % CONFLICT_HISTORY_SIZE;
    return &m_conflict_history[pos];
}

unsigned landscape_map::conflict_history_count() const {
    return m_conflict_history_count;
}

double landscape_map::conflict_recurrence_rate(unsigned window) const {
    if (!m_conflict_history || m_conflict_history_count < 2) return 0.0;
    unsigned w = window < m_conflict_history_count ? window : m_conflict_history_count;
    if (w < 2) return 0.0;

    // Check how many of the recent conflicts have duplicate hashes
    // in the same window. Use a simple quadratic scan (window is small).
    unsigned duplicates = 0;
    unsigned start = (m_conflict_history_pos + CONFLICT_HISTORY_SIZE - w) % CONFLICT_HISTORY_SIZE;
    for (unsigned i = 0; i < w; ++i) {
        unsigned idx_i = (start + i) % CONFLICT_HISTORY_SIZE;
        uint64_t hash_i = m_conflict_history[idx_i].learned_clause_hash;
        if (hash_i == 0) continue;
        for (unsigned j = i + 1; j < w; ++j) {
            unsigned idx_j = (start + j) % CONFLICT_HISTORY_SIZE;
            if (m_conflict_history[idx_j].learned_clause_hash == hash_i) {
                duplicates++;
                break;  // count each duplicate once
            }
        }
    }
    return static_cast<double>(duplicates) / w;
}

// -----------------------------------------------------------------------
// Tier 2c: Expanded Region Map
// -----------------------------------------------------------------------

void landscape_map::ensure_expanded_regions() {
    if (m_expanded_regions) return;
    m_expanded_regions     = new expanded_region_record[EXPANDED_REGION_MAP_SIZE];
    m_expanded_region_keys = new uint64_t[EXPANDED_REGION_MAP_SIZE];
    m_expanded_region_occ  = new bool[EXPANDED_REGION_MAP_SIZE];
    memset(m_expanded_regions, 0, sizeof(expanded_region_record) * EXPANDED_REGION_MAP_SIZE);
    memset(m_expanded_region_keys, 0, sizeof(uint64_t) * EXPANDED_REGION_MAP_SIZE);
    memset(m_expanded_region_occ, 0, sizeof(bool) * EXPANDED_REGION_MAP_SIZE);
    m_expanded_unique = 0;
}

unsigned landscape_map::expanded_region_slot(uint64_t key) const {
    // Use upper bits of fmix64 to distribute across 100K slots
    return static_cast<unsigned>(fmix64(key) % EXPANDED_REGION_MAP_SIZE);
}

unsigned landscape_map::expanded_region_find(uint64_t key) const {
    if (!m_expanded_regions) return EXPANDED_REGION_MAP_SIZE;
    unsigned slot = expanded_region_slot(key);
    // Linear probing with bounded search (cap at 64 probes)
    for (unsigned probe = 0; probe < 64; ++probe) {
        unsigned idx = (slot + probe) % EXPANDED_REGION_MAP_SIZE;
        if (!m_expanded_region_occ[idx])
            return EXPANDED_REGION_MAP_SIZE;
        if (m_expanded_region_keys[idx] == key)
            return idx;
    }
    return EXPANDED_REGION_MAP_SIZE;
}

unsigned landscape_map::expanded_region_insert_or_update(uint64_t key, float health) {
    ensure_expanded_regions();
    unsigned slot = expanded_region_slot(key);
    unsigned oldest_slot = slot;
    uint32_t oldest_visit = UINT32_MAX;

    for (unsigned probe = 0; probe < 64; ++probe) {
        unsigned idx = (slot + probe) % EXPANDED_REGION_MAP_SIZE;

        if (!m_expanded_region_occ[idx]) {
            m_expanded_region_occ[idx]  = true;
            m_expanded_region_keys[idx] = key;
            expanded_region_record& r = m_expanded_regions[idx];
            r.hash        = key;
            r.avg_health  = health;
            r.best_health = health;
            r.visit_count = 1;
            r.last_visit  = m_total_restarts;
            r.prev_region_hash = 0;
            r.entry_health     = health;
            r.exit_health      = 0.0f;
            m_expanded_unique++;
            return idx;
        }

        if (m_expanded_region_keys[idx] == key) {
            expanded_region_record& r = m_expanded_regions[idx];
            if (r.visit_count < UINT32_MAX) r.visit_count++;
            r.avg_health = 0.8f * r.avg_health + 0.2f * health;
            if (health > r.best_health) r.best_health = health;
            r.last_visit = m_total_restarts;
            return idx;
        }

        if (m_expanded_regions[idx].last_visit < oldest_visit) {
            oldest_visit = m_expanded_regions[idx].last_visit;
            oldest_slot = idx;
        }
    }

    // Probe limit hit — evict LRU entry in the probe window
    m_expanded_region_keys[oldest_slot] = key;
    expanded_region_record& r = m_expanded_regions[oldest_slot];
    r.hash        = key;
    r.avg_health  = health;
    r.best_health = health;
    r.visit_count = 1;
    r.last_visit  = m_total_restarts;
    r.prev_region_hash = 0;
    r.entry_health     = health;
    r.exit_health      = 0.0f;
    // unique count stays same (evicted one, inserted one)
    return oldest_slot;
}

// -----------------------------------------------------------------------
// Tier 3: Solver Dynamics — 20 lightweight datapoints
// -----------------------------------------------------------------------

void landscape_map::dynamics_phase_begin() {
    m_dynamics.phase_start_tsc = landscape_rdtsc();
}

void landscape_map::dynamics_phase_end_bcp() {
    uint64_t now = landscape_rdtsc();
    if (m_dynamics.phase_start_tsc > 0)
        m_dynamics.cycles_bcp += now - m_dynamics.phase_start_tsc;
    m_dynamics.cycles_total += now - m_dynamics.phase_start_tsc;
    m_dynamics.phase_start_tsc = now;
}

void landscape_map::dynamics_phase_end_theory() {
    uint64_t now = landscape_rdtsc();
    if (m_dynamics.phase_start_tsc > 0)
        m_dynamics.cycles_theory += now - m_dynamics.phase_start_tsc;
    m_dynamics.cycles_total += now - m_dynamics.phase_start_tsc;
    m_dynamics.phase_start_tsc = now;
}

void landscape_map::dynamics_phase_end_qi() {
    uint64_t now = landscape_rdtsc();
    if (m_dynamics.phase_start_tsc > 0)
        m_dynamics.cycles_qi += now - m_dynamics.phase_start_tsc;
    m_dynamics.cycles_total += now - m_dynamics.phase_start_tsc;
    m_dynamics.phase_start_tsc = now;
}

void landscape_map::dynamics_phase_end_decide() {
    uint64_t now = landscape_rdtsc();
    if (m_dynamics.phase_start_tsc > 0)
        m_dynamics.cycles_decide += now - m_dynamics.phase_start_tsc;
    m_dynamics.cycles_total += now - m_dynamics.phase_start_tsc;
    m_dynamics.phase_start_tsc = now;
}

void landscape_map::dynamics_phase_end_conflict() {
    uint64_t now = landscape_rdtsc();
    if (m_dynamics.phase_start_tsc > 0)
        m_dynamics.cycles_conflict += now - m_dynamics.phase_start_tsc;
    m_dynamics.cycles_total += now - m_dynamics.phase_start_tsc;
    m_dynamics.phase_start_tsc = now;
}

// Datapoint 6: BCP propagation chain length.
// Called on each decision. Computes chain = propagated_since_last_decision.
void landscape_map::dynamics_on_decision(unsigned trail_size) {
    if (m_decision_trail_start > 0 && trail_size > m_decision_trail_start) {
        unsigned chain = trail_size - m_decision_trail_start - 1; // subtract the decision itself
        // EMA alpha=0.05 (fast-changing metric)
        m_dynamics.avg_prop_chain_length =
            0.95f * m_dynamics.avg_prop_chain_length + 0.05f * static_cast<float>(chain);
    }
    m_decision_trail_start = trail_size;
}

// Datapoint 7: Decision reversal detection.
void landscape_map::dynamics_on_reversal() {
    m_dynamics.total_reversals++;
}

// Datapoints 8-11,14,16-17,20: Conflict-time metrics.
void landscape_map::dynamics_on_conflict(unsigned scope_lvl, unsigned trail_size,
                                          unsigned num_vars_total, unsigned num_lits,
                                          unsigned glue, unsigned conflict_lvl,
                                          unsigned backjump_lvl, bool theory_conflict) {
    constexpr float ALPHA = 0.01f;  // slow EMA for most metrics

    // 8: Assignment density at conflict
    if (num_vars_total > 0) {
        float density = static_cast<float>(trail_size) / static_cast<float>(num_vars_total);
        m_dynamics.avg_conflict_density = (1.0f - ALPHA) * m_dynamics.avg_conflict_density + ALPHA * density;
    }

    // 9: Decision level at conflict
    m_dynamics.avg_conflict_level = (1.0f - ALPHA) * m_dynamics.avg_conflict_level + ALPHA * static_cast<float>(scope_lvl);

    // 10: Learned clause size trend
    m_dynamics.avg_learned_size = (1.0f - ALPHA) * m_dynamics.avg_learned_size + ALPHA * static_cast<float>(num_lits);

    // 11: LBD/glue trend
    m_dynamics.avg_glue = (1.0f - ALPHA) * m_dynamics.avg_glue + ALPHA * static_cast<float>(glue);

    // 14: Backjump distance fraction
    if (conflict_lvl > 0) {
        float frac = static_cast<float>(conflict_lvl - backjump_lvl) / static_cast<float>(conflict_lvl);
        m_dynamics.avg_backjump_frac = (1.0f - ALPHA) * m_dynamics.avg_backjump_frac + ALPHA * frac;
    }

    // 16: Effective branching factor = trail_size / scope_level
    if (scope_lvl > 0) {
        float bf = static_cast<float>(trail_size) / static_cast<float>(scope_lvl);
        m_dynamics.avg_branching_factor = (1.0f - ALPHA) * m_dynamics.avg_branching_factor + ALPHA * bf;
    }

    // 17: Theory conflict fraction
    float tc = theory_conflict ? 1.0f : 0.0f;
    m_dynamics.theory_conflict_frac = (1.0f - ALPHA) * m_dynamics.theory_conflict_frac + ALPHA * tc;

    // 20: Conflict burstiness (inter-conflict gap in decisions)
    if (m_dynamics.last_conflict_decisions > 0) {
        float gap = static_cast<float>(m_total_decisions - m_dynamics.last_conflict_decisions);
        m_dynamics.ema_gap = (1.0f - ALPHA) * m_dynamics.ema_gap + ALPHA * gap;
        m_dynamics.ema_gap_sq = (1.0f - ALPHA) * m_dynamics.ema_gap_sq + ALPHA * gap * gap;
        // Burstiness = normalized variance = (E[gap^2] - E[gap]^2) / max(E[gap^2], eps)
        float var = m_dynamics.ema_gap_sq - m_dynamics.ema_gap * m_dynamics.ema_gap;
        if (var < 0.0f) var = 0.0f;
        float denom = m_dynamics.ema_gap_sq > 1e-6f ? m_dynamics.ema_gap_sq : 1e-6f;
        m_dynamics.conflict_burstiness = var / denom;
    }
    m_dynamics.last_conflict_decisions = m_total_decisions;
}

// Datapoint 18: Theory propagation density (per-round accumulation).
void landscape_map::dynamics_on_theory_prop() {
    m_dynamics.theory_props_this_round++;
}

void landscape_map::dynamics_on_bcp_prop() {
    m_dynamics.props_this_round++;
}

// Datapoints 12-13: GC-related metrics.
void landscape_map::dynamics_on_gc(unsigned survived, unsigned candidates, unsigned used) {
    // 13: GC survival rate
    if (candidates > 0)
        m_dynamics.gc_survival_rate = static_cast<float>(survived) / static_cast<float>(candidates);

    // 12: Clause early-use rate (fraction of candidates that were used as antecedent)
    if (candidates > 0) {
        float rate = static_cast<float>(used) / static_cast<float>(candidates);
        m_dynamics.clause_early_use_rate =
            0.9f * m_dynamics.clause_early_use_rate + 0.1f * rate;
    }
}

// Datapoint 15: Restart interval.
void landscape_map::dynamics_on_restart(unsigned conflicts_since_restart) {
    constexpr float ALPHA = 0.01f;
    m_dynamics.avg_restart_interval =
        (1.0f - ALPHA) * m_dynamics.avg_restart_interval + ALPHA * static_cast<float>(conflicts_since_restart);

    // A2: Actual restart interval with fast EMA (alpha=0.2) for SPSA responsiveness.
    m_dynamics.actual_restart_interval =
        0.8f * m_dynamics.actual_restart_interval + 0.2f * static_cast<float>(conflicts_since_restart);

    // 18: Finalize theory prop density for this restart interval.
    if (m_dynamics.props_this_round > 0) {
        float density = static_cast<float>(m_dynamics.theory_props_this_round) /
                        static_cast<float>(m_dynamics.props_this_round);
        m_dynamics.theory_prop_density =
            (1.0f - ALPHA) * m_dynamics.theory_prop_density + ALPHA * density;
    }
    m_dynamics.props_this_round = 0;
    m_dynamics.theory_props_this_round = 0;
}

// Datapoint 19: Binary clause ratio.
void landscape_map::dynamics_update_binary_ratio(unsigned binary, unsigned total) {
    m_dynamics.binary_clauses = binary;
    m_dynamics.total_clauses = total;
    if (total > 0)
        m_dynamics.binary_clause_ratio = static_cast<float>(binary) / static_cast<float>(total);
    else
        m_dynamics.binary_clause_ratio = 0.0f;
}

// -----------------------------------------------------------------------
// Causal response signals (for SPSA gradient estimation)
// -----------------------------------------------------------------------

// A3: Phase flip detection.  Called on each decision.
void landscape_map::dynamics_on_phase_flip(bool flipped) {
    m_dynamics.decisions_this_interval++;
    if (flipped)
        m_dynamics.phase_flip_count++;
}

// A4: Activity Gini coefficient.  Histogram-based O(N) with sampling.
void landscape_map::dynamics_compute_activity_gini(double const* activity, unsigned num_vars) {
    if (num_vars < 2) return;
    // Bucket activities into 256 bins (log scale).
    // Find max first, then bin relative to max.
    double max_act = 0.0;
    unsigned step = 1;
    if (num_vars > 8192) step = num_vars / 8192;
    for (unsigned v = 0; v < num_vars; v += step) {
        if (activity[v] > max_act) max_act = activity[v];
    }
    if (max_act < 1e-12) {
        m_dynamics.activity_concentration = 0.0f;
        return;
    }
    unsigned hist[256];
    memset(hist, 0, sizeof(hist));
    double inv_max = 255.0 / max_act;
    unsigned n_sampled = 0;
    for (unsigned v = 0; v < num_vars; v += step) {
        unsigned bin = static_cast<unsigned>(activity[v] * inv_max);
        if (bin > 255) bin = 255;
        hist[bin]++;
        n_sampled++;
    }
    // Compute Gini from sorted histogram (bins already in order).
    uint64_t total = 0, weighted = 0;
    unsigned rank = 0;
    for (unsigned b = 0; b < 256; ++b) {
        unsigned cnt = hist[b];
        if (cnt == 0) continue;
        for (unsigned j = 0; j < cnt; ++j) {
            rank++;
            total += b;
            weighted += static_cast<uint64_t>(rank) * b;
        }
    }
    if (total == 0) {
        m_dynamics.activity_concentration = 0.0f;
        return;
    }
    double gini = (2.0 * weighted) / (rank * static_cast<double>(total)) - (rank + 1.0) / rank;
    if (gini < 0.0) gini = 0.0;
    if (gini > 1.0) gini = 1.0;
    // EMA alpha=0.1
    m_dynamics.activity_concentration =
        0.9f * m_dynamics.activity_concentration + 0.1f * static_cast<float>(gini);
}

// B1: Fingerprint hit rate.  Called at LANDSCAPE dump with absolute counters.
void landscape_map::dynamics_update_fp_hit_rate(unsigned fp_hits, unsigned fp_misses) {
    unsigned delta_hits = fp_hits - m_dynamics.prev_fp_hits;
    unsigned delta_misses = fp_misses - m_dynamics.prev_fp_misses;
    unsigned total = delta_hits + delta_misses;
    if (total > 0) {
        float rate = static_cast<float>(delta_hits) / static_cast<float>(total);
        // EMA alpha=0.05
        m_dynamics.fp_hit_rate = 0.95f * m_dynamics.fp_hit_rate + 0.05f * rate;
    }
    m_dynamics.prev_fp_hits = fp_hits;
    m_dynamics.prev_fp_misses = fp_misses;
}

// B2: First-time variable decision.
void landscape_map::dynamics_on_first_decision() {
    m_dynamics.first_time_decisions++;
}

// B3: High stress count — incremental crossing detection.
void landscape_map::dynamics_stress_crossed_up() {
    m_dynamics.high_stress_count++;
}

void landscape_map::dynamics_stress_crossed_down() {
    if (m_dynamics.high_stress_count > 0)
        m_dynamics.high_stress_count--;
}

// C1: Trail stability.
void landscape_map::dynamics_update_trail_stability(float stability) {
    // EMA alpha=0.1
    m_dynamics.trail_stability = 0.9f * m_dynamics.trail_stability + 0.1f * stability;
}

// C2: Theory lemma counter.
void landscape_map::dynamics_on_theory_lemma() {
    m_dynamics.theory_lemma_count++;
}

// Batch update for rate signals at LANDSCAPE dump time.
void landscape_map::dynamics_update_rates(unsigned qi_inserts, unsigned decisions,
                                           unsigned theory_lemmas, double stress_gini) {
    // A1: QI instance rate = delta_inserts / max(delta_decisions, 1) * 1000
    unsigned delta_qi = qi_inserts - m_dynamics.prev_qi_inserts;
    unsigned delta_dec = decisions - m_dynamics.prev_decisions;
    if (delta_dec > 0) {
        float rate = static_cast<float>(delta_qi) / static_cast<float>(delta_dec) * 1000.0f;
        // EMA alpha=0.1
        m_dynamics.qi_instance_rate = 0.9f * m_dynamics.qi_instance_rate + 0.1f * rate;
    }

    // A3: Phase flip rate = phase_flip_count / decisions_this_interval
    if (m_dynamics.decisions_this_interval > 0) {
        float rate = static_cast<float>(m_dynamics.phase_flip_count) /
                     static_cast<float>(m_dynamics.decisions_this_interval);
        // EMA alpha=0.05
        m_dynamics.phase_flip_rate = 0.95f * m_dynamics.phase_flip_rate + 0.05f * rate;
    }

    // B2: New variable rate = first_time_decisions / decisions_this_interval
    if (m_dynamics.decisions_this_interval > 0) {
        float rate = static_cast<float>(m_dynamics.first_time_decisions) /
                     static_cast<float>(m_dynamics.decisions_this_interval);
        // EMA alpha=0.1
        m_dynamics.new_variable_rate = 0.9f * m_dynamics.new_variable_rate + 0.1f * rate;
    }

    // B4: Stress Gini trend = (gini_now - gini_prev) / interval
    float gini_now = static_cast<float>(stress_gini);
    if (m_dynamics.prev_stress_gini > 0.0f || gini_now > 0.0f) {
        float delta = gini_now - m_dynamics.prev_stress_gini;
        // EMA alpha=0.1
        m_dynamics.stress_gini_trend = 0.9f * m_dynamics.stress_gini_trend + 0.1f * delta;
    }
    m_dynamics.prev_stress_gini = gini_now;

    // C2: Theory lemma rate = delta_lemmas / max(delta_decisions, 1) * 1000
    unsigned delta_th = theory_lemmas - m_dynamics.prev_theory_lemmas;
    if (delta_dec > 0) {
        float rate = static_cast<float>(delta_th) / static_cast<float>(delta_dec) * 1000.0f;
        // EMA alpha=0.1
        m_dynamics.theory_lemma_rate = 0.9f * m_dynamics.theory_lemma_rate + 0.1f * rate;
    }

    // Update snapshots
    m_dynamics.prev_qi_inserts = qi_inserts;
    m_dynamics.prev_decisions = decisions;
    m_dynamics.prev_theory_lemmas = theory_lemmas;

    // Reset per-interval counters
    m_dynamics.phase_flip_count = 0;
    m_dynamics.decisions_this_interval = 0;
    m_dynamics.first_time_decisions = 0;
}

// C3: QI E-graph growth — just forward from existing egraph_metrics.
void landscape_map::dynamics_update_qi_egraph_growth(float growth_rate_ema) {
    m_dynamics.qi_egraph_growth = growth_rate_ema;
}

// C4: Agility — snapshot from solver.
void landscape_map::dynamics_update_agility(float agility) {
    m_dynamics.agility = agility;
}

// -----------------------------------------------------------------------
// Efficiency signals (E1-E4)
// -----------------------------------------------------------------------

// E1: Wasted work rate — EMA of decisions undone per conflict.
void landscape_map::dynamics_on_wasted_work(unsigned conflict_level, unsigned backjump_level) {
    float waste = (conflict_level > backjump_level)
                ? static_cast<float>(conflict_level - backjump_level)
                : 0.0f;
    constexpr float ALPHA = 0.02f;  // slow EMA — individual conflicts are noisy
    m_dynamics.wasted_work_rate = (1.0f - ALPHA) * m_dynamics.wasted_work_rate + ALPHA * waste;
}

// E2: Learned clause velocity — fraction of conflict antecedents that are learned.
// Called once per antecedent clause during the FUIP walk or post-conflict scan.
void landscape_map::dynamics_on_antecedent_clause(bool is_learned) {
    m_dynamics.velocity_total_num++;
    if (is_learned)
        m_dynamics.velocity_learned_num++;
    // Update EMA every 250 antecedents (batch to reduce float ops)
    if (m_dynamics.velocity_total_num >= 250) {
        float ratio = static_cast<float>(m_dynamics.velocity_learned_num)
                    / static_cast<float>(m_dynamics.velocity_total_num);
        constexpr float ALPHA = 0.05f;
        m_dynamics.learned_clause_velocity =
            (1.0f - ALPHA) * m_dynamics.learned_clause_velocity + ALPHA * ratio;
        m_dynamics.velocity_learned_num = 0;
        m_dynamics.velocity_total_num   = 0;
    }
}

// E3: Propagation-phase alignment — fraction of propagated literals matching phase cache.
// Called on sampled propagations (every 64th).
void landscape_map::dynamics_on_prop_alignment(bool matched) {
    m_dynamics.alignment_total_count++;
    if (matched)
        m_dynamics.alignment_match_count++;
    // Update EMA every 256 samples
    if (m_dynamics.alignment_total_count >= 256) {
        float ratio = static_cast<float>(m_dynamics.alignment_match_count)
                    / static_cast<float>(m_dynamics.alignment_total_count);
        constexpr float ALPHA = 0.02f;  // slow — alignment changes gradually
        m_dynamics.prop_phase_alignment =
            (1.0f - ALPHA) * m_dynamics.prop_phase_alignment + ALPHA * ratio;
        m_dynamics.alignment_match_count = 0;
        m_dynamics.alignment_total_count = 0;
    }
}

// E4: Conflict clause novelty — Jaccard novelty between consecutive conflict signatures.
// Uses a cheap 64-bit Bloom signature: each variable sets bit (var & 63).
void landscape_map::dynamics_on_conflict_novelty(unsigned num_lits, unsigned const* lit_vars) {
    uint64_t sig = 0;
    for (unsigned i = 0; i < num_lits; ++i)
        sig |= (1ULL << (lit_vars[i] & 63));
    if (m_dynamics.prev_conflict_sig != 0) {
        uint64_t both   = sig & m_dynamics.prev_conflict_sig;
        uint64_t either = sig | m_dynamics.prev_conflict_sig;
        unsigned overlap_bits = static_cast<unsigned>(__builtin_popcountll(both));
        unsigned total_bits   = static_cast<unsigned>(__builtin_popcountll(either));
        float novelty = (total_bits > 0)
                       ? 1.0f - static_cast<float>(overlap_bits) / static_cast<float>(total_bits)
                       : 1.0f;
        constexpr float ALPHA = 0.1f;  // moderate — changes at restart timescale
        m_dynamics.conflict_novelty =
            (1.0f - ALPHA) * m_dynamics.conflict_novelty + ALPHA * novelty;
    }
    m_dynamics.prev_conflict_sig = sig;
}

// -----------------------------------------------------------------------
// Aggregate snapshot (extended)
// -----------------------------------------------------------------------

landscape_map::health_snapshot landscape_map::snapshot(unsigned num_vars) const {
    health_snapshot s;
    s.avg_stress           = avg_stress();
    s.stress_concentration = stress_concentration();
    s.coverage             = coverage_fraction();
    s.unique_regions       = m_expanded_regions ? m_expanded_unique : m_unique_regions;
    s.region_diversity     = region_diversity();
    s.total_conflicts      = m_total_conflicts;
    s.total_decisions      = m_total_decisions;

    // New fields
    s.max_fanout_var       = 0;
    s.avg_fanout           = 0.0;
    s.conflict_recurrence  = 0.0;

    if (m_var_profiles) {
        uint16_t max_fo = 0;
        double sum_fo = 0.0;
        unsigned count_fo = 0;
        unsigned limit = num_vars < m_var_profiles_cap ? num_vars : m_var_profiles_cap;
        for (unsigned v = 0; v < limit; ++v) {
            uint16_t fo = std::max(m_var_profiles[v].avg_fanout_true,
                                   m_var_profiles[v].avg_fanout_false);
            if (fo > max_fo) {
                max_fo = fo;
                s.max_fanout_var = v;
            }
            if (m_var_profiles[v].decisions_true + m_var_profiles[v].decisions_false > 0) {
                sum_fo += fo;
                count_fo++;
            }
        }
        if (count_fo > 0)
            s.avg_fanout = sum_fo / count_fo;
    }

    if (m_conflict_history)
        s.conflict_recurrence = conflict_recurrence_rate(1000);

    return s;
}

// -----------------------------------------------------------------------
// Debug / trace
// -----------------------------------------------------------------------

void landscape_map::dump_to_stream(std::ostream& out, unsigned num_vars) const {
    out << "=== LANDSCAPE MAP (DEEP) ===\n";
    out << "Conflicts: " << m_total_conflicts
        << ", Decisions: " << m_total_decisions
        << ", Restarts: " << m_total_restarts << "\n";

    // Stress
    double avg = avg_stress();
    double gini = stress_concentration();
    uint8_t max_stress = 0;
    unsigned sz = m_lit_stress.size();
    const uint8_t* p = m_lit_stress.data();
    for (unsigned i = 0; i < sz; ++i) {
        if (p[i] > max_stress)
            max_stress = p[i];
    }
    out << "Literal Stress: avg=" << avg << ", max=" << (max_stress / 255.0)
        << ", gini=" << gini << "\n";

    // Top 10 stressed literals
    {
        struct entry { unsigned lit; uint8_t stress; };
        entry top[10];
        unsigned top_n = 0;
        for (unsigned i = 0; i < sz; ++i) {
            if (p[i] == 0) continue;
            if (top_n < 10) {
                top[top_n++] = {i, p[i]};
            } else {
                unsigned min_idx = 0;
                for (unsigned k = 1; k < 10; ++k)
                    if (top[k].stress < top[min_idx].stress) min_idx = k;
                if (p[i] > top[min_idx].stress)
                    top[min_idx] = {i, p[i]};
            }
        }
        for (unsigned i = 0; i < top_n; ++i)
            for (unsigned j = i + 1; j < top_n; ++j)
                if (top[j].stress > top[i].stress) std::swap(top[i], top[j]);
        out << "  Top stressed:";
        for (unsigned i = 0; i < top_n; ++i)
            out << " lit#" << top[i].lit << "(" << (top[i].stress / 255.0) << ")";
        out << "\n";
    }

    // Coverage
    double cov = coverage_fraction();
    out << "Coverage: " << (cov * 100.0) << "% ("
        << m_vars_explored << " / " << m_decisions_true.size() << " vars explored)\n";

    // Regions
    unsigned unique = m_expanded_regions ? m_expanded_unique : m_unique_regions;
    out << "Regions: " << unique << " unique / "
        << m_total_restarts << " restarts (diversity=" << region_diversity() << ")\n";

    // Tier 1b: Variable profile summary
    if (m_var_profiles) {
        uint16_t max_fo = 0;
        unsigned max_fo_var = 0;
        unsigned limit = num_vars < m_var_profiles_cap ? num_vars : m_var_profiles_cap;
        for (unsigned v = 0; v < limit; ++v) {
            uint16_t fo = std::max(m_var_profiles[v].avg_fanout_true,
                                   m_var_profiles[v].avg_fanout_false);
            if (fo > max_fo) { max_fo = fo; max_fo_var = v; }
        }
        out << "Max fanout var: " << max_fo_var << " (avg_fanout=" << max_fo << ")\n";
    }

    // Tier 2b: Conflict history summary
    if (m_conflict_history) {
        out << "Conflict history: " << m_conflict_history_count << " records, "
            << "recurrence=" << conflict_recurrence_rate(1000) << "\n";
    }

    // Bloom filter fill ratio
    {
        unsigned bits_set = 0;
        for (unsigned i = 0; i < BLOOM_BYTES; ++i) {
            unsigned b = m_conflict_pairs[i];
            b = b - ((b >> 1) & 0x55);
            b = (b & 0x33) + ((b >> 2) & 0x33);
            bits_set += (b + (b >> 4)) & 0x0F;
        }
        out << "Conflict pairs: Bloom filter "
            << (100.0 * bits_set / BLOOM_BITS) << "% full ("
            << bits_set << " / " << BLOOM_BITS << " bits set)\n";
    }
}

void landscape_map::dump_to_alog(FILE* alog, unsigned num_conflicts, unsigned num_vars) const {
    if (!alog) return;

    // Build top-10 stressed literals array as raw JSON
    char top_stressed_buf[512];
    int pos = 0;
    pos += snprintf(top_stressed_buf + pos, sizeof(top_stressed_buf) - pos, "[");

    {
        struct entry { unsigned lit; uint8_t stress; };
        entry top[10];
        unsigned top_n = 0;
        unsigned sz = m_lit_stress.size();
        const uint8_t* p = m_lit_stress.data();
        for (unsigned i = 0; i < sz; ++i) {
            if (p[i] == 0) continue;
            if (top_n < 10) {
                top[top_n++] = {i, p[i]};
            } else {
                unsigned min_idx = 0;
                for (unsigned k = 1; k < 10; ++k)
                    if (top[k].stress < top[min_idx].stress) min_idx = k;
                if (p[i] > top[min_idx].stress)
                    top[min_idx] = {i, p[i]};
            }
        }
        for (unsigned i = 0; i < top_n; ++i)
            for (unsigned j = i + 1; j < top_n; ++j)
                if (top[j].stress > top[i].stress) std::swap(top[i], top[j]);
        for (unsigned i = 0; i < top_n; ++i) {
            if (i > 0) pos += snprintf(top_stressed_buf + pos, sizeof(top_stressed_buf) - pos, ",");
            pos += snprintf(top_stressed_buf + pos, sizeof(top_stressed_buf) - pos,
                            "{\"lit\":%u,\"s\":%.2f}", top[i].lit, top[i].stress / 255.0);
        }
    }
    snprintf(top_stressed_buf + pos, sizeof(top_stressed_buf) - pos, "]");

    unsigned unexplored = most_unexplored_var(num_vars);

    // Compute new aggregate fields
    unsigned max_fanout_var = 0;
    double avg_fanout = 0.0;
    if (m_var_profiles) {
        uint16_t max_fo = 0;
        double sum_fo = 0.0;
        unsigned count_fo = 0;
        unsigned limit = num_vars < m_var_profiles_cap ? num_vars : m_var_profiles_cap;
        for (unsigned v = 0; v < limit; ++v) {
            uint16_t fo = std::max(m_var_profiles[v].avg_fanout_true,
                                   m_var_profiles[v].avg_fanout_false);
            if (fo > max_fo) { max_fo = fo; max_fanout_var = v; }
            if (m_var_profiles[v].decisions_true + m_var_profiles[v].decisions_false > 0) {
                sum_fo += fo;
                count_fo++;
            }
        }
        if (count_fo > 0) avg_fanout = sum_fo / count_fo;
    }

    double recurrence = m_conflict_history ? conflict_recurrence_rate(1000) : 0.0;
    unsigned unique = m_expanded_regions ? m_expanded_unique : m_unique_regions;

    // Compute dynamics phase time percentages (safe against div-by-zero)
    double time_bcp_pct = 0, time_decide_pct = 0, time_conflict_pct = 0,
           time_theory_pct = 0, time_qi_pct = 0;
    if (m_dynamics.cycles_total > 0) {
        double inv = 100.0 / static_cast<double>(m_dynamics.cycles_total);
        time_bcp_pct      = static_cast<double>(m_dynamics.cycles_bcp) * inv;
        time_decide_pct   = static_cast<double>(m_dynamics.cycles_decide) * inv;
        time_conflict_pct = static_cast<double>(m_dynamics.cycles_conflict) * inv;
        time_theory_pct   = static_cast<double>(m_dynamics.cycles_theory) * inv;
        time_qi_pct       = static_cast<double>(m_dynamics.cycles_qi) * inv;
    }
    // Reversal rate
    double reversal_rate = 0.0;
    if (m_dynamics.reversal_window > 0)
        reversal_rate = static_cast<double>(m_dynamics.total_reversals) / m_dynamics.reversal_window;

    ALOG(alog, "LANDSCAPE")
        .u("c", num_conflicts)
        .d("stress_avg", avg_stress())
        .d("stress_gini", stress_concentration())
        .d("coverage", coverage_fraction())
        .u("regions", unique)
        .d("diversity", region_diversity())
        .raw("top_stressed", top_stressed_buf)
        .u("unexplored", unexplored)
        .u("max_fanout_var", max_fanout_var)
        .d("avg_fanout", avg_fanout)
        .d("conflict_recurrence", recurrence)
        .u("conflict_history_n", m_conflict_history_count)
        // Dynamics: phase time breakdown (datapoints 1-5)
        .d("time_bcp_pct", time_bcp_pct)
        .d("time_decide_pct", time_decide_pct)
        .d("time_conflict_pct", time_conflict_pct)
        .d("time_theory_pct", time_theory_pct)
        .d("time_qi_pct", time_qi_pct)
        // Dynamics: BCP quality (6)
        .d("prop_chain", static_cast<double>(m_dynamics.avg_prop_chain_length))
        // Dynamics: decision quality (7-9)
        .d("reversals", reversal_rate)
        .d("conflict_density", static_cast<double>(m_dynamics.avg_conflict_density))
        .d("conflict_level", static_cast<double>(m_dynamics.avg_conflict_level))
        // Dynamics: learning quality (10-13)
        .d("learned_size", static_cast<double>(m_dynamics.avg_learned_size))
        .d("glue", static_cast<double>(m_dynamics.avg_glue))
        .d("early_use", static_cast<double>(m_dynamics.clause_early_use_rate))
        .d("gc_survival", static_cast<double>(m_dynamics.gc_survival_rate))
        // Dynamics: search structure (14-16)
        .d("backjump_frac", static_cast<double>(m_dynamics.avg_backjump_frac))
        .d("restart_interval", static_cast<double>(m_dynamics.avg_restart_interval))
        .d("branching_factor", static_cast<double>(m_dynamics.avg_branching_factor))
        // Dynamics: theory engagement (17-18)
        .d("theory_conflict_frac", static_cast<double>(m_dynamics.theory_conflict_frac))
        .d("theory_prop_density", static_cast<double>(m_dynamics.theory_prop_density))
        // Dynamics: problem structure (19-20)
        .d("binary_ratio", static_cast<double>(m_dynamics.binary_clause_ratio))
        .d("burstiness", static_cast<double>(m_dynamics.conflict_burstiness))
        // Causal response signals (A1-A4, B1-B4, C1-C4)
        .d("qi_inst_rate", static_cast<double>(m_dynamics.qi_instance_rate))
        .d("restart_int", static_cast<double>(m_dynamics.actual_restart_interval))
        .d("phase_flip", static_cast<double>(m_dynamics.phase_flip_rate))
        .d("activity_gini", static_cast<double>(m_dynamics.activity_concentration))
        .d("fp_hit", static_cast<double>(m_dynamics.fp_hit_rate))
        .d("new_var_rate", static_cast<double>(m_dynamics.new_variable_rate))
        .u("high_stress_n", m_dynamics.high_stress_count)
        .d("gini_trend", static_cast<double>(m_dynamics.stress_gini_trend))
        .d("trail_stab", static_cast<double>(m_dynamics.trail_stability))
        .d("th_lemma_rate", static_cast<double>(m_dynamics.theory_lemma_rate))
        .d("qi_egraph_gr", static_cast<double>(m_dynamics.qi_egraph_growth))
        .d("agility_val", static_cast<double>(m_dynamics.agility))
        // Efficiency signals (E1-E4)
        .d("wasted_work", static_cast<double>(m_dynamics.wasted_work_rate))
        .d("clause_velocity", static_cast<double>(m_dynamics.learned_clause_velocity))
        .d("prop_align", static_cast<double>(m_dynamics.prop_phase_alignment))
        .d("conflict_novelty", static_cast<double>(m_dynamics.conflict_novelty));
}

} // namespace smt
