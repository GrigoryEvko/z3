/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    smt_landscape.cpp

Abstract:

    Landscape map implementation.  See smt_landscape.h for design overview.

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

void landscape_map::init_search() {
    // Per-search counters reset.  The map itself persists across searches
    // so that cross-search spatial awareness is maintained.
    m_total_conflicts       = 0;
    m_total_decisions       = 0;
    m_conflicts_since_decay = 0;
    m_total_restarts        = 0;
    // NOTE: m_lit_stress, m_decisions_*, m_region_*, m_conflict_pairs
    // are intentionally NOT reset — they accumulate across check-sat calls.
}

void landscape_map::reset() {
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
}

// -----------------------------------------------------------------------
// Layer 1: Literal stress
// -----------------------------------------------------------------------

void landscape_map::ensure_literal(unsigned lit_idx) {
    if (lit_idx >= m_lit_stress.size())
        m_lit_stress.resize(lit_idx + 1, 0);
}

void landscape_map::on_conflict_antecedent(unsigned lit_idx) {
    ensure_literal(lit_idx);
    // EMA bump: stress = 0.95 * stress + 0.05 * 255
    // In uint8_t arithmetic:  new = old - (old >> 4) + (255 >> 4)
    //   ~= old * 0.9375 + 15.9375
    // This slightly differs from exact 0.95/0.05 but avoids float.
    unsigned old = m_lit_stress[lit_idx];
    unsigned bumped = old - (old >> 4) + 16;
    m_lit_stress[lit_idx] = static_cast<uint8_t>(bumped > 255 ? 255 : bumped);
}

void landscape_map::decay_stress() {
    // Called every 1000 conflicts.  Multiplicative decay: stress *= 0.99
    // In uint8_t: new = old - (old / 128) ≈ old * 0.992
    // Close enough; exact 0.99 would need float per entry.
    unsigned sz = m_lit_stress.size();
    uint8_t* p = m_lit_stress.data();
    for (unsigned i = 0; i < sz; ++i) {
        unsigned v = p[i];
        p[i] = static_cast<uint8_t>(v - (v >> 7));
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
    // Gini coefficient of the stress distribution.
    // For large arrays, we sample up to 4096 entries.
    unsigned sz = m_lit_stress.size();
    if (sz < 2) return 0.0;

    unsigned step = 1;
    unsigned n = sz;
    if (sz > 4096) {
        step = sz / 4096;
        n = 4096;
    }

    // Compute Gini via the sorted formula:
    // G = (2 * sum_i(i * x_i)) / (n * sum_i(x_i)) - (n+1)/n
    // We avoid a full sort by using a histogram (values are 0..255).
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
// Layer 2: Variable coverage
// -----------------------------------------------------------------------

void landscape_map::ensure_var(unsigned var) {
    if (var >= m_decisions_true.size()) {
        m_decisions_true.resize(var + 1, 0);
        m_decisions_false.resize(var + 1, 0);
    }
}

void landscape_map::on_decision(unsigned var, bool is_true) {
    ensure_var(var);
    m_total_decisions++;
    if (is_true) {
        uint16_t old = m_decisions_true[var];
        if (old == 0 && m_decisions_false[var] == 0)
            m_vars_explored++;
        if (old < 65535)
            m_decisions_true[var] = old + 1;
    } else {
        uint16_t old = m_decisions_false[var];
        if (old == 0 && m_decisions_true[var] == 0)
            m_vars_explored++;
        if (old < 65535)
            m_decisions_false[var] = old + 1;
    }
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
            if (t == 0) break;  // can't do better than zero
        }
    }
    // If num_vars > what we've tracked, those vars have 0 decisions.
    if (limit < num_vars && best_total > 0)
        best_var = limit;
    return best_var;
}

// -----------------------------------------------------------------------
// Layer 3: Region fingerprints
// -----------------------------------------------------------------------

unsigned landscape_map::region_slot(uint64_t key) const {
    // Open-addressing: primary slot from upper bits
    return static_cast<unsigned>(fmix64(key) >> 54) & (REGION_MAP_SIZE - 1);
}

unsigned landscape_map::region_find(uint64_t key) const {
    unsigned slot = region_slot(key);
    for (unsigned probe = 0; probe < REGION_MAP_SIZE; ++probe) {
        unsigned idx = (slot + probe) & (REGION_MAP_SIZE - 1);
        if (!m_region_occupied[idx])
            return REGION_MAP_SIZE;  // not found
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
            // Empty slot — insert here
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
            // Found — update
            region_record& r = m_region_vals[idx];
            if (r.visits < 65535) r.visits++;
            r.avg_health = 0.8f * r.avg_health + 0.2f * health;
            if (health > r.best_health) r.best_health = health;
            r.last_visit = m_total_restarts;
            return idx;
        }

        // Track LRU candidate for eviction
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
    // unique_regions stays the same (evicted one, inserted one)
    return oldest_slot;
}

void landscape_map::on_restart(uint64_t phase_hash, float health) {
    m_total_restarts++;
    region_insert_or_update(phase_hash, health);
}

unsigned landscape_map::region_visit_count(uint64_t phase_hash) const {
    unsigned idx = region_find(phase_hash);
    return idx < REGION_MAP_SIZE ? m_region_vals[idx].visits : 0;
}

float landscape_map::region_best_health(uint64_t phase_hash) const {
    unsigned idx = region_find(phase_hash);
    return idx < REGION_MAP_SIZE ? m_region_vals[idx].best_health : 0.0f;
}

double landscape_map::region_diversity() const {
    if (m_total_restarts == 0) return 0.0;
    return static_cast<double>(m_unique_regions) / m_total_restarts;
}

// -----------------------------------------------------------------------
// Layer 4: Conflict variable pairs (Bloom filter)
// -----------------------------------------------------------------------

void landscape_map::bloom_hashes(unsigned v1, unsigned v2, unsigned& h0, unsigned& h1, unsigned& h2) {
    // Canonical ordering
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
    // Mark pairs of the top-8 variables (by input order, which is
    // already sorted by activity in the FUIP lemma).
    unsigned top = num_vars < 8 ? num_vars : 8;
    for (unsigned i = 0; i < top; ++i) {
        for (unsigned j = i + 1; j < top; ++j) {
            bloom_set(vars[i], vars[j]);
        }
    }
}

double landscape_map::conflict_affinity(unsigned var, unsigned const* assigned_vars, unsigned num_assigned) const {
    if (num_assigned == 0) return 0.0;
    unsigned hits = 0;
    unsigned check = num_assigned < 32 ? num_assigned : 32;  // cap to avoid O(n) scan
    for (unsigned i = 0; i < check; ++i) {
        if (bloom_test(var, assigned_vars[i]))
            hits++;
    }
    return static_cast<double>(hits) / check;
}

// -----------------------------------------------------------------------
// Aggregate snapshot
// -----------------------------------------------------------------------

landscape_map::health_snapshot landscape_map::snapshot(unsigned num_vars) const {
    health_snapshot s;
    s.avg_stress           = avg_stress();
    s.stress_concentration = stress_concentration();
    s.coverage             = coverage_fraction();
    s.unique_regions       = m_unique_regions;
    s.region_diversity     = region_diversity();
    s.total_conflicts      = m_total_conflicts;
    s.total_decisions      = m_total_decisions;
    return s;
}

// -----------------------------------------------------------------------
// Debug / trace
// -----------------------------------------------------------------------

void landscape_map::dump_to_stream(std::ostream& out, unsigned num_vars) const {
    out << "=== LANDSCAPE MAP ===\n";
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
        // Collect top-10 via partial selection
        struct entry { unsigned lit; uint8_t stress; };
        entry top[10];
        unsigned top_n = 0;
        for (unsigned i = 0; i < sz; ++i) {
            if (p[i] == 0) continue;
            if (top_n < 10) {
                top[top_n++] = {i, p[i]};
            } else {
                // Find min in top
                unsigned min_idx = 0;
                for (unsigned k = 1; k < 10; ++k)
                    if (top[k].stress < top[min_idx].stress) min_idx = k;
                if (p[i] > top[min_idx].stress)
                    top[min_idx] = {i, p[i]};
            }
        }
        // Sort descending
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

    // Top 10 least explored
    {
        struct entry { unsigned var; unsigned total; };
        entry least[10];
        unsigned least_n = 0;
        unsigned limit = std::min(num_vars, static_cast<unsigned>(m_decisions_true.size()));
        for (unsigned v = 0; v < limit && least_n < 10; ++v) {
            unsigned t = static_cast<unsigned>(m_decisions_true[v]) + m_decisions_false[v];
            if (t == 0) {
                least[least_n++] = {v, 0};
            }
        }
        if (least_n < 10) {
            // Fill with lowest non-zero
            for (unsigned v = 0; v < limit && least_n < 10; ++v) {
                unsigned t = static_cast<unsigned>(m_decisions_true[v]) + m_decisions_false[v];
                if (t > 0) least[least_n++] = {v, t};
            }
        }
        out << "  Least explored:";
        for (unsigned i = 0; i < least_n; ++i)
            out << " var#" << least[i].var << "(" << least[i].total << ")";
        out << "\n";
    }

    // Regions
    out << "Regions: " << m_unique_regions << " unique / "
        << m_total_restarts << " restarts (diversity=" << region_diversity() << ")\n";
    {
        float best = 0.0f;
        uint64_t best_key = 0;
        unsigned best_visits = 0;
        for (unsigned i = 0; i < REGION_MAP_SIZE; ++i) {
            if (m_region_occupied[i] && m_region_vals[i].best_health > best) {
                best = m_region_vals[i].best_health;
                best_key = m_region_keys[i];
                best_visits = m_region_vals[i].visits;
            }
        }
        if (best > 0.0f) {
            char buf[32];
            snprintf(buf, sizeof(buf), "0x%016" PRIx64, static_cast<uint64_t>(best_key));
            out << "  Best region: hash=" << buf
                << " health=" << best << " visits=" << best_visits << "\n";
        }
    }

    // Bloom filter fill ratio
    {
        unsigned bits_set = 0;
        for (unsigned i = 0; i < BLOOM_BYTES; ++i) {
            // popcount byte
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
        // Sort descending
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

    ALOG(alog, "LANDSCAPE")
        .u("c", num_conflicts)
        .d("stress_avg", avg_stress())
        .d("stress_gini", stress_concentration())
        .d("coverage", coverage_fraction())
        .u("regions", m_unique_regions)
        .d("diversity", region_diversity())
        .raw("top_stressed", top_stressed_buf)
        .u("unexplored", unexplored);
}

} // namespace smt
