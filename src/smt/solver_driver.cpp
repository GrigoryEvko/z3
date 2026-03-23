/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    solver_driver.cpp

Abstract:

    Adaptive solver driver implementation.
    See solver_driver.h and solver_driver_design.md for architecture.

Author:

    Z3 contributors

--*/

#include "smt/solver_driver.h"
#include "smt/smt_context.h"
#include "smt/adaptive_log.h"

namespace smt {

// Parameter metadata table: matches the 8 parameters in design doc Section 4.1.
// Order must match the params struct field order.
const solver_driver::param_meta solver_driver::s_meta[N_PARAMS] = {
    // qi_eager_threshold:    [0.5, 100],  default 7.0,  log-space
    { 0.5, 100.0, 7.0, true },
    // qi_surprisal_scale:    [0.5, 3.0],  default 1.0,  log-space
    { 0.5, 3.0, 1.0, true },
    // restart_margin_scale:  [0.3, 5.0],  default 1.0,  log-space
    { 0.3, 5.0, 1.0, true },
    // activity_decay_scale:  [0.95, 1.05], default 1.0, linear (narrow range)
    { 0.95, 1.05, 1.0, false },
    // phase_noise:           [0.0, 0.20], default 0.0,  linear
    { 0.0, 0.20, 0.0, false },
    // relevancy_probability: [0.0, 1.0],  default 1.0,  linear
    { 0.0, 1.0, 1.0, false },
    // mbqi_probability:      [0.0, 1.0],  default 0.0,  linear
    { 0.0, 1.0, 0.0, false },
    // gc_aggressiveness:     [0.5, 2.0],  default 1.0,  log-space
    { 0.5, 2.0, 1.0, true },
};

solver_driver::solver_driver() {
    reset_to_defaults();
}

void solver_driver::reset_to_defaults() {
    // Parameters to defaults.
    m_params.qi_eager_threshold    = s_meta[0].default_val;
    m_params.qi_surprisal_scale    = s_meta[1].default_val;
    m_params.restart_margin_scale  = s_meta[2].default_val;
    m_params.activity_decay_scale  = s_meta[3].default_val;
    m_params.phase_noise           = s_meta[4].default_val;
    m_params.relevancy_probability = s_meta[5].default_val;
    m_params.mbqi_probability      = s_meta[6].default_val;
    m_params.gc_aggressiveness     = s_meta[7].default_val;

    // SPSA state.
    memset(m_adam_m1, 0, sizeof(m_adam_m1));
    memset(m_adam_m2, 0, sizeof(m_adam_m2));
    memset(m_delta, 0, sizeof(m_delta));

    // Temperature state.
    m_H_fast   = 0.0;
    m_H_slow   = 0.0;
    m_macd_m1  = 0.0;
    m_macd_m2  = 1e-4;  // init nonzero to avoid /0 in first update
    m_T        = 0.5;
    m_H_prev   = 0.0;

    // Internal glue EMAs.
    m_glue_fast = 0.0;
    m_glue_slow = 0.0;

    // Baselines (will be properly captured at init_search).
    m_base_restart_agility = 0.18;
    m_base_inv_decay       = 1.052;
    m_base_gc_factor       = 1.1;
    m_base_qi_eager        = 7.0;

    // Counters.
    m_total_decisions       = 0;
    m_total_conflicts       = 0;
    m_update_count          = 0;
    m_spsa_step_count       = 0;
    m_decisions_since_update = 0;
    m_conflicts_since_update = 0;

    // Safety.
    m_frozen           = false;
    m_consecutive_good = 0;

    // Warmup.
    m_warmup_cycle = 0;
    m_warmup_done  = false;
    memset(m_warmup_H, 0, sizeof(m_warmup_H));

    // Build warmup configurations (design doc Section 9.1).
    // Cycle 0: defaults (already set above, snapshot at init_search).
    for (unsigned i = 0; i < WARMUP_CYCLES; i++) {
        m_warmup_configs[i].qi_eager_threshold    = s_meta[0].default_val;
        m_warmup_configs[i].qi_surprisal_scale    = s_meta[1].default_val;
        m_warmup_configs[i].restart_margin_scale  = s_meta[2].default_val;
        m_warmup_configs[i].activity_decay_scale  = s_meta[3].default_val;
        m_warmup_configs[i].phase_noise           = s_meta[4].default_val;
        m_warmup_configs[i].relevancy_probability = s_meta[5].default_val;
        m_warmup_configs[i].mbqi_probability      = s_meta[6].default_val;
        m_warmup_configs[i].gc_aggressiveness     = s_meta[7].default_val;
    }
    // Cycle 1: SAT-seeking.
    m_warmup_configs[1].qi_eager_threshold    = 50.0;
    m_warmup_configs[1].mbqi_probability      = 0.4;
    m_warmup_configs[1].relevancy_probability = 0.3;
    // Cycle 2: UNSAT-seeking.
    m_warmup_configs[2].qi_eager_threshold    = 3.0;
    m_warmup_configs[2].mbqi_probability      = 0.0;
    m_warmup_configs[2].relevancy_probability = 1.0;
    // Cycle 3: QI-throttled.
    m_warmup_configs[3].qi_eager_threshold    = 80.0;
    m_warmup_configs[3].qi_surprisal_scale    = 2.5;
    // Cycle 4: Wide search.
    m_warmup_configs[4].phase_noise           = 0.15;
    m_warmup_configs[4].restart_margin_scale  = 0.5;

    // Scope stack.
    m_scopes.reset();

    // RNG seed.
    m_rng_state = 0x12345678u;
}

void solver_driver::init_search(context& ctx) {
    // Capture baseline solver parameters BEFORE any driver modifications.
    // The driver's scale params multiply these baselines, not hardcoded constants.
    m_base_restart_agility = ctx.get_fparams().m_restart_agility_threshold;
    m_base_inv_decay       = ctx.get_fparams().m_inv_decay;
    m_base_gc_factor       = ctx.get_fparams().m_lemma_gc_factor;
    m_base_qi_eager        = ctx.get_fparams().m_qi_eager_threshold;

    // Check if parameters are non-default (from previous check-sat).
    bool has_non_default = false;
    for (unsigned j = 0; j < N_PARAMS; j++) {
        if (get_param(j) != s_meta[j].default_val) {
            has_non_default = true;
            break;
        }
    }

    // Persist parameters across check-sat calls (the learned config).
    // Persist temperature.
    // Reset everything else for fresh gradient estimation.
    memset(m_adam_m1, 0, sizeof(m_adam_m1));
    memset(m_adam_m2, 0, sizeof(m_adam_m2));
    m_H_fast   = 0.5;  // neutral baseline
    m_H_slow   = 0.5;
    m_macd_m1  = 0.0;
    m_macd_m2  = 1e-4;
    m_H_prev   = 0.0;
    m_glue_fast = 0.0;
    m_glue_slow = 0.0;
    m_update_count          = 0;
    m_spsa_step_count       = 0;
    m_decisions_since_update = 0;
    m_conflicts_since_update = 0;
    m_frozen           = false;
    m_consecutive_good = 0;
    m_total_decisions  = 0;
    m_total_conflicts  = 0;

    // Warmup portfolio is Phase 3 (not yet implemented).
    // For now, SPSA starts from defaults (or persisted config if non-default).
    m_warmup_cycle = WARMUP_CYCLES;
    m_warmup_done  = true;
}

void solver_driver::push() {
    scope_save s;
    s.m_params       = m_params;
    memcpy(s.m_adam_m1, m_adam_m1, sizeof(m_adam_m1));
    memcpy(s.m_adam_m2, m_adam_m2, sizeof(m_adam_m2));
    s.m_H_fast       = m_H_fast;
    s.m_H_slow       = m_H_slow;
    s.m_T            = m_T;
    s.m_macd_m1      = m_macd_m1;
    s.m_macd_m2      = m_macd_m2;
    s.m_update_count = m_update_count;
    s.m_frozen       = m_frozen;
    s.m_warmup_done  = m_warmup_done;
    m_scopes.push_back(s);
}

void solver_driver::pop() {
    if (m_scopes.empty()) return;
    scope_save const& s = m_scopes.back();
    m_params       = s.m_params;
    memcpy(m_adam_m1, s.m_adam_m1, sizeof(m_adam_m1));
    memcpy(m_adam_m2, s.m_adam_m2, sizeof(m_adam_m2));
    m_H_fast       = s.m_H_fast;
    m_H_slow       = s.m_H_slow;
    m_T            = s.m_T;
    m_macd_m1      = s.m_macd_m1;
    m_macd_m2      = s.m_macd_m2;
    m_update_count = s.m_update_count;
    m_frozen       = s.m_frozen;
    m_warmup_done  = s.m_warmup_done;
    m_scopes.pop_back();
}

// ---------------------------------------------------------------
// Health function (design doc Section 2.1, 2.3)
// ---------------------------------------------------------------

double solver_driver::compute_health(context& ctx) {
    auto const& d = ctx.get_landscape().dynamics();
    unsigned decisions = std::max(m_total_decisions, 1u);

    // s1: conflict_rate -- conflicts per decision, normalized so 0.1 = max health.
    double raw_rate = static_cast<double>(m_total_conflicts) / static_cast<double>(decisions);
    double s1 = std::min(raw_rate / 0.1, 1.0);

    // s2: conflict_quality -- relative glue trend (improving = higher health).
    // Maintain fast/slow glue EMAs from the landscape's avg_glue.
    double glue = static_cast<double>(d.avg_glue);
    if (glue > 0.0) {
        m_glue_fast = (1.0 - 0.10) * m_glue_fast + 0.10 * glue;
        m_glue_slow = (1.0 - 0.01) * m_glue_slow + 0.01 * glue;
    }
    double s2 = 0.5;  // neutral if no glue data
    if (m_glue_slow > 0.01) {
        // ratio < 1 means recent glue is lower (better) than historical.
        s2 = std::max(0.0, std::min(1.0, 1.0 - m_glue_fast / m_glue_slow));
    }

    // s3: new_variable_rate -- directly from dynamics.
    double s3 = std::max(0.0, std::min(1.0, static_cast<double>(d.new_variable_rate)));

    // s4: stress_trend -- decreasing stress Gini = positive health.
    double s4 = std::max(0.0, std::min(1.0, -static_cast<double>(d.stress_gini_trend) * 10.0));

    // s5: trail_stability -- directly from dynamics.
    double s5 = std::max(0.0, std::min(1.0, static_cast<double>(d.trail_stability)));

    // s6: fp_hit_rate -- directly from dynamics (0 if no QI).
    double s6 = std::max(0.0, std::min(1.0, static_cast<double>(d.fp_hit_rate)));

    // s7: wasted_work_rate -- lower waste = higher health.
    // At waste=50, health contribution = 0. At waste=0, contribution = 1.
    double wasted = static_cast<double>(d.wasted_work_rate);
    double s7 = std::max(0.0, std::min(1.0, 1.0 - wasted / 50.0));

    // s8: conflict_novelty -- directly from dynamics.
    double s8 = std::max(0.0, std::min(1.0, static_cast<double>(d.conflict_novelty)));

    // Determine which signals are active (N/A signals get weight redistributed).
    bool has_qi   = (d.qi_instance_rate > 0.0f || d.fp_hit_rate > 0.0f);
    bool has_conf = (m_total_conflicts > 10);

    double w1 = W1, w2 = W2, w3 = W3, w4 = W4;
    double w5 = W5, w6 = W6, w7 = W7, w8 = W8;

    // Redistribute N/A signal weights.
    double dead_weight = 0.0;
    if (!has_qi) {
        dead_weight += w6;
        w6 = 0.0;
    }
    if (!has_conf) {
        // s1, s2, s8 are unreliable with < 10 conflicts.
        dead_weight += w1 + w2 + w8;
        w1 = 0.0;
        w2 = 0.0;
        w8 = 0.0;
    }

    // Redistribute proportionally to surviving weights.
    if (dead_weight > 0.0) {
        double alive = w1 + w2 + w3 + w4 + w5 + w6 + w7 + w8;
        if (alive > 0.01) {
            double scale = (alive + dead_weight) / alive;
            w1 *= scale; w2 *= scale; w3 *= scale; w4 *= scale;
            w5 *= scale; w6 *= scale; w7 *= scale; w8 *= scale;
        }
    }

    double H = w1*s1 + w2*s2 + w3*s3 + w4*s4 + w5*s5 + w6*s6 + w7*s7 + w8*s8;

    // Sanity: if health is NaN (all signals broken), return neutral.
    if (std::isnan(H) || std::isinf(H))
        H = 0.5;

    return std::max(0.0, std::min(1.0, H));
}

// ---------------------------------------------------------------
// Temperature dynamics (design doc Section 3)
// ---------------------------------------------------------------

void solver_driver::update_temperature(double H) {
    m_H_fast = (1.0 - H_FAST_ALPHA) * m_H_fast + H_FAST_ALPHA * H;
    m_H_slow = (1.0 - H_SLOW_ALPHA) * m_H_slow + H_SLOW_ALPHA * H;

    double macd = m_H_fast - m_H_slow;

    // Adam-normalize the MACD signal.
    m_macd_m1 = MACD_BETA1 * m_macd_m1 + (1.0 - MACD_BETA1) * macd;
    m_macd_m2 = MACD_BETA2 * m_macd_m2 + (1.0 - MACD_BETA2) * macd * macd;

    double macd_hat = m_macd_m1 / (std::sqrt(m_macd_m2) + ADAM_EPS);

    // Temperature: high when health worsening, low when improving.
    m_T = 0.5 * (1.0 - std::tanh(macd_hat * T_SCALE));
    m_T = std::max(0.05, std::min(0.95, m_T));
}

// ---------------------------------------------------------------
// SPSA gradient estimation (design doc Section 5)
// ---------------------------------------------------------------

void solver_driver::spsa_step(double H, context& /*ctx*/) {
    if (m_update_count % 2 == 0) {
        // PERTURBATION STEP: apply random perturbation, record health.
        generate_perturbation();

        double c_k = PERTURB_C / std::pow(1.0 + m_spsa_step_count, C_DECAY);

        for (unsigned j = 0; j < N_PARAMS; j++) {
            double range = param_range(j);
            double pert = c_k * m_delta[j] * range * m_T;
            double val = get_param(j);

            if (s_meta[j].log_space) {
                val = std::exp(std::log(std::max(val, 1e-10)) + pert);
            } else {
                val += pert;
            }
            val = std::max(s_meta[j].min_val, std::min(s_meta[j].max_val, val));
            set_param(j, val);
        }

        m_H_prev = H;
    } else {
        // GRADIENT STEP: estimate gradient, apply Adam update.
        double dH = H - m_H_prev;
        double c_k = PERTURB_C / std::pow(1.0 + m_spsa_step_count, C_DECAY);

        for (unsigned j = 0; j < N_PARAMS; j++) {
            // SPSA gradient estimate: dH / (2 * c_k * delta[j]).
            // delta[j] is +/-1, so division is exact (no near-zero denominator).
            double g = dH / (2.0 * c_k * m_delta[j] + 1e-10);

            // Adam update.
            m_adam_m1[j] = ADAM_BETA1 * m_adam_m1[j] + (1.0 - ADAM_BETA1) * g;
            m_adam_m2[j] = ADAM_BETA2 * m_adam_m2[j] + (1.0 - ADAM_BETA2) * g * g;

            // Bias-corrected moments.
            unsigned t = m_spsa_step_count + 1;
            double m1_hat = m_adam_m1[j] / (1.0 - std::pow(ADAM_BETA1, t));
            double m2_hat = m_adam_m2[j] / (1.0 - std::pow(ADAM_BETA2, t));
            double direction = m1_hat / (std::sqrt(m2_hat) + ADAM_EPS);

            double range = param_range(j);
            double step = LR * direction * range;

            // Add exploration noise scaled by temperature.
            double noise = m_T * c_k * range * (rng_bit() ? 1.0 : -1.0);

            double val = get_param(j);
            if (s_meta[j].log_space) {
                val = std::exp(std::log(std::max(val, 1e-10)) + step + noise);
            } else {
                val += step + noise;
            }
            val = std::max(s_meta[j].min_val, std::min(s_meta[j].max_val, val));
            set_param(j, val);
        }

        m_spsa_step_count++;
    }
}

// ---------------------------------------------------------------
// Apply parameters to solver (design doc Section 4.2)
// ---------------------------------------------------------------

void solver_driver::apply_params(context& ctx) {
    // qi_eager_threshold: write DIRECTLY to qi_queue's cached member.
    // The quantifier_manager forwards to qi_queue::set_eager_threshold().
    if (ctx.has_quantifiers()) {
        ctx.get_qmanager_ref().set_eager_threshold(m_params.qi_eager_threshold);
    }

    // restart_margin_scale: multiply the baseline restart agility threshold
    // captured at init_search time (NOT a hardcoded constant).
    ctx.get_fparams().m_restart_agility_threshold =
        m_base_restart_agility * m_params.restart_margin_scale;

    // activity_decay_scale: scale the baseline VSIDS inverse decay.
    ctx.get_fparams().m_inv_decay = m_base_inv_decay * m_params.activity_decay_scale;

    // gc_aggressiveness: scale the baseline GC factor.
    ctx.get_fparams().m_lemma_gc_factor = m_base_gc_factor * m_params.gc_aggressiveness;

    // phase_noise, relevancy_probability, mbqi_probability:
    // These are read by other subsystems at decision time / final_check time.
    // For now, store them in the driver params and let the subsystems query them.
    // Integration into guess()/final_check is Phase 2 (applied via context reads).
    //
    // TODO(Phase 2): Wire phase_noise into context::guess() random flip probability.
    // TODO(Phase 2): Wire relevancy_probability into context::relevancy_lvl() with
    //   probabilistic rounding (continuous [0,1] -> integer {0,1,2}).
    // TODO(Phase 2): Wire mbqi_probability into final_check_eh coin flip.
}

// ---------------------------------------------------------------
// Main update entry point
// ---------------------------------------------------------------

void solver_driver::update(context& ctx) {
    double H = compute_health(ctx);

    // Update temperature from health trajectory.
    update_temperature(H);

    // Safety freeze check.
    if (H > FREEZE_THRESH) {
        m_consecutive_good++;
        if (m_consecutive_good >= FREEZE_STREAK) {
            m_frozen = true;
        }
    } else {
        m_consecutive_good = 0;
    }

    // Unfreeze check: if frozen and health drops, resume exploration.
    if (m_frozen) {
        if (H < UNFREEZE_THRESH && m_update_count % UNFREEZE_CHECK == 0) {
            m_frozen = false;
            m_consecutive_good = 0;
        }
    }

    m_update_count++;

    // Activation gate (design doc Section 10.1):
    // Don't start SPSA until we have enough health measurements for the
    // safety freeze to have a chance to trigger. This protects productive
    // queries from any perturbation during the first 5 update cycles
    // (25K decisions at DECISION_INTERVAL=5000).
    static constexpr unsigned ACTIVATION_CYCLES = 5;
    bool activated = (m_update_count > ACTIVATION_CYCLES);

    // If frozen (solver doing well) or not yet activated, skip SPSA updates.
    // Still track health/temperature for freeze/unfreeze decisions.
    if (activated && !m_frozen) {
        spsa_step(H, ctx);
        apply_params(ctx);
    }

    dump_to_alog(ctx.get_adaptive_log());
}

// ---------------------------------------------------------------
// Warmup helpers (design doc Section 9.1)
// ---------------------------------------------------------------

void solver_driver::apply_warmup_config(unsigned cycle) {
    if (cycle >= WARMUP_CYCLES) return;
    m_params = m_warmup_configs[cycle];
}

void solver_driver::finish_warmup() {
    // Find the warmup configuration with the best health.
    unsigned best = 0;
    double best_H = m_warmup_H[0];
    for (unsigned i = 1; i < WARMUP_CYCLES; i++) {
        if (m_warmup_H[i] > best_H) {
            best_H = m_warmup_H[i];
            best = i;
        }
    }

    // Initialize SPSA theta from the best warmup config.
    m_params = m_warmup_configs[best];

    // Reset Adam moments for fresh gradient estimation.
    memset(m_adam_m1, 0, sizeof(m_adam_m1));
    memset(m_adam_m2, 0, sizeof(m_adam_m2));
    m_spsa_step_count = 0;

    m_warmup_done = true;
}

// ---------------------------------------------------------------
// Perturbation generation
// ---------------------------------------------------------------

void solver_driver::generate_perturbation() {
    for (unsigned j = 0; j < N_PARAMS; j++) {
        m_delta[j] = rng_bit() ? +1 : -1;
    }
}

// ---------------------------------------------------------------
// Parameter access helpers
// ---------------------------------------------------------------

double solver_driver::param_range(unsigned j) const {
    if (s_meta[j].log_space) {
        return std::log(s_meta[j].max_val / std::max(s_meta[j].min_val, 1e-10));
    }
    return s_meta[j].max_val - s_meta[j].min_val;
}

double solver_driver::get_param(unsigned j) const {
    // Access params struct as an array of doubles (they are contiguous).
    return reinterpret_cast<double const*>(&m_params)[j];
}

void solver_driver::set_param(unsigned j, double v) {
    reinterpret_cast<double*>(&m_params)[j] = v;
}

// ---------------------------------------------------------------
// RNG (xorshift32)
// ---------------------------------------------------------------

uint32_t solver_driver::rng_next() {
    uint32_t x = m_rng_state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    m_rng_state = x;
    return x;
}

bool solver_driver::rng_bit() {
    return (rng_next() & 1) != 0;
}

// ---------------------------------------------------------------
// Adaptive log output
// ---------------------------------------------------------------

void solver_driver::dump_to_alog(FILE* alog) const {
    if (!alog) return;
    ALOG(alog, "DRIVER")
        .u("cycle", m_update_count)
        .d("H_fast", m_H_fast)
        .d("H_slow", m_H_slow)
        .d("T", m_T)
        .b("frozen", m_frozen)
        .b("warmup", !m_warmup_done)
        .d("qi_eager", m_params.qi_eager_threshold)
        .d("qi_surprisal", m_params.qi_surprisal_scale)
        .d("restart_margin", m_params.restart_margin_scale)
        .d("activity_decay", m_params.activity_decay_scale)
        .d("phase_noise", m_params.phase_noise)
        .d("relevancy", m_params.relevancy_probability)
        .d("mbqi", m_params.mbqi_probability)
        .d("gc_aggr", m_params.gc_aggressiveness);
}

} // namespace smt
