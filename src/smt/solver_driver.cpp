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
    // mbqi_probability:      [0.0, 1.0],  default 1.0,  linear
    // Default 1.0: always attempt MBQI when user has m_mbqi=true.
    // SPSA can lower it toward 0 if e-matching alone is more productive.
    { 0.0, 1.0, 1.0, false },
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
    m_base_mbqi            = true;
    m_base_relevancy_lvl   = 2;

    // Counters.
    m_total_decisions       = 0;
    m_total_conflicts       = 0;
    m_update_count          = 0;
    m_spsa_step_count       = 0;
    m_decisions_since_update = 0;
    m_conflicts_since_update = 0;
    m_qi_inserts_at_notify      = 0;
    m_qi_inserts_at_last_update = 0;

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
    // Cycle 2: UNSAT-seeking (conservative: don't lower qi_eager below default
    // to avoid flooding the solver with QI instances that persist after warmup).
    m_warmup_configs[2].mbqi_probability      = 0.0;
    m_warmup_configs[2].relevancy_probability = 1.0;
    m_warmup_configs[2].restart_margin_scale  = 0.5;
    // Cycle 3: QI-throttled.
    m_warmup_configs[3].qi_eager_threshold    = 80.0;
    m_warmup_configs[3].qi_surprisal_scale    = 2.5;
    m_warmup_configs[3].mbqi_probability      = 0.8;
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
    m_base_mbqi            = ctx.get_fparams().m_mbqi;
    m_base_relevancy_lvl   = ctx.get_fparams().m_relevancy_lvl;

    // On first search, initialize parameters from solver's ACTUAL baselines
    // (not the driver's hardcoded defaults which may differ).
    // On subsequent searches (incremental), preserve learned parameters.
    bool has_non_default = false;
    for (unsigned j = 0; j < N_PARAMS; j++) {
        if (get_param(j) != s_meta[j].default_val) {
            has_non_default = true;
            break;
        }
    }
    if (!has_non_default) {
        // First search: sync driver params with solver's actual defaults
        m_params.qi_eager_threshold = m_base_qi_eager;
        m_params.qi_surprisal_scale = 1.0;
        m_params.restart_margin_scale = 1.0;
        m_params.activity_decay_scale = 1.0;
        m_params.gc_aggressiveness = 1.0;
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
    m_qi_inserts_at_notify      = 0;
    m_qi_inserts_at_last_update = 0;
    m_frozen           = false;
    m_consecutive_good = 0;
    m_total_decisions  = 0;
    m_total_conflicts  = 0;

    // Portfolio warmup: skip if parameters already learned from a previous check-sat.
    if (has_non_default) {
        m_warmup_cycle = WARMUP_CYCLES;
        m_warmup_done  = true;
    } else {
        m_warmup_cycle = 0;
        m_warmup_done  = false;
        memset(m_warmup_H, 0, sizeof(m_warmup_H));
    }
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

    // Blind spot #4: shallow backjump (theory bounce) correction.
    // avg_backjump_frac = (conflict_lvl - backjump_lvl) / conflict_lvl.
    // When < 0.05, conflicts only backjump 1-2 levels out of hundreds,
    // meaning the solver is bouncing off a wall. The high conflict rate
    // inflates s1 (conflict_rate signal), masking that the conflicts are
    // useless. Halve s1 so shallow-conflict queries don't appear healthy.
    if (has_conf && d.avg_backjump_frac < 0.05f && d.avg_backjump_frac > 0.0f) {
        s1 *= 0.5;
    }

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

void solver_driver::spsa_step(double H, context& ctx) {
    if (m_update_count % 2 == 0) {
        // PERTURBATION STEP: apply random perturbation, record health.
        generate_perturbation();

        // Blind spot #3: freeze QI parameters when no QI is active.
        // Indices 0,1 = qi_eager_threshold, qi_surprisal_scale.
        // Give QI 10 driver cycles to appear before freezing.
        {
            auto const& d = ctx.get_landscape().dynamics();
            bool has_qi = (d.qi_instance_rate > 0.0f || d.fp_hit_rate > 0.0f ||
                           m_update_count < 10);
            if (!has_qi) {
                m_delta[0] = 0;  // no perturbation for qi_eager
                m_delta[1] = 0;  // no perturbation for qi_surprisal
            }
        }

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
            // Skip frozen parameters (delta[j]==0 from blind spot #3).
            // Without this guard, the gradient estimate blows up (dH/1e-10).
            if (m_delta[j] == 0) continue;

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
    // P1: qi_eager_threshold -- write DIRECTLY to qi_queue's cached member.
    if (ctx.has_quantifiers()) {
        ctx.get_qmanager_ref().set_eager_threshold(m_params.qi_eager_threshold);
    }

    // P2: qi_surprisal_scale -- scale the Bayesian surprisal coefficient.
    // Base is 2.0; effective coeff = 2.0 * qi_surprisal_scale.
    if (ctx.has_quantifiers()) {
        ctx.get_qmanager_ref().set_surprisal_coeff(2.0 * m_params.qi_surprisal_scale);
    }

    // P3: restart_margin_scale -- multiply the baseline restart agility threshold.
    ctx.get_fparams().m_restart_agility_threshold =
        m_base_restart_agility * m_params.restart_margin_scale;

    // P4: activity_decay_scale -- scale the baseline VSIDS inverse decay.
    ctx.get_fparams().m_inv_decay = m_base_inv_decay * m_params.activity_decay_scale;

    // P5: phase_noise -- read directly from current_params() in decide().
    // No action needed here; the injection happens in smt_context::decide().

    // P6: relevancy_probability -- probabilistic rounding to integer level.
    // Maps continuous [0,1] to effective_level in {0, 1, 2} via probabilistic
    // rounding, giving SPSA a smooth gradient through a discrete parameter.
    // SAFETY: only apply when SPSA has actually moved the parameter away
    // from its default (1.0). At default, the solver's own relevancy
    // management (meta_update, G4 retry) should not be overridden.
    if (m_params.relevancy_probability < 0.99) {
        double v = m_params.relevancy_probability;
        double scaled = v * 2.0;
        unsigned base = static_cast<unsigned>(scaled);
        double frac = scaled - base;
        unsigned level = base;
        double r = static_cast<double>(rng_next() % 10000) / 10000.0;
        if (r < frac)
            level++;
        if (level > m_base_relevancy_lvl)
            level = m_base_relevancy_lvl;
        ctx.set_relevancy_lvl(level);
    }

    // P7: mbqi_probability -- probabilistic toggle of MBQI.
    // SAFETY: only toggle when SPSA has moved mbqi_probability away
    // from its default (1.0). At default, MBQI stays at user's setting.
    if (m_base_mbqi && m_params.mbqi_probability < 0.99) {
        double r = static_cast<double>(rng_next() % 10000) / 10000.0;
        ctx.get_fparams().m_mbqi = (r < m_params.mbqi_probability);
    }

    // P8: gc_aggressiveness -- scale the baseline GC factor.
    ctx.get_fparams().m_lemma_gc_factor = m_base_gc_factor * m_params.gc_aggressiveness;
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

        // During warmup: abort immediately on ANY good measurement.
        // Productive queries should never have params touched at all.
        // DON'T apply_params — the solver is already working fine.
        if (!m_warmup_done) {
            m_frozen = true;
            m_warmup_done = true;
            m_warmup_cycle = WARMUP_CYCLES;
        }
        // After warmup: require FREEZE_STREAK consecutive good measurements.
        else if (m_consecutive_good >= FREEZE_STREAK) {
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

    if (!m_warmup_done) {
        // ACTIVATION GATE with portfolio probing (design doc Sections 9.1, 10.1):
        //
        // Cycles 0 through WARMUP_CYCLES-1: observe health, don't perturb.
        // The safety freeze (above) can trigger during this phase, protecting
        // productive queries. After the observation gate, SPSA takes over.
        //
        // NOTE: Portfolio probing (applying SAT-seeking, QI-throttled, etc.)
        // is deferred to future work. Applying non-default configs during
        // warmup creates irreversible state (QI instances, E-graph merges)
        // that persists after config revert, causing regressions on
        // incremental F* queries.
        if (m_warmup_cycle < WARMUP_CYCLES) {
            m_warmup_H[m_warmup_cycle] = H;
            m_warmup_cycle++;
        } else {
            m_warmup_done = true;
        }
    } else if (m_frozen) {
        // Safety freeze: don't perturb parameters.
    } else {
        // Normal SPSA gradient descent.
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
        .u("warmup_cycle", m_warmup_done ? 0u : m_warmup_cycle)
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
