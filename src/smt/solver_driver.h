/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    solver_driver.h

Abstract:

    Adaptive solver driver -- continuous controller that reads landscape
    signals, computes a scalar health score, maintains an exploration
    temperature, and updates solver parameters via SPSA gradient estimation.

    Sits between the landscape map (sensor array) and the solver config
    (actuator). Runs every 5000 decisions OR 250 conflicts, whichever first.
    Gated behind m_fparams.m_auto_tune.

    State: ~320 bytes. Per-update cost: ~200ns.

Author:

    Z3 contributors

--*/
#pragma once

#include "util/vector.h"
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <algorithm>

namespace smt {

class context;

class solver_driver {
public:
    solver_driver();

    // Called every 5000 decisions OR 250 conflicts (whichever first)
    // from bounded_search() in smt_context.cpp.
    void update(context& ctx);

    // Called on each check-sat to reset per-search state.
    void init_search(context& ctx);

    // Called on push/pop for incremental lifecycle.
    void push();
    void pop();

    // Dump state to adaptive JSONL log.
    void dump_to_alog(FILE* alog) const;

    // Current tunable parameter values.
    struct params {
        double qi_eager_threshold;      // [0.5, 100], default 7.0, log-space
        double qi_surprisal_scale;      // [0.5, 3.0], default 1.0, log-space
        double restart_margin_scale;    // [0.3, 5.0], default 1.0, log-space
        double activity_decay_scale;    // [0.95, 1.05], default 1.0, linear
        double phase_noise;             // [0.0, 0.20], default 0.0, linear
        double relevancy_probability;   // [0.0, 1.0], default 1.0, linear
        double mbqi_probability;        // [0.0, 1.0], default 1.0, linear
        double gc_aggressiveness;       // [0.5, 2.0], default 1.0, log-space
    };

    static_assert(sizeof(params) == 8 * sizeof(double),
                  "params struct must be tightly packed doubles for array access");

    params const& current_params() const { return m_params; }

    // Counter accessors for integration into bounded_search().
    void inc_decisions()  { m_decisions_since_update++; m_total_decisions++; }
    void inc_conflicts()  { m_conflicts_since_update++; m_total_conflicts++; }

    // Notify the driver of QI insert count for blind spot #1 detection.
    // Called from bounded_search conflict/decision paths so the driver
    // can trigger when QI floods with no decisions/conflicts.
    void notify_qi_inserts(unsigned total_inserts) {
        m_qi_inserts_at_notify = total_inserts;
    }

    bool should_update() const {
        return m_decisions_since_update >= DECISION_INTERVAL ||
               m_conflicts_since_update >= CONFLICT_INTERVAL;
    }

    // QI flood awareness (blind spot #1): true when substantial QI
    // activity has occurred since the last update.
    bool qi_flood_detected() const {
        return (m_qi_inserts_at_notify - m_qi_inserts_at_last_update) >= QI_INSERT_INTERVAL;
    }

    // Reset interval counters after an update.
    void reset_interval() {
        m_decisions_since_update = 0;
        m_conflicts_since_update = 0;
        m_qi_inserts_at_last_update = m_qi_inserts_at_notify;
    }

private:
    static constexpr unsigned N_PARAMS = 8;

    // Update intervals.
    static constexpr unsigned DECISION_INTERVAL = 5000;
    static constexpr unsigned CONFLICT_INTERVAL = 250;
    // QI insert interval for blind spot #1: high enough that moderate-QI
    // queries (100K inserts) only trigger ~2x, avoiding over-perturbation.
    // True QI floods (3.6M inserts) still get ~72 triggers.
    static constexpr unsigned QI_INSERT_INTERVAL = 50000;

    // Warmup: don't activate SPSA before 25000 decisions (5 portfolio cycles).
    static constexpr unsigned WARMUP_DECISIONS = 25000;
    static constexpr unsigned WARMUP_CYCLES    = 5;

    // SPSA hyperparameters.
    static constexpr double LR         = 0.01;    // learning rate
    static constexpr double PERTURB_C  = 0.05;    // perturbation magnitude
    static constexpr double C_DECAY    = 0.101;   // perturbation decay exponent
    static constexpr double ADAM_BETA1 = 0.8;     // Adam first moment decay
    static constexpr double ADAM_BETA2 = 0.99;    // Adam second moment decay
    static constexpr double ADAM_EPS   = 1e-8;    // Adam denominator regularization

    // Temperature MACD EMA alphas.
    static constexpr double H_FAST_ALPHA = 0.15;
    static constexpr double H_SLOW_ALPHA = 0.01;
    static constexpr double MACD_BETA1   = 0.9;
    static constexpr double MACD_BETA2   = 0.999;
    static constexpr double T_SCALE      = 1.5;   // tanh temperature sensitivity

    // Health weights (Section 2.3 of design doc).
    static constexpr double W1 = 0.20;  // conflict_rate
    static constexpr double W2 = 0.10;  // conflict_quality
    static constexpr double W3 = 0.10;  // new_variable_rate
    static constexpr double W4 = 0.10;  // stress_trend
    static constexpr double W5 = 0.10;  // trail_stability
    static constexpr double W6 = 0.10;  // fp_hit_rate
    static constexpr double W7 = 0.20;  // wasted_work_rate
    static constexpr double W8 = 0.10;  // conflict_novelty

    // Safety freeze: if H > FREEZE_THRESH for FREEZE_STREAK consecutive
    // measurements, freeze parameters to protect productive queries.
    static constexpr unsigned FREEZE_STREAK  = 2;
    static constexpr double   FREEZE_THRESH  = 0.15;
    static constexpr double   UNFREEZE_THRESH = 0.05;

    static constexpr unsigned UNFREEZE_CHECK  = 50;  // re-check every 50 updates

    // Parameter metadata (compile-time constant after init).
    struct param_meta {
        double min_val, max_val, default_val;
        bool   log_space;
    };
    static const param_meta s_meta[N_PARAMS];

    // Current parameter values.
    params m_params;

    // SPSA per-parameter state.
    double m_adam_m1[N_PARAMS];     // Adam first moment
    double m_adam_m2[N_PARAMS];     // Adam second moment
    int    m_delta[N_PARAMS];       // Bernoulli {-1, +1} perturbation vector

    // Temperature state.
    double m_H_fast;       // fast health EMA (alpha = 0.15)
    double m_H_slow;       // slow health EMA (alpha = 0.01)
    double m_macd_m1;      // Adam m1 of MACD signal
    double m_macd_m2;      // Adam m2 of MACD signal
    double m_T;            // temperature in [0.05, 0.95]
    double m_H_prev;       // health at start of perturbation step

    // Internal glue EMAs for conflict_quality signal (s2).
    double m_glue_fast;    // fast glue EMA (alpha = 0.1)
    double m_glue_slow;    // slow glue EMA (alpha = 0.01)

    // Baseline values captured from solver at init_search time.
    // The driver's scale params (restart_margin_scale etc.) multiply these baselines.
    double m_base_restart_agility;  // from fparams.m_restart_agility_threshold
    double m_base_inv_decay;        // from fparams.m_inv_decay
    double m_base_gc_factor;        // from fparams.m_lemma_gc_factor
    double m_base_qi_eager;         // from qi_queue's initial eager threshold
    bool   m_base_mbqi;            // from fparams.m_mbqi (user's original setting)
    unsigned m_base_relevancy_lvl; // from fparams.m_relevancy_lvl

    // Counters.
    unsigned m_total_decisions;
    unsigned m_total_conflicts;
    unsigned m_update_count;
    unsigned m_spsa_step_count;    // incremented on each GRADIENT step (for decay)
    unsigned m_decisions_since_update;
    unsigned m_conflicts_since_update;
    unsigned m_qi_inserts_at_notify;      // latest QI insert count from notify
    unsigned m_qi_inserts_at_last_update; // QI insert count at last driver update

    // Safety freeze state.
    bool     m_frozen;
    unsigned m_consecutive_good;   // consecutive H > FREEZE_THRESH measurements

    // Warmup state.
    unsigned m_warmup_cycle;
    double   m_warmup_H[WARMUP_CYCLES];
    params   m_warmup_configs[WARMUP_CYCLES];
    bool     m_warmup_done;

    // Push/pop scope stack.
    struct scope_save {
        params   m_params;
        double   m_adam_m1[N_PARAMS];
        double   m_adam_m2[N_PARAMS];
        double   m_H_fast, m_H_slow, m_T;
        double   m_macd_m1, m_macd_m2;
        unsigned m_update_count;
        bool     m_frozen;
        bool     m_warmup_done;
    };
    svector<scope_save> m_scopes;

    // Simple xorshift RNG for perturbation generation.
    uint32_t m_rng_state;

    // Methods.
    double compute_health(context& ctx);
    void   update_temperature(double H);
    void   spsa_step(double H, context& ctx);
    void   apply_params(context& ctx);
    void   generate_perturbation();
    void   apply_warmup_config(unsigned cycle);
    void   finish_warmup();
    void   reset_to_defaults();
    double param_range(unsigned j) const;
    double get_param(unsigned j) const;
    void   set_param(unsigned j, double v);

    // RNG helpers.
    uint32_t rng_next();
    bool     rng_bit();
};

} // namespace smt
