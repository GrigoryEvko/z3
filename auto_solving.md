# Z3 Adaptive Auto-Solving: Manifold-Aware Configuration Optimization

## Table of Contents
1. [Vision](#vision)
2. [The Three-Level Architecture](#three-levels)
3. [Manifold Intrinsic Signals](#signals)
4. [Signal 1: Belief Convergence Rate](#signal-belief)
5. [Signal 2: Curvature Reliability](#signal-curvature)
6. [Signal 3: Reward Entropy](#signal-reward)
7. [Signal 4: Theory Importance Skew](#signal-theory)
8. [Signal 5: Conflict Velocity](#signal-velocity)
9. [The Auto-Profiler (Outer Loop)](#auto-profiler)
10. [The Meta-Update on Restart (Middle Loop)](#meta-update)
11. [The Fallback Cascade](#fallback)
12. [Incremental Profile Evolution](#incremental)
13. [Proof Cache with Effective Configuration](#proof-cache)
14. [Multi-Strategy Portfolio](#portfolio)
15. [Connection to the Manifold Optimizer](#manifold-connection)
16. [Implementation Plan](#implementation)
17. [Task Breakdown](#tasks)
18. [Testing Strategy](#testing)
19. [Expected Outcomes](#outcomes)

---

## 1. Vision <a name="vision"></a>

Z3 currently treats solver configuration as a static, one-shot decision.
The user (or the auto-profiler) picks parameters at startup, and the solver
commits to them for the entire solving session. If the parameters are wrong,
the solver grinds through an impossible configuration until timeout.

This is like training a neural network with a fixed learning rate chosen
before seeing the data. Modern ML abandoned this decades ago in favor of
adaptive optimizers (Adam, cosine annealing, warmup schedules) that read
the loss landscape and adjust.

Z3 has the same opportunity. The manifold framework (belief vector, Adam
moments, QI reward, theory importance, soft relevancy) already produces
rich signals about the solver's progress. These signals are currently used
only for inner-loop decisions (branching, phase, QI scoring). But they also
contain META-information about whether the current configuration is optimal.

The vision: the solver reads its own manifold state to continuously
optimize its configuration. Three nested optimization loops:

```
OUTER LOOP (per check-sat):
  Static profiling → initial configuration
  Proof cache → warm-start from similar queries

MIDDLE LOOP (per restart, ~5K-20K conflicts):
  Read manifold intrinsic signals
  Compute meta-gradient on configuration
  Nudge: QI threshold, phase strategy, relevancy, restart margin

INNER LOOP (per conflict, ~500ns):
  Gradient from conflict → update (x, m1, m2)
  Derive decisions from manifold position
```

The inner loop navigates the assignment space.
The middle loop tunes the navigator.
The outer loop transfers knowledge across queries.

---

## 2. The Three-Level Architecture <a name="three-levels"></a>

### Level 1: The Assignment Manifold (Inner Loop)

Already implemented in smt_roadmap.md Phases 0-7.

The solver maintains per-variable state:
- `x[v]` ∈ [-1, 1]: polarity belief (V1)
- `m1[v]`: first moment of bump signal (V2, Adam)
- `m2[v]`: second moment of bump signal (V3, Adam)
- `last_update[v]`: lazy timestamp (V4)

Updated every conflict by the enriched gradient:
```
gradient[v] = -(assigned_polarity) × (1/glue) × (1/√|C|)
x[v]  = 0.95 × x[v]  + 0.05 × gradient[v]    (belief update)
m1[v] = 0.95 × m1[v] + 0.05 × |gradient[v]|   (Adam first moment)
m2[v] = 0.999 × m2[v] + 0.001 × gradient[v]²  (Adam second moment)
```

Decisions derived:
- Branch order: `activity[v] = m1[v] / (√m2[v] + ε)`
- Phase: `sign(x[v])` (belief mode) or cached phase (caching mode)

### Level 2: The Configuration Manifold (Middle Loop) — NEW

The solver's configuration is a vector θ in a continuous space:

```
θ = {
    qi_eager_threshold:     double ∈ [0.1, 1000]
    qi_lazy_threshold:      double ∈ [1, 1000]
    relevancy_level:        int ∈ {0, 1, 2}
    phase_strategy:         enum {CACHING, BELIEF}
    branching_heuristic:    enum {VSIDS, ADAM, COMBINED}
    restart_margin:         double ∈ [0.5, 2.0]
    ematching:              bool
    mbqi:                   bool
    bv_delay_threshold:     int ∈ [8, 64]
    arith_solver:           int ∈ {2, 6}
}
```

Currently θ is set once (by the auto-profiler or defaults) and never
changed. The middle loop will UPDATE θ on each restart based on the
manifold's intrinsic signals.

The "meta-gradient" for θ is not computed analytically (the relationship
between θ and solving progress is not differentiable). Instead, it's
estimated from runtime metrics — the manifold's own signals.

### Level 3: The Transfer Manifold (Outer Loop)

Across check-sat calls and across sessions, the solver accumulates
knowledge about what works:
- Proof strategy cache: (assertion_hash → top quantifiers + rewards)
- Effective configuration cache: (assertion_hash → θ that solved it)
- Quantifier signature matching: fuzzy lookup for similar queries

This is the "long-term memory" that prevents the solver from re-learning
the same lessons on every query.

### How They Connect

```
┌─────────────────────────────────────────────────────────┐
│ OUTER LOOP: Transfer (per check-sat)                    │
│                                                          │
│   assertion_hash → lookup proof cache                    │
│   if hit: warm-start (x, m1, m2) + warm-start θ         │
│   if miss: static profiling → initial θ                  │
│                                                          │
│   ┌─────────────────────────────────────────────────┐   │
│   │ MIDDLE LOOP: Meta-optimization (per restart)     │   │
│   │                                                   │   │
│   │   read manifold signals → compute meta-gradient   │   │
│   │   θ ← θ + α × meta_gradient                      │   │
│   │   apply updated θ to solver parameters            │   │
│   │                                                   │   │
│   │   ┌─────────────────────────────────────────┐   │   │
│   │   │ INNER LOOP: Search (per conflict)        │   │   │
│   │   │                                           │   │   │
│   │   │   conflict → gradient                     │   │   │
│   │   │   (x, m1, m2) ← update by gradient       │   │   │
│   │   │   derive decisions from manifold          │   │   │
│   │   │   apply θ gates (QI threshold, etc.)      │   │   │
│   │   │                                           │   │   │
│   │   └─────────────────────────────────────────┘   │   │
│   │                                                   │   │
│   └─────────────────────────────────────────────────┘   │
│                                                          │
│   on solve: cache (assertion_hash → θ_final + rewards)   │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

---

## 3. Manifold Intrinsic Signals <a name="signals"></a>

Five signals extracted from the manifold state, computed cheaply on
each restart. Each signal tells us something about the solver's
progress and informs a specific configuration adjustment.

### Signal Summary

| Signal | Source | What it measures | Meta-action |
|--------|--------|-----------------|-------------|
| Belief variance | m_polarity_belief | Polarity certainty | Phase strategy |
| Curvature noise | m_adam_m2 + QI tags | Gradient quality | QI threshold |
| Reward entropy | quantifier_stat | QI productivity | QI strategy |
| Importance skew | m_theory_importance | Theory dominance | Theory focus |
| Conflict velocity | conflicts/time | Search progress | Restart/fallback |

### Design Principle: Read the Manifold, Don't Add Metrics

Every signal is derived from data structures that ALREADY EXIST in the
solver — the polarity belief vector, the Adam moments, the QI reward
EMAs, the theory importance scores, and the conflict counter. No new
per-conflict tracking is needed. The middle loop just READS what the
inner loop already computes.

This is the key architectural insight: the manifold's state is a
sufficient statistic for meta-optimization. We don't need separate
"performance monitoring" — the manifold IS the performance monitor.

---

## 4. Signal 1: Belief Convergence Rate <a name="signal-belief"></a>

### What It Measures

The polarity belief vector x[v] is updated every conflict. If beliefs
are changing rapidly, the solver is uncertain about variable polarities.
If beliefs are stable, the solver has converged on a consistent polarity
assignment.

### Computation

```cpp
double compute_belief_variance() const {
    // Compute variance of recent belief updates.
    // We track this incrementally using an EMA of squared updates.
    //
    // On each conflict, for each bumped variable v:
    //   delta = new_belief[v] - old_belief[v]
    //   m_belief_update_ema = 0.99 * m_belief_update_ema + 0.01 * delta²
    //
    // On restart, read m_belief_update_ema.
    return m_belief_update_ema;
}
```

### Tracking Mechanism

In `process_antecedent()`, when updating the belief (already done in P3.2):
```cpp
double old_belief = m_polarity_belief[var];
// ... update belief ...
double delta = m_polarity_belief[var] - old_belief;
m_belief_update_ema = 0.99 * m_belief_update_ema + 0.01 * delta * delta;
```

Cost: one FMA per bumped variable per conflict. Negligible.

### What It Tells Us

```
belief_variance > 0.1:
    Beliefs are oscillating wildly.
    The solver doesn't know which polarity to use.
    → Use CACHING phase (more stable, relies on deepest assignment)
    → Consider widening search (increase random_freq)
    → QI might be injecting noise (check curvature_noise signal)

belief_variance ∈ [0.01, 0.1]:
    Normal convergence. Beliefs are learning but not settled.
    → Keep current phase strategy
    → Normal QI thresholds

belief_variance < 0.01:
    Beliefs have converged. Solver is confident about polarities.
    → Switch to BELIEF phase (exploit learned polarities)
    → Tighten search (reduce restart frequency, reduce random_freq)
    → If still not solved: beliefs might be WRONG (converged to
      wrong values). Consider rephasing by resetting beliefs to 0.

belief_variance < 0.001 for 3+ consecutive restart intervals:
    Beliefs are STUCK. The solver converged but hasn't solved.
    → Force belief reset to 0 (exploration restart)
    → Or: switch to opposite phase (flip all beliefs)
    → This is similar to VMTF rephasing but on the belief vector
```

### Configuration Adjustment

```cpp
void adjust_phase_strategy(double bv) {
    if (m_num_conflicts < 1000) return;  // warmup

    if (bv < 0.01) {
        // Beliefs converged — exploit them
        if (m_config.m_phase_strategy != PHS_BELIEF) {
            m_config.m_phase_strategy = PHS_BELIEF;
            TRACE(auto_tune, tout << "phase → BELIEF (variance=" << bv << ")\n";);
        }
    } else if (bv > 0.1) {
        // Beliefs oscillating — stabilize with caching
        if (m_config.m_phase_strategy != PHS_CACHING) {
            m_config.m_phase_strategy = PHS_CACHING;
            TRACE(auto_tune, tout << "phase → CACHING (variance=" << bv << ")\n";);
        }
    }
}
```

---

## 5. Signal 2: Curvature Reliability <a name="signal-curvature"></a>

### What It Measures

The Adam second moment m2[v] estimates the "curvature" of the
optimization landscape for variable v. High m2 = variable is bumped
frequently and with consistent magnitude (sharp valley). Low m2 =
variable is bumped rarely or with varying magnitude (flat region).

When QI floods the solver with useless instances, variables that appear
in QI-generated clauses get their m2 inflated by noise. The curvature
estimate becomes unreliable — the solver thinks these variables are
important when they're just being bumped by garbage.

### Computation

```cpp
double compute_curvature_noise() const {
    // Compare m2 of variables bumped by QI-sourced clauses
    // vs m2 of variables bumped by non-QI clauses.
    //
    // If QI-bumped variables have much higher m2 than non-QI,
    // the QI signal is contaminating the curvature estimates.
    //
    // We track this with two accumulators updated in process_antecedent:
    //   m_m2_sum_qi     += m2[v] when antecedent is QI-sourced
    //   m_m2_count_qi   += 1
    //   m_m2_sum_non_qi += m2[v] when antecedent is not QI-sourced
    //   m_m2_count_non_qi += 1

    double avg_qi = (m_m2_count_qi > 0)
        ? m_m2_sum_qi / m_m2_count_qi : 0.0;
    double avg_non_qi = (m_m2_count_non_qi > 0)
        ? m_m2_sum_non_qi / m_m2_count_non_qi : 1.0;

    return avg_qi / std::max(avg_non_qi, 1e-10);
}
```

### What It Tells Us

```
curvature_noise > 3.0:
    QI is severely contaminating the curvature estimates.
    Variables bumped by QI instances have 3× the curvature of
    variables bumped by SAT conflicts. The Adam moments are lying.
    → Tighten QI threshold aggressively (×= 2.0)
    → This is GRADIENT CLIPPING applied to the QI signal
    → Consider temporarily disabling QI reward discount (P2.2)
      to let the threshold do the filtering instead

curvature_noise ∈ [1.0, 3.0]:
    Normal. QI and non-QI signals have similar curvature.
    → Keep current QI threshold
    → QI signal is probably healthy

curvature_noise < 1.0:
    QI-bumped variables have LOWER curvature than non-QI ones.
    This means QI instances are hitting different variables than
    the SAT conflicts — the QI and SAT search are exploring
    different regions. This is actually good (diverse exploration).
    → Keep or loosen QI threshold slightly
```

### Configuration Adjustment

```cpp
void adjust_qi_threshold_from_curvature(double cn) {
    if (m_num_conflicts < 500) return;  // warmup

    if (cn > 3.0) {
        // QI contaminating curvature — tighten
        m_fparams.m_qi_eager_threshold *= 1.5;
        m_fparams.m_qi_eager_threshold = std::min(
            m_fparams.m_qi_eager_threshold, 100.0);
        TRACE(auto_tune,
            tout << "qi_eager *= 1.5 (curvature_noise=" << cn << ")\n";);
    } else if (cn < 0.5 && m_fparams.m_qi_eager_threshold > 10.0) {
        // QI signal is clean and diverse — loosen
        m_fparams.m_qi_eager_threshold *= 0.8;
        TRACE(auto_tune,
            tout << "qi_eager *= 0.8 (curvature_noise=" << cn << ")\n";);
    }
}
```

### Implementation Note

Tracking whether an antecedent clause is QI-sourced requires the QI
clause tagging from P0.2. In the SMT conflict resolution (not SAT),
we already check `qi_source_quantifier()` for attribution. We can
piggyback on this to separate QI-bumped from non-QI-bumped curvature.

In the SAT solver's `process_antecedent()`, we don't have direct
access to the QI tag. Two approaches:
1. Set a per-conflict flag in the SMT layer before SAT conflict
   resolution that indicates "this conflict involves QI clauses"
2. Track at the SMT level only (smt::conflict_resolution)

Option 2 is cleaner since the QI tagging is an SMT concept.

---

## 6. Signal 3: Reward Entropy <a name="signal-reward"></a>

### What It Measures

The QI reward distribution across quantifiers tells us whether the
solver has identified which quantifiers are useful.

### Computation

```cpp
double compute_reward_entropy() const {
    // Compute Shannon entropy of the reward distribution.
    //
    // For each quantifier q with reward r_q > floor:
    //   p_q = r_q / Σ r_q
    //   entropy -= p_q × log(p_q)
    //
    // Normalize by log(num_quantifiers) to get ∈ [0, 1].

    double total_reward = 0.0;
    unsigned count = 0;

    // First pass: compute total
    for (auto it = m_qmanager->begin(); it != m_qmanager->end(); ++it) {
        quantifier* q = *it;
        auto* stat = m_qmanager->get_stat(q);
        double r = stat->get_reward();
        if (r > 0.02) {  // above floor
            total_reward += r;
            count++;
        }
    }

    if (count <= 1 || total_reward < 1e-10)
        return 0.0;  // degenerate: no reward signal yet

    // Second pass: compute entropy
    double entropy = 0.0;
    for (auto it = m_qmanager->begin(); it != m_qmanager->end(); ++it) {
        quantifier* q = *it;
        auto* stat = m_qmanager->get_stat(q);
        double r = stat->get_reward();
        if (r > 0.02) {
            double p = r / total_reward;
            entropy -= p * std::log(p);
        }
    }

    // Normalize to [0, 1]
    double max_entropy = std::log(static_cast<double>(count));
    return (max_entropy > 0) ? entropy / max_entropy : 0.0;
}
```

### What It Tells Us

```
entropy > 0.8:
    Rewards spread evenly across many quantifiers.
    The solver hasn't found a clear signal about which quantifiers
    matter. Two possibilities:
    a) Early in solving — not enough conflicts yet for rewards to diverge
    b) Many quantifiers are genuinely useful (complex proof)
    → Wide QI: keep current thresholds or loosen slightly
    → If also high curvature_noise: the even spread might be noise,
      not genuine — tighten QI instead

entropy ∈ [0.3, 0.8]:
    Moderate concentration. Some quantifiers are clearly more useful
    than others, but the distribution isn't extreme.
    → Normal QI thresholds
    → The reward-adjusted scoring (P2.2) is handling this well

entropy < 0.3:
    Rewards concentrated on a few quantifiers. The solver knows
    exactly which quantifiers drive the proof.
    → Tighten QI aggressively: the top-K quantifiers are the only
      ones that matter. Consider limiting to top-20.
    → The proof cache should capture these for future queries.

entropy = 0.0:
    No quantifier has meaningful reward. QI is fundamentally
    unhelpful for this query.
    → Consider disabling ematching entirely
    → Try MBQI as alternative instantiation strategy
    → If the query has quantifiers but QI isn't productive,
      the triggers might be wrong or the proof needs MBQI
```

### Configuration Adjustment

```cpp
void adjust_qi_strategy_from_entropy(double re) {
    if (m_num_conflicts < 1000) return;  // warmup

    if (re < 0.1) {
        // No useful QI signal at all
        if (m_fparams.m_ematching) {
            m_fparams.m_ematching = false;
            m_fparams.m_mbqi = true;
            TRACE(auto_tune,
                tout << "ematching OFF, mbqi ON (entropy=" << re << ")\n";);
        }
    } else if (re < 0.3) {
        // Concentrated rewards — tighten
        m_fparams.m_qi_eager_threshold *= 1.3;
        m_fparams.m_qi_eager_threshold = std::min(
            m_fparams.m_qi_eager_threshold, 50.0);
    }
    // High entropy: keep current settings, let rewards develop
}
```

---

## 7. Signal 4: Theory Importance Skew <a name="signal-theory"></a>

### What It Measures

The theory importance scores (TV1 from P4.4) tell us which theory is
ACTUALLY driving conflicts at runtime — regardless of what the static
profiler thought based on the assertion set.

### Computation

```cpp
struct theory_skew {
    double arith_importance;  // sum of importance for arith theory vars
    double uf_importance;     // sum for UF vars
    double bv_importance;     // sum for BV vars
    double total;

    double dominant_fraction() const {
        double max_imp = std::max({arith_importance, uf_importance, bv_importance});
        return (total > 0) ? max_imp / total : 0.0;
    }

    const char* dominant_theory() const {
        if (arith_importance >= uf_importance && arith_importance >= bv_importance)
            return "arith";
        if (bv_importance >= arith_importance && bv_importance >= uf_importance)
            return "bv";
        return "uf";
    }
};

theory_skew compute_importance_skew() const {
    theory_skew sk{};

    for (unsigned v = 0; v < m_bdata.size(); ++v) {
        double imp = m_theory_importance.get(v, 0.0);
        if (imp < 0.001) continue;  // skip negligible

        if (get_bdata(v).is_theory_atom()) {
            // Determine which theory owns this atom
            // The theory that registered this bool_var via
            // mk_bool_var with m_notify_theory set.
            theory* th = m_bdata[v].get_theory();
            if (th) {
                family_id fid = th->get_id();
                if (fid == m_manager.mk_family_id("arith"))
                    sk.arith_importance += imp;
                else if (fid == m_manager.mk_family_id("bv"))
                    sk.bv_importance += imp;
                else
                    sk.uf_importance += imp;
            } else {
                sk.uf_importance += imp;
            }
        } else {
            sk.uf_importance += imp;
        }
    }

    sk.total = sk.arith_importance + sk.uf_importance + sk.bv_importance;
    return sk;
}
```

### What It Tells Us

```
dominant_fraction > 0.8:
    One theory dominates runtime conflicts. The solver is spending
    most of its effort in that theory.
    → If profiler classified differently: reclassify
    → Specialize for the dominant theory

dominant_fraction < 0.4:
    No clear dominant theory. True mixed workload.
    → Keep balanced settings
    → Don't over-specialize

If arith dominates AND conflict_velocity is low:
    Arithmetic solver might be struggling.
    → Consider arith.solver=2 (old solver) if NLA detected
    → Consider boosting arith propagation aggressiveness

If UF dominates AND reward_entropy is high:
    E-matching is productive but spread across many quantifiers.
    → Don't throttle QI — it's working
    → Consider increasing QI budget

If BV dominates AND curvature_noise is high:
    BV bit-blasting is creating noisy SAT variables.
    → Increase BV delay threshold
    → Consider native BV propagation for large operations
```

### Configuration Adjustment

```cpp
void adjust_theory_focus(theory_skew const& sk) {
    if (m_num_conflicts < 2000) return;  // need significant sample

    if (sk.dominant_fraction() > 0.8) {
        if (strcmp(sk.dominant_theory(), "arith") == 0) {
            // Arith-dominated: ensure arith solver is optimal
            if (m_num_nla_conflicts > m_num_conflicts / 2) {
                // NLA is the bottleneck
                // Consider switching to old arith solver
                TRACE(auto_tune,
                    tout << "arith dominates (" << sk.arith_importance
                         << "), NLA fraction high\n";);
            }
        }
        else if (strcmp(sk.dominant_theory(), "bv") == 0) {
            // BV-dominated: increase delay threshold
            if (m_fparams.m_bv_delay_threshold < 24) {
                m_fparams.m_bv_delay_threshold = 24;
                TRACE(auto_tune,
                    tout << "bv dominates → delay_threshold=24\n";);
            }
        }
    }
}
```

---

## 8. Signal 5: Conflict Velocity <a name="signal-velocity"></a>

### What It Measures

How many conflicts per second the solver is producing, and whether
the rate is increasing (good) or decreasing (stuck).

### Computation

```cpp
struct conflict_velocity {
    double current;     // conflicts/second in current restart interval
    double baseline;    // conflicts/second in first few restart intervals
    double trend;       // ratio: current / baseline (> 1 = accelerating)
};

conflict_velocity compute_conflict_velocity() const {
    // Track conflicts at each restart, compute rate
    // m_restart_conflict_count and m_restart_timestamp are set at each restart

    unsigned interval_conflicts = m_num_conflicts - m_restart_conflict_count;
    double interval_seconds = elapsed_since_restart();

    conflict_velocity cv;
    cv.current = (interval_seconds > 0)
        ? interval_conflicts / interval_seconds : 0.0;
    cv.baseline = m_cv_baseline;  // set from first 3 restart intervals
    cv.trend = (cv.baseline > 0) ? cv.current / cv.baseline : 1.0;

    return cv;
}
```

### What It Tells Us

```
trend > 1.5:
    Solver is ACCELERATING. Conflicts are coming faster.
    This usually means the solver found a productive search region.
    → Don't change anything — the configuration is working
    → Possibly TIGHTEN the search (reduce restart frequency)
      to let the solver exploit the current trajectory

trend ∈ [0.7, 1.5]:
    Normal. Solver is making steady progress.
    → Keep current configuration
    → Minor adjustments from other signals are fine

trend ∈ [0.3, 0.7]:
    Solver is SLOWING DOWN. Conflict rate dropping.
    → Moderate intervention: adjust one parameter
    → If QI waste is also high: tighten QI
    → If beliefs are also stuck: force rephase
    → Increase restart frequency to break out

trend < 0.3:
    Solver is STUCK. Conflict rate collapsed.
    → Aggressive intervention: try multiple changes
    → Relax relevancy (2 → 0)
    → Disable ematching, try MBQI
    → Force restart with belief reset
    → If stuck for 3 consecutive restart intervals: FALLBACK CASCADE

trend ≈ 0 (no conflicts in interval):
    Solver is completely stuck. BCP is running but not finding
    conflicts. Usually means the formula is satisfiable and the
    solver is building a model, OR the solver is in an infinite
    propagation loop.
    → Force check-model
    → Or: timeout and declare unknown
```

### Configuration Adjustment

```cpp
void adjust_from_velocity(conflict_velocity const& cv) {
    if (m_num_conflicts < 500) return;  // warmup

    if (cv.trend < 0.3) {
        // STUCK: aggressive intervention
        m_stuck_count++;

        if (m_stuck_count == 1) {
            // First stuck: relax relevancy
            if (m_fparams.m_relevancy_lvl > 0) {
                m_fparams.m_relevancy_lvl = 0;
                TRACE(auto_tune,
                    tout << "STUCK: relevancy → 0 (velocity=" << cv.trend << ")\n";);
            }
        }
        else if (m_stuck_count == 2) {
            // Second consecutive stuck: try MBQI
            if (m_fparams.m_ematching && !m_fparams.m_mbqi) {
                m_fparams.m_ematching = false;
                m_fparams.m_mbqi = true;
                TRACE(auto_tune,
                    tout << "STUCK x2: ematching OFF, mbqi ON\n";);
            }
        }
        else if (m_stuck_count >= 3) {
            // Third consecutive stuck: NUCLEAR RESET
            reset_to_default_config();
            TRACE(auto_tune,
                tout << "STUCK x3: NUCLEAR RESET to defaults\n";);
        }
    } else {
        // Not stuck: reset counter
        if (cv.trend > 0.7) {
            m_stuck_count = 0;
        }
    }
}
```

---

## 9. The Auto-Profiler (Outer Loop) <a name="auto-profiler"></a>

### Already Implemented

The auto-profiler (commit e8fc37e73) classifies queries into 12
categories based on static features and applies per-category parameter
presets. This is the INITIAL configuration that the middle loop then
refines.

### Categories and Their Initial θ

```
Category            Initial θ settings
─────────────────── ──────────────────────────────────────────────────
PURE_SAT            relevancy=0, ematching=false, mbqi=false
QF_BV               relevancy=0, ematching=false, ext_gates=true
QF_LIA              relevancy=0, ematching=false, arith_reflect=false
QF_LRA              relevancy=0, phase=THEORY, ematching=false
QF_NLA              relevancy=0, ematching=false
QF_UF               relevancy=0, ematching=false
QF_AUFLIA           relevancy=0, ematching=false
UFLIA_LIGHT_QI      qi_eager=10, qi_lazy=20, mbqi=true
UFLIA_HEAVY_QI      qi_eager=default, max_eager_multipatterns=0 (for 1000+)
BV_WITH_QI           bv_cc=false, ext_gates=true, mbqi=true
DT_WITH_QI          qi_eager=10, qi_lazy=20, mbqi=true
MIXED               (conservative defaults)
```

### Connection to Middle Loop

The auto-profiler sets θ₀. The middle loop then adjusts θ based on
runtime signals. The auto-profiler's classification ALSO determines
WHICH middle-loop adjustments are allowed:

- For PURE_SAT: middle loop can adjust restart margin and phase, but
  should NOT enable QI (there are no quantifiers)
- For UFLIA_HEAVY_QI: middle loop can adjust QI threshold, relevancy,
  phase, and branching heuristic
- For QF_BV: middle loop can adjust BV delay threshold and restart
  margin, but should NOT enable QI

The category acts as a CONSTRAINT on the middle loop's search space.

---

## 10. The Meta-Update on Restart (Middle Loop) <a name="meta-update"></a>

### When It Runs

At every restart. Restarts happen naturally every few thousand conflicts
(governed by the glucose EMA-based restart condition). The meta-update
adds ~1μs of overhead per restart (reading a few accumulators and doing
comparisons). Given restarts happen every 5K-20K conflicts and each
conflict takes ~500ns, the total solving time between restarts is
2.5-10ms. The 1μs meta-update is 0.01-0.04% overhead.

### The Update Function

```cpp
void solver::meta_update_on_restart() {
    // Only run after warmup
    if (m_num_conflicts < 1000) return;

    // Compute manifold intrinsic signals
    double bv = compute_belief_variance();
    double cn = compute_curvature_noise();
    double re = compute_reward_entropy();
    theory_skew sk = compute_importance_skew();
    conflict_velocity cv = compute_conflict_velocity();

    TRACE(auto_tune,
        tout << "meta_update: conflicts=" << m_num_conflicts
             << " bv=" << bv << " cn=" << cn << " re=" << re
             << " dom=" << sk.dominant_theory()
             << " cv_trend=" << cv.trend << "\n";);

    // Apply adjustments (order matters: velocity first, then specifics)
    adjust_from_velocity(cv);
    adjust_phase_strategy(bv);
    adjust_qi_threshold_from_curvature(cn);
    adjust_qi_strategy_from_entropy(re);
    adjust_theory_focus(sk);

    // Record for proof cache
    m_last_meta_update_θ = current_θ();

    // Reset per-restart accumulators
    reset_restart_accumulators();
}
```

### Calling Point

In `sat_solver.cpp`, the restart logic is in `do_restart()` or
the equivalent function. Add the meta-update call:

```cpp
void solver::restart(bool to_base) {
    // ... existing restart logic ...

    // Meta-update: read manifold, adjust θ
    // (Only for SMT mode — pure SAT doesn't have QI/theory signals)
    if (m_ext) {
        meta_update_on_restart();
    }

    // ... continue restart ...
}
```

For the SMT context, the meta-update would be in
`smt::context::restart()` or wherever the restart hook is.

### Parameter Adjustment Rules

Each adjustment function applies a BOUNDED change:
- QI threshold: multiply by at most 2× per restart (no jumps)
- Relevancy: change by at most 1 level per restart
- Phase strategy: toggle at most once per 3 restart intervals
- Branching heuristic: DO NOT change during solving
  (too disruptive, changes heap ordering)

These bounds prevent oscillation. The meta-optimizer is a SLOW,
conservative tuner, not a jittery controller.

### Cooldown Between Changes

After any θ change, set a cooldown of 2 restart intervals before
the same parameter can be changed again. This gives the inner loop
time to respond to the new configuration before we evaluate whether
it helped.

```cpp
// Per-parameter cooldown tracker
struct param_cooldown {
    unsigned qi_threshold_last_change = 0;    // restart # of last change
    unsigned phase_strategy_last_change = 0;
    unsigned relevancy_last_change = 0;

    bool can_change_qi(unsigned restart_num) const {
        return restart_num >= qi_threshold_last_change + 2;
    }
    // ... similar for other params ...
};
```

---

## 11. The Fallback Cascade <a name="fallback"></a>

### Motivation

Sometimes the initial configuration is fundamentally wrong. No amount
of incremental nudging will fix "ematching=false" when the proof
requires QI. The fallback cascade provides RADICAL reconfiguration
when incremental adjustments fail.

### The Cascade

```
Level 0 (conflicts 0 → budget₁):
    θ₀ = profiler's initial guess
    Normal solving with middle-loop adjustments.

    budget₁ = 10K conflicts (small queries) or 50K (large queries)
    Detection: if solved → done
    If not: evaluate signals → proceed to Level 1

Level 1 (conflicts budget₁ → budget₂):
    θ₁ = θ₀ with incremental adjustments from middle loop
    This is the "normal adaptive" path.

    budget₂ = 3 × budget₁
    Detection: if conflict_velocity.trend > 0.3 for ≥ 2 restarts → stay
    If trend < 0.3 for 3 consecutive: proceed to Level 2

Level 2 (conflicts budget₂ → budget₃):
    θ₂ = RELAXED configuration:
      - relevancy = 0 (see everything)
      - qi_threshold = default (reset any tightening)
      - mbqi = true (try model-based QI)
    Keep learned clauses, activity scores, beliefs.

    budget₃ = 3 × budget₂
    Detection: if solved → done
    If velocity still stuck: proceed to Level 3

Level 3 (conflicts budget₃ → budget₄):
    θ₃ = OPPOSITE of initial guess:
      - If initial had ematching=true: try ematching=false
      - If initial had relevancy=2: try relevancy=0
      - If initial had arith.solver=6: try arith.solver=2
    This catches misclassifications.

    budget₄ = 3 × budget₃
    Detection: if solved → done
    If still stuck: proceed to Level 4

Level 4 (no budget limit):
    θ₄ = STOCK Z3 DEFAULTS
    Forget all our tuning. Go back to upstream behavior.
    This is the "our optimizations might be hurting" escape hatch.

    Run until timeout or solution.
```

### Key Principle: Keep Learned Clauses

At each level transition, we keep ALL learned clauses, activity scores,
and beliefs. Only the CONFIGURATION changes. The solver doesn't lose
the work it's done — it just navigates differently.

This is fundamentally different from restarting from scratch. The learned
clauses constrain the search space (permanently, per CDCL theory).
The configuration determines HOW we navigate within the constrained space.

### When Level Transitions Are Too Expensive

For queries with tight rlimits (F* sets rlimit=2.5M per check-sat),
the cascade might consume the entire rlimit on Level 0 before reaching
Level 1. In this case, the initial profiling must be more aggressive:
- Use proof cache warm-starting (Level 3 knowledge from similar queries)
- Use the effective configuration cache (skip to the θ that worked before)
- If no cache hit: run with conservative defaults (the safest choice)

### Implementation

```cpp
class fallback_cascade {
    unsigned m_level = 0;
    unsigned m_level_start_conflicts = 0;
    unsigned m_consecutive_stuck = 0;

    unsigned budget() const {
        // Exponential backoff: 10K, 30K, 90K, ...
        return 10000u * static_cast<unsigned>(std::pow(3, m_level));
    }

    bool should_escalate(unsigned conflicts, double velocity_trend) {
        unsigned elapsed = conflicts - m_level_start_conflicts;
        if (elapsed < budget()) return false;

        if (velocity_trend < 0.3)
            m_consecutive_stuck++;
        else
            m_consecutive_stuck = 0;

        return m_consecutive_stuck >= 3;
    }

    void escalate(smt_params& p, query_category cat) {
        m_level++;
        m_level_start_conflicts = /* current conflicts */;
        m_consecutive_stuck = 0;

        switch (m_level) {
        case 1: /* incremental adjustments already happening */ break;
        case 2: apply_relaxed(p); break;
        case 3: apply_opposite(p, cat); break;
        case 4: apply_stock_defaults(p); break;
        }
    }
};
```

---

## 12. Incremental Profile Evolution <a name="incremental"></a>

### The Problem

F* fires thousands of check-sat calls per module verification. Each
call adds assertions (via push) and may change the character of the
formula:

```
check-sat #1:  200 quantifiers, pure UF+LIA         → UFLIA_HEAVY_QI
check-sat #2:  same 200 + 50 BV assertions           → BV_WITH_QI (!)
check-sat #3:  pop'd BV, added NLA constraints        → mixed NLA (!)
check-sat #4:  back to pure UF+LIA                    → UFLIA_HEAVY_QI
```

The static profiler runs once at context setup. It doesn't see the
evolution. Between check-sat calls, the profile should be RE-COMPUTED.

### Solution: Delta Profiling

On each check-sat:
1. Compute the assertion content hash (already done in P8.3)
2. If hash matches the previous check-sat's hash → same profile, skip
3. If hash changed → re-run the profiler on the CURRENT assertion set
4. If category changed → apply new tuning
5. Warm-start from proof cache if available

### Implementation

```cpp
void context::on_check_sat() {
    compute_assertion_hash();

    if (m_assertion_hash != m_prev_assertion_hash) {
        // Profile changed — reclassify
        static_features st(m_manager);
        collect_static_features(st);

        query_profile prof;
        prof.classify(st);

        if (prof.cat != m_current_category) {
            // Category changed! Re-apply tuning.
            m_current_category = prof.cat;
            prof.apply_tuning(m_fparams);

            TRACE(auto_tune,
                tout << "profile evolved: " << m_prev_category_name
                     << " → " << prof.category_name() << "\n";);
        }

        m_prev_assertion_hash = m_assertion_hash;
    }

    // Warm-start from proof cache (existing P8.4)
    apply_proof_strategy();
}
```

### Lightweight Re-Profiling

Full `collect_static_features` is O(|formula|) which could be expensive
for large assertion sets. For incremental re-profiling, we can maintain
INCREMENTAL counters:

```cpp
// On each new assertion:
void on_assert(expr* e) {
    // Update incremental counters
    if (has_bv_sort(e)) m_incr_bv_count++;
    if (has_arith(e)) m_incr_arith_count++;
    if (is_quantifier(e)) m_incr_quant_count++;
    // ... etc
}

// On pop:
void on_pop(unsigned num_scopes) {
    // Decrement counters for popped assertions
    // (requires tracking per-scope assertion counts)
}
```

This avoids the full DAG walk and gives O(1) re-profiling.

---

## 13. Proof Cache with Effective Configuration <a name="proof-cache"></a>

### Extension of P8.4

The existing proof strategy cache stores:
- `assertion_hash → top-20 quantifiers by reward`

Extend it to also store:
- The CONFIGURATION that solved the query
- The runtime metrics at the point of solving
- How many conflicts it took

### Extended Cache Entry

```cpp
struct proof_strategy {
    // Existing: top quantifier rewards
    svector<entry> top_quantifiers;

    // NEW: effective configuration
    query_category detected_category;      // what the profiler thought
    query_category effective_category;     // what the middle loop converged to

    // Key θ parameters at solve time
    double effective_qi_threshold;
    unsigned effective_relevancy;
    bool effective_ematching;
    bool effective_mbqi;
    unsigned effective_bv_delay;

    // Performance data
    unsigned conflicts_to_solve;
    double wall_time_seconds;
    unsigned qi_instances_total;
    unsigned qi_instances_useful;

    // Meta: how many fallback levels were needed
    unsigned fallback_level;
};
```

### Warm-Starting θ from Cache

On a new check-sat with a matching (or fuzzy-matching) assertion hash:

```cpp
void apply_cached_configuration(proof_strategy const& cached) {
    // If the cached query solved at Level 0 (initial config was good):
    //   → use the profiler's initial config (it was right)

    // If the cached query needed Level 2+ fallback:
    //   → skip directly to the effective configuration
    //   → this saves the entire fallback cascade

    if (cached.fallback_level >= 2) {
        // The initial profiler was WRONG for this type of query.
        // Skip to the effective settings directly.
        m_fparams.m_qi_eager_threshold = cached.effective_qi_threshold;
        m_fparams.m_relevancy_lvl = cached.effective_relevancy;
        m_fparams.m_ematching = cached.effective_ematching;
        m_fparams.m_mbqi = cached.effective_mbqi;

        TRACE(auto_tune,
            tout << "cache hit (level " << cached.fallback_level
                 << "): skipping to effective config\n";);
    }

    // Always warm-start quantifier rewards
    // (existing P8.4 logic)
    warm_start_rewards(cached.top_quantifiers);
}
```

### Learning from Failures

If a cached configuration FAILS on a new query (the query is similar
but not identical), record the failure:

```cpp
void on_solve_failure(uint64_t assertion_hash) {
    auto it = m_proof_cache.find(assertion_hash);
    if (it != m_proof_cache.end()) {
        // The cached config didn't work for this variant.
        // Downgrade confidence in the cache entry.
        it->second.confidence *= 0.5;

        // If confidence drops below threshold, evict.
        if (it->second.confidence < 0.1) {
            m_proof_cache.erase(it);
        }
    }
}
```

---

## 14. Multi-Strategy Portfolio <a name="portfolio"></a>

### For Genuinely Hard Queries (> 10 seconds)

When the fallback cascade reaches Level 3+ without solving, the
query is genuinely hard. At this point, invest in parallel exploration:

```
Main thread:     current θ (whatever the cascade arrived at)
Worker thread 1: relevancy=0, ematching=true (broadest possible QI)
Worker thread 2: ematching=false, mbqi=true  (model-based instantiation)
```

All threads share the learned clause database (thread-safe). First
to solve wins.

### Connection to Z3's Existing Parallelism

Z3 already has `sat.threads` for parallel SAT solving. The portfolio
extends this to parallel CONFIGURATIONS:
- sat.threads parallelizes the SAT search (same formula, same config,
  different random seeds)
- portfolio parallelizes the CONFIGURATION (same formula, different
  solvers/settings)

These are orthogonal and can be combined:
- 8 cores: 2 configurations × 4 SAT threads each
- Or: 4 configurations × 2 SAT threads each
- Or: 8 configurations × 1 SAT thread each (maximum diversity)

### Clause Sharing Between Portfolio Members

Each portfolio member discovers different learned clauses (because
different configurations explore different parts of the search space).
Sharing these clauses between members accelerates ALL of them:
- Member 1 (wide QI) discovers that clause C is useful
- Share C with Member 2 (MBQI) which was not exploring that region
- Member 2 now benefits from Member 1's discovery

This is cooperative portfolio solving — each configuration contributes
its unique perspective to a shared knowledge base.

---

## 15. Connection to the Manifold Optimizer <a name="manifold-connection"></a>

### The Unified View

The three loops form a single optimization process on a product manifold:

```
M = M_assignment × M_config × M_transfer

M_assignment = [0,1]^n        navigated by inner loop (per-conflict)
M_config     = Θ              navigated by middle loop (per-restart)
M_transfer   = proof_cache    navigated by outer loop (per-check-sat)
```

Each level has its own learning rate, gradient source, and convergence
criterion:

```
Level      Learning rate   Gradient source         Convergence
──────     ─────────────   ──────────────────────   ──────────────────
Inner      m_activity_inc  Conflict clause          solution or proof
Middle     bounded nudge   Manifold intrinsic sigs  velocity stabilizes
Outer      cache update    solve/fail outcomes      cache fills up
```

### The Learning Rate Hierarchy

The inner loop has the fastest learning rate (every conflict updates
the manifold). The middle loop has a slower rate (every restart, with
cooldowns). The outer loop has the slowest rate (every check-sat,
bounded by cache size).

This hierarchy is essential: the inner loop must converge (or diverge)
before the middle loop can evaluate whether the current configuration
is working. The middle loop must stabilize before the outer loop can
decide whether to cache the effective configuration.

If the middle loop changes θ too fast, the inner loop never converges,
and the signals become noise. If the middle loop changes too slow,
the solver wastes time on a bad configuration. The restart interval
(5K-20K conflicts) is the natural timescale for θ changes.

### The Manifold's Curvature Informs the Meta-Optimizer

The key insight: the manifold's curvature (captured by Adam's m2)
tells us about the QUALITY of the current configuration.

Low curvature (flat m2): the solver isn't learning anything useful.
The conflicts are not informative. This means either:
a) The problem is almost solved (few conflicts remain)
b) The configuration is wrong (conflicts happen but aren't productive)

Distinguish (a) from (b) using conflict velocity:
- Low curvature + high velocity = almost solved (a)
- Low curvature + low velocity = stuck (b)

High curvature (sharp m2): the solver is learning rapidly. Conflicts
are highly informative. This usually means the configuration is good —
the solver is in a productive region of the search space.

High curvature for ALL variables: the gradient signal is very strong.
Possible causes:
a) Good configuration: every conflict teaches something
b) Too-aggressive QI: QI floods the solver with noisy bumps

Distinguish using curvature_noise (Signal 2).

### Component Double-Duty Table

Every manifold component serves the inner loop AND the meta-optimizer:

```
Component           Inner loop role              Meta-optimizer reading
────────────────    ──────────────────────────── ─────────────────────────────
Belief (x[v])       Phase selection              belief_variance → phase strategy
Adam m1[v]          Branching priority           (part of curvature calculation)
Adam m2[v]          Per-var adaptive LR          curvature_noise → QI threshold
QI reward[q]        QI queue scoring             reward_entropy → QI strategy
Theory imp[v]       Activity weighting           importance_skew → theory focus
Soft relevancy[v]   Bump scaling                 active_region → relevancy level
Conflict count      Restart timing               conflict_velocity → fallback
```

No new data structures needed. The meta-optimizer reads what the inner
loop already computes.

---

## 16. Implementation Plan <a name="implementation"></a>

### Phase A: Signal Extractors (Foundation)

Add 5 signal computation functions. These run on restart, reading
existing manifold state. Pure computation, no side effects.

Files:
- smt_context.h — declare signal functions
- smt_context.cpp — implement signal functions
- sat_solver.h — add per-restart accumulators (belief_update_ema, etc.)
- sat_solver.cpp — update accumulators in inner loop

### Phase B: Meta-Update on Restart

Wire the signal extractors into the restart path. Add the adjustment
functions (one per parameter). Add cooldown tracking.

Files:
- smt_context.cpp — meta_update_on_restart()
- smt_setup.cpp — initial θ from profiler (already done)

### Phase C: Fallback Cascade

Add the level tracker. Wire level transitions to parameter changes.
Add the nuclear reset (stock defaults).

Files:
- smt_context.h — fallback_cascade struct
- smt_context.cpp — escalation logic, apply_relaxed/opposite/defaults

### Phase D: Incremental Re-Profiling

On each check-sat, check if the assertion hash changed. If so,
re-profile and apply updated tuning.

Files:
- smt_context.cpp — on_check_sat delta detection

### Phase E: Extended Proof Cache

Store effective θ in the proof cache. Warm-start θ on cache hit.
Add failure tracking with confidence decay.

Files:
- smt_context.h — extend proof_strategy struct
- smt_context.cpp — capture/apply effective configuration

### Phase F: Portfolio (Optional, Advanced)

Add multi-configuration parallel solving for hard queries.

Files:
- solver/combined_solver.cpp or new portfolio_solver.cpp

---

## 17. Task Breakdown <a name="tasks"></a>

### Phase A: Signal Extractors

#### A1: Belief variance accumulator
Add `m_belief_update_ema` (double) to sat_solver. In process_antecedent,
after updating belief, compute `delta = new - old`, update EMA:
`ema = 0.99 * ema + 0.01 * delta²`. Initialize to 0.0. Reset on
init_search. Read on restart via accessor. ~10 lines total.

#### A2: Curvature noise accumulator
In smt::conflict_resolution::process_antecedent, when processing an
antecedent that is QI-sourced, add m2[v] to m_m2_sum_qi and increment
m_m2_count_qi. For non-QI antecedents, add to m_m2_sum_non_qi. Need
access to Adam m2 from SAT solver (via context bridge). Reset accumulators
on restart. ~20 lines.

#### A3: Reward entropy computation
In smt_context, add compute_reward_entropy(). Iterate all quantifiers
(via m_qmanager->begin/end), compute Shannon entropy of the reward
distribution. Normalize by log(num_quantifiers). Cache result for
the current restart interval (only recompute when dirty). ~30 lines.

#### A4: Theory importance skew computation
In smt_context, add compute_importance_skew(). Iterate m_theory_importance
vector, classify each bool_var's theory by its registered theory solver.
Sum importance per theory family. Return struct with fractions. ~30 lines.

#### A5: Conflict velocity tracker
Add m_restart_conflict_count, m_restart_timestamp, m_cv_baseline to
smt_context. Set on each restart. Compute rate and trend. Initialize
baseline from first 3 restart intervals. ~20 lines.

### Phase B: Meta-Update

#### B1: meta_update_on_restart main function
Call all 5 signal extractors. Call adjustment functions. Log via TRACE.
Guard with warmup (1000 conflicts minimum). ~15 lines.

#### B2: Phase strategy adjustment
Read belief_variance. If < 0.01 → BELIEF. If > 0.1 → CACHING.
With 2-restart cooldown. ~15 lines.

#### B3: QI threshold adjustment from curvature
Read curvature_noise. If > 3.0 → tighten ×1.5. If < 0.5 → loosen ×0.8.
Clamp to [1.0, 100.0]. With cooldown. ~15 lines.

#### B4: QI strategy adjustment from entropy
Read reward_entropy. If < 0.1 → disable ematching, enable MBQI.
If < 0.3 → tighten threshold. With cooldown. ~15 lines.

#### B5: Theory focus adjustment
Read importance_skew. If BV dominates → increase BV delay threshold.
If arith dominates + NLA + stuck → consider arith solver switch.
Conservative: only log, don't auto-switch arith solver yet. ~15 lines.

#### B6: Velocity-based stuck detection
Read conflict_velocity. Track consecutive_stuck count. Level 1: relax
relevancy. Level 2: try MBQI. Level 3: nuclear reset. ~25 lines.

#### B7: Cooldown tracker
Struct with per-parameter last_change restart number. can_change()
method. ~15 lines.

### Phase C: Fallback Cascade

#### C1: Fallback level tracker
Struct with level, budget(), should_escalate(), escalate(). ~30 lines.

#### C2: Apply relaxed configuration (Level 2)
relevancy=0, qi_threshold=default, mbqi=true. Keep learned clauses.
~10 lines.

#### C3: Apply opposite configuration (Level 3)
Flip ematching, flip relevancy, flip arith solver. ~15 lines.

#### C4: Apply stock defaults (Level 4)
Reset all θ to upstream Z3 defaults. ~20 lines.

#### C5: Wire cascade into restart path
In restart handler, check should_escalate. If yes, call escalate.
~10 lines.

### Phase D: Incremental Re-Profiling

#### D1: Delta detection
On check-sat, compare assertion_hash with previous. If changed,
re-run profiler. ~15 lines.

#### D2: Incremental category update
If category changed, apply new tuning. Log the transition. ~10 lines.

### Phase E: Extended Proof Cache

#### E1: Store effective θ in cache
On UNSAT, capture current θ values alongside quantifier rewards.
~15 lines.

#### E2: Warm-start θ from cache
On cache hit, if fallback_level >= 2, apply effective θ directly.
~15 lines.

#### E3: Failure tracking with confidence decay
On solve failure with cache hit, decay confidence by 0.5. Evict
below 0.1. ~10 lines.

### Phase F: Portfolio (Advanced)

#### F1: Configuration diversity generator
Given the auto-profiler's category, generate 2-3 diverse θ vectors
that cover the most likely failure modes. ~30 lines.

#### F2: Parallel configuration launcher
Fork solver with each θ variant. Share learned clause database.
First to solve cancels others. Requires thread-safe clause pool
(Z3 already has one for sat.threads). ~100 lines.

### Total Estimate

```
Phase A (signals):      ~110 lines, 5 tasks
Phase B (meta-update):  ~115 lines, 7 tasks
Phase C (fallback):     ~85 lines, 5 tasks
Phase D (incremental):  ~25 lines, 2 tasks
Phase E (cache):        ~40 lines, 3 tasks
Phase F (portfolio):    ~130 lines, 2 tasks (optional)
────────────────────────────────────────────
Total:                  ~505 lines, 24 tasks (22 without portfolio)
```

---

## 18. Testing Strategy <a name="testing"></a>

### Regression Testing

Every change must pass:
```bash
blast.sh -c smoke --fast       # 40/40
blast.sh -c critical           # ≥ 1387/1391
blast.sh -c everything --fast  # ≥ 11300/11911
```

### Signal Validation

For each signal extractor, validate on known queries:

```
ModifiesGen-195 (hard, QI-heavy):
  belief_variance:    should be moderate (0.01-0.1)
  curvature_noise:    should be high (QI dominates)
  reward_entropy:     should be low (few useful quantifiers)
  importance_skew:    UF should dominate
  conflict_velocity:  should be low (only 945 conflicts in 6.4s)

Matrix-116 (hard, arith-heavy):
  importance_skew:    arith should dominate

OrdSet-35 (unknown, 40ms):
  reward_entropy:     should be 0 or very low (no useful QI)
  → meta-update should recommend: try MBQI

UInt128-184 (unknown, NLA spiral):
  conflict_velocity:  should show rapid drop (NLA spinning)
  importance_skew:    arith dominant
  → fallback cascade should try arith.solver=2 at Level 3
```

### A/B Testing the Meta-Update

Run critical suite with meta-update ON vs OFF:
```bash
# Meta-update OFF (baseline):
z3 <file>

# Meta-update ON:
z3 smt.auto_tune=true <file>
```

Gate behind `smt.auto_tune` parameter (default false initially,
flip to true when confident).

### Fallback Cascade Validation

For the 4 failing critical queries, verify the cascade recovers them:
- OrdSet-35: cascade should try relevancy=0 at Level 2 → solve
- UInt128-184: cascade should try arith.solver=2 at Level 3 → solve
- Matrix-94: cascade should try wider QI at Level 2 → may solve
- ModifiesGen-172: timeout, cascade unlikely to help (genuine difficulty)

### Incremental Profile Evolution Testing

Test with F* incremental queries that change character:
```bash
# Find queries with multiple check-sat calls:
grep -l "check-sat" fstar_smt/*.smt2 | head -20
# (Actually ALL F* queries have multiple check-sat in the same file
#  via push/pop)
```

Verify that the profiler re-classifies correctly when assertions change.

---

## 19. Expected Outcomes <a name="outcomes"></a>

### Phase A+B (Signals + Meta-Update): +1-3 queries on critical

The meta-update addresses OrdSet-35 and UInt128-184 specifically:
- OrdSet-35: belief_variance and reward_entropy trigger relevancy
  relaxation → solve
- UInt128-184: conflict_velocity triggers stuck detection → Level 2+
  relaxation → solve

Expected: critical 1389/1391 (up from 1387).

### Phase C (Fallback Cascade): +0-2 more on critical

The cascade provides systematic exploration of configurations.
Matrix-94 might solve with a different QI threshold or with MBQI.

Expected: critical 1389-1391/1391.

### Phase D (Incremental Re-Profiling): +0-5 on everything

Queries that change character between check-sat calls benefit from
re-profiling. Currently the profiler's initial classification is
wrong for some intermediate check-sat calls.

Expected: everything 11300-11310.

### Phase E (Extended Proof Cache): +0-3 on everything

Warm-starting θ from cached effective configurations avoids the
entire fallback cascade on similar queries. Most impactful on
repeated F* verification runs (re-running the same module).

Expected: visible improvement on second runs of same query set.

### Phase F (Portfolio): +5-20 on everything (speculative)

The portfolio approach is the most impactful but also the most
complex. Multiple configurations in parallel cover more of the
search space. The main constraint is CPU budget — each portfolio
member consumes a core.

Expected: significant improvement on hard queries (> 5 seconds),
negligible overhead on easy queries (< 100ms).

### Cumulative Expected Outcome

```
Baseline (pre-roadmap):     critical 1385/1391, everything ~11297
After Phases 0-8 roadmap:   critical 1387/1391, everything ~11304
After auto-solving A+B:     critical 1389/1391, everything ~11305
After auto-solving C+D+E:   critical 1389-1391, everything ~11310
After portfolio (F):        critical 1391/1391(?), everything ~11330(?)
```

The auto-solving framework provides DIMINISHING but CUMULATIVE returns.
Each phase addresses a specific failure mode. The full stack handles:
- Wrong initial classification (fallback cascade)
- Changing query character (incremental re-profiling)
- Repeated queries (proof cache with effective θ)
- Genuinely hard queries (portfolio)
- All queries (manifold-aware meta-optimization on every restart)

### Long-Term Vision

The auto-solving framework makes Z3 SELF-TUNING. Users never need to
set parameters. The solver:
1. Classifies the query automatically (auto-profiler)
2. Starts with a good initial configuration (per-category presets)
3. Monitors its own progress via manifold signals (meta-update)
4. Adapts configuration on each restart (middle loop)
5. Escalates through fallback levels if stuck (cascade)
6. Caches what worked for next time (proof cache)
7. Gets better with every query it solves (learning from experience)

This is the SMT solver equivalent of "just press play" — it figures
out how to solve the problem without human intervention.

---

## Appendix A: Key Files Reference

### Signal Extraction Points
```
sat_solver.cpp:process_antecedent()     — belief variance accumulator
smt_conflict_resolution.cpp             — curvature noise (QI vs non-QI m2)
smt_quantifier.cpp                      — reward entropy (iterate quantifier_stats)
smt_context.cpp                         — theory importance skew
smt_context.cpp:restart()               — conflict velocity
```

### Meta-Update Calling Points
```
smt_context.cpp:restart()               — main meta_update_on_restart entry
sat_solver.cpp:do_restart()             — SAT-level restart hook
sat_dual_mode.cpp:stabilizing()         — mode switch hook
```

### Configuration Application Points
```
smt_setup.cpp:setup_auto_config()       — initial profiler tuning
smt_setup.cpp:setup_unknown()           — fallback profiler path
smt_context.cpp:check()                 — incremental re-profiling
smt_context.cpp:init_search()           — proof cache warm-start
qi_queue.cpp:get_cost()                 — QI threshold application
smt_context.cpp:resolve_conflict()      — relevancy application
sat_solver.cpp:guess()                  — phase strategy application
```

### Data Structure Locations
```
sat_solver.h:m_polarity_belief          — belief vector (V1)
sat_solver.h:m_adam_m1/m2               — Adam moments (V2, V3)
quantifier_stat.h:m_reward              — QI reward EMA (QV1)
smt_context.h:m_theory_importance       — theory importance (TV1)
smt_context.h:m_soft_relevancy          — soft relevancy (RV1)
smt_context.h:m_proof_cache             — proof strategy cache
smt_query_profile.h:query_profile       — static profiler
```

---

## Appendix B: The Optimization Theory Connection

### CDCL as Stochastic Gradient Descent

CDCL is SGD on the constraint polytope:
- Loss function: number of unsatisfied clauses (continuous relaxation)
- Gradient: conflict clause's normal vector
- Step: VSIDS bump = SGD update
- Learning rate: m_activity_inc (exponentially increasing)
- Momentum: phase saving (first moment estimator)
- Restart: learning rate reset (like warm restart in cosine annealing)

### The Auto-Tuning Framework as Meta-Learning

The three-loop architecture is meta-learning:
- Inner loop = base learner (SGD on assignment space)
- Middle loop = hyperparameter optimizer (adjusts base learner's config)
- Outer loop = transfer learner (warm-starts from similar problems)

This is the same structure as MAML (Model-Agnostic Meta-Learning):
- MAML inner loop: adapt model to task via gradient descent
- MAML outer loop: optimize initial parameters across tasks

Our version:
- Inner loop: adapt (x, m1, m2) to query via conflict gradients
- Middle loop: optimize θ during query via manifold signals
- Outer loop: optimize θ₀ across queries via proof cache

### The Manifold Signals as Second-Order Information

The 5 manifold signals approximate the HESSIAN of the meta-loss:
- Belief variance ≈ ∂²L/∂(phase)²
- Curvature noise ≈ ∂²L/∂(qi_threshold)²
- Reward entropy ≈ ∂²L/∂(qi_strategy)²
- Importance skew ≈ ∂²L/∂(theory_focus)²
- Conflict velocity ≈ ∂L/∂t (first-order but for the TIME dimension)

The meta-update uses these second-order signals to take NATURAL GRADIENT
steps on the configuration manifold — adapting the step size per
parameter based on the curvature of the meta-loss landscape.

This is Adam on the configuration space: the belief variance is m2
for the phase parameter, the curvature noise is m2 for the QI parameter,
etc. Optimizers all the way down.
