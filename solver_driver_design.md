# Z3 Solver Driver Design v2 -- Adaptive Data-Driven Exploration

## 1. Overview [REVISED]

The solver driver is a continuous adaptive controller that sits on top of Z3's
search loop. It observes the landscape map (~40 signals), computes a scalar
health score, maintains a temperature (exploration vs exploitation), and
updates 8 solver parameters via gradient estimation (SPSA + Adam).

No rules. No classification. No thresholds. The driver discovers what works
for each problem by trying perturbations and following the health gradient.

```
  landscape map (~40 signals)
         |
         v
  +---------------+
  |    HEALTH     |  single scalar H in [0, 1]
  |   FUNCTION    |  "is the solver making progress?"
  +-------+-------+
          |
          v
  +---------------+
  | TEMPERATURE   |  T in [0.05, 1.0]
  |  (from H      |  high T = explore, low T = exploit
  |  trajectory)  |  derived from MACD of H
  +-------+-------+
          |
          v
  +---------------+
  |  PARAMETER    |  8 continuous parameters
  |   UPDATE      |  gradient step (Adam) + exploration noise (T-scaled)
  |  (SPSA +      |  estimated from dH after Bernoulli perturbation
  |   Adam)       |
  +-------+-------+
          |
          v
  +---------------+
  |   APPLY       |  write parameters into solver config
  |   TO Z3       |  (qi threshold, restart margin, phase noise, etc.)
  +---------------+
```

Key changes from v1:
- Runs every 5000 decisions OR 250 conflicts (whichever first), NOT on restart.
- 8 parameters (down from 12). Polarity bias removed.
- Bernoulli {-1, +1} perturbations (standard SPSA).
- Coordinates with sat::solver dual-mode (stable/focused switching).
- Handles push/pop lifecycle across incremental check-sat calls.
- Portfolio warmup in the first 3-5 update cycles before SPSA takes over.
- Safety freeze: if H > 0.5 for 3 consecutive measurements, T=0 and freeze.

Total cost: ~200ns per update + 320 bytes of state.

---

## 2. Data Fed Into the Driver [REVISED]

### 2.1 The Health Function Inputs

The health function consumes 8 landscape signals, each measuring a different
dimension of "progress toward any answer." All signals are REAL -- verified
present in the `solver_dynamics` struct and maintained as incremental EMAs.
No array scans at driver update time (the only O(N) computation is
`activity_concentration` aka Gini, done once at restart, not per-update).

```
SIGNAL               SOURCE IN solver_dynamics     RANGE    WHAT IT MEASURES
------------------------------------------------------------------------

s1: conflict_rate    conflicts_this_interval /      [0, inf) Raw conflict production rate.
                     decisions_this_interval                  The most direct "are we learning?"
                                                             signal. Zero in dead zones.

s2: conflict_quality avg_glue (recent EMA) /        [0, 1]   Quality of learned clauses.
                     avg_glue (slow EMA)                      Ratio < 1 = improving quality.
                     Both from dynamics.avg_glue              Ratio > 1 = degrading. Uses
                     (fast alpha=0.1 / slow alpha=0.01)       RELATIVE glue, not max_glue.

s3: new_variable_rate dynamics.new_variable_rate    [0, 1]   Fraction of decisions on first-time
                     (B2: first_time_decisions /              variables. Responsive to parameter
                     decisions_this_interval)                  changes. Non-zero even with 0 conflicts.
                                                             Replaces v1's monotonic coverage_growth.

s4: stress_trend     -delta(stress_concentration)   [-1, 1]  Are clauses getting less stressed?
                     from Gini of lit_stress EMAs             Stress decreasing = constraints relaxing
                     via dynamics.stress_gini_trend            = closer to model. Works without conflicts.

s5: trail_stability  dynamics.trail_stability        [0, 1]   Fraction of assignments surviving
                     (C1: polarity survival EMA)              across restarts. High = model building
                                                             progress. Works without conflicts.

s6: fp_hit_rate      dynamics.fp_hit_rate            [0, 1]   Fingerprint dedup hit rate.
                     (B1: fp_hit EMA)                         Rising = E-graph stabilizing, fewer
                                                             new combos = convergence. Works
                                                             without conflicts. 0 if no QI.

s7: wasted_work_rate dynamics.wasted_work_rate       [0, inf) Decisions undone per conflict.
                     (E1: conflict_lvl - backjump_lvl        274 for UFLIA dead zone. 5-15 for
                     EMA)                                    productive UNSAT. CRITICAL efficiency
                                                             signal -- flat landscape becomes visible.

s8: conflict_novelty dynamics.conflict_novelty       [0, 1]   Jaccard distance between consecutive
                     (E4: 1.0 - intersection/union           conflict variable signatures. High =
                     of consecutive conflicts)                 exploring diverse failure modes. Low =
                                                             grinding same bottleneck. 0 if no conflicts.
```

### 2.2 Why These 8 Signals

Design principle: **at least 4 of 8 signals produce meaningful data even
when conflicts = 0.** This is critical because the UFLIA dead zone has zero
or near-zero conflicts, making conflict-based signals (s1, s2, s8) useless.
The driver must still steer using the remaining signals (s3, s4, s5, s6, s7).

The four efficiency signals (wasted_work_rate, learned_clause_velocity,
prop_phase_alignment, conflict_novelty) are crucial for detecting the UFLIA
dead zone. In v1, the health landscape was flat for UFLIA because all
signals went to zero with zero conflicts. Now wasted_work_rate (274 for UFLIA
vs 8 for productive F*) gives a massive gradient even at zero conflict rate.

```
SIGNAL         UFLIA TIMEOUT  PRODUCTIVE F*  QF_BV RESTART  QF_LIA SPIRAL
               (SAT, 0 confl) (UNSAT, many)  (SAT, few)     (UNSAT, many)
------------------------------------------------------------------------
s1 conf_rate   0 (dead)       HIGH           MODERATE       HIGH
s2 conf_qual   N/A            MEANINGFUL     MEANINGFUL     MEANINGFUL
s3 new_var     MEANINGFUL     MEANINGFUL     MEANINGFUL     MEANINGFUL
s4 stress      MEANINGFUL     MEANINGFUL     MEANINGFUL     MEANINGFUL
s5 trail_stab  MEANINGFUL     MEANINGFUL     MEANINGFUL     MEANINGFUL
s6 fp_hit      MEANINGFUL     MEANINGFUL     N/A            N/A
s7 wasted_work MEANINGFUL*    LOW (good)     MODERATE       MODERATE
s8 novelty     0 (dead)       MEANINGFUL     MEANINGFUL     MEANINGFUL

Active signals: 5/8           7/8            6/8            6/8
```

(*) wasted_work_rate is EXTREMELY meaningful for UFLIA: at 274 decisions
undone per conflict, it screams "everything you decide gets backtracked."
This is the signal that breaks the flat landscape.

Every scenario has at least 5 active signals. No single signal failure
blinds the driver.

### 2.3 Health Computation

```
H = sum(wi * normalize(si))

where normalize maps each signal to [0, 1]:
  conflict_rate:    min(rate / 0.1, 1.0) where rate = conflicts/decisions
                    (baseline: 1 conflict per 10 decisions = max health)
  conflict_quality: clamp(1.0 - recent_glue_ema / slow_glue_ema, 0, 1)
                    (improving glue ratio = higher health)
  new_variable_rate: directly [0, 1]
  stress_trend:     clamp(-stress_gini_trend * 10, 0, 1) (decreasing = positive)
  trail_stability:  directly [0, 1]
  fp_hit_rate:      directly [0, 1]
  wasted_work_rate: clamp(1.0 - wasted / 50.0, 0, 1)
                    (low waste = high health; at waste=50, health contribution = 0)
  conflict_novelty: directly [0, 1]

Weights:
  w1 = 0.20  (conflict rate -- strongest signal when available)
  w2 = 0.10  (conflict quality -- enriches conflict rate)
  w3 = 0.10  (new variable rate -- exploration progress)
  w4 = 0.10  (stress trend -- structural progress)
  w5 = 0.10  (trail stability -- model building)
  w6 = 0.10  (fp hit rate -- E-graph convergence, 0 weight if no QI)
  w7 = 0.20  (wasted work -- efficiency, CRITICAL for dead zone detection)
  w8 = 0.10  (conflict novelty -- diversity of learning)

When a signal is N/A (e.g., fp_hit_rate for QF_BV):
  redistribute its weight proportionally to the remaining signals.
```

### 2.4 Why wasted_work_rate Gets 0.20 Weight

The entire point of the driver is solving UFLIA dead zones. In v1, the health
function was blind to these because all conflict-dependent signals reported 0.
Now wasted_work_rate provides a strong negative signal: at 274 decisions undone
per conflict, `normalize(s7) = max(0, 1 - 274/50) = 0`. This drags H down
aggressively, pushing T up, triggering exploration. The 0.20 weight ensures
wasted_work dominates over the weaker zero-conflict signals.

For productive queries (wasted_work ~ 8-15), `normalize(s7) ~ 0.7-0.85`,
contributing positively to H. The signal has excellent dynamic range across
the scenarios that matter.

---

## 3. Temperature Dynamics [REVISED]

Temperature T controls the MAGNITUDE of parameter exploration.
It is derived from the health TRAJECTORY, not the health value.

```
On each driver update (every 5000 decisions or 250 conflicts):
  H_fast = 0.85 * H_fast + 0.15 * H_now
  H_slow = 0.99 * H_slow + 0.01 * H_now

  macd = H_fast - H_slow    // positive = improving, negative = worsening

  // Adam-normalize the MACD signal for stability
  macd_m1 = 0.9 * macd_m1 + 0.1 * macd
  macd_m2 = 0.999 * macd_m2 + 0.001 * macd^2

  // The normalized MACD is the temperature input
  macd_hat = macd_m1 / (sqrt(macd_m2) + 1e-8)   // in [-1, 1] typically

  // Temperature: high when health worsening, low when improving
  // CRITICAL FIX: scale factor must match actual signal magnitude.
  // Adam normalization produces macd_hat in roughly [-3, +3] (Student-t tails).
  // tanh(x * 1.5) saturates at |x| > 2, giving good [-1, +1] coverage.
  T = 0.5 * (1.0 - tanh(macd_hat * 1.5))
  T = clamp(T, 0.05, 0.95)
```

### 3.1 Scale Factor Calibration

v1 used `tanh(macd_normalized * 2.0)`. The problem: Adam normalization
already puts `macd_hat` in roughly [-3, +3]. With scale=2.0 and typical
UFLIA MACD values of +/-0.01 raw, the Adam-normalized value is ~+/-1.0,
giving `tanh(2.0) = 0.96`, which maps to T = 0.02 (frozen) or T = 0.98
(max explore). This seems correct but is fragile.

The new scale factor 1.5 is more conservative:
```
macd_hat = +2.0 (strong improvement): tanh(3.0) = 0.995, T = 0.05 (frozen)
macd_hat = +1.0 (moderate improvement): tanh(1.5) = 0.91, T = 0.05 (exploit)
macd_hat =  0.0 (flat):               tanh(0) = 0,       T = 0.50 (balanced)
macd_hat = -1.0 (moderate worsening):  tanh(-1.5) = -0.91, T = 0.95 (explore)
macd_hat = -2.0 (strong worsening):    tanh(-3.0) = -0.995, T = 0.95 (max)
```

The key insight: Adam normalization handles the scale problem. Raw MACD
values of +/-0.001 or +/-0.1 are both normalized to the same scale by the
second moment. The tanh scale factor only needs to map the [-3, +3] Adam
output to a useful temperature range. 1.5 provides smooth gradients across
the entire range without premature saturation.

### 3.2 Why MACD Instead of Raw Health

Raw health is ABSOLUTE -- it says "health is 0.3." But the driver needs to
know RELATIVE change -- "is health getting better or worse?" A solver at
H=0.3 and improving needs different treatment than one at H=0.3 and stuck.

The MACD (fast EMA - slow EMA) captures exactly this: the difference between
recent performance and historical average. Positive MACD = above average =
improving. Negative = below = worsening.

### 3.3 Update Rate Calibration

v1 used restart-based updates with EMA rates tuned to 10/100 restarts.
Since the driver now runs every 5000 decisions or 250 conflicts:
- Fast EMA alpha=0.15 responds in ~7 updates (~35K decisions or ~1750 conflicts)
- Slow EMA alpha=0.01 responds in ~100 updates (~500K decisions)
- For a typical UFLIA query doing 200K decisions in 120s, the fast EMA
  responds in ~18% of the query time. The slow EMA captures the full query.

---

## 4. Parameter Space [REVISED]

### 4.1 The 8 Parameters

Reduced from 12 to 8. The polarity meta-parameter (v1 theta_11) is removed;
SPSA discovers SAT/UNSAT correlations naturally through the individual
parameter responses. The fanout_boost and polarity_safety parameters are
removed (landscape guidance is orthogonal to the driver). The qi_batch_fraction
is removed (subsumed by qi_eager_threshold modulation).

Each parameter is continuous, bounded, and has a DIRECT causal signal
from the landscape that measures its effect.

```
#   NAME                    RANGE        DEFAULT  CAUSAL SIGNAL           SEMANTICS
--  ----------------------  -----------  -------  ---------------------   --------------------------
1   qi_eager_threshold      [0.5, 100]   7.0      qi_instance_rate (A1)   Cost threshold for eager QI.
                                                                          Higher = fewer eager instances.
                                                                          WRITES TO: qi_queue.m_eager_cost_threshold
                                                                          (direct field, NOT fparams)

2   qi_surprisal_scale      [0.5, 3.0]   1.0      fp_hit_rate (B1)        Multiplier on surprisal
                                                                          coefficient (2.0 base).
                                                                          >1 = faster loop suppression.
                                                                          WRITES TO: fparams.m_qi_surprisal_coeff

3   restart_margin_scale    [0.3, 5.0]   1.0      actual_restart_interval Multiplier on restart agility
                                                   (A2)                    threshold. >1 = restart less
                                                                          often (longer runs). <1 = more
                                                                          restarts. LOG-SPACE perturbation.
                                                                          WRITES TO: fparams.m_restart_agility_threshold

4   activity_decay_scale    [0.95, 1.05] 1.0      activity_concentration  Multiplier on VSIDS inverse
                                                   (A4, Gini)              decay. >1 = faster decay
                                                                          (focus recent). <1 = slower.
                                                                          WRITES TO: fparams.m_inv_decay

5   phase_noise             [0.0, 0.20]  0.0      phase_flip_rate (A3)    Probability of random phase
                                                                          flip per decision. 0 = pure
                                                                          phase caching. LINEAR perturbation.
                                                                          WRITES TO: fparams.m_random_phase_prob

6   relevancy_probability   [0.0, 1.0]   1.0      trail_stability (C1)    Continuous relevancy control.
                                                                          Applied as: effective_level =
                                                                          round(value * max_level) with
                                                                          probabilistic rounding for
                                                                          fractional values.
                                                                          WRITES TO: fparams.m_relevancy_lvl
                                                                          (probabilistic rounding at apply time)

7   mbqi_probability        [0.0, 1.0]   0.0      qi_egraph_growth (C3)   Probability of trying MBQI
                                                                          in final_check. Coin flip
                                                                          each final_check call.
                                                                          0 = ematching only. 1 = MBQI only.
                                                                          WRITES TO: coin flip in final_check_eh

8   gc_aggressiveness       [0.5, 2.0]   1.0      learned_clause_velocity GC threshold multiplier.
                                                   (E2)                    >1 = GC less often (keep more).
                                                                          <1 = GC more (leaner). LOG-SPACE.
                                                                          WRITES TO: fparams.m_lemma_gc_factor
```

### 4.2 The qi_queue Threshold Cache Fix (Issue #1)

`qi_queue::setup()` copies `m_params.m_qi_eager_threshold` into the private
field `m_eager_cost_threshold` once at search initialization. All subsequent
eager/delayed decisions in `qi_queue::instantiate()` use `m_eager_cost_threshold`,
NOT `m_params`. Writing to `fparams` has NO EFFECT on the runtime behavior.

The driver MUST write directly to `qi_queue.m_eager_cost_threshold`. This
requires one of:

Option A (preferred): Add a public setter to qi_queue:
```cpp
void qi_queue::set_eager_threshold(double t) { m_eager_cost_threshold = t; }
```

Option B: The driver gets a reference to `m_eager_cost_threshold` at init and
writes through it.

The design specifies Option A. The implementation adds `set_eager_threshold()`
to `qi_queue.h` and the driver calls it on each parameter application.

### 4.3 Discrete Parameter Handling (Issue #9)

Two parameters (relevancy_probability, mbqi_probability) control discrete
Z3 settings. The driver maintains them as continuous values in [0, 1] and
applies probabilistic wrappers:

**relevancy_probability**: Z3's `m_relevancy_lvl` is an integer in {0, 1, 2}.
The driver maps continuous value v in [0, 1] to:
```
effective_level = floor(v * 2)          // deterministic part
remainder = v * 2 - effective_level     // fractional part
if (random() < remainder)
    effective_level += 1                // probabilistic rounding
effective_level = min(effective_level, 2)
```
This means v=0.7 gives level 1 (40% of the time) or level 2 (60% of the time),
creating a smooth gradient for SPSA.

**mbqi_probability**: Each `final_check_eh` call flips a coin with bias
`mbqi_probability`. If heads, MBQI is attempted. If tails, pure e-matching.
This gives SPSA a smooth gradient: small changes in probability produce
proportional changes in the fraction of final_checks using MBQI.

### 4.4 Perturbation Space (Issue #12)

Parameters with multiplicative semantics (qi_eager_threshold, restart_margin_scale,
gc_aggressiveness) are perturbed in LOG space:
```
theta_perturbed = theta * exp(delta * c)    // delta in {-1, +1}
```
This ensures symmetric perturbations: doubling and halving are equally likely.

Parameters with additive semantics (phase_noise, relevancy_probability,
mbqi_probability) are perturbed in LINEAR space:
```
theta_perturbed = theta + delta * c * range
```

Parameters with small multiplicative range (activity_decay_scale: [0.95, 1.05])
use linear perturbation since log-space and linear-space are nearly identical
over such a narrow range.

### 4.5 Why 8 Parameters (Not 4, Not 12)

v1 had 12 parameters. Three were removed:
- polarity (meta-parameter): created a fixed bias vector that short-circuited
  SPSA's ability to discover correlations (Issue #14). SPSA finds SAT/UNSAT
  configurations faster through individual parameter gradients.
- fanout_boost_strength, polarity_safety_strength: landscape guidance operates
  in the inner loop (per-decision) and is orthogonal to the driver's
  outer-loop macro-configuration.
- qi_batch_fraction: modulating the eager threshold achieves the same
  throttling effect with fewer degrees of freedom.

Each remaining parameter controls a distinct "knob" on the solver:
- 2 knobs for QI (threshold, surprisal)
- 2 knobs for search (restart margin, activity decay)
- 1 knob for exploration (phase noise)
- 2 knobs for theory (relevancy, MBQI)
- 1 knob for GC

---

## 5. The SPSA Gradient Estimation [REVISED]

### 5.1 Bernoulli Perturbations (Issue #5)

SPSA (Simultaneous Perturbation Stochastic Approximation) estimates the
gradient of ALL parameters from a SINGLE pair of health measurements.

The driver alternates between PERTURBATION steps and GRADIENT steps
(Issue #6: eliminates the O(c) bias of one-sided SPSA).

```
State: step_type alternates between PERTURB and GRADIENT.

On each driver update:

if step_type == PERTURB:
  // Generate Bernoulli perturbation vector
  for each parameter j:
    delta[j] = (rng.next_bit() ? +1 : -1)   // Bernoulli {-1, +1}

  // Apply perturbation (respecting log/linear space per parameter)
  for each parameter j:
    if log_space[j]:
      theta_perturbed[j] = theta[j] * exp(delta[j] * c_k)
    else:
      theta_perturbed[j] = theta[j] + delta[j] * c_k * range[j]
    theta_perturbed[j] = clamp(theta_perturbed[j], min[j], max[j])

  // Record health at perturbation start
  H_before = H_now
  step_type = GRADIENT

else:  // step_type == GRADIENT
  // Compute health change
  dH = H_now - H_before

  // SPSA gradient estimate with Bernoulli perturbation
  for each parameter j:
    g[j] = dH / (2.0 * c_k * delta[j])    // delta[j] is +/-1 so division is exact

  // Adam update
  for each parameter j:
    m1[j] = beta1 * m1[j] + (1 - beta1) * g[j]
    m2[j] = beta2 * m2[j] + (1 - beta2) * g[j]^2
    m1_hat = m1[j] / (1 - beta1^t)   // bias correction
    m2_hat = m2[j] / (1 - beta2^t)
    direction[j] = m1_hat / (sqrt(m2_hat) + epsilon)

  // Parameter update: gradient step + exploration noise
  for each parameter j:
    if log_space[j]:
      theta[j] = theta[j] * exp(lr * direction[j] + T * c_k * (rng.next_bit() ? +1 : -1))
    else:
      theta[j] += lr * direction[j] * range[j] + T * c_k * range[j] * (rng.next_bit() ? +1 : -1)
    theta[j] = clamp(theta[j], min[j], max[j])

  step_type = PERTURB

Hyperparameters:
  c_k = 0.05 * (k + 1)^(-0.101)   // perturbation magnitude, decays slowly
  lr  = 0.01                        // learning rate
  beta1 = 0.8                       // Adam first moment decay
  beta2 = 0.99                      // Adam second moment decay
  epsilon = 1e-8                    // Adam denominator regularization
  k = update count (incremented each GRADIENT step)
```

### 5.2 Why Bernoulli {-1, +1} (Not Uniform)

Standard SPSA theory (Spall 1992) requires the perturbation distribution to
satisfy `E[1/delta] < infinity`. Bernoulli {-1, +1} is optimal: it minimizes
the variance of the gradient estimator because `1/delta = delta` (self-inverse).
Uniform perturbations have higher variance because `1/delta` can be very large
when delta is near zero.

### 5.3 Alternating Steps (Issue #6)

One-sided SPSA (v1) computes `dH = H_now - H_prev` where H_prev was measured
at a DIFFERENT perturbation point. This introduces O(c) bias because the
baseline measurement is corrupted by the previous perturbation.

Two-sided alternation fixes this: the PERTURB step applies a perturbation and
records the health. The GRADIENT step computes the difference FROM that
specific perturbation. The health is measured at the same operating point
for both measurements.

The cost: convergence takes 2x as many update cycles. But with decision-based
updates (every 5000 decisions), we get ~40 updates per typical UFLIA query
(200K decisions), giving ~20 gradient steps. This is more than enough for
8 parameters.

### 5.4 Noise Handling

SPSA gradient estimates are noisy (one sample per parameter per step).
Adam's second moment (m2) handles this naturally:
- High noise -> m2 is large -> direction = m1/sqrt(m2) is small -> small steps
- Low noise -> m2 is small -> direction is large -> confident steps

The driver automatically takes bigger steps when the signal is clear and
smaller steps when uncertain. No manual tuning of step sizes.

---

## 6. Update Schedule [REVISED]

### 6.1 Decision-Count-Based Updates (Issue #7)

v1 ran the driver on each restart. This is fatally flawed for UFLIA:
hard UFLIA queries produce only ~4 restarts in 120 seconds (the restart
threshold ramps geometrically while conflicts are rare). SPSA cannot
converge with 4 gradient steps.

The driver now runs on a DECISION-COUNT timer, completely decoupled from
the restart schedule:

```
update_trigger():
  Return true if:
    (decisions_since_last_update >= 5000) OR
    (conflicts_since_last_update >= 250)
  whichever comes first.
```

Rationale for the thresholds:
- 5000 decisions: In a typical UFLIA timeout (200K decisions in 120s),
  this gives 40 update cycles -- enough for 20 SPSA gradient steps with
  alternating perturbation/gradient. Each cycle takes ~0.6ms of wall time.
- 250 conflicts: For conflict-rich queries (productive F*), 250 conflicts
  is ~1 restart interval. This keeps the update rate comparable to v1 for
  queries where restarts are frequent.
- The OR ensures both fast-decision and fast-conflict regimes get adequate
  updates.

The update is hooked into the decision loop (in `bounded_search`, after
the `decide()` call) with a simple counter check. Cost: one integer
comparison per decision, one modular counter increment.

### 6.2 Signal Freshness

All landscape signals are maintained as incremental EMAs that update on
every conflict, decision, or GC event. By the time the driver runs (every
5000 decisions), the signals reflect the solver's recent behavior, not
stale snapshots. No explicit "refresh" step is needed.

The only caveat: `activity_concentration` (Gini) is computed at restart
time because it requires scanning the full activity array. Between restarts,
the driver uses the last computed Gini value. This is acceptable because
the Gini changes slowly (it's a structural property of the activity
distribution, not a transient signal).

---

## 7. Dual-Mode Coordination [REVISED]

### 7.1 The Problem (Issue #8)

sat::solver implements CaDiCaL-style dual-mode switching: alternating
between focused mode (VMTF queue + aggressive Glucose restarts) and
stable mode (VSIDS heap + reluctant doubling restarts). The switching
is controlled by `stabilizing()` with adaptive geometric intervals based
on per-mode learning quality (average glue ratio).

The driver must not fight this system. Specifically:
- The driver must NOT adjust activity_decay during focused mode (VMTF
  ignores VSIDS activities).
- The driver must NOT adjust restart_margin during stable mode (reluctant
  doubling uses a different restart schedule, not agility-based).
- The driver must NOT force mode switches; dual-mode handles its own
  switching based on glue comparison.

### 7.2 The Solution

The driver reads `m_stable_mode` from sat::solver as an INPUT signal.
It partitions its 8 parameters into three groups:

```
ALWAYS ACTIVE (both modes):
  qi_eager_threshold      -- QI is mode-independent
  qi_surprisal_scale      -- QI is mode-independent
  relevancy_probability   -- theory filtering is mode-independent
  mbqi_probability        -- theory strategy is mode-independent
  gc_aggressiveness       -- GC is mode-independent
  phase_noise             -- applies to both VSIDS and VMTF decisions

STABLE MODE ONLY:
  activity_decay_scale    -- VSIDS heap is only used in stable mode
  restart_margin_scale    -- agility-based restarts only in stable mode

FOCUSED MODE ONLY:
  (none currently -- VMTF bump rate and Glucose restart are self-tuning)
```

When in focused mode, the driver FREEZES activity_decay_scale and
restart_margin_scale at their current values. Their gradients are set to
zero and their Adam moments are not updated. This prevents SPSA from
wasting perturbation budget on parameters that have no effect.

When mode switches occur, the driver resumes gradient estimation for the
newly active parameters. The Adam moments carry over (they represent
the historical gradient signal from the last time this mode was active).

### 7.3 Mode-Switch Awareness

The driver maintains a `last_known_mode` flag. On each update, it checks
the current mode. If a switch occurred since the last update, the driver:

1. Records which parameters to freeze/unfreeze
2. Does NOT reset Adam moments (they carry information from prior phases)
3. Does NOT adjust temperature (the health function captures mode-switch
   effects naturally through the conflict/learning signals)

This is a READ-ONLY interaction: the driver never writes to dual-mode
state. If the driver discovers that one mode consistently produces better
health, this manifests as a parameter configuration that works better in
that mode -- the driver adapts its parameters to the mode, not vice versa.

---

## 8. How the Driver Solves Different Problems [REVISED]

### 8.1 UFLIA Matching Loop (Boogie, SAT, 0 conflicts)

Actual signal values from traces:
- wasted_work_rate: 274 (decisions undone per conflict)
- prop_phase_alignment: 0.46 (only 46% of propagations match phase cache)
- qi_instance_rate: ~5000 instances per 1000 decisions
- new_variable_rate: ~0.001 (almost no new variables being explored)
- trail_stability: ~0.3 (poor -- assignments change a lot across restarts)
- fp_hit_rate: ~0.85 (high -- E-graph is stable, same combos recycling)

```
Warmup gate (1000 conflicts): NOT triggered because conflicts ~= 0.
  But the driver activates after 5000 decisions regardless (decision-based).

Update 0-4 (portfolio warmup, ~25K decisions):
  Cycle 0: defaults.
    H = 0.18 (wasted_work drags health down hard: 1 - 274/50 = 0.0)
  Cycle 1: SAT-seeking config (qi_eager=50, mbqi=0.4, relevancy=0.3).
    H = 0.22 (slightly better: fewer QI means less wasted work)
  Cycle 2: UNSAT-seeking config (qi_eager=3, mbqi=0, relevancy=1.0).
    H = 0.12 (worse: more QI floods the solver)
  Cycle 3: QI-throttled config (qi_eager=80, surprisal=2.5).
    H = 0.30 (significantly better: QI nearly stopped, solver explores)
  Cycle 4: Wide search (phase_noise=0.15, restart_margin=0.5).
    H = 0.25 (moderate: random phases help exploration but waste effort)

  Best: cycle 3. SPSA starts from QI-throttled config.
  T is high (~0.8) because health trajectory is flat-to-worsening.

Update 5-15 (SPSA exploration, ~75K decisions):
  SPSA perturbations explore around the QI-throttled config.

  Perturbation: qi_eager_threshold increases to 90.
  H increases: new_variable_rate jumps to 0.05 (solver finally explores
  new variables instead of drowning in QI). trail_stability improves to 0.5.
  Gradient: g[qi_eager] > 0 -> Adam accumulates positive direction.

  Perturbation: mbqi_probability increases to 0.6.
  H increases slightly: when final_check happens, MBQI finds model
  fragments that survive longer. trail_stability reaches 0.6.

  Temperature slowly drops as H improves (MACD turns positive).

Update 15-25 (convergence, ~125K decisions):
  qi_eager_threshold has drifted to ~95 (heavy QI throttling).
  mbqi_probability is ~0.5 (trying MBQI half the time).
  relevancy_probability has drifted to ~0.3 (less filtering).
  H is now 0.35 (much better than initial 0.18).
  T drops to ~0.3 (less exploration).

RESULT: Instead of grinding for 120s on QI matching loops, the solver
  recognizes within ~25K decisions (~15s) that QI is unproductive, throttles
  it aggressively, and either finds SAT via MBQI or returns "unknown" quickly.
```

### 8.2 QF_BV Restart Storm (SAT, few conflicts, 2M restarts)

```
Update 0-4 (portfolio warmup, ~25K decisions):
  Cycle 0: defaults. H = 0.15 (some conflicts but low quality, poor coverage)
  Cycle 3: forces restart_margin_scale=4.0.
    H = 0.40 (dramatic improvement: longer runs, deeper exploration)

  SPSA starts from high-restart-margin config.

Update 5-10 (SPSA, ~50K decisions):
  Perturbation: restart_margin_scale jumps to 4.5.
  H increases: conflict_rate improves (more conflicts per decision when
  not restarting constantly). conflict_novelty is high (diverse conflicts).
  Gradient: g[restart_margin] >> 0 -> strong positive signal.

  Perturbation: activity_decay_scale drops to 0.97 -> faster VSIDS decay.
  H increases: solver focuses on recent hot variables, finds conflicts faster.

  NOTE: if in focused mode (VMTF), activity_decay is frozen.
  The restart_margin perturbation still works because even focused mode
  uses Glucose-style restarts that respond to the agility threshold.

Update 10-15 (convergence):
  restart_margin has drifted to ~4.5 (very infrequent restarts).
  The restart storm is broken.
  T drops to 0.15 (exploitation mode).

RESULT: The driver discovered that restart_margin was the critical
  parameter, purely from health feedback.
```

### 8.3 Productive F* Query (UNSAT, many conflicts)

```
Update 0-2 (portfolio warmup):
  Cycle 0: defaults.
    H = 0.62 (conflicts happening, good quality, QI productive,
    wasted_work ~8 -> normalize = 0.84).
  All portfolio configs score LOWER than defaults.

  Safety mechanism activates: H > 0.5 for 3 consecutive measurements.
  Driver FREEZES: T = 0, all parameters locked at defaults.

Rest of query:
  Parameters = defaults. Driver is invisible.
  The solver solves with its normal strategy, unperturbed.

RESULT: The driver is INVISIBLE for productive queries. The safety freeze
  ensures defaults are preserved. Zero overhead on the 90% of queries
  that don't need help.
```

### 8.4 QF_LIA Theory Spiral (UNSAT, many conflicts, deep scope)

```
Update 0-4 (portfolio warmup):
  Cycle 0: defaults. H = 0.30 (conflicts happening but high glue,
  low novelty, wasted_work ~25 -> normalize = 0.50).
  Cycle 1: SAT-seeking (relevancy=0.3). H = 0.35 (slightly better).

  SPSA starts from slightly relaxed relevancy config.

Update 5-15 (SPSA):
  Perturbation: relevancy_probability drops to 0.2.
  H improves: conflict_rate increases (solver sees more of the formula,
  finds better conflicts). conflict_novelty jumps (diverse failure modes).
  Gradient: g[relevancy] < 0 -> less relevancy is better.

  Perturbation: restart_margin drops to 0.6.
  H improves: solver escapes deep theory branches faster.
  wasted_work_rate drops from 25 to 18.

  Perturbation: gc_aggressiveness drops to 0.7.
  H improves slightly: leaner clause database, less memory pressure.

Update 15-25 (convergence):
  relevancy ~= 0.1 (nearly disabled)
  restart_margin ~= 0.6 (frequent restarts)
  gc_aggressiveness ~= 0.7 (aggressive GC)

RESULT: The driver discovered that the default relevancy filtering
  was hiding important clauses, and deep branches needed more frequent
  escape. It adapted without any theory-specific rules.
```

---

## 9. Driver Policies [REVISED]

The driver has a single policy with two phases: PORTFOLIO WARMUP followed
by SPSA GRADIENT DESCENT. No policy selection parameter. No mode switching
between policies.

### 9.1 Portfolio Warmup (First 3-5 Update Cycles)

The first 3-5 update cycles try predefined diverse configurations to quickly
discover which axis of the parameter space matters. This replaces v1's
multiple policy system (aggressive/conservative/annealing/portfolio).

```
Warmup configurations (5 cycles):
  cycle 0: defaults (baseline)
  cycle 1: SAT-seeking
    qi_eager_threshold = 50.0
    mbqi_probability = 0.4
    relevancy_probability = 0.3
    (others at default)
  cycle 2: UNSAT-seeking
    qi_eager_threshold = 3.0
    mbqi_probability = 0.0
    relevancy_probability = 1.0
    (others at default)
  cycle 3: QI-throttled
    qi_eager_threshold = 80.0
    qi_surprisal_scale = 2.5
    (others at default)
  cycle 4: Wide search
    phase_noise = 0.15
    restart_margin_scale = 0.5
    (others at default)

After all 5 cycles:
  - Find the configuration with the best H.
  - Initialize SPSA theta to that configuration.
  - Initialize Adam moments to zero.
  - Set T from the MACD of the H trajectory during warmup.
  - Switch to SPSA gradient descent.
```

The warmup serves the same purpose as v1's polarity meta-parameter: it
quickly identifies whether the problem is SAT-seeking, UNSAT-seeking,
QI-bottlenecked, or something else. But instead of biasing all parameters
through a fixed vector, it directly measures the health response to each
configuration and lets SPSA optimize from the best starting point.

### 9.2 SPSA Gradient Descent (After Warmup)

After warmup, the driver runs standard alternating SPSA as described in
Section 5. Hyperparameters:

```
lr = 0.01                   // learning rate (moderate)
c_0 = 0.05                  // initial perturbation scale
c_decay = 0.101             // perturbation decay exponent: c_k = c_0 * (k+1)^(-0.101)
beta1 = 0.8                 // Adam momentum (reactive)
beta2 = 0.99                // Adam variance tracking
epsilon = 1e-8              // Adam regularization
H_fast_alpha = 0.15         // fast health EMA (~7 update response)
H_slow_alpha = 0.01         // slow health EMA (~100 update response)
T_scale = 1.5               // tanh temperature sensitivity
```

The perturbation scale c_k decays as k^(-0.101), matching the standard
SPSA convergence requirement (c_k -> 0, sum c_k^2 < inf). The very slow
decay exponent (0.101 vs the textbook 0.167) keeps perturbations meaningful
for longer, which matters because we have limited update budget.

---

## 10. Safety Mechanisms [REVISED]

### 10.1 Warmup Gate (1000 Conflicts)

The driver does NOT activate until either:
- 1000 conflicts have occurred, OR
- 25000 decisions have occurred (5 warmup cycles at 5000 decisions each)

The conflict gate ensures trivial queries (solved in <1000 conflicts) are
never disturbed. The decision gate ensures the driver activates even for
UFLIA queries with near-zero conflicts.

### 10.2 Safety Freeze (Issue #20)

If the health score H exceeds 0.5 for 3 CONSECUTIVE measurements (including
warmup), the driver concludes that the solver is doing well with the current
configuration and FREEZES:

```
if H_history[t] > 0.5 AND H_history[t-1] > 0.5 AND H_history[t-2] > 0.5:
  T = 0                    // no exploration
  freeze all parameters    // skip all SPSA updates
  // Re-evaluate every 50 updates: if H drops below 0.3, unfreeze.
```

This prevents the driver from making things worse on easy queries. The
freeze is not permanent: if health degrades (e.g., the solver enters a
new phase where defaults fail), the driver unfreezes and resumes exploration.

### 10.3 Parameter Bounds

Each parameter has hard bounds (Section 4.1) that are NEVER violated.
The driver clamps after every update. The bounds are conservative:
- qi_eager_threshold max=100 (not infinity -- prevents total QI shutdown)
- phase_noise max=0.20 (not 1.0 -- prevents random search)
- activity_decay_scale within [0.95, 1.05] (tiny range -- VSIDS is fragile)

### 10.4 Health Function Sanity

If all 8 health signals report NaN or zero (complete sensor failure), the
driver sets H = 0.5 (neutral) and T = 0.5 (balanced). It does not amplify
phantom signals.

---

## 11. Push/Pop Lifecycle [REVISED]

### 11.1 Incremental Mode (Issue #16)

For incremental queries (Boogie with 182 check-sats), the driver must handle
push/pop scope transitions and multiple check-sat calls.

```
On push_scope():
  Save driver state to scope stack:
    - parameters theta[0..7]
    - Adam moments m1[0..7], m2[0..7]
    - H_fast, H_slow, T
    - update_count

On pop_scope():
  Restore driver state from scope stack.

On new check-sat (init_search):
  // Persist across check-sat calls:
  - parameters theta[0..7]        // the learned configuration
  - temperature T                  // current exploration level

  // Reset across check-sat calls:
  - Adam moments m1, m2 -> zero   // fresh gradient estimation
  - H_fast, H_slow -> 0.5         // neutral health baseline
  - MACD moments -> zero           // fresh trajectory estimation
  - step_type -> PERTURB           // restart alternation
  - update_count -> 0              // fresh perturbation decay
  - safety_freeze -> false         // re-evaluate freezing

  // Skip warmup if parameters are non-default:
  - If any theta[j] != default[j], skip portfolio warmup and go straight
    to SPSA. The parameters from the previous check-sat are the best
    starting point for the next one (incremental problems are similar).
  - If all theta[j] == default[j], run full warmup.
```

### 11.2 Rationale

Persisting parameters captures the "character" of the problem series. If
the first 50 check-sats are all QI-heavy UFLIA, the driver will have
converged on a QI-throttled configuration. The 51st check-sat starts from
that configuration, which is likely close to optimal.

Resetting Adam moments and health baselines avoids "momentum pollution":
the gradient from check-sat #50 is not relevant to check-sat #51 (different
assertions, different search space). Fresh moments let SPSA re-estimate
gradients from the new starting point.

Resetting safety_freeze forces re-evaluation: just because check-sat #50
was easy (H > 0.5) doesn't mean #51 will be.

---

## 12. Interaction with Existing Systems [REVISED]

### 12.1 Relationship to auto_tune / meta_update_on_restart

The existing `meta_update_on_restart()` in smt_context.cpp makes RULE-BASED
adjustments based on manifold signals. The solver driver REPLACES this with
gradient-driven adjustments. When the driver is active:

- The existing rule-based adjustments (B3-B9, C2-C5) are DISABLED.
- The velocity gate and QI fast-reject remain active (safety mechanisms).
- The driver controls the SAME parameters that auto_tune controls, but via
  continuous optimization rather than threshold-based rules.

The driver is gated behind `smt.solver_driver=true` (default: false),
separate from `smt.auto_tune`. When both are true, the driver takes
precedence and disables meta_update_on_restart's parameter adjustments.

### 12.2 Relationship to Landscape Map

The landscape map is the SENSOR ARRAY. The driver is the CONTROLLER.
The map collects data passively. The driver reads the data and acts.

The driver does NOT modify the landscape map. Information flows one way:
  landscape -> driver -> solver parameters

All signals consumed by the driver are maintained as incremental EMAs in
the `solver_dynamics` struct. The driver accesses them in O(1) time via
`m_landscape.dynamics()`. No array scans, no recomputation.

### 12.3 Relationship to VSIDS/Adam

The driver does NOT replace VSIDS or the per-variable Adam optimizer.
Those operate in the INNER LOOP (per conflict). The driver operates in the
OUTER LOOP (per 5000 decisions). They are complementary:

- VSIDS/Adam: which variable to branch on next (micro-decisions)
- Driver: how the branching heuristic BEHAVES (macro-configuration)

The driver adjusts activity_decay_scale, which affects how fast VSIDS
forgets old information. But it never directly sets variable activities.

### 12.4 Relationship to Dual-Mode (Issue #8)

The driver treats dual-mode as a READ-ONLY input signal. It reads
`m_stable_mode` and freezes mode-specific parameters during the wrong
mode (see Section 7). It never writes to dual-mode state or influences
mode switching decisions.

---

## 13. State and Memory [REVISED]

```
DRIVER STATE (320 bytes):

  Parameters:        8 x double = 64 bytes
  Adam m1:           8 x double = 64 bytes
  Adam m2:           8 x double = 64 bytes
  Previous delta:    8 x int8   =  8 bytes   (Bernoulli: only need +/-1)
  H_fast, H_slow:    2 x double = 16 bytes
  macd_m1, macd_m2:   2 x double = 16 bytes
  T, H_before:        2 x double = 16 bytes
  Counters:          update_count, step_type, decisions_since_update,
                     conflicts_since_update, warmup_cycle, safety_streak,
                     last_known_mode, frozen_flag  = 32 bytes
  Warmup H:          5 x double = 40 bytes   (one per portfolio config)
  Total:             320 bytes (fits in 5 cache lines)

  Parameter bounds:  8 x (min + max + default + log_space_flag) = 264 bytes (const, shared)
```

This is negligible compared to the landscape map (~60MB) or the solver
state (~100MB).

---

## 14. Evaluation Criteria

The driver is successful if:

1. **Easy queries unaffected**: 90% of queries that solve in <1s should
   have identical performance (within 5%) with and without the driver.
   The warmup gate + safety freeze ensures this.

2. **Hard queries improved**: The 2% of queries that currently timeout
   should see measurable improvement -- either solving or returning
   "unknown" faster.

3. **No new regressions**: The everything suite should maintain >= 11,305.
   Any query that passed before should still pass.

4. **CPU overhead < 1%**: The driver's computation (health + gradient +
   parameter update) adds one integer comparison per decision and ~200ns
   per update every 5000 decisions. For a 120s query: ~4800 updates at
   200ns = ~1ms total. Negligible.

---

## 15. Implementation Plan

Phase 1: Core driver struct + health function + temperature + SPSA
  New files: src/smt/solver_driver.h, src/smt/solver_driver.cpp
  Add `set_eager_threshold(double)` to qi_queue.h
  Integration: call driver.on_decision() from bounded_search inner loop
  Gate: smt.solver_driver=true enables driver

Phase 2: Apply parameters to solver
  Wire each theta[j] to its corresponding solver config (Section 4.1)
  Implement probabilistic wrappers for relevancy_probability, mbqi_probability
  Test: verify each parameter has measurable effect on its causal signal

Phase 3: Portfolio warmup
  Implement the 5 predefined configurations
  Implement best-config selection and SPSA initialization

Phase 4: Dual-mode coordination
  Read m_stable_mode from sat::solver
  Implement parameter freezing for mode-specific parameters

Phase 5: Push/pop lifecycle
  Save/restore driver state on push/pop
  Persist parameters, reset moments across check-sat calls

Phase 6: Safety mechanisms
  Implement safety freeze (H > 0.5 for 3 measurements)
  Implement health sanity checks

Phase 7: Evaluation and tuning
  Run everything suite comparing driver ON vs OFF
  Trace UFLIA + QF_BV + QF_LIA + F* benchmarks
  Tune warmup configs and SPSA hyperparameters

---

## 16. Open Questions

1. Should the warmup configurations be ADAPTIVE based on initial landscape
   signals? E.g., if qi_instance_rate is already zero at cycle 0 (no QI
   in the problem), skip the QI-throttled warmup and replace it with a
   different configuration. This would make warmup more efficient for
   QF logics.

2. Should the driver have a FALLBACK to the existing rule-based
   meta_update_on_restart if SPSA fails to improve health after N cycles?
   The rule-based system is known to work for some scenarios. A hybrid
   approach (SPSA when improving, rules when stuck) might be more robust.

3. The perturbation decay c_k -> 0 means the driver eventually stops
   exploring. For very long queries (>1M decisions), should c_k have a
   floor? E.g., c_floor = 0.01 to maintain minimum perturbation.

4. Should the driver track WHICH parameters produce the largest health
   changes and allocate more perturbation budget to them? This is
   "natural gradient" SPSA and could accelerate convergence for problems
   where only 1-2 parameters matter.

---

## 17. Changelog from v1

### CRITICAL fixes:

**Issue #1 (qi_queue threshold cache)**: The driver now writes DIRECTLY to
`qi_queue.m_eager_cost_threshold` via a new `set_eager_threshold(double)`
method. v1 wrote to `fparams.m_qi_eager_threshold` which had NO EFFECT
because `qi_queue::setup()` copies the value once at search init. Section 4.2.

**Issue #2 (phantom signals)**: Removed `model_progress` and `fp_convergence`
(phantom signals that did not exist in the codebase). Replaced with REAL
signals: `fp_hit_rate` (B1), `trail_stability` (C1), `new_variable_rate`
(B2), `wasted_work_rate` (E1). Section 2.1.

**Issue #7 (restart-based updates)**: Driver now runs every 5000 decisions
OR 250 conflicts, whichever comes first. Completely decoupled from the
restart schedule. UFLIA queries with ~4 restarts in 120s now get ~40
driver updates. Section 6.

### HIGH fixes:

**Issue #3 (glue normalization)**: Replaced `glue / max_glue` (meaningless --
max_glue is an unbounded integer) with `recent_glue_ema / slow_glue_ema`
(relative quality: improving ratio < 1, degrading ratio > 1). Section 2.1 s2.

**Issue #4 (monotonic coverage)**: Replaced `coverage_growth` (monotonically
increasing, unresponsive to parameter changes) with `new_variable_rate`
(B2: fraction of decisions on first-time variables, resets each interval).
Section 2.1 s3.

**Issue #5 (SPSA perturbation distribution)**: Changed from uniform [-1, +1]
to Bernoulli {-1, +1}. Standard SPSA: optimal variance, self-inverse for
clean gradient formula `g[j] = dH / (2 * c * delta[j])`. Section 5.1.

**Issue #8 (dual-mode conflict)**: Driver now reads `m_stable_mode` as input
signal. Freezes mode-specific parameters (activity_decay in focused mode,
restart_margin in stable mode). Never writes to dual-mode state. Section 7.

**Issue #9 (discrete parameters)**: `relevancy_probability` uses probabilistic
rounding of continuous value to integer level. `mbqi_probability` uses coin
flip in final_check. Both give smooth gradients for SPSA. Section 4.3.

### MEDIUM fixes:

**Issue #6 (one-sided SPSA bias)**: Driver now alternates PERTURBATION and
GRADIENT steps. Health is measured at the specific perturbation point, not
relative to a different operating point. Eliminates O(c) bias. Section 5.3.

**Issue #10 (flat UFLIA landscape)**: Added `wasted_work_rate` (274 for UFLIA!)
as a health signal with weight 0.20. The flat landscape is broken: UFLIA's
massive wasted work drags health to zero, creating a strong gradient toward
QI throttling. Section 2.1 s7, 2.4.

**Issue #12 (perturbation scale)**: Multiplicative parameters (qi_eager,
restart_margin, gc) perturbed in LOG space. Additive parameters (phase_noise,
relevancy, mbqi) perturbed in LINEAR space. Section 4.4.

**Issue #13 (O(N) data access)**: All signals are incremental EMAs in
`solver_dynamics`, accessed in O(1). The only O(N) computation
(`activity_concentration` Gini) runs at restart time, not per-update.
Section 6.2.

**Issue #14 (polarity bias)**: Removed the polarity meta-parameter and its
fixed bias vector. SPSA discovers SAT/UNSAT correlations naturally through
individual parameter responses. Portfolio warmup handles fast axis
exploration. Section 4.5.

**Issue #16 (push/pop lifecycle)**: Parameters persist across check-sat calls.
Adam moments and health baselines reset. Safety freeze re-evaluated. Warmup
skipped if parameters are non-default. Section 11.

**Issue #17 (qi_efficiency dynamic range)**: Removed the single `qi_efficiency`
signal. Replaced with three responsive signals: `qi_instance_rate` (A1,
via the causal pair for qi_eager_threshold), `qi_egraph_growth` (C3, via
the causal pair for mbqi_probability), and `fp_hit_rate` (B1, via the
causal pair for qi_surprisal_scale). Section 4.1.
