# Z3 SMT Optimization Roadmap — Unified Manifold & Learned Heuristics

## Table of Contents
1. [Vision](#vision)
2. [Current State & Baseline](#current-state)
3. [The Problem: 15 Disconnected Feedback Loops](#the-problem)
4. [Atomic Component Catalog](#component-catalog)
5. [Phase 0: Infrastructure](#phase-0)
6. [Phase 1: Signal Enrichment](#phase-1)
7. [Phase 2: QI Feedback Loop](#phase-2)
8. [Phase 3: Better Phase Selection](#phase-3)
9. [Phase 4: Adaptive Optimizers](#phase-4)
10. [Phase 5: Connected Manifold](#phase-5)
11. [Phase 6: Full Stack Optimizer](#phase-6)
12. [Phase 7: Learned Heuristics](#phase-7)
13. [Phase 8: Research Frontier](#phase-8)
14. [Dependency Graph & Priority Order](#dependencies)
15. [Testing Methodology](#testing)
16. [Expected Outcomes](#outcomes)

---

## 1. Vision <a name="vision"></a>

Z3 currently has ~15 independent heuristic feedback loops, each extracting a different
signal from the same source (conflicts) and making decisions that affect all the others.
None of them coordinate. The SAT layer (bottom) has the most sophisticated heuristics
(VSIDS, 25 years of tuning). The SMT layers above (QI, E-matching, theory propagation)
— which control what the SAT solver even SEES — use the crudest heuristics.

The vision: replace disconnected heuristics with a unified learned optimizer that:
- Extracts a SINGLE rich gradient from each conflict
- Updates a SINGLE per-variable state vector
- Derives ALL decisions (branching, phase, restart, GC, QI, theory prop) from that state
- Caches proof strategies in a Merkle DAG for cross-query transfer
- Gets smarter with every query it solves

This roadmap goes from "change 15 lines, zero risk" to "MuZero-guided QI with Merkle
DAG proof caching" in concrete, testable steps. Each step builds on the previous and
can be independently validated.

---

## 2. Current State & Baseline <a name="current-state"></a>

### Build Configuration
```bash
cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=RelWithDebInfo -DCMAKE_CXX_COMPILER=clang++
ninja -C build -j$(nproc)
```

### Baseline Numbers (commit 10319e2f3, 2026-03-21)
```
smoke:       40/40 pass
critical:    1385/1391 (60s timeout)
everything:  11297/11911 (94.9%), 942s CPU (RelWithDebInfo, default parallelism)
```

### Key Test Query: ModifiesGen-195
```
File:               fstar_smt/queries-FStar.ModifiesGen-195.smt2
Lines:              16,128
Asserts:            891 (819 quantified)
Quantifiers:        1,087 forall, 6 exists
Solve time:         6.4 seconds
QI instantiations:  873,788
Useful instances:   ~2,000-5,000 (estimated)
Conflicts:          945
Generations:        19 (cascade depth)
Memory:             56 MB

Diagnosis: 99.4% of QI work is wasted. SAT solver is idle.
The proof requires ~50 key instantiations. 873K are noise.
```

### Previously Completed Optimizations
- MurmurHash finalization (hash.h)
- Prefetch during hash table probing
- Hash entry compaction (packed state in top 2 bits)
- SInE rarity scoring for triggers
- Three-tier trigger weight system
- mimalloc as global allocator
- Persistent rewrite cache
- Arith sum coefficient merging
- Fingerprint dedup optimization
- Boolean attribute bit-packing
- SAT dual-mode (CaDiCaL-style stable/focused)
- SAT OTFS (on-the-fly strengthening)
- MAM BIND iteration reorder + cache
- enode func_decl cache + eager func_lbl_hash
- Swiss table migration (17 files)
- enode field reorder (CL1/CL2)
- root_hash mixing (fmix64)

---

## 3. The Problem: 15 Disconnected Feedback Loops <a name="the-problem"></a>

### The SMT Decision Stack (top to bottom)

```
┌─────────────────────────────────────────────────────┐
│  QI: Which quantifier? Which bindings? How many?    │ ← RIGID. cost=gen². No feedback.
├─────────────────────────────────────────────────────┤
│  E-matching: Which triggers? What order?            │ ← RIGID. Static weights. No adaptation.
├─────────────────────────────────────────────────────┤
│  Relevancy: Which subformulas matter?               │ ← BINARY. On/off. No gradient.
├─────────────────────────────────────────────────────┤
│  Theory prop: Which bounds to push? Priority?       │ ← FIFO. No priority at all.
├─────────────────────────────────────────────────────┤
│  BV strategy: Blast or reason natively?             │ ← ALWAYS BLAST. No adaptation.
├─────────────────────────────────────────────────────┤
│  SAT: Which variable? Which polarity? When restart? │ ← VSIDS. 25 years of tuning.
└─────────────────────────────────────────────────────┘
```

The irony: the BOTTOM layer has the most sophisticated heuristics. The TOP layers
— which control what the SAT solver even SEES — use the crudest heuristics.

### Where Learning Currently Happens
```
Step 2f — activity bump         YES  (VSIDS: 1 scalar/var, exponential decay)
Step 2f — phase cache           SORT OF  (saves last assignment, no gradient)
Step 2h — restart EMA           YES  (glue EMA tracks learning quality)
Step 2i — GC scoring            SORT OF  (LBD tiers, but no feedback)
Step 4d — QI scoring            NO   (static formula: cost × generation)
Step 4a — trigger selection     NO   (static weights, no adaptation)
Step 3  — theory prop priority  NO   (FIFO, no priority)
Step 1  — preprocessing         NO   (fixed pipeline)
Step 0  — internalization       NO   (no cross-query memory)
```

### The Solving Loop as a Training Loop

Each conflict is one training step:
```
Forward pass:  decisions + propagation (steps 2a-2c)
Loss:          conflict clause (step 2d)
Backward pass: resolution / antecedent tracing (step 2d)
Gradient:      which variables were in the conflict (step 2f)
Weight update: activity bump (step 2f)
```

Problem: we only update weights at step 2f, and only for SAT-level branching.
Steps 3, 4a, 4d — the SMT layers where most time is spent — have NO backward
pass at all. The conflict signal stops at SAT and never flows up.

### The Manifold View

The natural object: the assignment polytope [0,1]^n.

Given formula φ over n variables, the relaxed feasible region is:
  P = { x ∈ [0,1]^n : for each clause C, Σ(lit_value(x, l)) ≥ 1 }

The solver maintains ONE state per variable: x ∈ [0,1]^n — continuous belief.
- x_v ≈ 1: solver believes v should be TRUE
- x_v ≈ 0: solver believes v should be FALSE
- x_v ≈ 0.5: uncertain

Every decision derives from x:
- Branch: argmax |x_v - 0.5| (most confident first)
- Phase: sign(x_v - 0.5)
- Restart: ‖∇L‖ drops below threshold
- GC: clauses with low gradient contribution
- QI: quantifiers whose variables have high importance

One object → five decision types. No separate heuristics.

The gradient from conflict clause C with glue g:
  g_v = -(assigned_polarity) × (1/glue) × (1/√|C|)

Three terms, each meaningful:
- -(assigned_polarity): push AWAY from failing value
- 1/glue: low-glue conflicts are tighter, stronger signal
- 1/√|C|: Muon normalization, constant total per conflict

Adam's second moment provides Riemannian metric:
  m2_v = EMA of g_v² → local curvature estimate
  Update: x_v += m1_v / (√m2_v + ε) → natural gradient step

---

## 4. Atomic Component Catalog <a name="component-catalog"></a>

### SAT Signal Components

| ID  | Name              | What                                        | Code  |
|-----|-------------------|---------------------------------------------|-------|
| S1  | LBD weighting     | Multiply bump by 1/max(glue,1)              | 1 line|
| S2  | Clause-size norm  | Multiply bump by 1/√|C| (Muon)             | 3 lines|
| S3  | Polarity gradient | Signed bump: -(assigned_pol) × magnitude    | 5 lines|

### SAT Per-Variable State

| ID  | Name            | What                                        | Memory    |
|-----|-----------------|---------------------------------------------|-----------|
| V1  | Belief vector   | x[v] ∈ [-1,1] — continuous polarity         | 8 bytes/var|
| V2  | First moment    | m1[v] — EMA of gradient magnitude           | 8 bytes/var|
| V3  | Second moment   | m2[v] — EMA of squared gradient             | 8 bytes/var|
| V4  | Lazy timestamps | last_update[v] — for O(1) batch decay       | 8 bytes/var|

### SAT Decision Components

| ID  | Name               | Derives from        | Replaces              |
|-----|--------------------|--------------------|-----------------------|
| D1  | VSIDS heap         | m_activity[v]      | nothing (keep)        |
| D2  | Adam-score heap    | m1/(√m2+ε)         | VSIDS activity        |
| D3  | Combined score     | importance×|x-0.5| | VSIDS + phase priority|
| D4  | Belief phase       | sign(x[v])         | phase cache cascade   |
| D5  | Gradient-norm restart | ‖g‖ EMA < thr   | glue EMA restart      |
| D6  | Utility-scored GC  | per-clause grad EMA| LBD-tier GC           |

### SAT Infrastructure

| ID  | Name               | What                                       | Used by     |
|-----|--------------------|-------------------------------------------|-------------|
| I1  | Gradient extractor | Compute (magnitude, sign) per var, ONCE   | all consumers|
| I2  | Lazy decay engine  | Timestamped batch decay, precomputed tables| V1,V2,V3    |
| I3  | Conflict stats     | Precompute (glue, |C|, depth)             | S1,S2,S3,D5 |

### SMT Signal Components

| ID  | Name                  | What                                     | Cost      |
|-----|-----------------------|------------------------------------------|-----------|
| QS1 | QI clause tagging     | Mark QI clause with source quantifier ID | ~2 lines  |
| QS2 | QI conflict attrib    | Record QI antecedents in conflict chain  | ~10 lines |
| TS1 | Theory conflict signal| Which theory atoms caused conflict       | ~5 lines  |
| BS1 | BV blast size         | Measure SAT vars per BV blast operation  | ~3 lines  |

### SMT Per-Object State

| ID  | Name                   | What                                      | Memory        |
|-----|------------------------|-------------------------------------------|---------------|
| QV1 | Quantifier reward      | EMA of success rate                       | 8 bytes/quant |
| QV2 | Quantifier Adam moments| m1/m2 of reward signal                    | 16 bytes/quant|
| QV3 | Trigger effectiveness  | EMA of match_rate × success_rate          | 8 bytes/trigger|
| TV1 | Theory var importance  | EMA of theory-conflict participation      | 8 bytes/t_var |
| BV1 | BV blast confidence    | Continuous strategy selector              | 8 bytes/bv_op |
| RV1 | Soft relevancy         | Continuous ∈ [0,1] per formula node       | 8 bytes/expr  |

### SMT Decision Components

| ID  | Name                   | Derives from              | Replaces           |
|-----|------------------------|--------------------------|--------------------|
| QD1 | Reward-adjusted QI     | cost × gen / reward      | static cost×gen    |
| QD2 | Adaptive QI budget     | global success → cap     | fixed budget       |
| QD3 | Trigger priority       | effectiveness order      | static weight order|
| TD1 | Theory prop priority   | importance pqueue        | FIFO               |
| BD1 | Adaptive BV threshold  | confidence > θ → blast   | always blast       |
| RD1 | Relevancy-weighted bumps| SAT bumps × relevancy   | binary relevancy   |

### Cross-Stack Connections

| ID | Name                  | Direction | What flows                              |
|----|-----------------------|-----------|-----------------------------------------|
| C1 | SAT→QI gradient       | upward    | Conflict antecedent is QI → reward quant|
| C2 | QI→SAT belief weight  | downward  | QI quality weights belief updates       |
| C3 | SAT→Theory gradient   | upward    | Theory conflict → bump theory var imp   |
| C4 | Theory→SAT gradient   | downward  | High-imp theory prop → boost SAT var    |
| C5 | Relevancy→SAT modul   | downward  | Relevancy scores scale SAT bumps        |
| C6 | SAT→Relevancy gradient| upward    | Conflict participation → boost relevancy|

### Component × Track Matrix

```
                    T1   T2   T3   T4   T5   T6   T7
                   ──────────────────────────────────────
SAT SIGNALS
  I3 conflict stats  ●    ●    ●    ●    ●    ●    ●
  S1 LBD weight      ●    ●    ●    ●    ●    ●    ●
  S2 size norm       ●    ●    ●    ●    ●    ●    ●
  S3 polarity sign        ●         ●    ●    ●    ●
SAT STATE
  V1 belief x[v]          ●         ●    ●    ●    ●
  V2 Adam m1                   ●    ●    ●    ●    ●
  V3 Adam m2                   ●    ●    ●    ●    ●
  V4 timestamps                ●    ●    ●    ●    ●
  I2 lazy decay                ●    ●    ●    ●    ●
SAT DECISIONS
  D1 VSIDS heap       ●    ●
  D2 Adam score                ●    ●
  D3 combined score                      ●    ●    ●
  D4 belief phase          ●         ●    ●    ●    ●
  D5 gradient restart                    ●    ●    ●
  D6 utility GC                          ●    ●    ●
SMT SIGNALS
  QS1 QI tagging      ●    ●    ●    ●    ●    ●    ●
  QS2 QI attribution  ●    ●    ●    ●    ●    ●    ●
  TS1 theory conflict            ●    ●    ●    ●    ●
  BS1 BV blast size              ●    ●    ●    ●    ●
SMT STATE
  QV1 quant reward          ●         ●    ●    ●    ●
  QV2 quant Adam                 ●    ●    ●    ●    ●
  QV3 trigger effect             ●    ●    ●    ●    ●
  TV1 theory var imp             ●    ●    ●    ●    ●
  BV1 blast confidence                    ●    ●    ●
  RV1 soft relevancy                 ●    ●    ●    ●
SMT DECISIONS
  QD1 reward QI score       ●         ●    ●    ●    ●
  QD2 adaptive QI budget                   ●    ●    ●
  QD3 trigger priority           ●    ●    ●    ●    ●
  TD1 theory prop prio           ●    ●    ●    ●    ●
  BD1 adaptive BV                          ●    ●    ●
  RD1 relevancy bumps                 ●    ●    ●    ●
CROSS-STACK
  C1 SAT→QI gradient   ●    ●    ●    ●    ●    ●    ●
  C2 QI→SAT weight                    ●    ●    ●    ●
  C3 SAT→Theory grad             ●    ●    ●    ●    ●
  C4 Theory→SAT grad                  ●    ●    ●    ●
  C5 Relevancy→SAT                    ●    ●    ●    ●
  C6 SAT→Relevancy                    ●    ●    ●    ●
LEARNED
  W  weights                                ●    ●
  F  features                               ●    ●
  T  online training                        ●    ●
GPU
  G1-G7 SAT GPU                                  ●
  GQ1-GQ2 QI GPU                                 ●
  GB1-GB2 BV GPU                                 ●
```

---

## 5. Phase 0: Infrastructure <a name="phase-0"></a>

### Task 0.1: Conflict Statistics Extractor (I3)

**Goal**: Make (glue, clause_size, decision_depth) available to all consumers
after conflict analysis, computed ONCE per conflict.

**Current state**: Glue is computed in `resolve_conflict_core()` and used for
the EMA update, but not stored in a form accessible to the bump logic. Clause
size is known at the learned clause but not passed to `process_antecedent`.

**Implementation**:

In `sat_solver.h`, add to the solver class:
```cpp
// Per-conflict statistics, valid during process_antecedent callbacks.
unsigned m_conflict_glue = 0;
unsigned m_conflict_clause_size = 0;
unsigned m_conflict_decision_level = 0;
```

In `sat_solver.cpp`, in `resolve_conflict_core()`, after computing the learned
clause and its glue:
```cpp
m_conflict_glue = glue;
m_conflict_clause_size = m_lemma.size();
m_conflict_decision_level = m_conflict_lvl;
```

These are then available in `process_antecedent()` and `bump_reason_literals()`
without passing them as parameters (they're member variables, set once per conflict).

**Files**: `sat_solver.h` (3 member vars), `sat_solver.cpp` (~5 lines to set them).

**Testing**: `blast.sh -c smoke`. Zero behavioral change. Verify with `SASSERT`
that the values are non-zero when accessed in bump code.

**Risk**: Zero. Just stores values that are already computed.

---

### Task 0.2: QI Clause Tagging (QS1)

**Goal**: When QI creates a clause, mark it with the source quantifier's
identifier so we can trace back during conflict analysis.

**Current state**: QI clauses are created in `qi_queue::instantiate()` and
`smt_quantifier.cpp`. Once added to SAT, their origin is lost.

**Approach**: We need a way to associate a quantifier ID with a SAT clause.
Options:
1. Add a field to the clause struct (increases clause size — expensive, many clauses)
2. Use a side table: `clause* → quantifier_id` hash map
3. Use the justification/antecedent mechanism (clauses already track their justification)

Option 3 is cleanest. SAT clauses that come from theory solvers already have
`justification` objects. The QI justification should carry the quantifier pointer
or an index.

**Investigation needed**: Read `smt_justification.h`, `smt_model_finder.cpp`,
`qi_queue.cpp` to understand the existing justification flow.

The concrete implementation depends on what the justification already carries.
Key questions:
- Does the QI justification already reference the source quantifier?
- Can we extract it during conflict analysis without overhead?
- If not, what's the cheapest way to add it?

**Files**: `smt_justification.h`, `qi_queue.cpp`, `smt_quantifier.cpp`.

**Testing**: Add trace output showing "clause C created from quantifier Q with
binding B". Verify on ModifiesGen-195 that tags make sense.

**Risk**: Low. Adds metadata, doesn't change behavior.

---

### Task 0.3: QI Conflict Attribution (QS2)

**Goal**: During conflict analysis, identify which QI-sourced clauses are in
the antecedent chain, and record which quantifiers contributed.

**Current state**: Conflict analysis in `resolve_conflict_core()` walks the
implication graph via `process_antecedent()`. For each antecedent clause,
it could check if it's QI-sourced (from Task 0.2's tagging).

**Implementation**:

In `sat_solver.h`:
```cpp
// Per-conflict QI attribution — populated during conflict analysis.
svector<unsigned> m_conflict_qi_sources;  // quantifier IDs in this conflict
```

In `resolve_conflict_core()`, when processing each antecedent:
```cpp
// After resolving with antecedent clause 'c':
if (c->is_qi_clause()) {  // or however we check from Task 0.2
    unsigned qid = c->qi_source_id();
    m_conflict_qi_sources.push_back(qid);
}
```

After conflict analysis completes (before decay_activity), call a callback
to the SMT layer:
```cpp
if (!m_conflict_qi_sources.empty()) {
    // Notify SMT quantifier manager of which quantifiers contributed
    m_qi_attribution_callback(m_conflict_qi_sources);
    m_conflict_qi_sources.reset();
}
```

The callback mechanism needs to be wired through the SMT-SAT interface.
The `smt_context` or `theory_smt2` layer provides the bridge.

**Files**: `sat_solver.h` (member var + callback), `sat_solver.cpp` (populate
during conflict analysis), `smt_context.cpp` (receive callback).

**Testing**: Run ModifiesGen-195 with verbose output. After each conflict,
print the contributing quantifiers. Manually verify:
- Equation axioms appear frequently (high contribution)
- kick_partial_app appears rarely (low contribution)
- Numbers are consistent (same quantifier showing up in related conflicts)

**Risk**: Low. Read-only observation of existing conflict analysis.

---

## 6. Phase 1: Signal Enrichment (Track 1) <a name="phase-1"></a>

### Task 1.1: LBD-Weighted Bumps (S1)

**Goal**: Scale activity bumps by conflict quality. Low-glue (tight) conflicts
produce bigger bumps. High-glue (noisy) conflicts produce smaller bumps.

**Rationale**: Currently every variable in a 200-literal conflict gets the
same bump as one in a 3-literal conflict. Glue (LBD) is the strongest signal
we have about conflict quality, and it's already computed — just not used
for bump scaling.

**Implementation**:

In `process_antecedent()`:
```cpp
// BEFORE:
inc_activity(var);

// AFTER:
// m_conflict_glue set by Task 0.1
double scale = 1.0 / std::max(m_conflict_glue, 1u);
double bump = m_activity_inc * scale;
set_activity(var, get_activity(var) + bump);
if (get_activity(var) > 1e100) rescale_activity();
```

Also apply in `bump_reason_literals()` — reason-side bumps get the same scaling:
```cpp
// In the bump loop:
double scale = 1.0 / std::max(m_conflict_glue, 1u);
double bump = m_activity_inc * scale;
set_activity(bv, get_activity(bv) + bump);
```

Note: we need to handle `rescale_activity()` carefully since bumps now vary
in magnitude. The rescale threshold (1e100) should still work since individual
bumps are smaller (divided by glue), not larger.

**Files**: `sat_solver.cpp` — `process_antecedent()` (~5 lines), `bump_reason_literals()` (~5 lines).

**Testing**:
1. `blast.sh -c smoke` — sanity
2. `blast.sh -c critical` — must be ≥ 1385
3. `blast.sh -c everything --fast` — compare solved count and CPU time vs baseline

**Success criteria**: critical ≥ 1385, everything ≥ 11297. Any improvement is a win.

**Risk**: Near-zero. We're just weighting an existing mechanism. Worst case:
neutral (large-glue conflicts were already infrequent enough to not matter).

---

### Task 1.2: Per-Conflict Normalization (S2)

**Goal**: Normalize total activity injection per conflict by dividing by
√(num_bumped_vars). This prevents large conflict clauses from dominating
activity scores (Muon-style spectral normalization).

**Rationale**: A 200-variable conflict currently injects 200× the total
activity of a 3-variable conflict. But the 3-variable conflict is more
informative — it identifies a tight constraint. Normalization ensures
each conflict contributes equal total "learning" regardless of clause size.

**Implementation**:

Need to count bumped variables during conflict analysis. Two approaches:
1. Count in `process_antecedent()` (pre-pass)
2. Two-pass: first count, then bump with scaled values

Option 2 is cleaner but requires storing which variables to bump. Option 1
is simpler — just count during the existing pass, then apply the scale
retroactively via a global factor.

Actually, simplest approach: count num_bumped during the conflict pass,
then apply the Muon scale to `m_activity_inc` BEFORE the bumps happen:

```cpp
// At start of conflict analysis, after computing learned clause:
unsigned num_bumped = m_lemma.size();  // approximate: all vars in learned clause
                                       // plus reason-side (counted separately)
double muon_scale = 1.0 / std::sqrt(static_cast<double>(std::max(num_bumped, 1u)));

// Combined with LBD weight from Task 1.1:
double conflict_scale = muon_scale / std::max(m_conflict_glue, 1u);

// Store for use in process_antecedent:
m_conflict_bump_scale = conflict_scale;
```

Then in `process_antecedent()`:
```cpp
double bump = m_activity_inc * m_conflict_bump_scale;
set_activity(var, get_activity(var) + bump);
```

**Files**: `sat_solver.h` (add `m_conflict_bump_scale`), `sat_solver.cpp`
(compute scale, use in process_antecedent and bump_reason_literals).

**Testing**: Same as Task 1.1. Specifically compare performance on queries
with large conflict clauses (ModifiesGen suite).

**Success criteria**: critical ≥ 1385, everything ≥ 11297.

**Risk**: Low. Worst case: some queries where large conflicts ARE informative
get slightly worse. Mitigated by the 1/glue weighting already capturing quality.

---

## 7. Phase 2: QI Feedback Loop (Track 2 SMT) <a name="phase-2"></a>

This is the HIGHEST ROI phase. On hard F* queries, QI accounts for 60-80%
of solving time, and most QI instances are useless. Even a crude feedback
loop that suppresses the worst offenders could save 20-40% of total time.

### Task 2.1: Per-Quantifier Reward EMA (QV1)

**Goal**: Maintain a running estimate of how "useful" each quantifier is,
based on whether its instances participate in conflicts.

**Design**:

Per quantifier, track:
```cpp
struct quantifier_reward_state {
    double   reward = 0.01;          // EMA of success rate, floor at 0.01
    uint64_t instances_total = 0;    // total instances generated
    uint64_t instances_in_conflict = 0; // instances that appeared in conflict
    uint64_t last_conflict_time = 0; // for decay
};
```

Update rule (called from QS2 callback after each conflict):
```cpp
void update_qi_reward(unsigned qid) {
    auto& qs = m_qi_reward[qid];
    qs.instances_in_conflict++;
    // Update EMA: blend current sample with history
    double rate = static_cast<double>(qs.instances_in_conflict)
                / std::max(qs.instances_total, (uint64_t)1);
    qs.reward = 0.95 * qs.reward + 0.05 * rate;
    qs.last_conflict_time = m_num_conflicts;
}
```

On each QI instantiation:
```cpp
void on_qi_instance(unsigned qid) {
    m_qi_reward[qid].instances_total++;
}
```

Periodic decay (every 1000 conflicts): for quantifiers not seen recently,
decay reward toward the floor:
```cpp
void decay_qi_rewards() {
    for (auto& qs : m_qi_reward) {
        uint64_t staleness = m_num_conflicts - qs.last_conflict_time;
        if (staleness > 1000) {
            qs.reward = std::max(0.01, qs.reward * 0.99);
        }
    }
}
```

**Key insight**: The reward floor of 0.01 prevents complete suppression.
A quantifier might be rarely needed but critical when it fires. The floor
ensures it can still be instantiated, just at low priority.

**Files**: `smt_quantifier.cpp` or new file `qi_reward.h`.

**Testing**: Run ModifiesGen-195 with reward tracking. Print sorted rewards
after solving. Expected:
```
equation_FStar.ModifiesGen.loc_includes:         reward=0.65  (always useful)
equation_FStar.ModifiesGen.union_loc_of_loc:     reward=0.58  (always useful)
lemma_FStar.ModifiesGen.mem_union_aux...:         reward=0.32  (often useful)
...
interpretation_Tm_arrow_...:                      reward=0.02  (rarely useful)
kick_partial_app_..._non_live_addrs:             reward=0.01  (floor, never useful)
```

**Success criteria**: Rewards are sensible and distinguish useful from useless
quantifiers. No behavioral change yet (just observation).

---

### Task 2.2: Reward-Adjusted QI Scoring (QD1)

**Goal**: Modify the qi_queue priority function to use the reward signal.
High-reward quantifiers get priority. Low-reward get suppressed.

**Current scoring** (in qi_queue or smt_quantifier):
```cpp
// Roughly: lower cost = higher priority
double score = cost * generation;
```

**New scoring**:
```cpp
double reward = std::max(m_qi_reward[qid].reward, 0.01);
double score = cost * generation / reward;
// High reward → lower score → higher priority
// Low reward → higher score → deprioritized
```

Alternative: multiplicative weighting on the cost itself:
```cpp
double score = cost * generation * (1.0 / reward);
```

This means:
- Quantifier with reward 0.5: effective cost ×2 (slight deprioritization)
- Quantifier with reward 0.1: effective cost ×10 (moderate suppression)
- Quantifier with reward 0.01: effective cost ×100 (heavy suppression)

The natural logarithmic scale is exactly what we want. Good quantifiers
barely change. Bad quantifiers get pushed way down the queue.

**Files**: `qi_queue.cpp` or `smt_quantifier.cpp` — the scoring function.

**Testing**:
1. `blast.sh -c critical` — must be ≥ 1385 (HARD CONSTRAINT)
2. `blast.sh -c everything --fast` — compare solved count + CPU time
3. Time ModifiesGen-195 specifically: target < 5s (vs 6.4s baseline)
4. Time other hard ModifiesGen queries (195, 200, 225, etc.)

**Success criteria**:
- critical ≥ 1385 (no regression on correctness)
- everything ≥ 11297 (no regression on total)
- Measurable speedup on QI-heavy F* queries (ModifiesGen suite)
- ModifiesGen-195 specifically: target 3-5s (vs 6.4s baseline)

**Risk**: Medium. If reward estimation is noisy early in solving (before
enough conflicts to learn), we might suppress a quantifier that's actually
needed. The 0.01 floor mitigates this but doesn't eliminate it.

**Mitigation**: Add a "warmup" period — don't adjust scoring until after
100 conflicts. During warmup, use default scoring.

---

### Task 2.3: Adaptive QI Budget (QD2)

**Goal**: Dynamically adjust how many QI instances are added per round
based on recent success rate.

**Current behavior**: Fixed number of instances per round (or some static
threshold based on cost).

**New behavior**: Track global QI success rate. Adjust budget:
```cpp
double success_rate = global_instances_in_conflict / global_instances_total;

unsigned base_budget = m_params.qi_max_instances();  // default
unsigned adaptive_budget;

if (success_rate < 0.01) {
    // Less than 1% useful — aggressively throttle
    adaptive_budget = base_budget / 10;
} else if (success_rate < 0.05) {
    // 1-5% useful — moderate throttle
    adaptive_budget = base_budget / 3;
} else if (success_rate > 0.10) {
    // More than 10% useful — expand
    adaptive_budget = base_budget * 3;
} else {
    adaptive_budget = base_budget;
}
```

On queries where QI is productive (high success rate), the budget expands
and the solver finds proofs faster. On queries where QI is wasteful (low
success rate), the budget contracts and the solver stops drowning in garbage.

**Files**: `smt_quantifier.cpp` or `qi_queue.cpp`.

**Testing**: Same as Task 2.2. Additionally:
- Test on hard BV queries (from hard_queries/qf_bv) where QI is usually wasteful
- Test on QI-productive F* queries to ensure budget expansion works
- Verify: budget throttling kicks in within first 500 conflicts on wasteful queries

**Risk**: Medium. Too aggressive throttling could prevent finding proofs that
need rare but critical QI instances. The reward floor (Task 2.1) helps, but
budget limiting is a blunter instrument.

---

## 8. Phase 3: Better Phase Selection (Track 2 SAT) <a name="phase-3"></a>

### Task 3.1: Polarity Belief Vector (V1 + S3)

**Goal**: Add a continuous polarity belief per variable, updated from conflict
signals. This replaces the crude phase cache (save/target/best cascade) with
a proper EMA that integrates ALL conflict history.

**Design**:

New member in sat_solver:
```cpp
svector<double> m_polarity_belief;  // per variable, ∈ [-1, 1]
// positive → should be TRUE, negative → should be FALSE
// magnitude → confidence
```

Update rule during conflict analysis (for each variable v in conflict):
```cpp
// S3: polarity gradient
// If v was assigned TRUE and this led to conflict → push toward FALSE
// If v was assigned FALSE and this led to conflict → push toward TRUE
double polarity_sign = value(v) == l_true ? -1.0 : 1.0;
double gradient = polarity_sign * m_conflict_bump_scale;  // from Task 1.2

// V1: update belief with momentum
m_polarity_belief[v] = 0.95 * m_polarity_belief[v] + 0.05 * gradient;
// Clamp to [-1, 1]
m_polarity_belief[v] = std::max(-1.0, std::min(1.0, m_polarity_belief[v]));
```

Initialize to 0.0 (uncertain) for new variables.

**Properties**:
- Survives restarts (beliefs accumulate over entire solving)
- No rephasing needed (beliefs decay naturally via the 0.95 factor)
- Incorporates conflict quality (via gradient scale from Task 1.2)
- Replaces 3 bool arrays (m_phase, m_best_phase, m_target_phase) with 1 double array

**Files**: `sat_solver.h` (add svector), `sat_solver.cpp` (update in conflict
analysis, init in mk_var/reset_var, shrink in gc_vars, remap in gc).

**Testing**: `blast.sh -c smoke`. Add trace output to verify beliefs converge
to sensible values on simple queries. Beliefs should be positive for variables
that "should" be TRUE and negative for FALSE.

---

### Task 3.2: Belief-Derived Phase Selection (D4)

**Goal**: Replace phase cascade with belief-derived phase. Make it selectable
via parameter for safe A/B testing.

**New parameter**:
```python
# sat_params.pyg:
('phase.strategy', SYMBOL, 'caching', 'phase selection: caching, belief'),
```

**Implementation**:

In the phase selection code (wherever `select_phase()` or equivalent is called):
```cpp
bool select_phase(bool_var v) {
    if (m_config.m_phase_strategy == PS_BELIEF) {
        // D4: belief-derived phase
        return m_polarity_belief[v] > 0;  // positive belief → TRUE
    }
    // else: existing caching/target/best cascade
    return existing_phase_logic(v);
}
```

**Interaction with dual-mode**: In focused mode, the solver uses VMTF ordering
with always-false phase. With belief-derived phase, focused mode would use
VMTF ordering with belief-derived phase instead. This might help with the
BV regression (focused mode's always-false was bad for BV).

**Files**: `sat_solver.cpp` (phase selection), `sat_config.h/.cpp` (new enum),
`sat_params.pyg` (new parameter), `sat_dual_mode.cpp` (rephasing behavior).

**Testing**:
1. `blast.sh -c critical` with `sat.phase.strategy=belief`
2. Compare to baseline. Allow slight regression (≥ 1383) since this is a big change.
3. If ≥ 1385, strong win.
4. Also test with `sat.phase.strategy=caching` to verify no regression from
   the mere presence of the belief array.

**Risk**: Medium. Phase selection interacts with everything (restart timing,
conflict quality, search space). A wrong polarity just costs one backtrack,
but systematically wrong polarities can slow solving significantly.

---

## 9. Phase 4: Adaptive Optimizers (Track 3) <a name="phase-4"></a>

### Task 4.1: Adam Branching Heuristic

**Goal**: Replace VSIDS's single exponential decay with Adam optimizer for
per-variable adaptive learning rates.

**Design**: Per variable, maintain (m1, m2, last_update). On bump:
```cpp
void adam_bump(bool_var v) {
    // Lazy decay
    uint64_t dt = m_adam_step - m_adam_last_update[v];
    if (dt > 0) {
        m_adam_m1[v] *= pow_table.beta1[min(dt, 400)];
        m_adam_m2[v] *= pow_table.beta2[min(dt, 400)];
        m_adam_last_update[v] = m_adam_step;
    }
    // Gradient from Task 1.2: scaled by LBD and clause size
    double g = m_conflict_bump_scale;
    m_adam_m1[v] = 0.95 * m_adam_m1[v] + 0.05 * g;
    m_adam_m2[v] = 0.999 * m_adam_m2[v] + 0.001 * g * g;
    set_activity(v, m_adam_m1[v] / (std::sqrt(m_adam_m2[v]) + 0.01));
}
```

Precomputed power tables for lazy decay (β1^i, β2^i for i=0..400).

**Advantages over VSIDS**:
- Variables with consistent bumps get stable, moderate activity (dampened by m2)
- Variables with sporadic bumps get amplified when they appear (low m2 → big update)
- Per-variable adaptive learning rate (Adam's key property)
- Same O(1) per bump, just 6 more multiplies

**Files**: `sat_solver.h` (arrays + declaration), `sat_solver.cpp` (implementation,
hooks in process_antecedent, mk_var, reset_var, gc_vars), `sat_gc.cpp` (remap),
`sat_config.h/.cpp` (BH_ADAM enum), `sat_params.pyg` (parameter).

**Testing**: `blast.sh -c critical` with `sat.branching.heuristic=adam`.
Compare to VSIDS on everything suite.

**Risk**: Medium. Changes branching ORDER, which affects everything else.

---

### Task 4.2: Theory Variable Importance (TV1 + TD1)

**Goal**: Create VSIDS-like activity for theory variables. Bump when involved
in theory conflicts. Prioritize propagation of high-importance bounds.

**Implementation**: Each theory solver maintains an importance score per
theory variable. When the arithmetic solver detects an infeasibility:
```cpp
// In theory conflict handler:
for (auto atom : conflict_atoms) {
    m_theory_importance[atom] = 0.95 * m_theory_importance[atom] + 0.05;
}
```

Theory propagation uses importance as priority:
```cpp
// Instead of FIFO propagation:
// Pick the highest-importance bound to propagate next
auto next = max_importance_pending_propagation();
```

**Files**: Theory solver files (`theory_arith.cpp`, `smt_theory_var_list.h`).

**Testing**: Run arith-heavy F* queries. Profile theory propagation time.

---

### Task 4.3: Trigger Effectiveness Scheduling (QV3 + QD3)

**Goal**: Reorder MAM code tree execution by learned effectiveness.

**Design**: Per trigger pattern, track:
```cpp
struct trigger_effectiveness {
    double effectiveness = 1.0;  // EMA of (matches that led to useful instances)
    uint64_t total_matches = 0;
    uint64_t useful_matches = 0;
};
```

A match is "useful" if the resulting QI instance participates in a conflict
(tracked via QS1/QS2 from Phase 0).

Execute code trees in descending effectiveness order. Triggers that consistently
produce useful matches go first. Triggers that produce lots of matches but few
useful instances are deferred.

**Files**: `mam.cpp`, `pattern_inference.cpp`.

---

## 10. Phase 5: Connected Manifold (Track 4) <a name="phase-5"></a>

### Task 5.1: Cross-Stack Gradient Flow (C1-C4)

Wire bidirectional signals between SAT and SMT layers:

**C1 (SAT→QI)**: Already done in Phase 2 — conflict antecedent is QI clause
→ reward that quantifier.

**C2 (QI→SAT)**: When processing a conflict, if an antecedent clause was
QI-generated, weight the belief update by the source quantifier's reward:
```cpp
// In conflict analysis, for each antecedent:
double qi_quality = 1.0;  // default for non-QI clauses
if (clause->is_qi()) {
    qi_quality = 0.3 + 0.7 * m_qi_reward[clause->qi_source()].reward;
}
// Weight belief and activity updates:
double effective_gradient = m_conflict_bump_scale * qi_quality;
```

This means: conflicts arising from reliable QI instances produce stronger
learning signals. Conflicts from questionable instances are dampened.

**C3 (SAT→Theory)**: When a theory conflict occurs, the involved theory
atoms are identified. Bump their importance (from Task 4.2).

**C4 (Theory→SAT)**: When a high-importance theory bound is propagated,
give a bonus bump to the corresponding SAT variable:
```cpp
// In theory propagation callback to SAT:
if (m_theory_importance[atom] > threshold) {
    inc_activity(sat_var_of(atom), bonus);
}
```

**Files**: `sat_solver.cpp`, `smt_context.cpp`, theory solver files.

---

### Task 5.2: Soft Relevancy (RV1 + RD1 + C5 + C6)

Replace binary relevancy with continuous scores.

**Design**: Per expression node, maintain `relevancy ∈ [0, 1]`:
```
Root formula: relevancy = 1.0
AND children: inherit parent's relevancy
OR children: relevancy / num_children (attention split)
NOT: inherit parent's relevancy
```

**C6**: Conflict participation boosts relevancy:
```cpp
// After conflict, for each formula containing conflict variables:
relevancy[formula] = 0.99 * relevancy[formula] + 0.01;
```

**C5**: Relevancy modulates SAT bumps:
```cpp
// In process_antecedent:
double relevancy_weight = clause_relevancy(antecedent);
gradient_magnitude *= (0.5 + 0.5 * relevancy_weight);
```

This prevents the solver from being distracted by irrelevant subformulas
— a huge problem in F* where the context is mostly irrelevant.

**Files**: `smt_relevancy.cpp` (~100 lines), `sat_solver.cpp`.

---

## 11. Phase 6: Full Stack Optimizer (Track 5) <a name="phase-6"></a>

### Task 6.1: Combined Branching Score (D3)

Replace separate importance and confidence with unified score:
```cpp
double importance = std::abs(m_adam_m1[v]) / (std::sqrt(m_adam_m2[v]) + EPS);
double confidence = std::abs(m_polarity_belief[v]);
double score = importance * (0.5 + confidence);
set_activity(v, score);
```

On UNSAT instances: importance dominates (lots of conflicts). On SAT: confidence
dominates (variables settle). Auto-adapts without mode switching.

### Task 6.2: Gradient-Norm Restart (D5)

Track gradient norm per conflict:
```cpp
double norm = 0;
for (var in conflict) norm += gradient[var] * gradient[var];
norm = std::sqrt(norm);

m_grad_norm_fast = 0.03 * norm + 0.97 * m_grad_norm_fast;
m_grad_norm_slow = 1e-5 * norm + (1-1e-5) * m_grad_norm_slow;

bool should_restart = m_grad_norm_fast < 0.8 * m_grad_norm_slow;
```

Replace glue EMA restart with direct learning-progress measurement.

### Task 6.3: Adaptive BV Strategy (BD1)

Per BV operation, track blast reward:
```cpp
struct bv_op_state {
    double blast_reward = 0.5;   // did blasting help?
    double native_reward = 0.5;  // did native reasoning help?
    unsigned blast_size;         // estimated SAT vars if blasted
};

bool should_blast(bv_op_state& s) {
    if (s.blast_size < 100) return true;        // small: always blast
    if (s.blast_size > 10000) return false;      // huge: never blast
    return s.blast_reward > s.native_reward * 2; // middle: compare
}
```

Target: recover ≥ 10 of 20 lost BV queries.

### Task 6.4: Utility-Scored GC (D6)

Replace LBD-tier GC with gradient-based clause utility:
```cpp
// Per learned clause: track gradient contribution
// When clause is used as antecedent:
clause_utility[c] = 0.99 * clause_utility[c] + 0.01 * gradient_magnitude;

// GC: delete clauses with lowest utility
```

---

## 12. Phase 7: Learned Heuristics (Track 6) <a name="phase-7"></a>

### Task 7.1: Feature Extraction Pipeline

Extract 8 structural features per variable per conflict:
```cpp
double features[8] = {
    m_adam_m1[v],                    // momentum
    m_adam_m2[v],                    // curvature
    m_polarity_belief[v],           // polarity belief
    conflicts_since_last_bump(v),    // age
    propagation_rate(v),             // how often causes implications
    avg_decision_depth(v),           // typical depth when assigned
    avg_glue_contribution(v),        // avg LBD of conflicts involving v
    clause_degree(v)                 // number of clauses containing v
};
```

### Task 7.2: SIMD Linear Scorer

AVX-512 inference: 8 features × 8 weights = one FMA + reduce ≈ 3ns.
Online training: ~6 AVX-512 instructions ≈ 3ns per conflict.

```cpp
// Inference:
__m512d f = _mm512_load_pd(features);
__m512d w = _mm512_load_pd(weights);
double score = _mm512_reduce_add_pd(_mm512_mul_pd(f, w));

// Training (after each conflict):
for (int i = 0; i < 8; i++) {
    double g = -(1.0/glue) * features[i];
    w_m1[i] = 0.9 * w_m1[i] + 0.1 * g;
    w_m2[i] = 0.999 * w_m2[i] + 0.001 * g * g;
    weights[i] -= 0.001 * w_m1[i] / (sqrt(w_m2[i]) + 1e-8);
}
```

---

## 13. Phase 8: Research Frontier <a name="phase-8"></a>

### Task 8.1: Pre-Trained QI Scorer

Domain-invariant features per quantifier (not names!):
```
num_bound_vars, body_depth, num_triggers, trigger_width,
body_num_distinct_funcs, body_has_equality, body_has_arithmetic,
body_is_implication, body_is_iff, num_ground_matches
```

Train offline on diverse corpus (F*, Pulse, SMT-LIB, Dafny).
Ship as ~2MB weight file inside Z3. Works out of the box on novel domains.

### Task 8.2: Merkle DAG Proof Cache

Content-hash assertion sets. Cache proof strategies (QI decision sequences)
keyed by structural signature. Replay on cache hit.

**Architecture** (from Crucible):
```
RegionNode  → cached QI sequence (proof fragment)
BranchNode  → strategy fork (problem structure check)
LoopNode    → QI fixpoint (instantiate until saturated)
ContentHash → QI sequence identity
MerkleHash  → proof subtree identity
dag_diff()  → cross-query structural comparison
```

**Cross-query flow**:
```
Query arrives → hash assertion set → Merkle compare with cache
  ├─ identical subtree? → replay cached QI strategy
  ├─ small delta? → warm-start, search only the diff
  └─ novel? → full MCTS search, cache when done
```

**Memory management**:
- Merkle DAG = explicit memory (exact, growing)
- Neural value net = implicit memory (approximate, fixed-size)
- Distillation: periodically train net on DAG contents, then prune DAG
- Budget invariant: DAG_SIZE ≤ 256MB, evict lowest-value nodes

### Task 8.3: MCTS for QI Decisions

QI instantiation is a TREE of decisions, not independent bandits:
```
inst Q1(y=x)  →  creates f(x)  →  triggers Q2  →  inst Q2(z=f(x))  → ...
```

MCTS searches this tree:
```
State:   (E-graph, partial assignment, QI history)
Action:  instantiate quantifier Q with binding B
Value:   predicted distance to proof
Policy:  learned from structural features
Reward:  +1 for UNSAT, -1 for timeout
```

Value network (tiny, ~3ns inference):
```
8 features per candidate → linear model → score ∈ [0, 1]
MCTS: 32 rollouts per QI decision = ~100ns
With 5000 QI decisions per query = 0.5ms total overhead
```

### Task 8.4: GPU-Accelerated Solving (Track 7)

**Mode A: Batch throughput** (F*/Pulse: thousands of small queries)
- GPU batch-solve 4000 trivial queries simultaneously
- Tensor core GEMM on formula-as-matrix representation
- 1000 queries in ~1ms (vs 1 second sequential on CPU)

**Mode B: Single hard instance**
- GPU Survey Propagation → reduce formula 10-100×
- GPU DDFW local search → parallel flip evaluation
- CPU CDCL on reduced formula, warm-started with GPU beliefs

**Mode C: Hybrid continuous**
- CPU thread: CDCL + theory solvers
- GPU stream: continuous belief refinement (Adam on differentiable relaxation)
- Every 5000 CPU conflicts: exchange beliefs (async, ~70μs)

### Task 8.5: MuZero Kernel Synthesis (Level 4)

For attention kernels with sophisticated masking/windowing:
```
State:     (hardware_spec, attention_spec, partial_kernel)
Action:    emit operation (load, compute, sync, store) with parameters
Value:     predicted throughput
Training:  self-play (generate → compile → benchmark → train)
```

~45 action types × ~40 steps per kernel = 200^40 ≈ 10^92 search space.
Self-play: 256 kernels × 200ms = ~50s per iteration.
15 minutes from zero knowledge → ~88% of roofline.

Correctness verification pipeline:
1. Compilation gate (ptxas, ~50ms)
2. Quick smoke test (1 random input, ~2ms)
3. Reference check (8 diverse inputs vs PyTorch, ~80ms)
4. Property check (row-sum, masking, monotonicity, ~20ms)
5. Benchmark (100 iterations, ~50ms)

---

## 14. Dependency Graph & Priority Order <a name="dependencies"></a>

### Dependency DAG

```
Phase 0 (Infrastructure)
  ├─ 0.1 (Conflict Stats) ──→ 1.1 ──→ 1.2 ──→ [Phase 1 DONE]
  └─ 0.2 (QI Tags) ──→ 0.3 (QI Attrib) ──→ 2.1 ──→ 2.2 ──→ 2.3 ──→ [Phase 2 DONE]

Phase 1 + 0.1 ──→ 3.1 (Belief Vector) ──→ 3.2 (Belief Phase) ──→ [Phase 3 DONE]

Phase 1 ──→ 4.1 (Adam Branching) ──→ [Adam DONE]
Phase 2 ──→ 4.3 (Trigger Scheduling) ──→ [Triggers DONE]
  0.1 ──→ 4.2 (Theory Importance) ──→ [Theory DONE]

Phase 2 + 3 + 4 ──→ 5.1 (Cross-Stack) ──→ 5.2 (Soft Relevancy) ──→ [Phase 5 DONE]

Phase 3 + 4 ──→ 6.1 (Combined Score)
Phase 0   ──→ 6.2 (Gradient Restart)
Phase 4   ──→ 6.3 (Adaptive BV)
Phase 5   ──→ 6.4 (Utility GC)                                    ──→ [Phase 6 DONE]

Phase 5 ──→ 7.1 (Features) ──→ 7.2 (SIMD Scorer) ──→ [Phase 7 DONE]

Phase 2 ──→ 8.1 (Pre-Trained QI Scorer)
Phase 2 ──→ 8.2 (Merkle DAG Proof Cache)
Phase 2 + 8.1 ──→ 8.3 (MCTS for QI)                              ──→ [Phase 8: Research]
```

### Implementation Priority Order

```
SESSION  TASKS               DESCRIPTION                      EST. TIME
──────── ─────────────────── ──────────────────────────────── ──────────
  1      0.1 + 0.2           Conflict stats + QI tagging       1h
  2      1.1 + 1.2 + 0.3    LBD bumps + normalization + QI    2h
  3      2.1 + 2.2           QI reward EMA + adjusted scoring  3h ★★★
  4      2.3 + 3.1           QI budget + belief vector          2h
  5      3.2                 Belief-derived phase               2h
  6      4.1                 Adam branching                     3h
  7      4.2 + 4.3           Theory importance + triggers       3h
  8      5.1                 Cross-stack gradient flow          3h
  9      5.2                 Soft relevancy                     3h
 10      6.1 + 6.2           Combined score + gradient restart  3h
 11      6.3                 Adaptive BV                        2h
 12      6.4                 Utility GC                         2h
 13      7.1                 Feature extraction                 2h
 14      7.2                 SIMD learned scorer                3h
 15+     8.x                 Research frontier                  ongoing
```

★★★ = Session 3 (QI reward + adjusted scoring) is the HIGHEST ROI single change.
If we build nothing else, this alone could save 20-40% on hard F* queries.

### ROI Ranking (for F*/Pulse workloads)

```
RANK  TASK              PHASE   EXPECTED IMPACT         RISK
────  ────────────────  ──────  ────────────────────── ──────
 1    QI feedback       Ph 2    20-40% of hard query    low-med
 2    Soft relevancy    Ph 5    10-20% of hard query    med
 3    Belief phase      Ph 3    3-8% fewer backtracks   low-med
 4    Theory prop prio  Ph 4    5-10% on arith-heavy    low
 5    Adaptive BV       Ph 6    recovers 20 lost BV     med
 6    Adam branching    Ph 4    0-3% (uncertain)        med
 7    Trigger sched     Ph 4    2-5%                    low
 8    Signal enrich     Ph 1    0.2-0.5%                ~zero
 9    Combined score    Ph 6    0-2% over best of above med-high
10    Gradient restart  Ph 6    0-2%                    med-high
11    Utility GC        Ph 6    0-1%                    high
12    SIMD scorer       Ph 7    0-3% on top of above    high
13    GPU batch         Ph 8    4× throughput on batch   research
14    MCTS QI           Ph 8    additional 2-5× on hard research
```

---

## 15. Testing Methodology <a name="testing"></a>

### Test Suites

```bash
# Location: /root/iprit/z3_testing/
# Harness: blast.sh

# Quick sanity (must always pass first):
./blast.sh -c smoke /root/iprit/z3/build/z3

# Main regression gate:
./blast.sh -c critical /root/iprit/z3/build/z3

# Full benchmark (solved count + CPU time):
./blast.sh -c everything --fast /root/iprit/z3/build/z3
```

### Per-Task Testing Protocol

1. **Build**: `ninja -C build -j$(nproc)` — must compile clean
2. **Smoke**: `blast.sh -c smoke` — 40/40 (HARD requirement)
3. **Critical**: `blast.sh -c critical` — ≥ 1385 (baseline match)
4. **Everything**: `blast.sh -c everything --fast` — ≥ 11297 solved, ≤ 942s CPU
5. **Hard queries**: Time specific hard queries (ModifiesGen-195, etc.)
6. **New parameter testing**: Run with parameter enabled AND disabled to verify
   clean A/B comparison

### Specific Test Queries for QI Optimization

```bash
# Hard F* queries (QI-heavy):
ModifiesGen-195:  6.4s  (target: < 4s with QI feedback)
ModifiesGen-200:  >10s  (target: < 8s)
ModifiesGen-225:  2.6s  (target: < 2s)
ModifiesGen-149:  2.9s  (target: < 2s)
Buffer-145:       3.7s  (target: < 3s)

# Hard BV queries:
hard_queries/qf_bv/*  (target: recover ≥ 10 of 20 lost with adaptive BV)
```

### A/B Testing with Parameters

Every new feature should be parameter-gated:
```bash
# Test with feature ON:
z3 sat.phase.strategy=belief file.smt2

# Test with feature OFF (baseline):
z3 sat.phase.strategy=caching file.smt2

# Both must be tested on critical + everything
```

### Regression Detection

If critical drops below 1385 OR everything drops below 11297:
1. Identify which specific queries regressed
2. Run those queries with verbose tracing
3. Compare conflict count, QI count, decision count
4. Determine if regression is from the new feature or noise
5. If from feature: tune parameters or revert. NEVER ship a regression.

---

## 16. Expected Outcomes <a name="outcomes"></a>

### Phase 1 (Signal Enrichment): +0.2-0.5% solved
- LBD-weighted bumps + normalization
- Near-zero risk, foundation for everything
- Expected: everything 11297-11350, CPU time 930-942s

### Phase 2 (QI Feedback): +1-3% on hard queries
- Per-quantifier reward + adjusted scoring + adaptive budget
- Expected: ModifiesGen-195 drops from 6.4s to 3-5s
- Expected: everything 11310-11400, some hard timeouts become solved
- This is the single highest-ROI phase

### Phase 3 (Better Phase): +0.5-1.5% solved
- Belief-derived phase replacing cache cascade
- Expected: fewer backtracks, especially on structured queries
- Expected: everything 11310-11450

### Phase 4 (Adaptive Optimizers): +0.5-2% solved
- Adam branching + theory importance + trigger scheduling
- Expected: everything 11320-11500

### Phase 5 (Connected Manifold): +1-4% total
- Cross-stack gradient + soft relevancy
- Expected: everything 11350-11550, CPU time 850-920s

### Phase 6 (Full Stack): +0-2% on top of Phase 5
- High risk, high ceiling. Combined scoring + gradient restart + adaptive BV
- Expected: everything 11350-11600, recover some BV queries

### Phase 7 (Learned): +0-3% on top of everything
- SIMD neural scorer, online training
- Speculative but low overhead if it doesn't help

### Phase 8 (Research): transformative if successful
- Merkle DAG: 5-10× on repeated F* verification workloads
- MCTS QI: 2-5× additional on hard QI-heavy queries
- GPU batch: 4× throughput on F*/Pulse workloads

### Cumulative Expected Outcome (Phases 1-6)

```
Baseline:              11297/11911 (94.9%), 942s CPU
After all phases:      11400-11600/11911 (95.7-97.4%), 800-900s CPU
Hard F* queries:       2-5× faster (QI-heavy)
BV queries:            10-20 recovered (adaptive strategy)
```

### Long-Term Vision (Phases 7-8)

```
With pre-trained QI scorer:  works on novel domains out of the box
With Merkle DAG:             gets faster with every query it solves
With MCTS:                   finds proofs that heuristic QI can't
With GPU acceleration:       4× throughput on verification workloads
```

---

## Appendix: Key Files Reference

### SAT Layer
```
src/sat/sat_solver.h          — solver class, all per-variable state
src/sat/sat_solver.cpp        — main solving loop, conflict analysis, bumps
src/sat/sat_config.h          — branching heuristic enum, parameters
src/sat/sat_config.cpp        — parameter parsing
src/sat/sat_gc.cpp            — garbage collection, variable remapping
src/sat/sat_dual_mode.cpp     — stable/focused mode switching
src/params/sat_params.pyg     — parameter definitions
```

### SMT Layer
```
src/smt/smt_quantifier.cpp    — QI management, instantiation control
src/smt/smt_context.cpp       — SMT core, theory-SAT interface
src/smt/qi_queue.h            — QI priority queue
src/smt/mam.cpp               — matching abstract machine (E-matching)
src/smt/smt_relevancy.cpp     — relevancy propagation
```

### Theory Solvers
```
src/smt/theory_arith.cpp      — arithmetic theory solver
src/smt/theory_bv.cpp         — bitvector theory solver
src/ast/pattern/pattern_inference.cpp — trigger pattern selection
```

### Key Data Structures
```
src/util/hashtable.h           — hash tables (swiss_table migration done)
src/ast/ast.h                  — AST nodes, app_flags (13 spare bits)
src/smt/fingerprints.cpp       — QI fingerprint dedup
```
