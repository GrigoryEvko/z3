#!/usr/bin/env python3
"""
z3trace — non-interactive query tool for Z3 adaptive engine JSONL traces.

Designed for programmatic access: every subcommand writes clean, parseable
text to stdout.  No TUI, no colors, no interactivity.

Usage:
    z3trace.py summary   <trace.jsonl>                  # per-query stats
    z3trace.py top       <trace.jsonl> [--by reward|inst|conflicts] [--n 10]
    z3trace.py conflicts <trace.jsonl> [--limit 20]
    z3trace.py restarts  <trace.jsonl>
    z3trace.py filter    <trace.jsonl> --type QI_INSERT [--q name] [--min-cost 5]
    z3trace.py diff      <base.jsonl> <other.jsonl>
    z3trace.py diagnose  <base.jsonl> <regressed.jsonl>
    z3trace.py timeline  <trace.jsonl> [--q name]       # per-quantifier timeline
    z3trace.py cost      <trace.jsonl>                  # cost distribution
"""

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def load_trace(path: str) -> list[dict]:
    """Load JSONL, skipping malformed lines."""
    events = []
    with open(path) as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                events.append(json.loads(line))
            except json.JSONDecodeError:
                print(f"# WARN: skipped malformed line {lineno}", file=sys.stderr)
    return events


def by_type(events: list[dict]) -> dict[str, list[dict]]:
    """Group events by their 't' field."""
    groups: dict[str, list[dict]] = defaultdict(list)
    for e in events:
        groups[e.get("t", "UNKNOWN")].append(e)
    return groups


def fmt_pct(num: int, denom: int) -> str:
    if denom == 0:
        return "0.0%"
    return f"{100.0 * num / denom:.1f}%"


def fmt_num(n) -> str:
    if isinstance(n, float):
        return f"{n:.4f}"
    return str(n)


# ---------------------------------------------------------------------------
# Subcommand: summary
# ---------------------------------------------------------------------------

def cmd_summary(args):
    events = load_trace(args.trace)
    groups = by_type(events)

    total = len(events)
    inserts = groups.get("QI_INSERT", [])
    conflicts = groups.get("CONFLICT", [])
    rewards = groups.get("REWARD", [])
    restarts = groups.get("RESTART", [])
    solves = groups.get("SOLVE", [])

    print(f"trace: {args.trace}")
    print(f"events: {total}")
    print()

    # Event type distribution
    print("event_counts:")
    for t, evs in sorted(groups.items(), key=lambda x: -len(x[1])):
        print(f"  {t}: {len(evs)}")
    print()

    # QI stats
    if inserts:
        costs = [e.get("cost", 0) for e in inserts]
        heats = [e.get("heat", 0) for e in inserts]
        print(f"qi_inserts: {len(inserts)}")
        print(f"  cost_min: {min(costs):.4f}")
        print(f"  cost_max: {max(costs):.4f}")
        print(f"  cost_mean: {sum(costs)/len(costs):.4f}")
        print(f"  cost_median: {sorted(costs)[len(costs)//2]:.4f}")
        nonzero_heat = [h for h in heats if h > 0]
        print(f"  heat_nonzero: {len(nonzero_heat)} ({fmt_pct(len(nonzero_heat), len(inserts))})")
        # Unique quantifiers
        qi_names = Counter(e.get("q", "?") for e in inserts)
        print(f"  unique_quantifiers: {len(qi_names)}")
        print()

    # Conflict stats
    if conflicts:
        sizes = [e.get("sz", 0) for e in conflicts]
        qi_counts = [e.get("qi_count", 0) for e in conflicts]
        with_qi = [c for c in conflicts if c.get("qi_count", 0) > 0]
        print(f"conflicts: {len(conflicts)}")
        print(f"  with_qi_antecedents: {len(with_qi)} ({fmt_pct(len(with_qi), len(conflicts))})")
        print(f"  avg_clause_size: {sum(sizes)/len(sizes):.1f}")
        print(f"  avg_qi_per_conflict: {sum(qi_counts)/len(qi_counts):.2f}")
        print()

    # Reward stats
    if rewards:
        # Get final reward per quantifier
        final_rewards = {}
        for r in rewards:
            final_rewards[r.get("q", "?")] = r.get("new", 0)
        positive = {k: v for k, v in final_rewards.items() if v > 0.01}
        print(f"reward_updates: {len(rewards)}")
        print(f"  quantifiers_with_reward: {len(positive)}")
        if positive:
            top = sorted(positive.items(), key=lambda x: -x[1])[:5]
            print(f"  top_5:")
            for name, rew in top:
                print(f"    {rew:.4f}  {name}")
        print()

    # Restart stats
    if restarts:
        print(f"restarts: {len(restarts)}")
        vels = [r.get("vel", 0) for r in restarts]
        bvs = [r.get("bv", 0) for r in restarts]
        cns = [r.get("cn", 0) for r in restarts]
        print(f"  vel_range: [{min(vels):.4f}, {max(vels):.4f}]")
        print(f"  bv_range: [{min(bvs):.4f}, {max(bvs):.4f}]")
        print(f"  cn_range: [{min(cns):.4f}, {max(cns):.4f}]")
        max_stuck = max(r.get("stuck", 0) for r in restarts)
        max_cascade = max(r.get("cascade", 0) for r in restarts)
        print(f"  max_stuck: {max_stuck}")
        print(f"  max_cascade_level: {max_cascade}")
        print()

    # Solve result
    if solves:
        s = solves[-1]
        print(f"result: {s.get('result', '?')}")
        for k in ["conflicts", "restarts", "cache_hits", "cache_misses",
                   "cache_size", "replay", "cascade"]:
            if k in s:
                print(f"  {k}: {fmt_num(s[k])}")


# ---------------------------------------------------------------------------
# Subcommand: top
# ---------------------------------------------------------------------------

def cmd_top(args):
    events = load_trace(args.trace)
    groups = by_type(events)

    inserts = groups.get("QI_INSERT", [])
    rewards = groups.get("REWARD", [])
    conflicts = groups.get("CONFLICT", [])

    # Count instances per quantifier
    inst_count = Counter(e.get("q", "?") for e in inserts)

    # Final reward per quantifier
    final_reward = {}
    for r in rewards:
        final_reward[r.get("q", "?")] = r.get("new", 0)

    # Count conflict participations per quantifier
    conflict_count: Counter = Counter()
    for c in conflicts:
        for qi in c.get("qi", []):
            conflict_count[qi.get("q", "?")] += 1

    # All quantifier names
    all_q = set(inst_count.keys()) | set(final_reward.keys()) | set(conflict_count.keys())

    # Build rows
    rows = []
    for q in all_q:
        rows.append({
            "q": q,
            "instances": inst_count.get(q, 0),
            "reward": final_reward.get(q, 0.0),
            "conflicts": conflict_count.get(q, 0),
            "hit_rate": conflict_count.get(q, 0) / max(inst_count.get(q, 0), 1),
        })

    # Sort
    sort_key = args.by if args.by else "reward"
    key_map = {
        "reward": lambda r: -r["reward"],
        "inst": lambda r: -r["instances"],
        "instances": lambda r: -r["instances"],
        "conflicts": lambda r: -r["conflicts"],
        "hit_rate": lambda r: -r["hit_rate"],
    }
    rows.sort(key=key_map.get(sort_key, key_map["reward"]))

    n = args.n or 20
    print(f"{'RANK':>4}  {'REWARD':>8}  {'INST':>7}  {'CONFLICTS':>9}  {'HIT_RATE':>8}  QUANTIFIER")
    for i, r in enumerate(rows[:n], 1):
        print(f"{i:>4}  {r['reward']:>8.4f}  {r['instances']:>7}  {r['conflicts']:>9}  "
              f"{r['hit_rate']:>7.4f}%  {r['q']}")

    if len(rows) > n:
        print(f"  ... {len(rows) - n} more quantifiers")


# ---------------------------------------------------------------------------
# Subcommand: conflicts
# ---------------------------------------------------------------------------

def cmd_conflicts(args):
    events = load_trace(args.trace)
    conflicts = [e for e in events if e.get("t") == "CONFLICT"]

    limit = args.limit or 20
    print(f"total_conflicts: {len(conflicts)}")
    print()

    # Show conflict details
    print(f"{'#':>6}  {'SIZE':>4}  {'QI_CNT':>6}  QI_SOURCES")
    for c in conflicts[:limit]:
        qi_str = ", ".join(
            f"{qi['q']}@d{qi['d']}" for qi in c.get("qi", [])
        ) if c.get("qi") else "(none)"
        print(f"{c.get('c', '?'):>6}  {c.get('sz', '?'):>4}  "
              f"{c.get('qi_count', 0):>6}  {qi_str}")

    if len(conflicts) > limit:
        print(f"  ... {len(conflicts) - limit} more conflicts (use --limit N)")

    # Quantifier conflict frequency
    print()
    freq: Counter = Counter()
    depth_sum: dict[str, float] = defaultdict(float)
    depth_count: dict[str, int] = defaultdict(int)
    for c in conflicts:
        for qi in c.get("qi", []):
            q = qi.get("q", "?")
            freq[q] += 1
            depth_sum[q] += qi.get("d", 0)
            depth_count[q] += 1

    print(f"{'FREQ':>6}  {'AVG_DEPTH':>9}  QUANTIFIER")
    for q, cnt in freq.most_common(20):
        avg_d = depth_sum[q] / max(depth_count[q], 1)
        print(f"{cnt:>6}  {avg_d:>9.2f}  {q}")


# ---------------------------------------------------------------------------
# Subcommand: restarts
# ---------------------------------------------------------------------------

def cmd_restarts(args):
    events = load_trace(args.trace)
    restarts = [e for e in events if e.get("t") == "RESTART"]

    if not restarts:
        print("no restarts recorded")
        return

    print(f"{'R':>4}  {'CONF':>6}  {'VEL':>7}  {'BV':>7}  {'CN':>7}  {'RE':>7}  "
          f"{'STUCK':>5}  {'CASC':>4}  {'SKEW':>12}")
    for r in restarts:
        skew_str = f"{r.get('skew', '?')}/{r.get('skew_frac', 0):.2f}" if "skew" in r else "-"
        print(f"{r.get('r', '?'):>4}  {r.get('c', '?'):>6}  "
              f"{r.get('vel', 0):>7.4f}  {r.get('bv', 0):>7.4f}  "
              f"{r.get('cn', 0):>7.4f}  {r.get('re', 0):>7.4f}  "
              f"{r.get('stuck', 0):>5}  {r.get('cascade', 0):>4}  {skew_str:>12}")


# ---------------------------------------------------------------------------
# Subcommand: filter
# ---------------------------------------------------------------------------

def cmd_filter(args):
    events = load_trace(args.trace)

    # Filter by type
    if args.type:
        events = [e for e in events if e.get("t") == args.type]

    # Filter by quantifier name (substring match)
    if args.q:
        events = [e for e in events if args.q in e.get("q", "")]

    # Filter by minimum cost
    if args.min_cost is not None:
        events = [e for e in events if e.get("cost", 0) >= args.min_cost]

    # Filter by conflict range
    if args.after_conflict is not None:
        events = [e for e in events if e.get("c", 0) >= args.after_conflict]
    if args.before_conflict is not None:
        events = [e for e in events if e.get("c", 0) <= args.before_conflict]

    limit = args.limit or 50
    print(f"matched: {len(events)}")
    for e in events[:limit]:
        print(json.dumps(e))

    if len(events) > limit:
        print(f"# ... {len(events) - limit} more (use --limit N)", file=sys.stderr)


# ---------------------------------------------------------------------------
# Subcommand: diff
# ---------------------------------------------------------------------------

def cmd_diff(args):
    evA = load_trace(args.base)
    evB = load_trace(args.other)

    gA = by_type(evA)
    gB = by_type(evB)

    # Compare high-level stats
    def stat(groups, key):
        evs = groups.get(key, [])
        return len(evs)

    print(f"{'METRIC':<25}  {'BASE':>8}  {'OTHER':>8}  {'DELTA':>10}")
    print("-" * 60)

    for key in ["QI_INSERT", "CONFLICT", "REWARD", "RESTART"]:
        a, b = stat(gA, key), stat(gB, key)
        delta = b - a
        pct = f"{100.0 * delta / max(a, 1):+.1f}%" if a > 0 else "n/a"
        marker = "+" if delta > 0 else ("-" if delta < 0 else "=")
        print(f"{key:<25}  {a:>8}  {b:>8}  {delta:>+8} {pct:>6}")

    # Compare results
    solveA = gA.get("SOLVE", [{}])[-1] if gA.get("SOLVE") else {}
    solveB = gB.get("SOLVE", [{}])[-1] if gB.get("SOLVE") else {}

    print()
    print(f"result_base: {solveA.get('result', '?')}")
    print(f"result_other: {solveB.get('result', '?')}")
    print()

    # Compare per-quantifier instances
    instA = Counter(e.get("q", "?") for e in gA.get("QI_INSERT", []))
    instB = Counter(e.get("q", "?") for e in gB.get("QI_INSERT", []))

    all_q = set(instA.keys()) | set(instB.keys())
    diffs = []
    for q in all_q:
        a, b = instA.get(q, 0), instB.get(q, 0)
        if a != b:
            diffs.append((q, a, b, b - a))

    diffs.sort(key=lambda x: -abs(x[3]))

    if diffs:
        print(f"quantifier_instance_diffs: {len(diffs)}")
        print(f"{'DELTA':>8}  {'BASE':>7}  {'OTHER':>7}  QUANTIFIER")
        for q, a, b, d in diffs[:20]:
            print(f"{d:>+8}  {a:>7}  {b:>7}  {q}")
        if len(diffs) > 20:
            print(f"  ... {len(diffs) - 20} more")
    else:
        print("quantifier_instance_diffs: 0 (identical)")

    # Compare reward distributions
    print()
    rewA = {}
    for r in gA.get("REWARD", []):
        rewA[r.get("q", "?")] = r.get("new", 0)
    rewB = {}
    for r in gB.get("REWARD", []):
        rewB[r.get("q", "?")] = r.get("new", 0)

    all_rew_q = set(rewA.keys()) | set(rewB.keys())
    rew_diffs = []
    for q in all_rew_q:
        a, b = rewA.get(q, 0), rewB.get(q, 0)
        if abs(a - b) > 0.001:
            rew_diffs.append((q, a, b, b - a))

    rew_diffs.sort(key=lambda x: -abs(x[3]))

    if rew_diffs:
        print(f"reward_diffs: {len(rew_diffs)}")
        print(f"{'DELTA':>8}  {'BASE':>8}  {'OTHER':>8}  QUANTIFIER")
        for q, a, b, d in rew_diffs[:15]:
            print(f"{d:>+8.4f}  {a:>8.4f}  {b:>8.4f}  {q}")
    else:
        print("reward_diffs: 0 (identical)")


# ---------------------------------------------------------------------------
# Subcommand: diagnose
# ---------------------------------------------------------------------------

def cmd_diagnose(args):
    evBase = load_trace(args.base)
    evReg = load_trace(args.regressed)

    gBase = by_type(evBase)
    gReg = by_type(evReg)

    # Results
    solveBase = gBase.get("SOLVE", [{}])[-1] if gBase.get("SOLVE") else {}
    solveReg = gReg.get("SOLVE", [{}])[-1] if gReg.get("SOLVE") else {}

    resBase = solveBase.get("result", "?")
    resReg = solveReg.get("result", "?")

    print(f"base_result: {resBase}")
    print(f"regressed_result: {resReg}")
    print()

    confBase = len(gBase.get("CONFLICT", []))
    confReg = len(gReg.get("CONFLICT", []))

    qiBase = len(gBase.get("QI_INSERT", []))
    qiReg = len(gReg.get("QI_INSERT", []))

    print(f"base_conflicts: {confBase}")
    print(f"regressed_conflicts: {confReg}")
    print(f"base_qi_inserts: {qiBase}")
    print(f"regressed_qi_inserts: {qiReg}")
    print()

    # Find first divergence point in conflict sequence
    confsBase = gBase.get("CONFLICT", [])
    confsReg = gReg.get("CONFLICT", [])

    # Compare conflict-producing quantifiers at each step
    def qi_set(conf):
        return frozenset(qi.get("q", "?") for qi in conf.get("qi", []))

    first_div = None
    for i in range(min(len(confsBase), len(confsReg))):
        if qi_set(confsBase[i]) != qi_set(confsReg[i]):
            first_div = i
            break

    if first_div is not None:
        print(f"first_divergence_at_conflict_index: {first_div}")
        cb = confsBase[first_div]
        cr = confsReg[first_div]
        base_qi = [qi.get("q", "?") for qi in cb.get("qi", [])]
        reg_qi = [qi.get("q", "?") for qi in cr.get("qi", [])]
        print(f"  base_qi: {base_qi}")
        print(f"  regressed_qi: {reg_qi}")
        only_in_base = set(base_qi) - set(reg_qi)
        only_in_reg = set(reg_qi) - set(base_qi)
        if only_in_base:
            print(f"  only_in_base: {list(only_in_base)}")
        if only_in_reg:
            print(f"  only_in_regressed: {list(only_in_reg)}")
        print()

    # Compare restart actions
    restBase = gBase.get("RESTART", [])
    restReg = gReg.get("RESTART", [])

    # Check if regressed had more stuck/cascade events
    maxStuckBase = max((r.get("stuck", 0) for r in restBase), default=0)
    maxStuckReg = max((r.get("stuck", 0) for r in restReg), default=0)
    maxCascBase = max((r.get("cascade", 0) for r in restBase), default=0)
    maxCascReg = max((r.get("cascade", 0) for r in restReg), default=0)

    if maxStuckReg > maxStuckBase:
        print(f"WARNING: regressed had higher stuck count ({maxStuckReg} vs {maxStuckBase})")
    if maxCascReg > maxCascBase:
        print(f"WARNING: regressed escalated cascade further (L{maxCascReg} vs L{maxCascBase})")
    print()

    # Quantifiers that disappeared or appeared
    instBase = Counter(e.get("q", "?") for e in gBase.get("QI_INSERT", []))
    instReg = Counter(e.get("q", "?") for e in gReg.get("QI_INSERT", []))

    appeared = set(instReg.keys()) - set(instBase.keys())
    disappeared = set(instBase.keys()) - set(instReg.keys())

    if appeared:
        print(f"new_quantifiers_in_regressed: {len(appeared)}")
        for q in list(appeared)[:10]:
            print(f"  {instReg[q]:>6} instances  {q}")

    if disappeared:
        print(f"quantifiers_missing_in_regressed: {len(disappeared)}")
        for q in list(disappeared)[:10]:
            print(f"  was {instBase[q]:>6} instances  {q}")

    # Biggest instance count changes
    all_q = set(instBase.keys()) | set(instReg.keys())
    changes = []
    for q in all_q:
        a, b = instBase.get(q, 0), instReg.get(q, 0)
        if a != b:
            changes.append((q, a, b, b - a))
    changes.sort(key=lambda x: -abs(x[3]))

    if changes:
        print()
        print("biggest_qi_count_changes:")
        print(f"  {'DELTA':>8}  {'BASE':>7}  {'REG':>7}  QUANTIFIER")
        for q, a, b, d in changes[:15]:
            print(f"  {d:>+8}  {a:>7}  {b:>7}  {q}")


# ---------------------------------------------------------------------------
# Subcommand: timeline
# ---------------------------------------------------------------------------

def cmd_timeline(args):
    events = load_trace(args.trace)

    if args.q:
        # Per-quantifier timeline: show all events for this quantifier
        matched = [e for e in events if args.q in e.get("q", "")]
        print(f"events_for_quantifier '{args.q}': {len(matched)}")
        print()

        # Group by type
        groups = by_type(matched)
        for t, evs in sorted(groups.items()):
            print(f"{t}: {len(evs)}")

        # Show reward progression
        rewards = [e for e in matched if e.get("t") == "REWARD"]
        if rewards:
            print()
            print("reward_progression:")
            print(f"  {'CONFLICT':>8}  {'OLD':>8}  {'NEW':>8}  {'WEIGHT':>7}  {'DEPTH':>5}")
            for r in rewards[:50]:
                print(f"  {r.get('c', '?'):>8}  {r.get('old', 0):>8.4f}  "
                      f"{r.get('new', 0):>8.4f}  {r.get('weight', 0):>7.4f}  "
                      f"{r.get('depth', 0):>5}")
            if len(rewards) > 50:
                print(f"  ... {len(rewards) - 50} more")

        # Show QI insert cost progression
        inserts = [e for e in matched if e.get("t") == "QI_INSERT"]
        if inserts:
            print()
            print("cost_progression:")
            costs = [e.get("cost", 0) for e in inserts]
            print(f"  first_cost: {costs[0]:.4f}")
            print(f"  last_cost: {costs[-1]:.4f}")
            print(f"  min_cost: {min(costs):.4f}")
            print(f"  max_cost: {max(costs):.4f}")
    else:
        # Global timeline: conflicts over time
        conflicts = [e for e in events if e.get("t") == "CONFLICT"]
        restarts = [e for e in events if e.get("t") == "RESTART"]

        print(f"total_conflicts: {len(conflicts)}")
        print(f"total_restarts: {len(restarts)}")
        print()

        # Bucket conflicts by windows
        if conflicts:
            max_c = max(e.get("c", 0) for e in conflicts)
            bucket_size = max(max_c // 20, 1)
            buckets: Counter = Counter()
            for c in conflicts:
                bucket = c.get("c", 0) // bucket_size
                buckets[bucket] += 1

            print("conflict_density (per window):")
            for b in sorted(buckets.keys()):
                bar = "#" * min(buckets[b], 60)
                print(f"  [{b*bucket_size:>6}-{(b+1)*bucket_size:>6})  {buckets[b]:>4}  {bar}")


# ---------------------------------------------------------------------------
# Subcommand: cost
# ---------------------------------------------------------------------------

def cmd_cost(args):
    events = load_trace(args.trace)
    inserts = [e for e in events if e.get("t") == "QI_INSERT"]

    if not inserts:
        print("no QI_INSERT events")
        return

    costs = [e.get("cost", 0) for e in inserts]
    heats = [e.get("heat", 0) for e in inserts]

    # Cost histogram
    print(f"qi_inserts: {len(inserts)}")
    print()

    # Buckets: [0,1), [1,2), ..., [9,10), [10,20), [20,inf)
    buckets = [0] * 12  # 0-9 individual, 10-20, 20+
    for c in costs:
        if c < 10:
            buckets[int(c)] += 1
        elif c < 20:
            buckets[10] += 1
        else:
            buckets[11] += 1

    labels = [f"[{i},{i+1})" for i in range(10)] + ["[10,20)", "[20,inf)"]
    max_count = max(buckets) if buckets else 1

    print("cost_distribution:")
    for label, count in zip(labels, buckets):
        bar_len = int(50 * count / max_count) if max_count > 0 else 0
        bar = "#" * bar_len
        print(f"  {label:>10}  {count:>7}  {bar}")

    print()

    # Heat distribution
    heat_zero = sum(1 for h in heats if h == 0)
    heat_nonzero = len(heats) - heat_zero
    print(f"heat_zero: {heat_zero} ({fmt_pct(heat_zero, len(heats))})")
    print(f"heat_nonzero: {heat_nonzero} ({fmt_pct(heat_nonzero, len(heats))})")
    if heat_nonzero:
        nz = [h for h in heats if h > 0]
        print(f"  heat_min: {min(nz):.4f}")
        print(f"  heat_max: {max(nz):.4f}")
        print(f"  heat_mean: {sum(nz)/len(nz):.4f}")

    # Per-quantifier average cost
    print()
    qi_costs: dict[str, list[float]] = defaultdict(list)
    for e in inserts:
        qi_costs[e.get("q", "?")].append(e.get("cost", 0))

    print(f"per_quantifier_avg_cost (top 20 by instance count):")
    print(f"  {'AVG_COST':>8}  {'INST':>7}  QUANTIFIER")
    ranked = sorted(qi_costs.items(), key=lambda x: -len(x[1]))
    for q, costs_list in ranked[:20]:
        avg = sum(costs_list) / len(costs_list)
        print(f"  {avg:>8.4f}  {len(costs_list):>7}  {q}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        prog="z3trace",
        description="Query tool for Z3 adaptive engine JSONL traces",
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    # summary
    p = sub.add_parser("summary", help="Overall trace statistics")
    p.add_argument("trace")

    # top
    p = sub.add_parser("top", help="Top quantifiers by metric")
    p.add_argument("trace")
    p.add_argument("--by", choices=["reward", "inst", "instances", "conflicts", "hit_rate"],
                   default="reward")
    p.add_argument("--n", type=int, default=20)

    # conflicts
    p = sub.add_parser("conflicts", help="Conflict details")
    p.add_argument("trace")
    p.add_argument("--limit", type=int, default=20)

    # restarts
    p = sub.add_parser("restarts", help="Restart signal timeline")
    p.add_argument("trace")

    # filter
    p = sub.add_parser("filter", help="Filter events by criteria")
    p.add_argument("trace")
    p.add_argument("--type", help="Event type (QI_INSERT, CONFLICT, etc.)")
    p.add_argument("--q", help="Quantifier name substring")
    p.add_argument("--min-cost", type=float, dest="min_cost")
    p.add_argument("--after-conflict", type=int, dest="after_conflict")
    p.add_argument("--before-conflict", type=int, dest="before_conflict")
    p.add_argument("--limit", type=int, default=50)

    # diff
    p = sub.add_parser("diff", help="Compare two traces")
    p.add_argument("base")
    p.add_argument("other")

    # diagnose
    p = sub.add_parser("diagnose", help="Find root cause of regression")
    p.add_argument("base")
    p.add_argument("regressed")

    # timeline
    p = sub.add_parser("timeline", help="Event timeline (global or per-quantifier)")
    p.add_argument("trace")
    p.add_argument("--q", help="Quantifier name substring for per-quantifier view")

    # cost
    p = sub.add_parser("cost", help="Cost distribution analysis")
    p.add_argument("trace")

    args = parser.parse_args()

    cmds = {
        "summary": cmd_summary,
        "top": cmd_top,
        "conflicts": cmd_conflicts,
        "restarts": cmd_restarts,
        "filter": cmd_filter,
        "diff": cmd_diff,
        "diagnose": cmd_diagnose,
        "timeline": cmd_timeline,
        "cost": cmd_cost,
    }

    cmds[args.cmd](args)


if __name__ == "__main__":
    main()
