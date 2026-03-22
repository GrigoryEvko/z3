#!/usr/bin/env python3
"""
z3trace -- CLI query tool for Z3 adaptive engine JSONL traces.

Six commands cover all analysis needs:

    z3trace.py show      [trace.jsonl]  [--section SECTION ...] [--by KEY] [--n N]
    z3trace.py diff      <base.jsonl>   <other.jsonl>
    z3trace.py diagnose  <base.jsonl>   <regressed.jsonl>
    z3trace.py filter    [trace.jsonl]  [--type T] [--q NAME] [--min-cost V] ...
    z3trace.py run       <input.smt2>   [--z3 PATH] [--feedback] [--auto-tune]
    z3trace.py batch     <dir_or_glob>  [--z3 PATH] [--feedback] [--auto-tune]

If no trace file is given to 'show' or 'filter', the most recent
trace*.jsonl or z3*.jsonl in /tmp/ is auto-detected.

Global flags (before the command):
    --format table|tsv   Output format (default: table)
    --quiet              Suppress section headers and decorative lines
    --head N             Show only the first N lines of output
    --tail N             Show only the last N lines of output

Sections for 'show' (default: all):
    overview    Event counts, QI stats, conflict stats, reward summary, result
    top         Top quantifiers ranked by reward/instances/conflicts
    conflicts   Per-conflict details and quantifier conflict frequency
    restarts    Per-restart signal values
    cost        Cost distribution histogram and per-quantifier average cost
    timeline    Conflict density over time (or per-quantifier with --q)

Filter shortcuts for common patterns:
    --expensive  QI_INSERT events with cost >= 10
    --useful     QI_INSERT quantifiers that appear in CONFLICT qi arrays
    --wasted     QI_INSERT quantifiers that never appear in any CONFLICT
"""

from __future__ import annotations

import argparse
import glob as globmod
import json
import os
import shutil
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Any, Sequence


# ---------------------------------------------------------------------------
# Table: auto-width, alignment, truncation, render-to-string
# ---------------------------------------------------------------------------

class Table:
    """Reusable table formatter with auto-calculated column widths.

    Supports two output modes via render(fmt):
      - 'table': padded columns with auto-calculated widths, 2-space gap
      - 'tsv':   tab-separated values, no padding

    Column alignment is specified per-column: 'r' (right) or 'l' (left).
    The last column can be auto-truncated to fit terminal width.
    """

    def __init__(self, columns: list[str], alignments: str | None = None,
                 truncate_last: bool = False):
        """
        columns:       header names
        alignments:    string of 'r'/'l' per column, e.g. "rrrl".
                       Default: right-align all except last column.
        truncate_last: if True, truncate last column to fit terminal width.
        """
        self.columns = columns
        self.rows: list[list[str]] = []
        n = len(columns)
        if alignments is None:
            self.alignments = ['r'] * (n - 1) + ['l'] if n > 1 else ['l']
        else:
            self.alignments = list(alignments.ljust(n, 'l'))
        self.truncate_last = truncate_last

    def add(self, *values) -> Table:
        """Add a row. Values are converted to strings."""
        self.rows.append([str(v) for v in values])
        return self

    def render(self, fmt: str = 'table') -> str:
        """Render the table as a string.

        fmt: 'table' for padded columns, 'tsv' for tab-separated.
        """
        if fmt == 'tsv':
            return self._render_tsv()
        return self._render_table()

    def _terminal_width(self) -> int:
        try:
            return os.get_terminal_size().columns
        except (OSError, ValueError):
            return 120

    def _render_tsv(self) -> str:
        lines = ['\t'.join(self.columns)]
        for row in self.rows:
            lines.append('\t'.join(row))
        return '\n'.join(lines)

    def _render_table(self) -> str:
        n = len(self.columns)
        # Auto-calculate widths from headers and all data rows
        widths = [len(c) for c in self.columns]
        for row in self.rows:
            for i, cell in enumerate(row):
                if i < n:
                    widths[i] = max(widths[i], len(cell))

        # If truncate_last, compute max width for last column to fit terminal
        max_last: int | None = None
        if self.truncate_last and n > 1:
            prefix_w = sum(widths[:-1]) + 2 * (n - 1)
            term_w = self._terminal_width()
            max_last = max(term_w - prefix_w, 20)

        def fmt_cell(val: str, idx: int) -> str:
            w = widths[idx]
            if max_last is not None and idx == n - 1:
                if len(val) > max_last:
                    val = val[:max_last - 3] + '...'
                w = min(w, max_last)
            if self.alignments[idx] == 'r':
                return val.rjust(w)
            return val.ljust(w)

        lines: list[str] = []
        header = '  '.join(fmt_cell(c, i) for i, c in enumerate(self.columns))
        lines.append(header)

        for row in self.rows:
            padded = row + [''] * (n - len(row))
            line = '  '.join(fmt_cell(padded[i], i) for i in range(n))
            lines.append(line.rstrip())
        return '\n'.join(lines)

    def to_dicts(self) -> list[dict[str, str]]:
        """Return rows as list of dicts keyed by column name (for JSON)."""
        result = []
        for row in self.rows:
            d: dict[str, str] = {}
            for i, col in enumerate(self.columns):
                d[col] = row[i] if i < len(row) else ''
            result.append(d)
        return result

    def __str__(self) -> str:
        return self.render()


# ---------------------------------------------------------------------------
# Output formatting
# ---------------------------------------------------------------------------

class TableWriter:
    """Writes aligned table or TSV output.  Handles headers, section breaks,
    and key-value lines.  All output goes through this so --format, --quiet,
    --head and --tail are respected everywhere.

    When head/tail limits are set, all output is buffered and truncated at
    flush time (end of command).  Otherwise output streams directly."""

    def __init__(self, fmt: str = "table", quiet: bool = False,
                 head: int | None = None, tail: int | None = None):
        self.tsv = (fmt == "tsv")
        self.quiet = quiet
        self._head = head
        self._tail = tail
        self._buffered = head is not None or tail is not None
        self._buf: list[str] = []

    # -- internal output -----------------------------------------------------

    def _emit(self, line: str) -> None:
        """Route a line to stdout or the internal buffer."""
        if self._buffered:
            self._buf.append(line)
        else:
            print(line)

    def flush(self) -> None:
        """Flush buffered output, applying --head/--tail truncation."""
        if not self._buffered:
            return
        lines = self._buf
        if self._tail is not None:
            lines = lines[-self._tail:]
        if self._head is not None:
            lines = lines[:self._head]
        for line in lines:
            print(line)
        self._buf.clear()

    # -- primitives ---------------------------------------------------------

    def section(self, title: str) -> None:
        """Print a section header (suppressed in quiet or tsv mode)."""
        if self.quiet or self.tsv:
            return
        self._emit("")
        self._emit(f"=== {title} ===")

    def blank(self) -> None:
        """Print an empty line (suppressed in tsv mode)."""
        if not self.tsv:
            self._emit("")

    def separator(self, width: int = 60) -> None:
        """Print a horizontal rule (suppressed in tsv/quiet mode)."""
        if self.quiet or self.tsv:
            return
        self._emit("-" * width)

    def kv(self, key: str, value) -> None:
        """Print a key: value line."""
        if self.tsv:
            self._emit(f"{key}\t{value}")
        else:
            self._emit(f"{key}: {value}")

    def kv_indented(self, key: str, value, indent: int = 2) -> None:
        """Print an indented key: value line."""
        if self.tsv:
            self._emit(f"{key}\t{value}")
        else:
            self._emit(f"{' ' * indent}{key}: {value}")

    def info(self, msg: str) -> None:
        """Print an informational line (suppressed in quiet mode)."""
        if self.quiet:
            return
        self._emit(msg)

    def warn(self, msg: str) -> None:
        """Print a warning line (never suppressed)."""
        self._emit(f"WARNING: {msg}")

    def row(self, cells: Sequence, widths: Sequence[int] | None = None,
            aligns: str | None = None) -> None:
        """Print one table row.

        *widths* is a sequence of field widths (positive = right-align,
        negative = left-align).  *aligns* overrides: 'l' left, 'r' right
        per position.  In TSV mode widths/aligns are ignored.
        """
        if self.tsv:
            self._emit("\t".join(str(c) for c in cells))
            return
        parts: list[str] = []
        for i, cell in enumerate(cells):
            s = str(cell)
            if widths and i < len(widths):
                w = widths[i]
                align_char = "l"
                if aligns and i < len(aligns):
                    align_char = aligns[i]
                elif w > 0:
                    align_char = "r"
                else:
                    align_char = "l"
                    w = -w
                if align_char == "r":
                    parts.append(s.rjust(w))
                else:
                    parts.append(s.ljust(w))
            else:
                parts.append(s)
        self._emit("  ".join(parts))

    def header_row(self, cells: Sequence, widths: Sequence[int] | None = None,
                   aligns: str | None = None) -> None:
        """Print a header row (suppressed in quiet mode)."""
        if self.quiet:
            return
        self.row(cells, widths, aligns)

    def footer(self, msg: str) -> None:
        """Print a footer/overflow line (suppressed in quiet mode)."""
        if self.quiet:
            return
        if self.tsv:
            return
        self._emit(f"  ... {msg}")


# ---------------------------------------------------------------------------
# Auto-detection
# ---------------------------------------------------------------------------

def auto_detect_trace() -> str | None:
    """Find the most recent trace JSONL file in /tmp/."""
    candidates: list[str] = []
    for pattern in ["trace*.jsonl", "z3*.jsonl"]:
        candidates.extend(globmod.glob(f"/tmp/{pattern}"))
    if not candidates:
        return None
    candidates.sort(key=lambda p: os.path.getmtime(p), reverse=True)
    return candidates[0]


def resolve_trace_path(raw: str | None) -> str:
    """Resolve a trace file path: use explicit arg, or auto-detect from /tmp/.
    Prints which file was chosen to stderr when auto-detecting."""
    if raw:
        return raw
    detected = auto_detect_trace()
    if detected:
        print(f"# auto-detected trace: {detected}", file=sys.stderr)
        return detected
    print("error: no trace file specified and none found in /tmp/",
          file=sys.stderr)
    print("hint: look for trace*.jsonl or z3*.jsonl, or pass path explicitly",
          file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------------------
# Trace loading
# ---------------------------------------------------------------------------

def load_trace(path: str) -> list[dict]:
    """Load JSONL trace, skipping malformed lines.

    Raises SystemExit with a clear message on missing/unreadable files
    or empty traces.
    """
    p = Path(path)
    if not p.exists():
        print(f"ERROR: file not found: {path}", file=sys.stderr)
        sys.exit(1)
    if not p.is_file():
        print(f"ERROR: not a regular file: {path}", file=sys.stderr)
        sys.exit(1)

    events: list[dict] = []
    malformed = 0
    with open(p) as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                events.append(json.loads(line))
            except json.JSONDecodeError:
                malformed += 1
                if malformed <= 5:
                    print(f"# WARN: skipped malformed line {lineno}",
                          file=sys.stderr)

    if malformed > 5:
        print(f"# WARN: {malformed} total malformed lines skipped",
              file=sys.stderr)

    if not events:
        print(f"ERROR: trace file is empty (no valid JSONL lines): {path}",
              file=sys.stderr)
        sys.exit(1)

    return events


def by_type(events: list[dict]) -> dict[str, list[dict]]:
    """Group events by their 't' (type) field."""
    groups: dict[str, list[dict]] = defaultdict(list)
    for e in events:
        groups[e.get("t", "UNKNOWN")].append(e)
    return groups


def check_nonempty_trace(events: list[dict], path: str) -> None:
    """Warn if the trace has only an INIT event and nothing else."""
    types = {e.get("t") for e in events}
    if types <= {"INIT", "UNKNOWN"}:
        print(f"NOTE: trace contains only INIT event(s), "
              f"no solver activity recorded: {path}", file=sys.stderr)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def fmt_pct(num: int, denom: int) -> str:
    if denom == 0:
        return "0.0%"
    return f"{100.0 * num / denom:.1f}%"


def fmt_num(n) -> str:
    if isinstance(n, float):
        return f"{n:.4f}"
    return str(n)


def safe_div(a: float, b: float, default: float = 0.0) -> float:
    return a / b if b != 0 else default


def build_useful_set(events: list[dict]) -> set[str]:
    """Return set of quantifier names that appear in any CONFLICT qi array."""
    useful: set[str] = set()
    for e in events:
        if e.get("t") == "CONFLICT":
            for qi in e.get("qi", []):
                useful.add(qi.get("q", "?"))
    return useful


# ---------------------------------------------------------------------------
# Show sections -- each writes its output through the TableWriter
# ---------------------------------------------------------------------------

SHOW_SECTIONS = ["overview", "top", "conflicts", "restarts", "cost", "timeline"]


def show_overview(events: list[dict], groups: dict[str, list[dict]],
                  w: TableWriter, path: str) -> None:
    """Overview: event counts, QI stats, conflict summary, rewards, result."""
    w.section("OVERVIEW")

    total = len(events)
    inserts = groups.get("QI_INSERT", [])
    conflicts = groups.get("CONFLICT", [])
    rewards = groups.get("REWARD", [])
    restarts = groups.get("RESTART", [])
    solves = groups.get("SOLVE", [])

    w.kv("trace", path)
    w.kv("events", total)
    w.blank()

    # Event type distribution
    w.info("event_counts:")
    for t, evs in sorted(groups.items(), key=lambda x: -len(x[1])):
        w.kv_indented(t, len(evs))
    w.blank()

    # QI stats
    if inserts:
        costs = [e.get("cost", 0) for e in inserts]
        heats = [e.get("heat", 0) for e in inserts]
        w.kv("qi_inserts", len(inserts))
        w.kv_indented("cost_min", f"{min(costs):.4f}")
        w.kv_indented("cost_max", f"{max(costs):.4f}")
        w.kv_indented("cost_mean", f"{safe_div(sum(costs), len(costs)):.4f}")
        w.kv_indented("cost_median", f"{sorted(costs)[len(costs) // 2]:.4f}")
        nonzero_heat = [h for h in heats if h > 0]
        w.kv_indented("heat_nonzero",
                      f"{len(nonzero_heat)} ({fmt_pct(len(nonzero_heat), len(inserts))})")
        qi_names = Counter(e.get("q", "?") for e in inserts)
        w.kv_indented("unique_quantifiers", len(qi_names))
        w.blank()

    # Conflict stats
    if conflicts:
        sizes = [e.get("sz", 0) for e in conflicts]
        qi_counts = [e.get("qi_count", 0) for e in conflicts]
        with_qi = [c for c in conflicts if c.get("qi_count", 0) > 0]
        w.kv("conflicts", len(conflicts))
        w.kv_indented("with_qi_antecedents",
                      f"{len(with_qi)} ({fmt_pct(len(with_qi), len(conflicts))})")
        w.kv_indented("avg_clause_size",
                      f"{safe_div(sum(sizes), len(sizes)):.1f}")
        w.kv_indented("avg_qi_per_conflict",
                      f"{safe_div(sum(qi_counts), len(qi_counts)):.2f}")
        w.blank()

    # Reward stats
    if rewards:
        final_rewards: dict[str, float] = {}
        for r in rewards:
            final_rewards[r.get("q", "?")] = r.get("new", 0)
        positive = {k: v for k, v in final_rewards.items() if v > 0.01}
        w.kv("reward_updates", len(rewards))
        w.kv_indented("quantifiers_with_reward", len(positive))
        if positive:
            top = sorted(positive.items(), key=lambda x: -x[1])[:5]
            w.info("  top_5:")
            for name, rew in top:
                w.kv_indented(name, f"{rew:.4f}", indent=4)
        w.blank()

    # Restart stats
    if restarts:
        vels = [r.get("vel", 0) for r in restarts]
        bvs = [r.get("bv", 0) for r in restarts]
        cns = [r.get("cn", 0) for r in restarts]
        w.kv("restarts", len(restarts))
        w.kv_indented("vel_range", f"[{min(vels):.4f}, {max(vels):.4f}]")
        w.kv_indented("bv_range", f"[{min(bvs):.4f}, {max(bvs):.4f}]")
        w.kv_indented("cn_range", f"[{min(cns):.4f}, {max(cns):.4f}]")
        max_stuck = max(r.get("stuck", 0) for r in restarts)
        max_cascade = max(r.get("cascade", 0) for r in restarts)
        w.kv_indented("max_stuck", max_stuck)
        w.kv_indented("max_cascade_level", max_cascade)
        w.blank()

    # Solve result
    if solves:
        s = solves[-1]
        w.kv("result", s.get("result", "?"))
        for k in ["conflicts", "restarts", "cache_hits", "cache_misses",
                   "cache_size", "replay", "cascade"]:
            if k in s:
                w.kv_indented(k, fmt_num(s[k]))


def show_top(events: list[dict], groups: dict[str, list[dict]],
             w: TableWriter, sort_by: str = "reward", n: int = 20) -> None:
    """Top quantifiers ranked by a chosen metric."""
    w.section("TOP QUANTIFIERS")

    inserts = groups.get("QI_INSERT", [])
    rewards = groups.get("REWARD", [])
    conflicts = groups.get("CONFLICT", [])

    inst_count = Counter(e.get("q", "?") for e in inserts)

    final_reward: dict[str, float] = {}
    for r in rewards:
        final_reward[r.get("q", "?")] = r.get("new", 0)

    conflict_count: Counter = Counter()
    for c in conflicts:
        for qi in c.get("qi", []):
            conflict_count[qi.get("q", "?")] += 1

    all_q = set(inst_count.keys()) | set(final_reward.keys()) | set(conflict_count.keys())
    if not all_q:
        w.info("(no quantifier data)")
        return

    rows: list[dict] = []
    for q in all_q:
        inst = inst_count.get(q, 0)
        rows.append({
            "q": q,
            "instances": inst,
            "reward": final_reward.get(q, 0.0),
            "conflicts": conflict_count.get(q, 0),
            "hit_rate": safe_div(conflict_count.get(q, 0), inst),
        })

    key_map = {
        "reward":    lambda r: (-r["reward"], -r["instances"]),
        "inst":      lambda r: (-r["instances"], -r["reward"]),
        "instances": lambda r: (-r["instances"], -r["reward"]),
        "conflicts": lambda r: (-r["conflicts"], -r["reward"]),
        "hit_rate":  lambda r: (-r["hit_rate"], -r["instances"]),
    }
    rows.sort(key=key_map.get(sort_by, key_map["reward"]))

    widths = [4, 8, 7, 9, 8, -40]
    headers = ["RANK", "REWARD", "INST", "CONFLICTS", "HIT_RATE", "QUANTIFIER"]
    w.header_row(headers, widths)

    for i, r in enumerate(rows[:n], 1):
        w.row([i,
               f"{r['reward']:.4f}",
               r["instances"],
               r["conflicts"],
               f"{r['hit_rate']:.4f}",
               r["q"]],
              widths)

    if len(rows) > n:
        w.footer(f"{len(rows) - n} more quantifiers")


def show_conflicts(events: list[dict], groups: dict[str, list[dict]],
                   w: TableWriter, limit: int = 20) -> None:
    """Conflict details and per-quantifier conflict frequency."""
    w.section("CONFLICTS")

    conflicts = groups.get("CONFLICT", [])
    if not conflicts:
        w.info("(no conflicts recorded)")
        return

    w.kv("total_conflicts", len(conflicts))
    w.blank()

    # Per-conflict detail table
    widths_detail = [6, 4, 6, -60]
    w.header_row(["#", "SIZE", "QI_CNT", "QI_SOURCES"], widths_detail)

    for c in conflicts[:limit]:
        qi_str = ", ".join(
            f"{qi['q']}@d{qi['d']}" for qi in c.get("qi", [])
        ) if c.get("qi") else "(none)"
        w.row([c.get("c", "?"), c.get("sz", "?"),
               c.get("qi_count", 0), qi_str], widths_detail)

    if len(conflicts) > limit:
        w.footer(f"{len(conflicts) - limit} more conflicts")

    # Quantifier conflict frequency
    w.blank()
    freq: Counter = Counter()
    depth_sum: dict[str, float] = defaultdict(float)
    depth_count: dict[str, int] = defaultdict(int)
    for c in conflicts:
        for qi in c.get("qi", []):
            q = qi.get("q", "?")
            freq[q] += 1
            depth_sum[q] += qi.get("d", 0)
            depth_count[q] += 1

    if freq:
        widths_freq = [6, 9, -40]
        w.header_row(["FREQ", "AVG_DEPTH", "QUANTIFIER"], widths_freq)
        for q, cnt in freq.most_common(20):
            avg_d = safe_div(depth_sum[q], depth_count[q])
            w.row([cnt, f"{avg_d:.2f}", q], widths_freq)


def show_restarts(events: list[dict], groups: dict[str, list[dict]],
                  w: TableWriter) -> None:
    """Per-restart signal values table."""
    w.section("RESTARTS")

    restarts = groups.get("RESTART", [])
    if not restarts:
        w.info("(no restarts recorded)")
        return

    widths = [4, 6, 7, 7, 7, 7, 5, 4, -14]
    headers = ["R", "CONF", "VEL", "BV", "CN", "RE", "STUCK", "CASC", "SKEW"]
    w.header_row(headers, widths)

    for r in restarts:
        if "skew" in r:
            skew_str = f"{r.get('skew', '?')}/{r.get('skew_frac', 0):.2f}"
        else:
            skew_str = "-"
        w.row([
            r.get("r", "?"),
            r.get("c", "?"),
            f"{r.get('vel', 0):.4f}",
            f"{r.get('bv', 0):.4f}",
            f"{r.get('cn', 0):.4f}",
            f"{r.get('re', 0):.4f}",
            r.get("stuck", 0),
            r.get("cascade", 0),
            skew_str,
        ], widths)


def show_cost(events: list[dict], groups: dict[str, list[dict]],
              w: TableWriter) -> None:
    """Cost distribution histogram and per-quantifier average cost."""
    w.section("COST DISTRIBUTION")

    inserts = groups.get("QI_INSERT", [])
    if not inserts:
        w.info("(no QI_INSERT events)")
        return

    costs = [e.get("cost", 0) for e in inserts]
    heats = [e.get("heat", 0) for e in inserts]

    w.kv("qi_inserts", len(inserts))
    w.blank()

    # Cost histogram: [0,1), [1,2), ..., [9,10), [10,20), [20,inf)
    buckets = [0] * 12
    for c in costs:
        if c < 10:
            buckets[int(c)] += 1
        elif c < 20:
            buckets[10] += 1
        else:
            buckets[11] += 1

    labels = [f"[{i},{i+1})" for i in range(10)] + ["[10,20)", "[20,inf)"]
    max_count = max(buckets) if buckets else 1

    w.info("cost_distribution:")
    widths_hist = [10, 7, -50]
    for label, count in zip(labels, buckets):
        if w.tsv:
            w.row([label, count], widths_hist)
        else:
            bar_len = int(50 * count / max_count) if max_count > 0 else 0
            bar = "#" * bar_len
            w.row([label, count, bar], widths_hist)
    w.blank()

    # Heat distribution
    heat_zero = sum(1 for h in heats if h == 0)
    heat_nonzero = len(heats) - heat_zero
    w.kv("heat_zero", f"{heat_zero} ({fmt_pct(heat_zero, len(heats))})")
    w.kv("heat_nonzero", f"{heat_nonzero} ({fmt_pct(heat_nonzero, len(heats))})")
    if heat_nonzero:
        nz = [h for h in heats if h > 0]
        w.kv_indented("heat_min", f"{min(nz):.4f}")
        w.kv_indented("heat_max", f"{max(nz):.4f}")
        w.kv_indented("heat_mean", f"{safe_div(sum(nz), len(nz)):.4f}")
    w.blank()

    # Per-quantifier average cost
    qi_costs: dict[str, list[float]] = defaultdict(list)
    for e in inserts:
        qi_costs[e.get("q", "?")].append(e.get("cost", 0))

    w.info("per_quantifier_avg_cost (top 20 by instance count):")
    widths_qc = [8, 7, -40]
    w.header_row(["AVG_COST", "INST", "QUANTIFIER"], widths_qc)
    ranked = sorted(qi_costs.items(), key=lambda x: -len(x[1]))
    for q, costs_list in ranked[:20]:
        avg = safe_div(sum(costs_list), len(costs_list))
        w.row([f"{avg:.4f}", len(costs_list), q], widths_qc)


def show_timeline(events: list[dict], groups: dict[str, list[dict]],
                  w: TableWriter, q_filter: str | None = None) -> None:
    """Conflict density over time, or per-quantifier timeline with --q."""
    w.section("TIMELINE")

    if q_filter:
        # Per-quantifier timeline
        matched = [e for e in events if q_filter in e.get("q", "")]
        w.kv(f"events for '{q_filter}'", len(matched))
        if not matched:
            return
        w.blank()

        # Event type counts
        sub_groups = by_type(matched)
        for t, evs in sorted(sub_groups.items()):
            w.kv_indented(t, len(evs))
        w.blank()

        # Reward progression
        rewards = [e for e in matched if e.get("t") == "REWARD"]
        if rewards:
            w.info("reward_progression:")
            widths_rew = [8, 8, 8, 7, 5]
            w.header_row(["CONFLICT", "OLD", "NEW", "WEIGHT", "DEPTH"],
                         widths_rew)
            for r in rewards[:50]:
                w.row([
                    r.get("c", "?"),
                    f"{r.get('old', 0):.4f}",
                    f"{r.get('new', 0):.4f}",
                    f"{r.get('weight', 0):.4f}",
                    r.get("depth", 0),
                ], widths_rew)
            if len(rewards) > 50:
                w.footer(f"{len(rewards) - 50} more")

        # Cost progression
        qi_inserts = [e for e in matched if e.get("t") == "QI_INSERT"]
        if qi_inserts:
            w.blank()
            qi_costs = [e.get("cost", 0) for e in qi_inserts]
            w.info("cost_progression:")
            w.kv_indented("first_cost", f"{qi_costs[0]:.4f}")
            w.kv_indented("last_cost", f"{qi_costs[-1]:.4f}")
            w.kv_indented("min_cost", f"{min(qi_costs):.4f}")
            w.kv_indented("max_cost", f"{max(qi_costs):.4f}")
    else:
        # Global timeline: conflict density
        conflicts = groups.get("CONFLICT", [])
        restarts = groups.get("RESTART", [])

        w.kv("total_conflicts", len(conflicts))
        w.kv("total_restarts", len(restarts))
        w.blank()

        if conflicts:
            max_c = max(e.get("c", 0) for e in conflicts)
            bucket_size = max(max_c // 20, 1)
            density: Counter = Counter()
            for c in conflicts:
                bucket = c.get("c", 0) // bucket_size
                density[bucket] += 1

            w.info("conflict_density (per window):")
            widths_cd = [-16, 4, -60]
            for b in sorted(density.keys()):
                label = f"[{b * bucket_size}-{(b + 1) * bucket_size})"
                count = density[b]
                if w.tsv:
                    w.row([label, count], widths_cd)
                else:
                    bar = "#" * min(count, 60)
                    w.row([label, count, bar], widths_cd)


# ---------------------------------------------------------------------------
# Command: show
# ---------------------------------------------------------------------------

def cmd_show(args) -> None:
    w = TableWriter(fmt=args.format, quiet=args.quiet,
                    head=args.head, tail=args.tail)
    trace_path = resolve_trace_path(args.trace)
    events = load_trace(trace_path)
    check_nonempty_trace(events, trace_path)
    groups = by_type(events)

    sections = args.section if args.section else SHOW_SECTIONS

    for sec in sections:
        if sec == "overview":
            show_overview(events, groups, w, trace_path)
        elif sec == "top":
            show_top(events, groups, w,
                     sort_by=args.by or "reward",
                     n=args.n or 20)
        elif sec == "conflicts":
            show_conflicts(events, groups, w, limit=args.limit or 20)
        elif sec == "restarts":
            show_restarts(events, groups, w)
        elif sec == "cost":
            show_cost(events, groups, w)
        elif sec == "timeline":
            show_timeline(events, groups, w, q_filter=args.q)
        else:
            print(f"ERROR: unknown section '{sec}'. "
                  f"Valid: {', '.join(SHOW_SECTIONS)}", file=sys.stderr)
            sys.exit(1)

    w.flush()


# ---------------------------------------------------------------------------
# Command: diff
# ---------------------------------------------------------------------------

def cmd_diff(args) -> None:
    w = TableWriter(fmt=args.format, quiet=args.quiet,
                    head=args.head, tail=args.tail)
    evA = load_trace(args.base)
    evB = load_trace(args.other)

    gA = by_type(evA)
    gB = by_type(evB)

    # High-level stat comparison
    w.section("EVENT COUNT COMPARISON")
    widths_cmp = [-25, 8, 8, 10]
    w.header_row(["METRIC", "BASE", "OTHER", "DELTA"], widths_cmp)
    w.separator(60)

    for key in ["QI_INSERT", "CONFLICT", "REWARD", "RESTART"]:
        a = len(gA.get(key, []))
        b = len(gB.get(key, []))
        delta = b - a
        pct = f"{100.0 * delta / max(a, 1):+.1f}%" if a > 0 else "n/a"
        w.row([key, a, b, f"{delta:+d} {pct}"], widths_cmp)

    # Compare results
    solveA = gA.get("SOLVE", [{}])[-1] if gA.get("SOLVE") else {}
    solveB = gB.get("SOLVE", [{}])[-1] if gB.get("SOLVE") else {}

    w.blank()
    w.kv("result_base", solveA.get("result", "?"))
    w.kv("result_other", solveB.get("result", "?"))

    # Per-quantifier instance diffs
    w.section("QUANTIFIER INSTANCE DIFFS")
    instA = Counter(e.get("q", "?") for e in gA.get("QI_INSERT", []))
    instB = Counter(e.get("q", "?") for e in gB.get("QI_INSERT", []))

    all_q = set(instA.keys()) | set(instB.keys())
    diffs: list[tuple[str, int, int, int]] = []
    for q in all_q:
        a, b = instA.get(q, 0), instB.get(q, 0)
        if a != b:
            diffs.append((q, a, b, b - a))
    diffs.sort(key=lambda x: -abs(x[3]))

    w.kv("changed_quantifiers", len(diffs))
    if diffs:
        widths_qi = [8, 7, 7, -40]
        w.header_row(["DELTA", "BASE", "OTHER", "QUANTIFIER"], widths_qi)
        for q, a, b, d in diffs[:20]:
            w.row([f"{d:+d}", a, b, q], widths_qi)
        if len(diffs) > 20:
            w.footer(f"{len(diffs) - 20} more")
    else:
        w.info("(identical)")

    # Reward diffs
    w.section("REWARD DIFFS")
    rewA: dict[str, float] = {}
    for r in gA.get("REWARD", []):
        rewA[r.get("q", "?")] = r.get("new", 0)
    rewB: dict[str, float] = {}
    for r in gB.get("REWARD", []):
        rewB[r.get("q", "?")] = r.get("new", 0)

    all_rew_q = set(rewA.keys()) | set(rewB.keys())
    rew_diffs: list[tuple[str, float, float, float]] = []
    for q in all_rew_q:
        a, b = rewA.get(q, 0), rewB.get(q, 0)
        if abs(a - b) > 0.001:
            rew_diffs.append((q, a, b, b - a))
    rew_diffs.sort(key=lambda x: -abs(x[3]))

    w.kv("changed_rewards", len(rew_diffs))
    if rew_diffs:
        widths_rew = [8, 8, 8, -40]
        w.header_row(["DELTA", "BASE", "OTHER", "QUANTIFIER"], widths_rew)
        for q, a, b, d in rew_diffs[:15]:
            w.row([f"{d:+.4f}", f"{a:.4f}", f"{b:.4f}", q], widths_rew)
    else:
        w.info("(identical)")

    w.flush()


# ---------------------------------------------------------------------------
# Command: diagnose
# ---------------------------------------------------------------------------

def cmd_diagnose(args) -> None:
    w = TableWriter(fmt=args.format, quiet=args.quiet,
                    head=args.head, tail=args.tail)
    evBase = load_trace(args.base)
    evReg = load_trace(args.regressed)

    gBase = by_type(evBase)
    gReg = by_type(evReg)

    # Results
    solveBase = gBase.get("SOLVE", [{}])[-1] if gBase.get("SOLVE") else {}
    solveReg = gReg.get("SOLVE", [{}])[-1] if gReg.get("SOLVE") else {}

    w.section("REGRESSION DIAGNOSIS")
    w.kv("base_result", solveBase.get("result", "?"))
    w.kv("regressed_result", solveReg.get("result", "?"))
    w.blank()

    confBase = len(gBase.get("CONFLICT", []))
    confReg = len(gReg.get("CONFLICT", []))
    qiBase = len(gBase.get("QI_INSERT", []))
    qiReg = len(gReg.get("QI_INSERT", []))

    w.kv("base_conflicts", confBase)
    w.kv("regressed_conflicts", confReg)
    w.kv("base_qi_inserts", qiBase)
    w.kv("regressed_qi_inserts", qiReg)
    w.blank()

    # First divergence in conflict sequence
    confsBase = gBase.get("CONFLICT", [])
    confsReg = gReg.get("CONFLICT", [])

    def qi_set(conf: dict) -> frozenset:
        return frozenset(qi.get("q", "?") for qi in conf.get("qi", []))

    first_div = None
    for i in range(min(len(confsBase), len(confsReg))):
        if qi_set(confsBase[i]) != qi_set(confsReg[i]):
            first_div = i
            break

    if first_div is not None:
        w.kv("first_divergence_at_conflict_index", first_div)
        cb = confsBase[first_div]
        cr = confsReg[first_div]
        base_qi = [qi.get("q", "?") for qi in cb.get("qi", [])]
        reg_qi = [qi.get("q", "?") for qi in cr.get("qi", [])]
        w.kv_indented("base_qi", str(base_qi))
        w.kv_indented("regressed_qi", str(reg_qi))
        only_in_base = set(base_qi) - set(reg_qi)
        only_in_reg = set(reg_qi) - set(base_qi)
        if only_in_base:
            w.kv_indented("only_in_base", str(list(only_in_base)))
        if only_in_reg:
            w.kv_indented("only_in_regressed", str(list(only_in_reg)))
        w.blank()
    elif confsBase or confsReg:
        w.info("(no divergence found in shared conflict prefix)")
        w.blank()

    # Restart escalation warnings
    restBase = gBase.get("RESTART", [])
    restReg = gReg.get("RESTART", [])

    maxStuckBase = max((r.get("stuck", 0) for r in restBase), default=0)
    maxStuckReg = max((r.get("stuck", 0) for r in restReg), default=0)
    maxCascBase = max((r.get("cascade", 0) for r in restBase), default=0)
    maxCascReg = max((r.get("cascade", 0) for r in restReg), default=0)

    if maxStuckReg > maxStuckBase:
        w.warn(f"regressed had higher stuck count "
               f"({maxStuckReg} vs {maxStuckBase})")
    if maxCascReg > maxCascBase:
        w.warn(f"regressed escalated cascade further "
               f"(L{maxCascReg} vs L{maxCascBase})")

    # Quantifiers that appeared or disappeared
    w.section("QUANTIFIER CHANGES")
    instBase = Counter(e.get("q", "?") for e in gBase.get("QI_INSERT", []))
    instReg = Counter(e.get("q", "?") for e in gReg.get("QI_INSERT", []))

    appeared = set(instReg.keys()) - set(instBase.keys())
    disappeared = set(instBase.keys()) - set(instReg.keys())

    if appeared:
        w.kv("new_quantifiers_in_regressed", len(appeared))
        for q in sorted(appeared, key=lambda x: -instReg[x])[:10]:
            w.kv_indented(q, f"{instReg[q]} instances")

    if disappeared:
        w.kv("quantifiers_missing_in_regressed", len(disappeared))
        for q in sorted(disappeared, key=lambda x: -instBase[x])[:10]:
            w.kv_indented(q, f"was {instBase[q]} instances")

    # Biggest instance count changes
    all_q = set(instBase.keys()) | set(instReg.keys())
    changes: list[tuple[str, int, int, int]] = []
    for q in all_q:
        a, b = instBase.get(q, 0), instReg.get(q, 0)
        if a != b:
            changes.append((q, a, b, b - a))
    changes.sort(key=lambda x: -abs(x[3]))

    if changes:
        w.blank()
        w.info("biggest_qi_count_changes:")
        widths_ch = [8, 7, 7, -40]
        w.header_row(["DELTA", "BASE", "REG", "QUANTIFIER"], widths_ch)
        for q, a, b, d in changes[:15]:
            w.row([f"{d:+d}", a, b, q], widths_ch)

    w.flush()


# ---------------------------------------------------------------------------
# Command: filter
# ---------------------------------------------------------------------------

def cmd_filter(args) -> None:
    w = TableWriter(fmt=args.format, quiet=args.quiet,
                    head=args.head, tail=args.tail)
    trace_path = resolve_trace_path(args.trace)
    events = load_trace(trace_path)

    # Handle preset shortcuts (they imply --type QI_INSERT)
    if args.expensive:
        args.type = args.type or "QI_INSERT"
        if args.min_cost is None:
            args.min_cost = 10.0

    if args.useful or args.wasted:
        useful_set = build_useful_set(events)
        # Restrict to QI_INSERT events
        events = [e for e in events if e.get("t") == "QI_INSERT"]
        if args.useful:
            events = [e for e in events if e.get("q", "?") in useful_set]
        elif args.wasted:
            events = [e for e in events if e.get("q", "?") not in useful_set]
        # Don't apply --type again since we already filtered
        args.type = None

    if args.type:
        events = [e for e in events if e.get("t") == args.type]
    if args.q:
        events = [e for e in events if args.q in e.get("q", "")]
    if args.min_cost is not None:
        events = [e for e in events if e.get("cost", 0) >= args.min_cost]
    if args.after_conflict is not None:
        events = [e for e in events if e.get("c", 0) >= args.after_conflict]
    if args.before_conflict is not None:
        events = [e for e in events if e.get("c", 0) <= args.before_conflict]

    limit = args.limit or 50
    w.kv("matched", len(events))
    for e in events[:limit]:
        w._emit(json.dumps(e))

    if len(events) > limit:
        print(f"# ... {len(events) - limit} more (use --limit N)",
              file=sys.stderr)

    w.flush()


# ---------------------------------------------------------------------------
# Command: run
# ---------------------------------------------------------------------------

def find_z3_binary() -> str:
    """Find z3 binary: check build/z3 relative to repo root, then PATH."""
    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parent
    for candidate in [
        repo_root / "build" / "z3",
        repo_root / "build" / "Release" / "z3",
        repo_root / "build" / "Debug" / "z3",
    ]:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate)
    found = shutil.which("z3")
    if found:
        return found
    return "z3"


def cmd_run(args) -> None:
    z3_bin = args.z3 or find_z3_binary()

    if not shutil.which(z3_bin) and not os.path.isfile(z3_bin):
        print(f"error: z3 binary not found: {z3_bin}", file=sys.stderr)
        sys.exit(1)

    if not os.path.isfile(args.input):
        print(f"error: input file not found: {args.input}", file=sys.stderr)
        sys.exit(1)

    fd, trace_path = tempfile.mkstemp(prefix="z3trace_", suffix=".jsonl")
    os.close(fd)

    try:
        # Build Z3 command line
        z3_cmd = [z3_bin, args.input, f"smt.adaptive_log={trace_path}"]
        if args.feedback:
            z3_cmd.append("smt.qi.feedback=true")
        if args.auto_tune:
            z3_cmd.append("smt.auto_tune=true")
        timeout_sec = args.timeout or 60
        z3_cmd.append(f"-T:{timeout_sec}")

        # Pass through any extra Z3 parameters
        if args.extra:
            z3_cmd.extend(args.extra)

        print(f"# running: {' '.join(z3_cmd)}", file=sys.stderr)

        try:
            result = subprocess.run(
                z3_cmd, capture_output=True, text=True,
                timeout=timeout_sec * 2 + 10,
            )
            if result.stdout.strip():
                print(f"# z3 output: {result.stdout.strip()}", file=sys.stderr)
            if result.returncode != 0 and result.stderr.strip():
                print(f"# z3 stderr: {result.stderr.strip()}", file=sys.stderr)
        except subprocess.TimeoutExpired:
            print(f"# z3 timed out (subprocess killed)", file=sys.stderr)

        # Check trace was produced
        if not os.path.isfile(trace_path) or os.path.getsize(trace_path) == 0:
            print("error: no trace produced (z3 may have exited before INIT)",
                  file=sys.stderr)
            sys.exit(1)

        # Determine which sections to display
        sections = [s.strip() for s in args.section.split(",")]

        # Reuse cmd_show with a synthetic args namespace
        show_args = argparse.Namespace(
            trace=trace_path,
            format=args.format,
            quiet=args.quiet,
            head=args.head,
            tail=args.tail,
            section=sections,
            by="reward",
            n=10,
            limit=10,
            q=None,
        )
        cmd_show(show_args)

        if args.keep_trace:
            print(f"# trace kept at: {trace_path}", file=sys.stderr)
    finally:
        if not args.keep_trace:
            try:
                os.unlink(trace_path)
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Command: batch
# ---------------------------------------------------------------------------

def cmd_batch(args) -> None:
    z3_bin = args.z3 or find_z3_binary()

    # Collect input files
    target = args.target
    input_files: list[str] = []
    if os.path.isdir(target):
        for f in sorted(Path(target).glob("*.smt2")):
            input_files.append(str(f))
    else:
        input_files = sorted(globmod.glob(target))

    if not input_files:
        print(f"error: no .smt2 files found matching: {target}",
              file=sys.stderr)
        sys.exit(1)

    print(f"# found {len(input_files)} input files", file=sys.stderr)

    w = TableWriter(fmt=args.format, quiet=args.quiet,
                    head=args.head, tail=args.tail)

    name_width = max(len(Path(f).stem) for f in input_files)
    name_width = max(name_width, 6)

    widths = [-name_width, 7, 9, 8, 9, -50]
    headers = ["QUERY", "RESULT", "CONFLICTS", "QI_TOTAL",
               "QI_USEFUL", "TOP_QUANTIFIER"]
    w.header_row(headers, widths)
    w.separator(name_width + 7 + 9 + 8 + 9 + 50 + 10)

    timeout_sec = args.timeout or 60

    for input_file in input_files:
        query_name = Path(input_file).stem

        fd, trace_path = tempfile.mkstemp(prefix="z3batch_", suffix=".jsonl")
        os.close(fd)

        try:
            z3_cmd = [z3_bin, input_file, f"smt.adaptive_log={trace_path}"]
            if args.feedback:
                z3_cmd.append("smt.qi.feedback=true")
            if args.auto_tune:
                z3_cmd.append("smt.auto_tune=true")
            z3_cmd.append(f"-T:{timeout_sec}")

            try:
                result = subprocess.run(
                    z3_cmd, capture_output=True, text=True,
                    timeout=timeout_sec * 2 + 10,
                )
                z3_stdout = result.stdout.strip().split("\n")[0] \
                    if result.stdout.strip() else "?"
            except subprocess.TimeoutExpired:
                z3_stdout = "TIMEOUT"

            # Analyze trace
            if os.path.isfile(trace_path) and os.path.getsize(trace_path) > 0:
                events = load_trace(trace_path)
                groups = by_type(events)

                conflicts = groups.get("CONFLICT", [])
                inserts = groups.get("QI_INSERT", [])
                solves = groups.get("SOLVE", [])

                solve_result = z3_stdout
                if solves:
                    solve_result = solves[-1].get("result", z3_stdout)

                num_conflicts = len(conflicts)
                qi_total = len(inserts)

                useful_names = build_useful_set(events)
                qi_useful = sum(1 for e in inserts
                                if e.get("q", "?") in useful_names)

                if inserts:
                    inst_count = Counter(e.get("q", "?") for e in inserts)
                    top_q_name, top_q_count = inst_count.most_common(1)[0]
                    top_q_str = f"{top_q_name} ({top_q_count})"
                else:
                    top_q_str = "-"
            else:
                solve_result = z3_stdout
                num_conflicts = 0
                qi_total = 0
                qi_useful = 0
                top_q_str = "-"

            w.row([query_name, solve_result, num_conflicts, qi_total,
                   qi_useful, top_q_str], widths)

        finally:
            try:
                os.unlink(trace_path)
            except OSError:
                pass

    w.separator(name_width + 7 + 9 + 8 + 9 + 50 + 10)
    w.info(f"# {len(input_files)} queries processed")
    w.flush()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

USAGE_EXAMPLES = """
examples:
  z3trace.py show                                      # auto-detect trace
  z3trace.py show trace.jsonl                          # all sections
  z3trace.py show trace.jsonl --section overview top    # specific sections
  z3trace.py show trace.jsonl --section top --by inst --n 30
  z3trace.py show trace.jsonl --section timeline --q "my_lemma"
  z3trace.py show trace.jsonl --format tsv --quiet      # machine-readable
  z3trace.py --head 20 show trace.jsonl                 # first 20 lines only
  z3trace.py --tail 10 show trace.jsonl                 # last 10 lines only
  z3trace.py diff base.jsonl other.jsonl
  z3trace.py diagnose base.jsonl regressed.jsonl
  z3trace.py filter trace.jsonl --type QI_INSERT --q "lemma" --min-cost 5
  z3trace.py filter --expensive                         # auto-detect, cost>=10
  z3trace.py filter --useful                            # quantifiers in conflicts
  z3trace.py filter --wasted                            # quantifiers never useful
  z3trace.py run input.smt2 --feedback                  # run Z3 + analyze
  z3trace.py run input.smt2 --section overview,top      # run + specific sections
  z3trace.py batch ./benchmarks/ --feedback --timeout 30
  z3trace.py batch "tests/*.smt2" --auto-tune

sections for 'show':
  overview   Event counts, QI/conflict/reward/restart summaries, result
  top        Top quantifiers ranked by reward (--by reward|inst|conflicts|hit_rate)
  conflicts  Per-conflict details and quantifier conflict frequency
  restarts   Per-restart signal values (vel, bv, cn, re, stuck, cascade, skew)
  cost       Cost histogram, heat stats, per-quantifier average cost
  timeline   Conflict density over time (or per-quantifier with --q)
"""


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="z3trace",
        description="CLI query tool for Z3 adaptive engine JSONL traces.",
        epilog=USAGE_EXAMPLES,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--format", choices=["table", "tsv"], default="table",
                        help="Output format: table (aligned columns) "
                             "or tsv (tab-separated, no decoration)")
    parser.add_argument("--quiet", action="store_true",
                        help="Suppress section headers and decorative lines")
    parser.add_argument("--head", type=int, default=None,
                        help="Show only the first N lines of output")
    parser.add_argument("--tail", type=int, default=None,
                        help="Show only the last N lines of output")

    sub = parser.add_subparsers(dest="cmd")

    # -- show ---------------------------------------------------------------
    p = sub.add_parser(
        "show",
        help="Single-trace analysis (all sections or selected)",
        description="Unified single-trace analysis.  Shows all sections by "
                    "default, or use --section to pick specific ones.",
    )
    p.add_argument("trace", nargs="?", default=None,
                   help="Path to JSONL trace file (auto-detected if omitted)")
    p.add_argument("--section", nargs="+", choices=SHOW_SECTIONS,
                   metavar="SECTION",
                   help=f"Sections to show (default: all). "
                        f"Choices: {', '.join(SHOW_SECTIONS)}")
    p.add_argument("--by",
                   choices=["reward", "inst", "instances",
                            "conflicts", "hit_rate"],
                   default="reward",
                   help="Sort key for 'top' section (default: reward)")
    p.add_argument("--n", type=int, default=20,
                   help="Number of rows for 'top' section (default: 20)")
    p.add_argument("--limit", type=int, default=20,
                   help="Max conflict rows for 'conflicts' section "
                        "(default: 20)")
    p.add_argument("--q", metavar="NAME",
                   help="Quantifier name substring for 'timeline' section")

    # -- diff ---------------------------------------------------------------
    p = sub.add_parser(
        "diff",
        help="Compare two traces side by side",
        description="Compare event counts, quantifier instances, and reward "
                    "distributions between two traces.",
    )
    p.add_argument("base", help="Baseline trace file")
    p.add_argument("other", help="Other trace file to compare")

    # -- diagnose -----------------------------------------------------------
    p = sub.add_parser(
        "diagnose",
        help="Find root cause of a regression",
        description="Analyze two traces to find where behavior diverged.  "
                    "Reports first conflict divergence, quantifier changes, "
                    "and restart escalation.",
    )
    p.add_argument("base", help="Baseline (good) trace file")
    p.add_argument("regressed", help="Regressed (bad) trace file")

    # -- filter -------------------------------------------------------------
    p = sub.add_parser(
        "filter",
        help="Filter raw events by criteria",
        description="Output matching events as JSONL.  Combine multiple "
                    "filters (all must match).",
    )
    p.add_argument("trace", nargs="?", default=None,
                   help="Path to JSONL trace file (auto-detected if omitted)")
    p.add_argument("--type", help="Event type (QI_INSERT, CONFLICT, etc.)")
    p.add_argument("--q", metavar="NAME",
                   help="Quantifier name substring match")
    p.add_argument("--min-cost", type=float, dest="min_cost",
                   help="Minimum cost threshold")
    p.add_argument("--after-conflict", type=int, dest="after_conflict",
                   help="Only events at or after this conflict number")
    p.add_argument("--before-conflict", type=int, dest="before_conflict",
                   help="Only events at or before this conflict number")
    p.add_argument("--limit", type=int, default=50,
                   help="Max events to output (default: 50)")
    p.add_argument("--expensive", action="store_true",
                   help="Shortcut: QI_INSERT events with cost >= 10")
    p.add_argument("--useful", action="store_true",
                   help="Shortcut: QI_INSERT quantifiers that appear "
                        "in CONFLICT qi arrays")
    p.add_argument("--wasted", action="store_true",
                   help="Shortcut: QI_INSERT quantifiers that never "
                        "appear in any CONFLICT")

    # -- run ----------------------------------------------------------------
    p = sub.add_parser(
        "run",
        help="Run Z3 on a query and analyze the trace",
        description="Run Z3 with adaptive tracing, then display analysis.  "
                    "Combines z3 invocation and z3trace show in one step.",
    )
    p.add_argument("input", help="Path to .smt2 input file")
    p.add_argument("--z3", default=None,
                   help="Path to z3 binary (auto-detected if omitted)")
    p.add_argument("--feedback", action="store_true",
                   help="Enable smt.qi.feedback=true")
    p.add_argument("--auto-tune", action="store_true", dest="auto_tune",
                   help="Enable smt.auto_tune=true")
    p.add_argument("--section", default="overview,top",
                   help="Comma-separated sections to show "
                        "(default: overview,top)")
    p.add_argument("--keep-trace", action="store_true", dest="keep_trace",
                   help="Keep the trace file instead of deleting it")
    p.add_argument("--timeout", type=int, default=60,
                   help="Z3 timeout in seconds (default: 60)")
    p.add_argument("extra", nargs="*",
                   help="Extra Z3 parameters passed through")

    # -- batch --------------------------------------------------------------
    p = sub.add_parser(
        "batch",
        help="Run analysis on multiple queries, produce comparison table",
        description="Run Z3 with tracing on each .smt2 file in a directory "
                    "or glob pattern, and produce a single summary table.",
    )
    p.add_argument("target",
                   help="Directory of .smt2 files or glob pattern")
    p.add_argument("--z3", default=None,
                   help="Path to z3 binary (auto-detected if omitted)")
    p.add_argument("--feedback", action="store_true",
                   help="Enable smt.qi.feedback=true")
    p.add_argument("--auto-tune", action="store_true", dest="auto_tune",
                   help="Enable smt.auto_tune=true")
    p.add_argument("--timeout", type=int, default=60,
                   help="Z3 timeout in seconds per query (default: 60)")
    p.add_argument("--top", type=int, default=5,
                   help="Unused; reserved for future per-query top-N display")

    args = parser.parse_args()

    # No command given -- print help
    if not args.cmd:
        parser.print_help()
        sys.exit(0)

    dispatch = {
        "show": cmd_show,
        "diff": cmd_diff,
        "diagnose": cmd_diagnose,
        "filter": cmd_filter,
        "run": cmd_run,
        "batch": cmd_batch,
    }
    dispatch[args.cmd](args)


if __name__ == "__main__":
    main()
