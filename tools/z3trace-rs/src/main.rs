use clap::{Parser, Subcommand, ValueEnum};
use simd_json::prelude::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, Read};
use std::path::PathBuf;

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

#[derive(Parser)]
#[command(name = "z3trace", about = "Fast CLI for Z3 adaptive engine JSONL traces")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Single-trace analysis (all sections or selected)
    Show {
        /// Path to JSONL trace file
        trace: PathBuf,

        /// Sections to show (default: all)
        #[arg(long, value_delimiter = ' ', num_args = 1..)]
        section: Option<Vec<Section>>,

        /// Sort key for 'top' section
        #[arg(long, default_value = "reward")]
        by: SortKey,

        /// Number of rows for 'top' and 'waste' sections
        #[arg(short, long, default_value_t = 20)]
        n: usize,

        /// Max conflict rows for 'conflicts' section
        #[arg(long, default_value_t = 20)]
        limit: usize,
    },
}

#[derive(Clone, ValueEnum, PartialEq, Eq, Debug)]
enum Section {
    Overview,
    Top,
    Conflicts,
    Restarts,
    Cost,
    Timeline,
    Waste,
    Chain,
    Engine,
}

#[derive(Clone, ValueEnum, PartialEq, Eq)]
enum SortKey {
    Reward,
    Inst,
    Instances,
    Conflicts,
    HitRate,
}

// ---------------------------------------------------------------------------
// Data structures -- accumulated in a single pass
// ---------------------------------------------------------------------------

#[derive(Default, Clone)]
struct QuantifierStats {
    instances: u64,
    total_cost: f64,
    conflicts: u64,
    heat_nonzero: u64,
    last_reward: f64,
    conflict_depth_sum: f64,
    conflict_depth_count: u64,
}

#[derive(Clone)]
struct ConflictInfo {
    c: i64,
    sz: i64,
    qi_count: i64,
    qi_sources: Vec<(String, i64)>,
}

#[derive(Clone)]
struct RestartInfo {
    r: i64,
    c: i64,
    vel: f64,
    bv: f64,
    cn: f64,
    re: f64,
    stuck: i64,
    cascade: i64,
    skew: Option<String>,
    skew_frac: Option<f64>,
}

#[derive(Default)]
struct SolveInfo {
    result: String,
    conflicts: Option<i64>,
    restarts: Option<i64>,
    cache_hits: Option<i64>,
    cache_misses: Option<i64>,
    cache_size: Option<i64>,
    replay: Option<bool>,
    cascade: Option<i64>,
}

// ---------------------------------------------------------------------------
// Engine stats -- accumulated from new trace event types
// ---------------------------------------------------------------------------

#[derive(Default)]
struct EngineStats {
    mam_matches: u64,
    fp_hits: u64,
    fp_misses: u64,
    qi_eager: u64,
    qi_delayed: u64,
    max_delayed_q: u64,
    last_enodes: u64,
    last_merges: u64,
    last_decisions: u64,
    last_props: u64,
    last_clauses: u64,
    pushes: u64,
    pops: u64,
    max_scope: u64,
    final_checks: u64,
    // Internal tracking
    propagate_total: u64,
    propagate_conflicts: u64,
    sat_restarts: u64,
    egraph_snapshots: u64,
    sat_snapshots: u64,
    qi_batch_count: u64,
    final_consistent: u64,
    final_inconsistent: u64,
}

/// P-square algorithm for streaming percentile estimation.
/// Estimates the p-th percentile without storing all values.
struct PSquare {
    n: [f64; 5],       // marker positions (actual counts)
    ns: [f64; 5],      // desired marker positions
    dns: [f64; 5],     // desired position increments
    q: [f64; 5],       // marker heights (quantile estimates)
    count: u64,
}

impl PSquare {
    fn new(p: f64) -> Self {
        PSquare {
            n: [1.0, 2.0, 3.0, 4.0, 5.0],
            ns: [1.0, 1.0 + 2.0 * p, 1.0 + 4.0 * p, 3.0 + 2.0 * p, 5.0],
            dns: [0.0, p / 2.0, p, (1.0 + p) / 2.0, 1.0],
            q: [0.0; 5],
            count: 0,
        }
    }

    fn add(&mut self, x: f64) {
        self.count += 1;
        if self.count <= 5 {
            self.q[self.count as usize - 1] = x;
            if self.count == 5 {
                // Sort initial 5 values
                self.q.sort_by(|a, b| a.partial_cmp(b).unwrap());
            }
            return;
        }

        // Find cell k
        let k;
        if x < self.q[0] {
            self.q[0] = x;
            k = 0;
        } else if x < self.q[1] {
            k = 0;
        } else if x < self.q[2] {
            k = 1;
        } else if x < self.q[3] {
            k = 2;
        } else if x <= self.q[4] {
            k = 3;
        } else {
            self.q[4] = x;
            k = 3;
        }

        // Increment positions above k
        for i in (k + 1)..5 {
            self.n[i] += 1.0;
        }

        // Update desired positions
        for i in 0..5 {
            self.ns[i] += self.dns[i];
        }

        // Adjust markers 1..3
        for i in 1..4 {
            let d = self.ns[i] - self.n[i];
            if (d >= 1.0 && self.n[i + 1] - self.n[i] > 1.0)
                || (d <= -1.0 && self.n[i - 1] - self.n[i] < -1.0)
            {
                let sign = if d > 0.0 { 1.0 } else { -1.0 };
                // P^2 parabolic formula
                let qi = self.q[i];
                let qim1 = self.q[i - 1];
                let qip1 = self.q[i + 1];
                let ni = self.n[i];
                let nim1 = self.n[i - 1];
                let nip1 = self.n[i + 1];

                let new_q = qi
                    + (sign / (nip1 - nim1))
                        * ((ni - nim1 + sign) * (qip1 - qi) / (nip1 - ni)
                            + (nip1 - ni - sign) * (qi - qim1) / (ni - nim1));

                if new_q > qim1 && new_q < qip1 {
                    self.q[i] = new_q;
                } else {
                    // Linear interpolation fallback
                    let idx = if sign > 0.0 { i + 1 } else { i - 1 };
                    self.q[i] = qi + sign * (self.q[idx] - qi) / (self.n[idx] - ni);
                }
                self.n[i] += sign;
            }
        }
    }

    fn estimate(&self) -> f64 {
        if self.count < 5 {
            if self.count == 0 {
                return 0.0;
            }
            // For small counts, sort and pick median directly
            let mut vals: Vec<f64> = self.q[..self.count as usize].to_vec();
            vals.sort_by(|a, b| a.partial_cmp(b).unwrap());
            vals[vals.len() / 2]
        } else {
            self.q[2] // The middle marker is the percentile estimate
        }
    }
}

const CONFLICT_CAP: usize = 1000;
const RESTART_CAP: usize = 10000;

struct TraceAccumulator {
    qi_stats: HashMap<String, QuantifierStats>,
    event_counts: HashMap<String, u64>,
    total_events: u64,
    cost_histogram: [u64; 12],
    cost_min: f64,
    cost_max: f64,
    cost_sum: f64,
    cost_median: PSquare,
    qi_insert_count: u64,
    heat_nonzero_count: u64,
    conflicts: Vec<ConflictInfo>,
    conflict_total: u64,
    restarts: Vec<RestartInfo>,
    restart_total: u64,
    reward_count: u64,
    solve: Option<SolveInfo>,
    conflict_qi_names: HashMap<String, u64>,
    pair_counts: HashMap<(String, String), u64>,
    chain_lengths: HashMap<usize, u64>,
    depth_distribution: HashMap<i64, u64>,
    malformed: u64,
    restart_vel_min: f64,
    restart_vel_max: f64,
    restart_bv_min: f64,
    restart_bv_max: f64,
    restart_cn_min: f64,
    restart_cn_max: f64,
    restart_max_stuck: i64,
    restart_max_cascade: i64,
    // Engine stats
    engine: EngineStats,
}

impl TraceAccumulator {
    fn new() -> Self {
        Self {
            qi_stats: HashMap::with_capacity(256),
            event_counts: HashMap::with_capacity(16),
            total_events: 0,
            cost_histogram: [0; 12],
            cost_min: f64::MAX,
            cost_max: f64::MIN,
            cost_sum: 0.0,
            cost_median: PSquare::new(0.5),
            qi_insert_count: 0,
            heat_nonzero_count: 0,
            conflicts: Vec::with_capacity(CONFLICT_CAP),
            conflict_total: 0,
            restarts: Vec::with_capacity(128),
            restart_total: 0,
            reward_count: 0,
            solve: None,
            conflict_qi_names: HashMap::with_capacity(64),
            pair_counts: HashMap::with_capacity(256),
            chain_lengths: HashMap::with_capacity(32),
            depth_distribution: HashMap::with_capacity(32),
            malformed: 0,
            restart_vel_min: f64::MAX,
            restart_vel_max: f64::MIN,
            restart_bv_min: f64::MAX,
            restart_bv_max: f64::MIN,
            restart_cn_min: f64::MAX,
            restart_cn_max: f64::MIN,
            restart_max_stuck: 0,
            restart_max_cascade: 0,
            engine: EngineStats::default(),
        }
    }

    /// Process a single event from a borrowed JSON value.
    /// The value borrows from the mutable byte buffer, so all strings
    /// extracted here must be copied to owned Strings.
    #[inline]
    fn process(&mut self, val: &simd_json::BorrowedValue<'_>) {
        let event_type = match val.get_str("t") {
            Some(t) => t,
            None => "UNKNOWN",
        };
        *self
            .event_counts
            .entry(event_type.to_string())
            .or_insert(0) += 1;
        self.total_events += 1;

        match event_type {
            "QI_INSERT" => self.on_qi_insert(val),
            "CONFLICT" => self.on_conflict(val),
            "REWARD" => self.on_reward(val),
            "RESTART" => self.on_restart(val),
            "SOLVE" => self.on_solve(val),
            "MAM" => self.on_mam(val),
            "QI_BATCH" => self.on_qi_batch(val),
            "EGRAPH" => self.on_egraph(val),
            "SAT" => self.on_sat(val),
            "PUSH" => self.on_push(val),
            "POP" => self.on_pop(val),
            "FINAL_CHECK" => self.on_final_check(val),
            "PROPAGATE" => self.on_propagate(val),
            _ => {}
        }
    }

    #[inline]
    fn on_qi_insert(&mut self, val: &simd_json::BorrowedValue<'_>) {
        let q = val.get_str("q").unwrap_or("?");
        let cost = bval_f64(val, "cost");
        let heat = bval_f64(val, "heat");

        self.qi_insert_count += 1;

        if cost < self.cost_min { self.cost_min = cost; }
        if cost > self.cost_max { self.cost_max = cost; }
        self.cost_sum += cost;
        self.cost_median.add(cost);

        let bucket = if cost < 10.0 {
            (cost as usize).min(9)
        } else if cost < 20.0 {
            10
        } else {
            11
        };
        self.cost_histogram[bucket] += 1;

        if heat > 0.0 {
            self.heat_nonzero_count += 1;
        }

        // Avoid allocating a String on every call when the key already exists
        if let Some(stats) = self.qi_stats.get_mut(q) {
            stats.instances += 1;
            stats.total_cost += cost;
            if heat > 0.0 {
                stats.heat_nonzero += 1;
            }
        } else {
            let mut stats = QuantifierStats::default();
            stats.instances = 1;
            stats.total_cost = cost;
            if heat > 0.0 {
                stats.heat_nonzero = 1;
            }
            self.qi_stats.insert(q.to_string(), stats);
        }
    }

    /// Fast path: accept already-parsed q, cost, heat from manual parser.
    #[inline]
    fn on_qi_insert_raw(&mut self, q: &str, cost: f64, heat: f64) {
        self.qi_insert_count += 1;

        if cost < self.cost_min { self.cost_min = cost; }
        if cost > self.cost_max { self.cost_max = cost; }
        self.cost_sum += cost;
        self.cost_median.add(cost);

        let bucket = if cost < 10.0 {
            (cost as usize).min(9)
        } else if cost < 20.0 {
            10
        } else {
            11
        };
        self.cost_histogram[bucket] += 1;

        if heat > 0.0 {
            self.heat_nonzero_count += 1;
        }

        // Avoid allocating a String on every call when the key already exists
        if let Some(stats) = self.qi_stats.get_mut(q) {
            stats.instances += 1;
            stats.total_cost += cost;
            if heat > 0.0 {
                stats.heat_nonzero += 1;
            }
        } else {
            let mut stats = QuantifierStats::default();
            stats.instances = 1;
            stats.total_cost = cost;
            if heat > 0.0 {
                stats.heat_nonzero = 1;
            }
            self.qi_stats.insert(q.to_string(), stats);
        }
    }

    fn on_conflict(&mut self, val: &simd_json::BorrowedValue<'_>) {
        let c = bval_i64(val, "c");
        let sz = bval_i64(val, "sz");
        let qi_count = bval_i64(val, "qi_count");

        self.conflict_total += 1;

        let mut qi_sources: Vec<(String, i64)> = Vec::new();
        let mut unique_names: Vec<String> = Vec::new();

        if let Some(qi_arr) = val.get("qi") {
            if let Some(arr) = qi_arr.as_array() {
                for entry in arr {
                    let q = entry.get_str("q").unwrap_or("?").to_string();
                    let d = bval_i64(entry, "d");
                    qi_sources.push((q.clone(), d));

                    *self.conflict_qi_names.entry(q.clone()).or_insert(0) += 1;

                    let stats = self.qi_stats.entry(q.clone()).or_default();
                    stats.conflicts += 1;
                    stats.conflict_depth_sum += d as f64;
                    stats.conflict_depth_count += 1;

                    *self.depth_distribution.entry(d).or_insert(0) += 1;

                    if !unique_names.contains(&q) {
                        unique_names.push(q);
                    }
                }
            }
        }

        *self.chain_lengths.entry(unique_names.len()).or_insert(0) += 1;

        unique_names.sort();
        for i in 0..unique_names.len() {
            for j in (i + 1)..unique_names.len() {
                let key = (unique_names[i].clone(), unique_names[j].clone());
                *self.pair_counts.entry(key).or_insert(0) += 1;
            }
        }

        if self.conflicts.len() < CONFLICT_CAP {
            self.conflicts.push(ConflictInfo {
                c, sz, qi_count, qi_sources,
            });
        }
    }

    fn on_reward(&mut self, val: &simd_json::BorrowedValue<'_>) {
        self.reward_count += 1;
        let q = val.get_str("q").unwrap_or("?");
        let new_reward = bval_f64(val, "new");
        let stats = self.qi_stats.entry(q.to_string()).or_default();
        stats.last_reward = new_reward;
    }

    fn on_restart(&mut self, val: &simd_json::BorrowedValue<'_>) {
        self.restart_total += 1;

        let vel = bval_f64(val, "vel");
        let bv = bval_f64(val, "bv");
        let cn = bval_f64(val, "cn");
        let re = bval_f64(val, "re");
        let stuck = bval_i64(val, "stuck");
        let cascade = bval_i64(val, "cascade");

        if vel < self.restart_vel_min { self.restart_vel_min = vel; }
        if vel > self.restart_vel_max { self.restart_vel_max = vel; }
        if bv < self.restart_bv_min { self.restart_bv_min = bv; }
        if bv > self.restart_bv_max { self.restart_bv_max = bv; }
        if cn < self.restart_cn_min { self.restart_cn_min = cn; }
        if cn > self.restart_cn_max { self.restart_cn_max = cn; }
        if stuck > self.restart_max_stuck { self.restart_max_stuck = stuck; }
        if cascade > self.restart_max_cascade { self.restart_max_cascade = cascade; }

        if self.restarts.len() < RESTART_CAP {
            let skew = val.get_str("skew").map(|s| s.to_string());
            let skew_frac = if skew.is_some() {
                Some(bval_f64(val, "skew_frac"))
            } else {
                None
            };
            self.restarts.push(RestartInfo {
                r: bval_i64(val, "r"),
                c: bval_i64(val, "c"),
                vel, bv, cn, re, stuck, cascade, skew, skew_frac,
            });
        }
    }

    fn on_solve(&mut self, val: &simd_json::BorrowedValue<'_>) {
        let result = val.get_str("result").unwrap_or("?").to_string();
        let mut info = SolveInfo { result, ..Default::default() };

        if let Some(v) = val.get("conflicts") { info.conflicts = v.as_i64(); }
        if let Some(v) = val.get("restarts") { info.restarts = v.as_i64(); }
        if let Some(v) = val.get("cache_hits") { info.cache_hits = v.as_i64(); }
        if let Some(v) = val.get("cache_misses") { info.cache_misses = v.as_i64(); }
        if let Some(v) = val.get("cache_size") { info.cache_size = v.as_i64(); }
        if let Some(v) = val.get("replay") { info.replay = v.as_bool(); }
        if let Some(v) = val.get("cascade") { info.cascade = v.as_i64(); }

        self.solve = Some(info);
    }

    // -----------------------------------------------------------------------
    // Engine event handlers
    // -----------------------------------------------------------------------

    fn on_mam(&mut self, val: &simd_json::BorrowedValue<'_>) {
        // C++ emits cumulative m_mam_match_total / m_fp_hit_total / m_fp_miss_total
        // at every 10K-match interval, so take the latest snapshot (not sum).
        self.engine.mam_matches = bval_i64(val, "matches") as u64;
        self.engine.fp_hits = bval_i64(val, "fp_hit") as u64;
        self.engine.fp_misses = bval_i64(val, "fp_miss") as u64;
    }

    fn on_qi_batch(&mut self, val: &simd_json::BorrowedValue<'_>) {
        let eager = bval_i64(val, "eager") as u64;
        let delayed = bval_i64(val, "delayed") as u64;
        let delayed_q = bval_i64(val, "delayed_q") as u64;
        self.engine.qi_eager += eager;
        self.engine.qi_delayed += delayed;
        if delayed_q > self.engine.max_delayed_q {
            self.engine.max_delayed_q = delayed_q;
        }
        self.engine.qi_batch_count += 1;
    }

    fn on_egraph(&mut self, val: &simd_json::BorrowedValue<'_>) {
        self.engine.last_enodes = bval_i64(val, "enodes") as u64;
        self.engine.last_merges = bval_i64(val, "eq") as u64;
        self.engine.egraph_snapshots += 1;
    }

    fn on_sat(&mut self, val: &simd_json::BorrowedValue<'_>) {
        self.engine.last_decisions = bval_i64(val, "decisions") as u64;
        self.engine.last_props = bval_i64(val, "props") as u64;
        self.engine.last_clauses = bval_i64(val, "clauses") as u64;
        let restarts = bval_i64(val, "restarts") as u64;
        if restarts > self.engine.sat_restarts {
            self.engine.sat_restarts = restarts;
        }
        self.engine.sat_snapshots += 1;
    }

    fn on_push(&mut self, val: &simd_json::BorrowedValue<'_>) {
        let scope = bval_i64(val, "scope") as u64;
        self.engine.pushes += 1;
        if scope > self.engine.max_scope {
            self.engine.max_scope = scope;
        }
    }

    fn on_pop(&mut self, val: &simd_json::BorrowedValue<'_>) {
        let scope = bval_i64(val, "scope") as u64;
        self.engine.pops += 1;
        if scope > self.engine.max_scope {
            self.engine.max_scope = scope;
        }
    }

    fn on_final_check(&mut self, val: &simd_json::BorrowedValue<'_>) {
        self.engine.final_checks += 1;
        // C++ emits "consistent" as a JSON boolean (true/false), not an integer.
        let consistent = bval_bool(val, "consistent");
        if consistent {
            self.engine.final_consistent += 1;
        } else {
            self.engine.final_inconsistent += 1;
        }
    }

    fn on_propagate(&mut self, val: &simd_json::BorrowedValue<'_>) {
        // C++ emits cumulative m_stats.m_num_propagations and m_num_conflicts,
        // so take the latest snapshot rather than accumulating.
        self.engine.propagate_total = bval_i64(val, "props") as u64;
        self.engine.propagate_conflicts = bval_i64(val, "c") as u64;
    }
}

// ---------------------------------------------------------------------------
// BorrowedValue helpers
// ---------------------------------------------------------------------------

#[inline]
fn bval_f64(val: &simd_json::BorrowedValue<'_>, key: &str) -> f64 {
    match val.get(key) {
        Some(v) => {
            if let Some(f) = v.as_f64() { f }
            else if let Some(i) = v.as_i64() { i as f64 }
            else if let Some(u) = v.as_u64() { u as f64 }
            else { 0.0 }
        }
        None => 0.0,
    }
}

#[inline]
fn bval_i64(val: &simd_json::BorrowedValue<'_>, key: &str) -> i64 {
    match val.get(key) {
        Some(v) => {
            if let Some(i) = v.as_i64() { i }
            else if let Some(u) = v.as_u64() { u as i64 }
            else if let Some(f) = v.as_f64() { f as i64 }
            else { 0 }
        }
        None => 0,
    }
}

#[inline]
fn bval_bool(val: &simd_json::BorrowedValue<'_>, key: &str) -> bool {
    match val.get(key) {
        Some(v) => {
            if let Some(b) = v.as_bool() { b }
            else if let Some(i) = v.as_i64() { i != 0 }
            else if let Some(u) = v.as_u64() { u != 0 }
            else { false }
        }
        None => false,
    }
}

// ---------------------------------------------------------------------------
// Formatting helpers
// ---------------------------------------------------------------------------

fn fmt_pct(num: u64, denom: u64) -> String {
    if denom == 0 {
        "0.0%".to_string()
    } else {
        format!("{:.1}%", 100.0 * num as f64 / denom as f64)
    }
}

#[inline]
fn safe_div(a: f64, b: f64) -> f64 {
    if b == 0.0 { 0.0 } else { a / b }
}

// ---------------------------------------------------------------------------
// Fast QI_INSERT manual parser
// ---------------------------------------------------------------------------

/// Manually extract (q, cost, heat) from a QI_INSERT JSONL line without
/// full JSON parsing. Returns None if the line doesn't match expected format.
///
/// Expected format:
///   {"t":"QI_INSERT","c":0,"q":"k!247","vars":3,"cost":1.0000,"heat":0.0000,"gen":0}
///
/// We only need q, cost, and heat. Everything else is ignored.
#[inline]
fn parse_qi_insert_fast(line: &[u8]) -> Option<(&str, f64, f64)> {
    // Find "q":" -- the quantifier name
    let q_key = b"\"q\":\"";
    let q_pos = find_subslice(line, q_key)?;
    let q_start = q_pos + q_key.len();
    let q_end = q_start + memchr_byte(line.get(q_start..)?, b'"')?;
    let q = std::str::from_utf8(line.get(q_start..q_end)?).ok()?;

    // Find "cost": -- the cost value
    let cost_key = b"\"cost\":";
    let cost_pos = find_subslice(line, cost_key)?;
    let cost_start = cost_pos + cost_key.len();
    let cost = parse_f64_fast(line, cost_start)?;

    // Find "heat": -- the heat value
    let heat_key = b"\"heat\":";
    let heat_pos = find_subslice(line, heat_key)?;
    let heat_start = heat_pos + heat_key.len();
    let heat = parse_f64_fast(line, heat_start)?;

    Some((q, cost, heat))
}

/// Find a subslice in a byte slice.
#[inline]
fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.len() > haystack.len() {
        return None;
    }
    haystack
        .windows(needle.len())
        .position(|w| w == needle)
}

/// Find first occurrence of a byte.
#[inline]
fn memchr_byte(haystack: &[u8], needle: u8) -> Option<usize> {
    haystack.iter().position(|&b| b == needle)
}

/// Parse f64 starting at `start` until comma, closing brace, or end.
/// Uses a fast integer-based approach for the common case of numbers
/// with up to 4 decimal places (e.g. "1.0000", "11.2345").
#[inline]
fn parse_f64_fast(line: &[u8], start: usize) -> Option<f64> {
    let rest = line.get(start..)?;

    // Fast path: parse digits directly without going through str::parse
    let mut i = 0;
    let len = rest.len();

    // Parse integer part
    let mut int_part: u64 = 0;
    while i < len && rest[i] >= b'0' && rest[i] <= b'9' {
        int_part = int_part * 10 + (rest[i] - b'0') as u64;
        i += 1;
    }

    // Parse fractional part
    let mut frac_part: u64 = 0;
    let mut frac_digits: u32 = 0;
    if i < len && rest[i] == b'.' {
        i += 1;
        while i < len && rest[i] >= b'0' && rest[i] <= b'9' {
            frac_part = frac_part * 10 + (rest[i] - b'0') as u64;
            frac_digits += 1;
            i += 1;
        }
    }

    // Check terminator
    if i < len && rest[i] != b',' && rest[i] != b'}' && rest[i] != b' ' {
        // Unexpected character (exponent notation, etc.) -- fall back to std parse
        let end = rest.iter().position(|&b| b == b',' || b == b'}' || b == b' ').unwrap_or(len);
        let s = std::str::from_utf8(rest.get(..end)?).ok()?;
        return s.parse::<f64>().ok();
    }

    static POW10: [f64; 8] = [1.0, 10.0, 100.0, 1000.0, 10000.0, 100000.0, 1000000.0, 10000000.0];
    let divisor = if (frac_digits as usize) < POW10.len() {
        POW10[frac_digits as usize]
    } else {
        10f64.powi(frac_digits as i32)
    };

    Some(int_part as f64 + frac_part as f64 / divisor)
}

// ---------------------------------------------------------------------------
// Single-pass file reader -- optimized hot path
// ---------------------------------------------------------------------------

fn read_trace(path: &PathBuf) -> TraceAccumulator {
    let file = match File::open(path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("ERROR: failed to open {}: {}", path.display(), e);
            std::process::exit(1);
        }
    };

    // Read entire file into memory for maximum SIMD throughput.
    // For a 3GB file this uses ~3GB RAM which is fine for analysis tooling.
    let file_size = file.metadata().map(|m| m.len() as usize).unwrap_or(0);
    let mut data = Vec::with_capacity(file_size + 1);
    let mut reader = BufReader::with_capacity(1 << 20, file);
    reader.read_to_end(&mut data).unwrap_or_else(|e| {
        eprintln!("ERROR: failed to read {}: {}", path.display(), e);
        std::process::exit(1);
    });

    let mut acc = TraceAccumulator::new();

    // QI_INSERT prefix for fast-path detection (>99% of lines in large traces)
    const QI_PREFIX: &[u8] = b"{\"t\":\"QI_INSERT\"";

    let mut pos = 0;
    let len = data.len();

    while pos < len {
        let line_end = memchr_newline(&data[pos..]).map(|i| pos + i).unwrap_or(len);

        // Trim whitespace
        let mut start = pos;
        let mut end = line_end;
        while start < end && data[start].is_ascii_whitespace() {
            start += 1;
        }
        while end > start && data[end - 1].is_ascii_whitespace() {
            end -= 1;
        }

        if start < end {
            let line_bytes = &data[start..end];

            // Fast path: parse QI_INSERT manually without JSON library
            if line_bytes.len() > QI_PREFIX.len() && line_bytes[..QI_PREFIX.len()] == *QI_PREFIX {
                if let Some((q, cost, heat)) = parse_qi_insert_fast(line_bytes) {
                    acc.on_qi_insert_raw(q, cost, heat);
                    *acc.event_counts.entry("QI_INSERT".to_string()).or_insert(0) += 1;
                    acc.total_events += 1;
                } else {
                    // Fallback to full parser
                    let slice = &mut data[start..end];
                    match simd_json::to_borrowed_value(slice) {
                        Ok(val) => acc.process(&val),
                        Err(_) => {
                            acc.malformed += 1;
                            if acc.malformed <= 5 {
                                eprintln!("# WARN: skipped malformed line");
                            }
                        }
                    }
                }
            } else {
                // Slow path: full JSON parse for CONFLICT, REWARD, RESTART, SOLVE, etc.
                let slice = &mut data[start..end];
                match simd_json::to_borrowed_value(slice) {
                    Ok(val) => acc.process(&val),
                    Err(_) => {
                        acc.malformed += 1;
                        if acc.malformed <= 5 {
                            eprintln!("# WARN: skipped malformed line");
                        }
                    }
                }
            }
        }

        pos = line_end + 1;
    }

    if acc.malformed > 5 {
        eprintln!("# WARN: {} total malformed lines skipped", acc.malformed);
    }

    if acc.total_events == 0 {
        eprintln!(
            "ERROR: trace file is empty (no valid JSONL lines): {}",
            path.display()
        );
        std::process::exit(1);
    }

    acc
}

/// Fast newline search. Uses memchr-style byte scan.
#[inline]
fn memchr_newline(haystack: &[u8]) -> Option<usize> {
    haystack.iter().position(|&b| b == b'\n')
}

// ---------------------------------------------------------------------------
// Show sections
// ---------------------------------------------------------------------------

fn show_overview(acc: &TraceAccumulator, path: &str) {
    println!();
    println!("=== OVERVIEW ===");
    println!("trace: {}", path);
    println!("events: {}", acc.total_events);
    println!();

    println!("event_counts:");
    let mut type_counts: Vec<(&String, &u64)> = acc.event_counts.iter().collect();
    type_counts.sort_by(|a, b| b.1.cmp(a.1));
    for (t, count) in &type_counts {
        println!("  {}: {}", t, count);
    }
    println!();

    if acc.qi_insert_count > 0 {
        let cost_mean = safe_div(acc.cost_sum, acc.qi_insert_count as f64);
        let cost_median = acc.cost_median.estimate();

        println!("qi_inserts: {}", acc.qi_insert_count);
        println!("  cost_min: {:.4}", acc.cost_min);
        println!("  cost_max: {:.4}", acc.cost_max);
        println!("  cost_mean: {:.4}", cost_mean);
        println!("  cost_median: {:.4}", cost_median);
        println!(
            "  heat_nonzero: {} ({})",
            acc.heat_nonzero_count,
            fmt_pct(acc.heat_nonzero_count, acc.qi_insert_count)
        );
        println!("  unique_quantifiers: {}", acc.qi_stats.len());
        println!();
    }

    if acc.conflict_total > 0 {
        let with_qi = acc.conflicts.iter().filter(|c| c.qi_count > 0).count() as u64;
        let avg_sz = safe_div(
            acc.conflicts.iter().map(|c| c.sz as f64).sum(),
            acc.conflicts.len() as f64,
        );
        let avg_qi = safe_div(
            acc.conflicts.iter().map(|c| c.qi_count as f64).sum(),
            acc.conflicts.len() as f64,
        );
        println!("conflicts: {}", acc.conflict_total);
        println!(
            "  with_qi_antecedents: {} ({})",
            with_qi,
            fmt_pct(with_qi, acc.conflict_total)
        );
        println!("  avg_clause_size: {:.1}", avg_sz);
        println!("  avg_qi_per_conflict: {:.2}", avg_qi);
        println!();
    }

    if acc.reward_count > 0 {
        let mut positive: Vec<(&String, f64)> = acc
            .qi_stats
            .iter()
            .filter(|(_, s)| s.last_reward > 0.01)
            .map(|(q, s)| (q, s.last_reward))
            .collect();
        println!("reward_updates: {}", acc.reward_count);
        println!("  quantifiers_with_reward: {}", positive.len());
        if !positive.is_empty() {
            positive.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
            println!("  top_5:");
            for (name, rew) in positive.iter().take(5) {
                println!("    {}: {:.4}", name, rew);
            }
        }
        println!();
    }

    if acc.restart_total > 0 {
        println!("restarts: {}", acc.restart_total);
        println!(
            "  vel_range: [{:.4}, {:.4}]",
            acc.restart_vel_min, acc.restart_vel_max
        );
        println!(
            "  bv_range: [{:.4}, {:.4}]",
            acc.restart_bv_min, acc.restart_bv_max
        );
        println!(
            "  cn_range: [{:.4}, {:.4}]",
            acc.restart_cn_min, acc.restart_cn_max
        );
        println!("  max_stuck: {}", acc.restart_max_stuck);
        println!("  max_cascade_level: {}", acc.restart_max_cascade);
        println!();
    }

    if let Some(ref s) = acc.solve {
        println!("result: {}", s.result);
        if let Some(v) = s.conflicts { println!("  conflicts: {}", v); }
        if let Some(v) = s.restarts { println!("  restarts: {}", v); }
        if let Some(v) = s.cache_hits { println!("  cache_hits: {}", v); }
        if let Some(v) = s.cache_misses { println!("  cache_misses: {}", v); }
        if let Some(v) = s.cache_size { println!("  cache_size: {}", v); }
        if let Some(v) = s.replay {
            println!("  replay: {}", if v { "True" } else { "False" });
        }
        if let Some(v) = s.cascade { println!("  cascade: {}", v); }
    }
}

fn show_top(acc: &TraceAccumulator, sort_by: &SortKey, n: usize) {
    println!();
    println!("=== TOP QUANTIFIERS ===");

    if acc.qi_stats.is_empty() {
        println!("(no quantifier data)");
        return;
    }

    struct TopRow {
        q: String,
        instances: u64,
        reward: f64,
        conflicts: u64,
        hit_rate: f64,
    }

    let mut rows: Vec<TopRow> = acc
        .qi_stats
        .iter()
        .map(|(q, s)| TopRow {
            q: q.clone(),
            instances: s.instances,
            reward: s.last_reward,
            conflicts: s.conflicts,
            hit_rate: safe_div(s.conflicts as f64, s.instances as f64),
        })
        .collect();

    match sort_by {
        SortKey::Reward => rows.sort_by(|a, b| {
            b.reward
                .partial_cmp(&a.reward)
                .unwrap()
                .then(b.instances.cmp(&a.instances))
        }),
        SortKey::Inst | SortKey::Instances => rows.sort_by(|a, b| {
            b.instances
                .cmp(&a.instances)
                .then(b.reward.partial_cmp(&a.reward).unwrap())
        }),
        SortKey::Conflicts => rows.sort_by(|a, b| {
            b.conflicts
                .cmp(&a.conflicts)
                .then(b.reward.partial_cmp(&a.reward).unwrap())
        }),
        SortKey::HitRate => rows.sort_by(|a, b| {
            b.hit_rate
                .partial_cmp(&a.hit_rate)
                .unwrap()
                .then(b.instances.cmp(&a.instances))
        }),
    }

    println!(
        "{:>4}  {:>8}  {:>7}  {:>9}  {:>8}  {:<40}",
        "RANK", "REWARD", "INST", "CONFLICTS", "HIT_RATE", "QUANTIFIER"
    );

    for (i, r) in rows.iter().take(n).enumerate() {
        println!(
            "{:>4}  {:>8.4}  {:>7}  {:>9}  {:>8.4}  {:<40}",
            i + 1,
            r.reward,
            r.instances,
            r.conflicts,
            r.hit_rate,
            r.q
        );
    }

    if rows.len() > n {
        println!("  ... {} more quantifiers", rows.len() - n);
    }
}

fn show_conflicts(acc: &TraceAccumulator, limit: usize) {
    println!();
    println!("=== CONFLICTS ===");

    if acc.conflict_total == 0 {
        println!("(no conflicts recorded)");
        return;
    }

    println!("total_conflicts: {}", acc.conflict_total);
    println!();

    println!(
        "{:>6}  {:>4}  {:>6}  {:<60}",
        "#", "SIZE", "QI_CNT", "QI_SOURCES"
    );

    for c in acc.conflicts.iter().take(limit) {
        let qi_str = if c.qi_sources.is_empty() {
            "(none)".to_string()
        } else {
            c.qi_sources
                .iter()
                .map(|(q, d)| format!("{}@d{}", q, d))
                .collect::<Vec<_>>()
                .join(", ")
        };
        println!("{:>6}  {:>4}  {:>6}  {:<60}", c.c, c.sz, c.qi_count, qi_str);
    }

    if acc.conflict_total as usize > limit {
        println!(
            "  ... {} more conflicts",
            acc.conflict_total as usize - limit
        );
    }

    println!();
    if !acc.conflict_qi_names.is_empty() {
        println!(
            "{:>6}  {:>9}  {:<40}",
            "FREQ", "AVG_DEPTH", "QUANTIFIER"
        );

        let mut freq_list: Vec<(&String, &u64)> = acc.conflict_qi_names.iter().collect();
        freq_list.sort_by(|a, b| b.1.cmp(a.1));

        for (q, count) in freq_list.iter().take(20) {
            let avg_depth = match acc.qi_stats.get(*q) {
                Some(s) if s.conflict_depth_count > 0 => {
                    safe_div(s.conflict_depth_sum, s.conflict_depth_count as f64)
                }
                _ => 0.0,
            };
            println!("{:>6}  {:>9.2}  {:<40}", count, avg_depth, q);
        }
    }
}

fn show_restarts(acc: &TraceAccumulator) {
    println!();
    println!("=== RESTARTS ===");

    if acc.restart_total == 0 {
        println!("(no restarts recorded)");
        return;
    }

    println!(
        "{:>4}  {:>6}  {:>7}  {:>7}  {:>7}  {:>7}  {:>5}  {:>4}  {:<14}",
        "R", "CONF", "VEL", "BV", "CN", "RE", "STUCK", "CASC", "SKEW"
    );

    for r in &acc.restarts {
        let skew_str = match (&r.skew, r.skew_frac) {
            (Some(s), Some(f)) => format!("{}/{:.2}", s, f),
            _ => "-".to_string(),
        };
        println!(
            "{:>4}  {:>6}  {:>7.4}  {:>7.4}  {:>7.4}  {:>7.4}  {:>5}  {:>4}  {:<14}",
            r.r, r.c, r.vel, r.bv, r.cn, r.re, r.stuck, r.cascade, skew_str
        );
    }
}

fn show_cost(acc: &TraceAccumulator) {
    println!();
    println!("=== COST DISTRIBUTION ===");

    if acc.qi_insert_count == 0 {
        println!("(no QI_INSERT events)");
        return;
    }

    println!("qi_inserts: {}", acc.qi_insert_count);
    println!();

    let labels = [
        "[0,1)", "[1,2)", "[2,3)", "[3,4)", "[4,5)", "[5,6)", "[6,7)", "[7,8)", "[8,9)",
        "[9,10)", "[10,20)", "[20,inf)",
    ];
    let max_count = *acc.cost_histogram.iter().max().unwrap_or(&1);

    println!("cost_distribution:");
    for (i, label) in labels.iter().enumerate() {
        let count = acc.cost_histogram[i];
        let bar_len = if max_count > 0 {
            (50 * count / max_count) as usize
        } else {
            0
        };
        let bar: String = "#".repeat(bar_len);
        println!("{:>10}  {:>7}  {:<50}", label, count, bar);
    }
    println!();

    let heat_zero = acc.qi_insert_count - acc.heat_nonzero_count;
    println!(
        "heat_zero: {} ({})",
        heat_zero,
        fmt_pct(heat_zero, acc.qi_insert_count)
    );
    println!(
        "heat_nonzero: {} ({})",
        acc.heat_nonzero_count,
        fmt_pct(acc.heat_nonzero_count, acc.qi_insert_count)
    );
    println!();

    println!("per_quantifier_avg_cost (top 20 by instance count):");
    println!(
        "{:>8}  {:>7}  {:<40}",
        "AVG_COST", "INST", "QUANTIFIER"
    );

    let mut ranked: Vec<(&String, &QuantifierStats)> = acc.qi_stats.iter().collect();
    ranked.sort_by(|a, b| b.1.instances.cmp(&a.1.instances));

    for (q, stats) in ranked.iter().take(20) {
        let avg = safe_div(stats.total_cost, stats.instances as f64);
        println!("{:>8.4}  {:>7}  {:<40}", avg, stats.instances, q);
    }
}

fn show_timeline(acc: &TraceAccumulator) {
    println!();
    println!("=== TIMELINE ===");

    println!("total_conflicts: {}", acc.conflict_total);
    println!("total_restarts: {}", acc.restart_total);
    println!();

    if acc.conflicts.is_empty() {
        return;
    }

    let max_c = acc.conflicts.iter().map(|c| c.c).max().unwrap_or(0);
    if max_c == 0 {
        return;
    }

    let bucket_size = std::cmp::max(max_c / 20, 1);
    let mut density: HashMap<i64, u64> = HashMap::new();
    for c in &acc.conflicts {
        let bucket = c.c / bucket_size;
        *density.entry(bucket).or_insert(0) += 1;
    }

    println!("conflict_density (per window):");
    let mut buckets: Vec<i64> = density.keys().cloned().collect();
    buckets.sort();
    for b in &buckets {
        let label = format!("[{}-{})", b * bucket_size, (b + 1) * bucket_size);
        let count = density[b];
        let bar = "#".repeat(count.min(60) as usize);
        println!("{:<16}  {:>4}  {:<60}", label, count, bar);
    }
}

fn show_waste(acc: &TraceAccumulator, n: usize) {
    println!();
    println!("=== WASTE ANALYSIS ===");

    if acc.qi_insert_count == 0 {
        println!("(no QI_INSERT events)");
        return;
    }

    let mut total_wasted_instances: u64 = 0;
    let mut total_wasted_cost: f64 = 0.0;
    let mut wasted_quantifiers: Vec<(&String, &QuantifierStats)> = Vec::new();

    for (q, stats) in &acc.qi_stats {
        if stats.instances > 0 && !acc.conflict_qi_names.contains_key(q) {
            total_wasted_instances += stats.instances;
            total_wasted_cost += stats.total_cost;
            wasted_quantifiers.push((q, stats));
        }
    }

    let wasted_pct = if acc.qi_insert_count > 0 {
        100.0 * total_wasted_instances as f64 / acc.qi_insert_count as f64
    } else {
        0.0
    };

    println!(
        "wasted_qi_instances: {} / {} ({:.1}%)",
        total_wasted_instances, acc.qi_insert_count, wasted_pct
    );
    println!("wasted_quantifiers: {}", wasted_quantifiers.len());
    println!("wasted_total_cost: {:.2}", total_wasted_cost);

    wasted_quantifiers.sort_by(|a, b| b.1.instances.cmp(&a.1.instances));

    if !wasted_quantifiers.is_empty() {
        println!();
        println!("top_wasted_quantifiers (zero conflict participation):");
        println!("{:>6}  {:>8}  {}", "INST", "COST", "QUANTIFIER");
        for (q, stats) in wasted_quantifiers.iter().take(n) {
            println!("{:>6}  {:>8.2}  {}", stats.instances, stats.total_cost, q);
        }
    }

    let mut low_yield: Vec<(&String, u64, u64, f64)> = Vec::new();
    for (q, stats) in &acc.qi_stats {
        if stats.instances >= 10 && stats.conflicts > 0 {
            let ratio = stats.conflicts as f64 / stats.instances as f64;
            if ratio < 0.01 {
                low_yield.push((q, stats.instances, stats.conflicts, ratio));
            }
        }
    }
    low_yield.sort_by(|a, b| b.1.cmp(&a.1));

    if !low_yield.is_empty() {
        println!();
        println!("low_yield_quantifiers (<1% hit rate, >= 10 instances):");
        println!(
            "{:>6}  {:>9}  {:>8}  {}",
            "INST", "CONFLICTS", "HIT_RATE", "QUANTIFIER"
        );
        for (q, inst, conf, rate) in low_yield.iter().take(n) {
            println!("{:>6}  {:>9}  {:>8.6}  {}", inst, conf, rate, q);
        }
    }
}

fn show_chain(acc: &TraceAccumulator, n: usize) {
    println!();
    println!("=== CHAIN ANALYSIS ===");

    if acc.conflict_total == 0 {
        println!("(no CONFLICT events)");
        return;
    }

    let zero_qi = *acc.chain_lengths.get(&0).unwrap_or(&0);
    let with_qi = acc.conflict_total - zero_qi;

    println!("total_conflicts: {}", acc.conflict_total);
    println!("with_qi_antecedents: {}", with_qi);
    println!();

    if !acc.chain_lengths.is_empty() {
        let max_cl = *acc.chain_lengths.values().max().unwrap_or(&1);
        println!("chain_length_distribution (QI per conflict):");
        let mut lengths: Vec<(&usize, &u64)> = acc.chain_lengths.iter().collect();
        lengths.sort_by_key(|&(k, _)| *k);
        for (length, cnt) in &lengths {
            let pct = fmt_pct(**cnt, acc.conflict_total);
            let bar_len = std::cmp::min((50 * **cnt / std::cmp::max(max_cl, 1)) as usize, 60);
            let bar = "#".repeat(bar_len);
            println!("  {} QI: {:>6} ({:>6})  {}", length, cnt, pct, bar);
        }
        println!();
    }

    if !acc.depth_distribution.is_empty() {
        println!("qi_attribution_depth_distribution:");
        let mut depths: Vec<(&i64, &u64)> = acc.depth_distribution.iter().collect();
        depths.sort_by_key(|&(k, _)| *k);
        for (depth, cnt) in &depths {
            println!("  depth {}: {}", depth, cnt);
        }
        println!();
    }

    if !acc.pair_counts.is_empty() {
        let mut pairs: Vec<(&(String, String), &u64)> = acc.pair_counts.iter().collect();
        pairs.sort_by(|a, b| b.1.cmp(a.1));

        let shown = std::cmp::min(n, pairs.len());
        println!("top_co_occurring_pairs (top {}):", shown);
        println!("{:>5}  {}  {}", "COUNT", "QUANTIFIER_A", "QUANTIFIER_B");
        for ((a, b), cnt) in pairs.iter().take(n) {
            println!("{:>5}  {}  {}", cnt, a, b);
        }
        println!();
    }

    let mut always_together: Vec<(&String, &String, u64)> = Vec::new();
    for ((a, b), cnt) in &acc.pair_counts {
        let solo_a = acc.conflict_qi_names.get(a).copied().unwrap_or(0);
        let solo_b = acc.conflict_qi_names.get(b).copied().unwrap_or(0);
        let min_solo = solo_a.min(solo_b);
        if min_solo > 0 && *cnt == min_solo && *cnt >= 3 {
            always_together.push((a, b, *cnt));
        }
    }
    always_together.sort_by(|a, b| b.2.cmp(&a.2));

    if !always_together.is_empty() {
        println!(
            "always_together_pairs ({} total, min 3 occurrences):",
            always_together.len()
        );
        println!("{:>5}  {}  {}", "COUNT", "QUANTIFIER_A", "QUANTIFIER_B");
        for (a, b, cnt) in always_together.iter().take(n) {
            println!("{:>5}  {}  {}", cnt, a, b);
        }
    } else {
        println!("always_together_pairs: none found (min 3 occurrences)");
    }
}

fn show_engine(acc: &TraceAccumulator) {
    println!();
    println!("=== ENGINE STATS ===");

    let e = &acc.engine;
    let has_data = e.mam_matches > 0
        || e.fp_hits > 0
        || e.qi_eager > 0
        || e.last_enodes > 0
        || e.last_decisions > 0
        || e.pushes > 0
        || e.final_checks > 0
        || e.propagate_total > 0;

    if !has_data {
        println!("(no engine events recorded)");
        return;
    }

    // MAM section
    if e.mam_matches > 0 || e.fp_hits > 0 || e.fp_misses > 0 {
        let fp_total = e.fp_hits + e.fp_misses;
        println!();
        println!("MAM (E-matching):");
        println!("  matches:       {:>12}", e.mam_matches);
        println!("  fp_hits:       {:>12}", e.fp_hits);
        println!("  fp_misses:     {:>12}", e.fp_misses);
        if fp_total > 0 {
            println!(
                "  fp_hit_rate:   {:>11.1}%",
                100.0 * e.fp_hits as f64 / fp_total as f64
            );
        }
    }

    // QI batch section
    if e.qi_eager > 0 || e.qi_delayed > 0 {
        let qi_total = e.qi_eager + e.qi_delayed;
        println!();
        println!("QI batching:");
        println!("  eager:         {:>12}", e.qi_eager);
        println!("  delayed:       {:>12}", e.qi_delayed);
        println!("  total:         {:>12}", qi_total);
        println!("  max_delayed_q: {:>12}", e.max_delayed_q);
        println!("  batches:       {:>12}", e.qi_batch_count);
        if qi_total > 0 {
            println!(
                "  eager_pct:     {:>11.1}%",
                100.0 * e.qi_eager as f64 / qi_total as f64
            );
        }
    }

    // E-graph section
    if e.last_enodes > 0 || e.egraph_snapshots > 0 {
        println!();
        println!("E-graph (last snapshot):");
        println!("  enodes:        {:>12}", e.last_enodes);
        println!("  merges:        {:>12}", e.last_merges);
        println!("  snapshots:     {:>12}", e.egraph_snapshots);
    }

    // SAT section
    if e.last_decisions > 0 || e.sat_snapshots > 0 {
        println!();
        println!("SAT (last snapshot):");
        println!("  decisions:     {:>12}", e.last_decisions);
        println!("  propagations:  {:>12}", e.last_props);
        println!("  clauses:       {:>12}", e.last_clauses);
        println!("  restarts:      {:>12}", e.sat_restarts);
        println!("  snapshots:     {:>12}", e.sat_snapshots);
    }

    // Scope section
    if e.pushes > 0 || e.pops > 0 {
        println!();
        println!("Scope management:");
        println!("  pushes:        {:>12}", e.pushes);
        println!("  pops:          {:>12}", e.pops);
        println!("  max_scope:     {:>12}", e.max_scope);
    }

    // Final check section
    if e.final_checks > 0 {
        println!();
        println!("Final checks:");
        println!("  total:         {:>12}", e.final_checks);
        println!("  consistent:    {:>12}", e.final_consistent);
        println!("  inconsistent:  {:>12}", e.final_inconsistent);
    }

    // Propagate section
    if e.propagate_total > 0 || e.propagate_conflicts > 0 {
        println!();
        println!("Theory propagation:");
        println!("  propagations:  {:>12}", e.propagate_total);
        println!("  conflicts:     {:>12}", e.propagate_conflicts);
    }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Show {
            trace,
            section,
            by,
            n,
            limit,
        } => {
            if !trace.exists() {
                eprintln!("ERROR: file not found: {}", trace.display());
                std::process::exit(1);
            }
            if !trace.is_file() {
                eprintln!("ERROR: not a regular file: {}", trace.display());
                std::process::exit(1);
            }

            let acc = read_trace(&trace);

            let all_sections = vec![
                Section::Overview,
                Section::Top,
                Section::Conflicts,
                Section::Restarts,
                Section::Cost,
                Section::Timeline,
                Section::Waste,
                Section::Chain,
                Section::Engine,
            ];
            let sections = section.unwrap_or(all_sections);
            let path_str = trace.display().to_string();

            for sec in &sections {
                match sec {
                    Section::Overview => show_overview(&acc, &path_str),
                    Section::Top => show_top(&acc, &by, n),
                    Section::Conflicts => show_conflicts(&acc, limit),
                    Section::Restarts => show_restarts(&acc),
                    Section::Cost => show_cost(&acc),
                    Section::Timeline => show_timeline(&acc),
                    Section::Waste => show_waste(&acc, n),
                    Section::Chain => show_chain(&acc, n),
                    Section::Engine => show_engine(&acc),
                }
            }
        }
    }
}
