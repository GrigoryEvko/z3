/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    smt_query_profile.cpp

Abstract:

    Automatic query profiler — the static-analysis layer of Z3's auto-tune system.

    ═══════════════════════════════════════════════════════════════════════
    AUTO-TUNE SYSTEM OVERVIEW
    ═══════════════════════════════════════════════════════════════════════

    Three user-facing parameters control the adaptive machinery:

      smt.auto_solve   Master switch. Forces qi.feedback=true AND auto_tune=true.
      smt.auto_tune    Enables manifold-aware meta-updates on restart (Phase B/C).
      smt.qi.feedback  Enables conflict-driven QI reward scoring and adaptive budget.

    When auto_solve is set, all adaptive features activate together.

    ── 1. Auto-profiler (this file) ──────────────────────────────────────

    Runs once per check-sat (or on incremental re-profile). Classifies the
    query into one of 12 categories using static_features collected from the
    assertion set:

      Quantifier-free: PURE_SAT, QF_UF, QF_BV, QF_LIA, QF_LRA, QF_NLA,
                       QF_AUFLIA, MIXED
      Quantified:      UFLIA_LIGHT_QI (<100 quants), UFLIA_HEAVY_QI (>=100),
                       BV_WITH_QI, DT_WITH_QI

    Classification examines theory term/atom counts per family, computes a
    fractional breakdown (UF, arith, BV, array, DT), and selects the category
    from the dominant theory combined with quantifier count. Each category maps
    to a tuned parameter preset applied on top of the logic-specific defaults.

    ── 2. Five manifold signals (smt_context.cpp) ────────────────────────

    Continuously accumulated during search, read at every restart:

      belief_variance      EMA of phase-flip rate. Low = strong polarity
                           consensus, high = chaotic search.
      curvature_noise      Variance of conflict-resolution bump magnitudes,
                           split into QI vs non-QI streams. High values
                           signal unstable reward gradients.
      reward_entropy       Shannon entropy over per-quantifier reward EMAs.
                           Low = few quantifiers dominate, high = uniform.
      theory_importance    Per-theory activity skew (arith, BV, array, UF).
                           Tracked per bool_var via VSIDS-style bumps on
                           theory-propagated conflicts.
      conflict_velocity    Ratio of recent conflict rate to calibrated
                           baseline. Values <1 indicate the solver is stuck.

    ── 3. Meta-update on restart (auto_tune=true) ────────────────────────

    meta_update_on_restart() fires after a warmup gate (>=1000 conflicts,
    >=3 restarts) and reads all 5 signals. Adjustments (B3-B9):

      B3  Phase strategy:    belief_variance < 0.15 → PS_THEORY,
                              belief_variance > 0.45 → PS_CACHING.
      B4  QI threshold:      curvature_noise > 0.6 → tighten threshold,
                              curvature_noise < 0.2 → relax.
      B5  QI strategy:       reward_entropy < 0.5 → switch ematching→MBQI.
      B6  Theory focus:      importance skew → adjust arith/BV-specific params.
      B7  Stuck detection:   conflict_velocity < 0.5 → increment consecutive_stuck.
      B8  Relevancy:         consecutive_stuck >= 2 → drop relevancy level.
      B9  MBQI toggle:       consecutive_stuck >= 3 → enable MBQI fallback.

    Each parameter has a per-restart cooldown to prevent oscillation.

    ── 4. Fallback cascade (Phases C) ────────────────────────────────────

    When consecutive_stuck >= 3, the solver escalates through 4 levels with
    exponential conflict budgets (10000 * 3^level, capped at 270000):

      Level 1  Incremental adjustments (already done by B3-B9).
      Level 2  Relaxed: drop relevancy, reset QI threshold, enable MBQI.
      Level 3  Opposite: flip ematching polarity.
      Level 4  Nuclear: reset ALL parameters to upstream Z3 stock defaults.

    Budget is clamped to remaining rlimit / 4 when a resource limit is active.

    ── 5. Proof strategy cache (Phase E) ─────────────────────────────────

    On UNSAT, capture_proof_strategy() records the top-K quantifiers by
    reward EMA, their structural signatures (quantifier_signature()), and
    the effective solver configuration (θ). Keyed by assertion_hash.

    On subsequent check-sat, apply_proof_strategy() performs two-tier lookup:
      Tier 1: Exact assertion_hash match → apply cached rewards (scale 1.0)
              and warm-start θ (qi threshold, relevancy, ematching, mbqi).
      Tier 2: Fuzzy match — scan all cached strategies, compute signature
              overlap. If >= 80% match, apply with scale = overlap ratio.
    Cache is LRU-bounded at 64 entries (~20KB).

    ── 6. Incremental re-profiling (Phase D) ─────────────────────────────

    Between check-sat calls (push/pop, new assertions), compute_assertion_hash()
    detects content changes via a 64-bit hash over assertion structure. When the
    hash differs from the previous call, check_reprofile() re-runs static_features
    and reclassifies. If the category changes, new tuning is applied and all
    meta-update state (cascade level, stuck counter) is reset.

    ═══════════════════════════════════════════════════════════════════════

Author:

    Z3 contributors

--*/
#include "smt/smt_query_profile.h"
#include "ast/static_features.h"
#include "util/trace.h"

namespace smt {

    void query_profile::classify(static_features const & st) {
        num_quantifiers       = st.m_num_quantifiers;
        num_assertions        = st.m_num_roots;
        num_uninterpreted_fns = st.m_num_uninterpreted_functions;
        num_non_linear        = st.m_num_non_linear;
        has_nla               = st.m_num_non_linear > 0;
        has_int               = st.m_has_int;
        has_real              = st.m_has_real;
        has_bv                = st.m_has_bv;
        has_arrays            = st.m_has_arrays;
        is_cnf                = st.m_cnf;

        // Compute average quantifier body depth
        // static_features doesn't track sum of quantifier body depths directly,
        // so we approximate from the max depth and quantifier count.
        avg_quantifier_depth = (num_quantifiers > 0) ? static_cast<double>(st.m_max_depth) : 0.0;

        // Trigger density: patterns per quantifier
        trigger_density = (num_quantifiers > 0)
            ? static_cast<double>(st.m_num_quantifiers_with_patterns) / static_cast<double>(num_quantifiers)
            : 0.0;

        // Theory breakdown: count theory terms + atoms per family
        // static_features tracks m_num_theory_terms and m_num_theory_atoms indexed by family_id.
        // We sum them per-family, then normalize.
        family_id afid  = st.m.mk_family_id(symbol("arith"));
        family_id bvfid = st.m.mk_family_id(symbol("bv"));
        family_id arfid = st.m.mk_family_id(symbol("array"));
        family_id dtfid = st.m.mk_family_id(symbol("datatype"));

        auto safe_terms = [&](family_id fid) -> unsigned {
            if (fid < 0) return 0;
            unsigned idx = static_cast<unsigned>(fid);
            unsigned t = (idx < st.m_num_theory_terms.size()) ? st.m_num_theory_terms[idx] : 0;
            unsigned a = (idx < st.m_num_theory_atoms.size()) ? st.m_num_theory_atoms[idx] : 0;
            return t + a;
        };

        unsigned c_arith = safe_terms(afid);
        unsigned c_bv    = safe_terms(bvfid);
        unsigned c_array = safe_terms(arfid);
        unsigned c_dt    = safe_terms(dtfid);
        unsigned c_uf    = st.m_num_uninterpreted_exprs;

        // Check for datatypes via the theories bitset
        has_dt = st.m_theories.get(static_cast<unsigned>(dtfid), false);

        unsigned total = c_uf + c_arith + c_bv + c_array + c_dt;
        if (total == 0) total = 1; // avoid division by zero

        frac_uf    = static_cast<double>(c_uf)    / total;
        frac_arith = static_cast<double>(c_arith) / total;
        frac_bv    = static_cast<double>(c_bv)    / total;
        frac_array = static_cast<double>(c_array) / total;
        frac_dt    = static_cast<double>(c_dt)    / total;
        frac_other = 0.0; // remainder if any special theories

        // --- Classification ---
        bool quantified = (num_quantifiers > 0);
        unsigned num_theories = st.num_non_uf_theories();

        if (!quantified) {
            // Quantifier-free classification
            if (num_theories == 0 && c_uf == 0 && st.m_num_bool_exprs > 0) {
                cat = query_category::PURE_SAT;
            }
            else if (num_theories == 0) {
                cat = query_category::QF_UF;
            }
            else if (has_bv && !has_int && !has_real && !has_arrays) {
                cat = query_category::QF_BV;
            }
            else if (has_nla && !has_bv) {
                cat = query_category::QF_NLA;
            }
            else if (has_int && !has_real && !has_bv && !has_nla) {
                if (has_arrays || c_uf > 0)
                    cat = query_category::QF_AUFLIA;
                else
                    cat = query_category::QF_LIA;
            }
            else if (has_real && !has_int && !has_bv && !has_nla) {
                cat = query_category::QF_LRA;
            }
            else {
                cat = query_category::MIXED;
            }
        }
        else {
            // Quantified classification
            if (has_bv) {
                cat = query_category::BV_WITH_QI;
            }
            else if (has_dt && !has_bv && frac_dt > 0.2) {
                cat = query_category::DT_WITH_QI;
            }
            else if (num_quantifiers < 100) {
                cat = query_category::UFLIA_LIGHT_QI;
            }
            else {
                cat = query_category::UFLIA_HEAVY_QI;
            }
        }

        TRACE(query_profile,
            tout << "query_profile: cat=" << category_name()
                 << " asserts=" << num_assertions
                 << " quants=" << num_quantifiers
                 << " uf_fns=" << num_uninterpreted_fns
                 << " nla=" << num_non_linear
                 << " frac_uf=" << frac_uf
                 << " frac_arith=" << frac_arith
                 << " frac_bv=" << frac_bv
                 << " frac_array=" << frac_array
                 << " frac_dt=" << frac_dt
                 << " trigger_density=" << trigger_density
                 << "\n";
        );
    }

    void query_profile::apply_tuning(smt_params & p) const {
        // Apply category-specific parameter tuning.
        // These settings are refinements on top of what setup_<logic>() already did.
        // We only override settings where we have high confidence.

        // Relevancy-dependent case split strategies (CS_RELEVANCY, CS_RELEVANCY_ACTIVITY,
        // CS_RELEVANCY_GOAL) require relevancy_lvl >= 2 to populate the case split queue.
        // The case split queue is already created before apply_tuning runs, so if the
        // user chose a relevancy-based strategy, we must not disable relevancy here.
        bool relevancy_required =
            (p.m_case_split_strategy == CS_RELEVANCY ||
             p.m_case_split_strategy == CS_RELEVANCY_ACTIVITY ||
             p.m_case_split_strategy == CS_RELEVANCY_GOAL);

        switch (cat) {

        case query_category::PURE_SAT:
            // No theories: disable all QI overhead, strip relevancy
            if (!relevancy_required) p.m_relevancy_lvl = 0;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            p.m_qi_eager_threshold    = 1000.0; // effectively disable
            break;

        case query_category::QF_BV:
            // Pure bitvectors: disable QI, low relevancy, enable ext gates
            if (!relevancy_required) p.m_relevancy_lvl = 0;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            p.m_bv_cc                 = false;
            p.m_bb_ext_gates          = true;
            p.m_nnf_cnf               = false;
            break;

        case query_category::QF_LIA:
            // Linear integer arithmetic: theory-based phase selection
            if (!relevancy_required) p.m_relevancy_lvl = 0;
            p.m_arith_reflect         = false;
            p.m_arith_propagate_eqs   = false;
            p.m_nnf_cnf               = false;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            break;

        case query_category::QF_LRA:
            // Linear real arithmetic: similar to QF_LIA with theory phase
            if (!relevancy_required) p.m_relevancy_lvl = 0;
            p.m_arith_reflect         = false;
            p.m_arith_propagate_eqs   = false;
            p.m_eliminate_term_ite    = true;
            p.m_nnf_cnf               = false;
            p.m_phase_selection       = PS_THEORY;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            break;

        case query_category::QF_NLA:
            // Non-linear arithmetic: use old arith solver which handles NLA better
            if (!relevancy_required) p.m_relevancy_lvl = 0;
            p.m_nnf_cnf               = false;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            break;

        case query_category::QF_UF:
            // Pure UF: fast congruence closure
            if (!relevancy_required) p.m_relevancy_lvl = 0;
            p.m_nnf_cnf               = false;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            break;

        case query_category::QF_AUFLIA:
            // Quantifier-free arrays + UF + LIA
            if (!relevancy_required) p.m_relevancy_lvl = 0;
            p.m_nnf_cnf               = false;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            break;

        case query_category::UFLIA_LIGHT_QI:
            // Few quantifiers: moderate QI, MBQI can help
            p.m_qi_eager_threshold    = 10.0;
            p.m_qi_lazy_threshold     = 20.0;
            p.m_mbqi                  = true;
            // Use relevancy to prune but don't be too aggressive
            if (num_quantifiers < 20) {
                if (!relevancy_required) p.m_relevancy_lvl = 0;
            }
            break;

        case query_category::UFLIA_HEAVY_QI:
            // Heavy quantifier workloads (Fstar, Boogie, Dafny: typically 100+ quantifiers).
            // AUFLIA already sets good defaults (qi_quick_checker, phase, restart, mbqi).
            // For very large problems, limit multipattern instantiation to prevent
            // combinatorial explosion.
            if (num_quantifiers > 1000) {
                p.m_qi_max_eager_multipatterns = 0;
            }
            break;

        case query_category::BV_WITH_QI:
            // Bitvectors + quantifiers: enable BV optimizations but keep QI.
            // Do NOT force relevancy=0 here -- quantified BV queries need
            // relevancy pruning to avoid instantiation explosion.
            p.m_bv_cc                 = false;
            p.m_bb_ext_gates          = true;
            p.m_qi_eager_threshold    = 10.0;
            p.m_qi_lazy_threshold     = 20.0;
            p.m_mbqi                  = true;
            break;

        case query_category::DT_WITH_QI:
            // Datatypes + quantifiers: common in Lean/Isabelle exports
            p.m_qi_eager_threshold    = 10.0;
            p.m_qi_lazy_threshold     = 20.0;
            p.m_mbqi                  = true;
            break;

        case query_category::MIXED:
            // Mixed theories: conservative defaults, don't override much
            // The logic-specific setup already handles theory installation.
            break;
        }

        TRACE(query_profile,
            tout << "apply_tuning: cat=" << category_name()
                 << " relevancy=" << p.m_relevancy_lvl
                 << " ematching=" << p.m_ematching
                 << " mbqi=" << p.m_mbqi
                 << " qi_eager=" << p.m_qi_eager_threshold
                 << " qi_lazy=" << p.m_qi_lazy_threshold
                 << " phase=" << p.m_phase_selection
                 << "\n";
        );
    }

    char const * query_profile::category_name() const {
        switch (cat) {
        case query_category::PURE_SAT:        return "PURE_SAT";
        case query_category::QF_BV:           return "QF_BV";
        case query_category::QF_LIA:          return "QF_LIA";
        case query_category::QF_LRA:          return "QF_LRA";
        case query_category::QF_NLA:          return "QF_NLA";
        case query_category::QF_UF:           return "QF_UF";
        case query_category::QF_AUFLIA:       return "QF_AUFLIA";
        case query_category::UFLIA_LIGHT_QI:  return "UFLIA_LIGHT_QI";
        case query_category::UFLIA_HEAVY_QI:  return "UFLIA_HEAVY_QI";
        case query_category::BV_WITH_QI:      return "BV_WITH_QI";
        case query_category::DT_WITH_QI:      return "DT_WITH_QI";
        case query_category::MIXED:           return "MIXED";
        default:                              return "UNKNOWN";
        }
    }

}
