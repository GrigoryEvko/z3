/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    smt_query_profile.cpp

Abstract:

    Automatic query profiler for SMT solver configuration.

    Classification logic:
      1. Count theory term/atom occurrences from static_features
      2. Compute fractional breakdown across UF, arith, BV, array, DT
      3. Map to a query_category based on dominant theory + quantifier count
      4. Apply tuned parameters for that category

    Tuning rationale:
      - QF_BV:  relevancy=0, no QI overhead, ext gates for bit-blasting
      - QF_LIA: relevancy=0, phase=theory for arith-heavy search
      - UFLIA_HEAVY_QI: Fstar/Boogie pattern - QI feedback, conservative restart,
        eager threshold based on pattern density, relevancy=2 for pruning
      - PURE_SAT: stripped-down config, no theory overhead
      - BV_WITH_QI: combine BV bit-blasting with QI

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
        switch (cat) {

        case query_category::PURE_SAT:
            // No theories: disable all QI overhead, strip relevancy
            p.m_relevancy_lvl         = 0;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            p.m_qi_eager_threshold    = 1000.0; // effectively disable
            break;

        case query_category::QF_BV:
            // Pure bitvectors: disable QI, low relevancy, enable ext gates
            p.m_relevancy_lvl         = 0;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            p.m_bv_cc                 = false;
            p.m_bb_ext_gates          = true;
            p.m_nnf_cnf               = false;
            break;

        case query_category::QF_LIA:
            // Linear integer arithmetic: theory-based phase selection
            p.m_relevancy_lvl         = 0;
            p.m_arith_reflect         = false;
            p.m_arith_propagate_eqs   = false;
            p.m_nnf_cnf               = false;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            break;

        case query_category::QF_LRA:
            // Linear real arithmetic: similar to QF_LIA with theory phase
            p.m_relevancy_lvl         = 0;
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
            p.m_relevancy_lvl         = 0;
            p.m_nnf_cnf               = false;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            break;

        case query_category::QF_UF:
            // Pure UF: fast congruence closure
            p.m_relevancy_lvl         = 0;
            p.m_nnf_cnf               = false;
            p.m_ematching             = false;
            p.m_mbqi                  = false;
            break;

        case query_category::QF_AUFLIA:
            // Quantifier-free arrays + UF + LIA
            p.m_relevancy_lvl         = 0;
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
                p.m_relevancy_lvl     = 0;
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
