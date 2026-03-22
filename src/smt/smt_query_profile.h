/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    smt_query_profile.h

Abstract:

    Lightweight query profiler that classifies SMT queries by their structural
    features and selects optimal solver configuration before search begins.

    The profiler runs in O(|assertions|) time by reusing the static_features
    collection that setup_auto_config already performs. It produces a category
    enum and fractional theory breakdown, which map to tuned parameter presets.

Author:

    Z3 contributors

--*/
#pragma once

#include "ast/static_features.h"
#include "params/smt_params.h"

namespace smt {

    enum class query_category {
        PURE_SAT,           // no theories, no quantifiers
        QF_BV,              // quantifier-free bitvectors
        QF_LIA,             // quantifier-free linear integer arithmetic
        QF_LRA,             // quantifier-free linear real arithmetic
        QF_NLA,             // quantifier-free non-linear arithmetic
        QF_UF,              // quantifier-free uninterpreted functions only
        QF_AUFLIA,          // quantifier-free arrays + UF + LIA
        UFLIA_LIGHT_QI,     // UF+LIA with few quantifiers (< 100)
        UFLIA_HEAVY_QI,     // UF+LIA with many quantifiers (F*/Boogie/Dafny style)
        BV_WITH_QI,         // bitvectors + quantifiers
        DT_WITH_QI,         // datatypes + quantifiers (common in Lean/Isabelle)
        MIXED,              // multiple theories, hard to classify
    };

    struct query_profile {
        // Theory mix (fractions, sum to ~1.0)
        double frac_uf       = 0.0;
        double frac_arith    = 0.0;
        double frac_bv       = 0.0;
        double frac_array    = 0.0;
        double frac_dt       = 0.0;
        double frac_other    = 0.0;

        // Structural features
        unsigned num_quantifiers        = 0;
        unsigned num_assertions         = 0;
        unsigned num_uninterpreted_fns  = 0;
        unsigned num_non_linear         = 0;
        double   avg_quantifier_depth   = 0.0;   // avg body depth per quantifier
        double   trigger_density        = 0.0;    // patterns per quantifier
        bool     has_nla                = false;
        bool     has_int                = false;
        bool     has_real               = false;
        bool     has_bv                 = false;
        bool     has_arrays             = false;
        bool     has_dt                 = false;
        bool     is_cnf                 = false;

        // Derived classification
        query_category cat = query_category::MIXED;

        /**
         * Classify the query from static_features.
         * Must be called after static_features::collect().
         */
        void classify(static_features const & st);

        /**
         * Apply profile-tuned parameters on top of existing settings.
         * Only overrides settings that the profile has strong opinions about.
         * Respects theory installation already done by setup_<logic>().
         */
        void apply_tuning(smt_params & p) const;

        char const * category_name() const;
    };

    // Free function for converting a bare query_category to a name string.
    inline char const * query_profile_category_name(query_category cat) {
        query_profile tmp;
        tmp.cat = cat;
        return tmp.category_name();
    }

}
