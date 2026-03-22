/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qi_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include "params/qi_params.h"
#include "params/smt_params_helper.hpp"

void qi_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_mbqi = p.mbqi();
    m_mbqi_max_cexs = p.mbqi_max_cexs();
    m_mbqi_max_cexs_incr = p.mbqi_max_cexs_incr();
    m_mbqi_max_iterations = p.mbqi_max_iterations();
    m_mbqi_trace = p.mbqi_trace();
    m_mbqi_force_template = p.mbqi_force_template();
    m_mbqi_id = p.mbqi_id();
    m_qe_lite = p.q_lite();
    m_qi_profile = p.qi_profile();
    m_qi_profile_freq = p.qi_profile_freq();
    m_qi_max_instances = p.qi_max_instances();
    m_qi_eager_threshold = p.qi_eager_threshold();
    m_qi_lazy_threshold = p.qi_lazy_threshold();
    m_qi_cost = p.qi_cost();
    m_qi_max_eager_multipatterns = p.qi_max_multi_patterns();
    m_qi_quick_checker = static_cast<quick_checker_mode>(p.qi_quick_checker());
    m_qi_trigger_selectivity = p.qi_trigger_selectivity();
    m_qi_feedback = p.qi_feedback();
    m_qi_relevancy_weight = p.qi_relevancy_weight();
    m_qi_ucb_c = p.qi_ucb_c();
    m_auto_tune = p.auto_tune();
    m_polarity_detection = p.polarity_detection();
    m_cache_file = p.cache_file();
    m_adaptive_log = p.adaptive_log();
    if (p.auto_solve()) {
        m_qi_feedback = true;
        m_auto_tune = true;
        // NOTE: do NOT set m_qi_relevancy_weight here.
        // Relevancy gating (E1) is broken for F* queries because soft_relevancy
        // returns 0 for non-boolean terms, causing 5.5× cost inflation that
        // chokes QI completely. Keep relevancy_weight at its explicit setting.
    }
}

#define DISPLAY_PARAM(X) out << #X"=" << X << '\n';

void qi_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_qi_cost);
    DISPLAY_PARAM(m_qi_new_gen);
    DISPLAY_PARAM(m_qi_eager_threshold);
    DISPLAY_PARAM(m_qi_lazy_threshold);
    DISPLAY_PARAM(m_qi_max_eager_multipatterns);
    DISPLAY_PARAM(m_qi_max_lazy_multipattern_matching);
    DISPLAY_PARAM(m_qi_profile);
    DISPLAY_PARAM(m_qi_profile_freq);
    DISPLAY_PARAM(m_qi_quick_checker);
    DISPLAY_PARAM(m_qi_lazy_quick_checker);
    DISPLAY_PARAM(m_qi_promote_unsat);
    DISPLAY_PARAM(m_qi_max_instances);
    DISPLAY_PARAM(m_qi_lazy_instantiation);
    DISPLAY_PARAM(m_qi_conservative_final_check);
    DISPLAY_PARAM(m_qi_feedback);
    DISPLAY_PARAM(m_mbqi);
    DISPLAY_PARAM(m_mbqi_max_cexs);
    DISPLAY_PARAM(m_mbqi_max_cexs_incr);
    DISPLAY_PARAM(m_mbqi_max_iterations);
    DISPLAY_PARAM(m_mbqi_trace);
    DISPLAY_PARAM(m_mbqi_force_template);
    DISPLAY_PARAM(m_mbqi_id);
}
