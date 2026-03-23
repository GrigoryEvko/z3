/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_solver.cpp

Abstract:

    SAT solver main class.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/


#include <cmath>
#include <climits>
#include <atomic>
#ifndef SINGLE_THREAD
#include <thread>
#endif
#include "util/luby.h"
#include "util/trace.h"
#include "util/max_cliques.h"
#include "util/gparams.h"
#include "sat/sat_solver.h"
#include "sat/sat_integrity_checker.h"
#include "sat/sat_lookahead.h"
#include "sat/sat_ddfw_wrapper.h"
#include "sat/sat_prob.h"
#include "sat/sat_probsat.h"
#include "sat/sat_anf_simplifier.h"
#include "smt/adaptive_log.h"
#include "params/smt_params_helper.hpp"
#if defined(_MSC_VER) && !defined(_M_ARM) && !defined(_M_ARM64)
# include <xmmintrin.h>
#endif

// Precomputed exponential decay tables for branching heuristics.
// beta1 (0.95^i): anti-exploration decay, Adam first-moment bias correction.
// beta2 (0.999^i): Adam second-moment bias correction.
// constexpr => zero runtime init cost, ~6.4KB total, fits in L1 cache.
// For i > SIZE: beta1 returns 0.0 (0.95^400 ~ 1.2e-9, negligible).
//               beta2 falls back to std::pow (0.999^400 ~ 0.67, NOT negligible).
namespace {
    struct decay_pow_table {
        static constexpr unsigned SIZE = 400;
        double beta1[SIZE + 1];  // 0.95^i
        double beta2[SIZE + 1];  // 0.999^i
        constexpr decay_pow_table() : beta1{}, beta2{} {
            beta1[0] = beta2[0] = 1.0;
            for (unsigned i = 1; i <= SIZE; ++i) {
                beta1[i] = beta1[i - 1] * 0.95;
                beta2[i] = beta2[i - 1] * 0.999;
            }
        }
    };
    static constexpr decay_pow_table s_decay_pow{};
}

static inline double decay_pow095(uint64_t age) {
    if (age > decay_pow_table::SIZE) return 0.0;
    return s_decay_pow.beta1[static_cast<unsigned>(age)];
}

static inline double decay_pow0999(uint64_t age) {
    if (age <= decay_pow_table::SIZE)
        return s_decay_pow.beta2[static_cast<unsigned>(age)];
    // 0.999 decays slowly: 0.999^400 = 0.67, 0.999^10000 = 4.5e-5.
    // Returning 0.0 would create a cliff edge at age=401 that distorts
    // Adam's second moment (m2).  Fall back to std::pow for rare large dt.
    return std::pow(0.999, static_cast<double>(age));
}

namespace sat {


    solver::solver(params_ref const & p, reslimit& l):
        solver_core(l),
        m_checkpoint_enabled(true),
        m_config(p),
        m_par(nullptr),
        m_drat(*this),
        m_cls_allocator_idx(false),
        m_cleaner(*this),
        m_simplifier(*this, p),
        m_scc(*this, p),
        m_asymm_branch(*this, p),
        m_probing(*this, p),
        m_mus(*this),
        m_inconsistent(false),
        m_searching(false),
        m_conflict(justification(0)),
        m_num_frozen(0),
        m_activity_inc(1.0),
        m_case_split_queue(m_activity),
        m_qhead(0),
        m_qhead_binary(0),
        m_scope_lvl(0),
        m_search_lvl(0),
        m_fast_glue_avg(),
        m_slow_glue_avg(),
        m_fast_glue_backup(),
        m_slow_glue_backup(),
        m_trail_avg(),
        m_params(p),
        m_par_id(0),
        m_par_syncing_clauses(false) {
        init_reason_unknown();
        updt_params(p);
        m_conflict_glue           = 0;
        m_conflict_clause_size    = 0;
        m_conflict_decision_level = 0;
        m_conflict_bump_scale     = 1.0;
        m_bump_scale_fast         = 0.0;
        m_bump_scale_slow         = 0.0;
        m_belief_update_ema       = 0.0;
        m_best_phase_size         = 0;
        m_target_assigned         = 0;
        m_conflicts_since_gc      = 0;
        m_conflicts_since_init    = 0;
        m_next_simplify           = 0;
        m_num_checkpoints         = 0;
        m_simplifications         = 0;
        m_touch_index             = 0;
        m_ext                     = nullptr;
        m_cuber                   = nullptr;
        m_local_search            = nullptr;
        m_mc.set_solver(this);
        mk_var(false, false);
    }

    solver::~solver() {
        if (m_adaptive_log) {
            fclose(m_adaptive_log);
            m_adaptive_log = nullptr;
        }
        m_ext = nullptr;
        SASSERT(m_config.m_num_threads > 1 || m_trim || rlimit().is_canceled() || check_invariant());
        CTRACE(sat, !m_clauses.empty(), tout << "Delete clauses\n";);
        del_clauses(m_clauses);
        CTRACE(sat, !m_learned.empty(), tout << "Delete learned\n";);
        del_clauses(m_learned);
        dealloc(m_cuber);
        m_cuber = nullptr;
    }

    void solver::del_clauses(clause_vector& clauses) {
        for (clause * cp : clauses) 
            dealloc_clause(cp);
        clauses.reset();
        ++m_stats.m_non_learned_generation;
    }

    void solver::set_extension(extension* ext) {
        m_ext = ext;
        if (ext) {
            ext->set_solver(this);
            for (unsigned i = num_user_scopes(); i-- > 0;)
                ext->user_push();
            for (unsigned i = num_scopes(); i-- > 0;)
                ext->push();
        }
    }

    void solver::copy(solver const & src, bool copy_learned) {
        pop_to_base_level();
        del_clauses(m_clauses);
        del_clauses(m_learned);
        m_watches.reset();
        m_assignment.reset();
        m_justification.reset();
        m_decision.reset();
        m_eliminated.reset();
        m_external.reset();
        m_var_scope.reset();
        m_activity.reset();
        m_polarity_belief.reset();
        m_mark.reset();
        m_poison.reset();
        m_removable.reset();
        m_lit_mark.reset();
        m_best_phase.reset();
        m_target_phase.reset();
        m_phase.reset();
        m_prev_phase.reset();
        m_assigned_since_gc.reset();
        m_last_conflict.reset();
        m_last_propagation.reset();
        m_participated.reset();
        m_canceled.reset();
        m_reasoned.reset();
        m_case_split_queue.reset();
        m_simplifier.reset_todos();
        m_qhead = 0;
        m_qhead_binary = 0;
        m_trail.reset();
        m_scopes.reset();
        mk_var(false, false);

        if (src.inconsistent()) {
            set_conflict();
            return;
        }
        
        // create new vars
        for (bool_var v = num_vars(); v < src.num_vars(); ++v) {
            bool ext  = src.m_external[v];
            bool dvar = src.m_decision[v];
            VERIFY(v == mk_var(ext, dvar));
            if (src.was_eliminated(v)) {
                set_eliminated(v, true);
            }
            m_phase[v] = src.m_phase[v];
            m_best_phase[v] = src.m_best_phase[v];
            m_prev_phase[v] = src.m_prev_phase[v];

            // inherit activity:
            m_activity[v] = src.m_activity[v];
            m_polarity_belief[v] = src.m_polarity_belief[v];
            m_case_split_queue.activity_changed_eh(v, false);
        }

        //
        // register the extension before performing assignments.
        // the assignments may call back into the extension.
        //
        if (src.get_extension()) {
            m_ext = src.get_extension()->copy(this);
        }

        unsigned trail_sz = src.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            assign_unit(src.m_trail[i]);
        }

        // copy binary clauses
        {
            unsigned sz = src.m_bin_watches.size();
            for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
                literal l = ~to_literal(l_idx);
                if (src.was_eliminated(l.var())) continue;
                watch_list const & wlist = src.m_bin_watches[l_idx];
                for (auto & wi : wlist) {
                    SASSERT(wi.is_binary_clause());
                    literal l2 = wi.get_literal();
                    if (l.index() > l2.index() ||
                        src.was_eliminated(l2.var()))
                        continue;

                    watched w1(l2, wi.is_learned());
                    watched w2(l, wi.is_learned());
                    m_bin_watches[(~l).index()].push_back(w1);
                    m_bin_watches[(~l2).index()].push_back(w2);
                }
            }
        }

        {
            literal_vector buffer;
            // copy clauses
            for (clause* c : src.m_clauses) {
                buffer.reset();
                for (literal l : *c) buffer.push_back(l);
                mk_clause_core(buffer);
            }

            // copy high quality lemmas
            unsigned num_learned = 0;
            for (clause* c : src.m_learned) {
                if (c->glue() <= 2 || (c->size() <= 40 && c->glue() <= 8) || copy_learned) {
                    buffer.reset();
                    for (literal l : *c) buffer.push_back(l);
                    clause* c1 = mk_clause_core(buffer.size(), buffer.data(), sat::status::redundant());
                    if (c1) {
                        ++num_learned;
                        c1->set_glue(c->glue());
                        c1->set_psm(c->psm());
                        c1->set_tier(c->tier());
                    }
                }
            }
            IF_VERBOSE(2, verbose_stream() << "(sat.copy :learned " << num_learned << ")\n";);
        }
        m_best_phase_size = src.m_best_phase_size;
        if (m_best_phase_size > 0) {
            for (bool_var v = 0; v < num_vars(); ++v) {
                m_best_phase[v] = src.m_best_phase[v];
            }
        }
        m_target_assigned = src.m_target_assigned;
        if (m_target_assigned > 0) {
            for (bool_var v = 0; v < num_vars(); ++v) {
                m_target_phase[v] = src.m_target_phase[v];
            }
        }

        m_user_scope_literals.reset();
        for (auto lit : src.m_user_scope_literals)
            assign_unit(~lit);

        m_mc = src.m_mc;
        m_stats.m_units = init_trail_size();
    }

    // -----------------------
    //
    // Variable & Clause creation
    //
    // -----------------------

    void solver::reset_var(bool_var v, bool ext, bool dvar) {
        m_watches[2*v].reset();
        m_watches[2*v+1].reset();
        m_bin_watches[2*v].reset();
        m_bin_watches[2*v+1].reset();
        m_assignment[2*v] = l_undef;
        m_assignment[2*v+1] = l_undef;
        m_justification[v] = justification(UINT_MAX);
        m_trail_pos[v] = UINT_MAX;
        m_decision[v] = dvar;
        m_eliminated[v] = false;
        m_external[v] = ext;
        m_var_scope[v] = scope_lvl();
        m_touched[v] = 0;
        m_activity[v] = 0.0;
        m_polarity_belief[v] = 0.0;
        m_mark[v] = false;
        m_poison[v] = false;
        m_removable[v] = false;
        m_lit_mark[2*v] = false;
        m_lit_mark[2*v+1] = false;
        m_phase[v] = false;
        m_best_phase[v] = false;
        m_prev_phase[v] = false;
        m_target_phase[v] = l_undef;
        m_assigned_since_gc[v] = false;
        m_last_conflict[v] = 0;        
        m_last_propagation[v] = 0;
        m_participated[v] = 0;
        m_canceled[v] = 0;
        m_reasoned[v] = 0;
        if ((m_config.m_branching_heuristic == BH_ADAM || m_config.m_branching_heuristic == BH_COMBINED) && v < m_adam_m1.size()) {
            m_adam_m1[v] = 0.0;
            m_adam_m2[v] = 0.0;
            m_adam_last_update[v] = m_adam_step;
        }
        m_case_split_queue.mk_var_eh(v);
        if (m_config.m_dual_mode)
            vmtf_init_var(v);
        m_simplifier.insert_elim_todo(v);
    }

    bool_var solver::mk_var(bool ext, bool dvar) {
        m_model_is_current = false;
        m_stats.m_mk_var++;
        bool_var v = m_justification.size();
        
        if (!m_free_vars.empty()) {
            v = m_free_vars.back();
            m_free_vars.pop_back();
            m_active_vars.push_back(v);
            reset_var(v, ext, dvar);
            SASSERT(v < m_justification.size());
            return v;
        }
        m_active_vars.push_back(v);
        m_watches.push_back(watch_list());
        m_watches.push_back(watch_list());
        m_bin_watches.push_back(watch_list());
        m_bin_watches.push_back(watch_list());
        m_assignment.push_back(l_undef);
        m_assignment.push_back(l_undef);
        m_justification.push_back(justification(UINT_MAX));
        m_trail_pos.push_back(UINT_MAX);
        m_decision.push_back(dvar);
        m_eliminated.push_back(false);
        m_external.push_back(ext);
        m_var_scope.push_back(scope_lvl());
        m_touched.push_back(0);
        m_activity.push_back(0.0);
        m_polarity_belief.push_back(0.0);
        m_mark.push_back(false);
        m_poison.push_back(false);
        m_removable.push_back(false);
        m_lit_mark.push_back(false);
        m_lit_mark.push_back(false);
        m_phase.push_back(false);
        m_best_phase.push_back(false);
        m_prev_phase.push_back(false);
        m_target_phase.push_back(l_undef);
        m_assigned_since_gc.push_back(false);
        m_last_conflict.push_back(0);
        m_last_propagation.push_back(0);
        m_participated.push_back(0);
        m_canceled.push_back(0);
        m_reasoned.push_back(0);
        if (m_config.m_branching_heuristic == BH_ADAM || m_config.m_branching_heuristic == BH_COMBINED) {
            m_adam_m1.push_back(0.0);
            m_adam_m2.push_back(0.0);
            m_adam_last_update.push_back(m_adam_step);
        }
        m_case_split_queue.mk_var_eh(v);
        if (m_config.m_dual_mode)
            vmtf_init_var(v);
        m_simplifier.insert_elim_todo(v);
        SASSERT(!was_eliminated(v));
        return v;
    }

    void solver::set_non_external(bool_var v) {
        m_external[v] = false;
    }

    void solver::set_external(bool_var v) {
        m_external[v] = true;
    }

    void solver::set_eliminated(bool_var v, bool f) { 
        if (m_eliminated[v] == f)
            return;
        if (!f) 
            reset_var(v, m_external[v], m_decision[v]);
        else if (f && m_ext)
            m_ext->set_eliminated(v);
        m_eliminated[v] = f; 
    }


    clause* solver::mk_clause(unsigned num_lits, literal * lits, sat::status st) {
        m_model_is_current = false;
            

        DEBUG_CODE({
                for (unsigned i = 0; i < num_lits; ++i) {
                    CTRACE(sat, was_eliminated(lits[i]), tout << lits[i] << " was eliminated\n";);
                    SASSERT(!was_eliminated(lits[i]));
                }
        });

        if (m_user_scope_literals.empty()) {
            return mk_clause_core(num_lits, lits, st);
        }
        else {
            m_aux_literals.reset();
            m_aux_literals.append(num_lits, lits);
            m_aux_literals.append(m_user_scope_literals);
            return mk_clause_core(m_aux_literals.size(), m_aux_literals.data(), st);
        }
    }

    clause* solver::mk_clause(literal l1, literal l2, sat::status st) {
        literal ls[2] = { l1, l2 };
        return mk_clause(2, ls, st);
    }

    clause* solver::mk_clause(literal l1, literal l2, literal l3, sat::status st) {
        literal ls[3] = { l1, l2, l3 };
        return mk_clause(3, ls, st);
    }

    void solver::del_clause(clause& c) {
        if (!c.is_learned()) 
            m_stats.m_non_learned_generation++;
        
        if (c.frozen()) 
            --m_num_frozen;
        
        if (!c.was_removed() && m_config.m_drat && !m_drat.is_cleaned(c)) 
            m_drat.del(c);
        
        dealloc_clause(&c);        
        if (m_searching) 
            m_stats.m_del_clause++;
    }

    void solver::drat_explain_conflict() {
        if (m_config.m_drat && m_ext) {
            extension::scoped_drating _sd(*m_ext);
            bool unique_max;
            m_conflict_lvl = get_max_lvl(m_not_l, m_conflict, unique_max);        
            resolve_conflict_for_unsat_core();                
        }
    }

    void solver::drat_log_unit(literal lit, justification j) {
        if (!m_ext)
            return;
        extension::scoped_drating _sd(*m_ext.get());
        if (j.get_kind() == justification::EXT_JUSTIFICATION) 
            fill_ext_antecedents(lit, j, false);
        else 
            m_drat.add(lit, m_searching);       
    }

    void solver::drat_log_clause(unsigned num_lits, literal const* lits, sat::status st) {
        m_drat.add(num_lits, lits, st);
    }

    clause * solver::mk_clause_core(unsigned num_lits, literal * lits, sat::status st) {
        bool redundant = st.is_redundant();
        TRACE(sat, tout << "mk_clause: "  << mk_lits_pp(num_lits, lits) << (redundant?" learned":" aux") << "\n";);
        bool logged = false;
        if (!redundant || !st.is_sat()) {
            unsigned old_sz = num_lits;
            bool keep = m_trim || simplify_clause(num_lits, lits);
            TRACE(sat_mk_clause, tout << "mk_clause (after simp), keep: " << keep << "\n" << mk_lits_pp(num_lits, lits) << "\n";);
            if (!keep) {
                return nullptr; // clause is equivalent to true.
            }
            // if an input clause is simplified, then log the simplified version as learned
            if (m_config.m_drat && old_sz > num_lits) {
                drat_log_clause(num_lits, lits, st);
                logged = true;
            }

            ++m_stats.m_non_learned_generation;
            if (!m_searching) 
                m_mc.add_clause(num_lits, lits);            
        }       

        switch (num_lits) {
        case 0:
            set_conflict();
            return nullptr;
        case 1:
            if (!logged && m_config.m_drat)
                drat_log_clause(num_lits, lits, st);
            {
                flet<bool> _disable_drat(m_config.m_drat, false);
                assign(lits[0], justification(0));
            }
            return nullptr;
        case 2:
            mk_bin_clause(lits[0], lits[1], st);
            if (redundant && m_par) 
                m_par->share_clause(*this, lits[0], lits[1]);
            return nullptr;
        default:
            return mk_nary_clause(num_lits, lits, st);
        }
    }

    void solver::mk_bin_clause(literal l1, literal l2, sat::status st) {
        bool redundant = st.is_redundant();
        m_touched[l1.var()] = m_touch_index;
        m_touched[l2.var()] = m_touch_index;

        if (m_config.m_drat)
            m_drat.add(l1, l2, st);
        
        if (redundant && !m_trim && find_binary_watch(get_bin_wlist(~l1), ~l2) && value(l1) == l_undef) {
            assign_unit(l1);
            return;
        }
        if (redundant && !m_trim && find_binary_watch(get_bin_wlist(~l2), ~l1) && value(l2) == l_undef) {
            assign_unit(l2);
            return;
        }
        watched* w0 = redundant ? find_binary_watch(get_bin_wlist(~l1), l2) : nullptr;
        if (w0 && !m_trim) {
            TRACE(sat, tout << "found binary " << l1 << " " << l2 << "\n";);
            if (w0->is_learned() && !redundant) {
                w0->set_learned(false);
                w0 = find_binary_watch(get_bin_wlist(~l2), l1);
                VERIFY(w0);
                w0->set_learned(false);
            }
            if (propagate_bin_clause(l1, l2) && !at_base_lvl() && !redundant)
                push_reinit_stack(l1, l2);
            else if (has_variables_to_reinit(l1, l2))
                push_reinit_stack(l1, l2);
            return;
        }

        if (propagate_bin_clause(l1, l2)) {
            if (!at_base_lvl())
                push_reinit_stack(l1, l2);
            else if (!m_trim)
                return;
        }
        else if (has_variables_to_reinit(l1, l2))
            push_reinit_stack(l1, l2);
        m_stats.m_mk_bin_clause++;
        get_bin_wlist(~l1).push_back(watched(l2, redundant));
        get_bin_wlist(~l2).push_back(watched(l1, redundant));
    }

    bool solver::has_variables_to_reinit(clause const& c) const {
        for (auto lit : c)
            if (m_var_scope[lit.var()] > 0)
                return true;
        return false;
    }

    bool solver::has_variables_to_reinit(literal l1, literal l2) const {
        if (at_base_lvl())
            return false;
        if (m_var_scope[l1.var()] > 0)
            return true;
        if (m_var_scope[l2.var()] > 0)
            return true;
        return false;
    }

    bool solver::propagate_bin_clause(literal l1, literal l2) {
        if (value(l2) == l_false && value(l1) != l_true) {
            m_stats.m_bin_propagate++;
            assign(l1, justification(lvl(l2), l2));            
            return true;
        }
        if (value(l1) == l_false && value(l2) != l_true) {
            m_stats.m_bin_propagate++;
            assign(l2, justification(lvl(l1), l1));
            return true;
        }
        return false;
    }

    void solver::push_reinit_stack(clause & c) {
        SASSERT(!at_base_lvl());
        TRACE(sat_reinit, tout << "adding to reinit stack: " << c << "\n";);
        m_clauses_to_reinit.push_back(clause_wrapper(c));
        c.set_reinit_stack(true);
    }

    void solver::push_reinit_stack(literal l1, literal l2) {
        TRACE(sat_reinit, tout << "adding to reinit stack: " << l1 << " " << l2 << "\n";);
        m_clauses_to_reinit.push_back(clause_wrapper(l1, l2));
    }

    clause * solver::mk_nary_clause(unsigned num_lits, literal * lits, sat::status st) {
        m_stats.m_mk_clause++;
        clause * r = alloc_clause(num_lits, lits, st.is_redundant());
        SASSERT(!st.is_redundant() || r->is_learned());
        if (m_is_probing && st.is_redundant())
            r->set_hyper(true);
        bool reinit = attach_nary_clause(*r, st.is_sat() && st.is_redundant());
 
        if (reinit || has_variables_to_reinit(*r)) 
            push_reinit_stack(*r);
        if (st.is_redundant()) 
            m_learned.push_back(r);
        else 
            m_clauses.push_back(r);
        if (m_config.m_drat) 
            m_drat.add(*r, st);
        for (literal l : *r) 
            m_touched[l.var()] = m_touch_index;
        return r;
    }

    bool solver::attach_nary_clause(clause & c, bool is_asserting) {
        bool reinit = false;
        clause_offset cls_off = cls_allocator().get_offset(&c);
        if (!at_base_lvl()) {
            if (is_asserting) {
                unsigned w2_idx = select_learned_watch_lit(c);
                std::swap(c[1], c[w2_idx]);
            }
            else {
                unsigned w1_idx = select_watch_lit(c, 0);
                std::swap(c[0], c[w1_idx]);
                unsigned w2_idx = select_watch_lit(c, 1);
                std::swap(c[1], c[w2_idx]);
            }

            if (value(c[0]) == l_false) {
                m_stats.m_propagate++; 
                unsigned level = lvl(c[0]);
                for (unsigned i = c.size(); i-- > 2; ) {
                    level = std::max(level, lvl(c[i]));
                }
                assign(c[1], justification(level, cls_off));
                reinit |= !c.is_learned();
            }
            else if (value(c[1]) == l_false) {
                m_stats.m_propagate++;
                unsigned level = lvl(c[1]);
                for (unsigned i = c.size(); i-- > 2; ) {
                    level = std::max(level, lvl(c[i]));
                }
                assign(c[0], justification(level, cls_off));
                reinit |= !c.is_learned();
            }
        }
        unsigned some_idx = c.size() >> 1;
        literal block_lit = c[some_idx];
        VERIFY(!c.frozen());
        DEBUG_CODE(for (auto const& w : m_watches[(~c[0]).index()]) SASSERT(!w.is_clause() || w.get_clause_offset() != cls_off););
        DEBUG_CODE(for (auto const& w : m_watches[(~c[1]).index()]) SASSERT(!w.is_clause() || w.get_clause_offset() != cls_off););
        SASSERT(c[0] != c[1]);
        m_watches[(~c[0]).index()].push_back(watched(block_lit, cls_off));
        m_watches[(~c[1]).index()].push_back(watched(block_lit, cls_off));
        return reinit;
    }

    void solver::attach_clause(clause & c, bool & reinit) {
        SASSERT(c.size() > 2);
        reinit = attach_nary_clause(c, c.is_learned() && !c.on_reinit_stack());
    }

    void solver::set_learned(clause& c, bool redundant) {
        if (c.is_learned() != redundant) 
            c.set_learned(redundant);
    }

    void solver::set_learned1(literal l1, literal l2, bool redundant) {
        for (watched& w : get_bin_wlist(~l1)) {
            if (w.is_binary_clause() && l2 == w.get_literal() && !w.is_learned()) {
                w.set_learned(redundant);
                break;
            }
        }
    }

    void solver::shrink(clause& c, unsigned old_sz, unsigned new_sz) {
        SASSERT(new_sz > 2);
        SASSERT(old_sz >= new_sz);
        if (old_sz != new_sz) {
            c.shrink(new_sz);
            for (literal l : c) {
                m_touched[l.var()] = m_touch_index;
            }
            if (m_config.m_drat) {
                m_drat.add(c, status::redundant());
                c.restore(old_sz);
                m_drat.del(c);
                c.shrink(new_sz);
            }
            // CaDiCaL: clamp glue to size-1 after shrinking.
            // A clause with N literals spans at most N-1 decision levels.
            if (c.is_learned() && c.glue() >= c.size())
                c.set_glue(c.size() - 1);
        }
    }

    bool solver::memory_pressure() {
        return 3*cls_allocator().get_allocation_size()/2 + memory::get_allocation_size() > memory::get_max_memory_size();
    }

    struct solver::cmp_activity {
        solver const& s;
        cmp_activity(solver const& s):s(s) {}
        bool operator()(bool_var v1, bool_var v2) const {
            return s.m_activity[v1] > s.m_activity[v2];
        }
    };

    bool solver::should_defrag() {
        if (m_defrag_threshold > 0) --m_defrag_threshold;
        return m_defrag_threshold == 0 && m_config.m_gc_defrag;
    }

    clause* solver::arena_copy_clause(clause& src) {
        size_t bytes = src.bytes();
        char* dst = m_arena.copy(reinterpret_cast<char const*>(&src), bytes);
        clause* c = reinterpret_cast<clause*>(dst);
        c->m_capacity = src.size();
        return c;
    }

    void solver::defrag_clauses() {
        m_defrag_threshold = 2;
        if (memory_pressure()) return;
        pop(scope_lvl());
        IF_VERBOSE(2, verbose_stream() << "(sat-defrag-arena)\n");

        size_t total_bytes = 0;
        for (clause* c : m_clauses) {
            total_bytes += c->bytes();
            c->unmark_used();
        }
        for (clause* c : m_learned) {
            total_bytes += c->bytes();
            c->unmark_used();
        }
        m_arena.prepare(total_bytes);

        svector<bool_var> vars;
        for (unsigned i = 0; i < num_vars(); ++i) vars.push_back(i);
        std::stable_sort(vars.begin(), vars.end(), cmp_activity(*this));

        ptr_vector<clause> new_clauses, new_learned;
        for (bool_var v : vars) {
            for (unsigned sign = 0; sign < 2; ++sign) {
                literal lit = literal(v, sign != 0);
                watch_list& wlist = m_watches[lit.index()];
                for (watched& w : wlist) {
                    if (!w.is_clause()) continue;
                    clause& c1 = get_clause(w);
                    clause_offset offset;
                    if (c1.was_used()) {
                        offset = c1.get_new_offset();
                    }
                    else {
                        clause* c2 = arena_copy_clause(c1);
                        c1.mark_used();
                        if (c1.is_learned())
                            new_learned.push_back(c2);
                        else
                            new_clauses.push_back(c2);
                        offset = cls_allocator().get_offset(c2);
                        c1.set_new_offset(offset);
                    }
                    w = watched(w.get_blocked_literal(), offset);
                }
            }
        }

        for (clause* c : m_clauses) {
            if (!c->was_used())
                new_clauses.push_back(arena_copy_clause(*c));
        }
        for (clause* c : m_learned) {
            if (!c->was_used())
                new_learned.push_back(arena_copy_clause(*c));
        }

        for (clause* c : m_clauses) {
            if (!m_arena.contains(c))
                cls_allocator().free_clause_memory(c);
        }
        for (clause* c : m_learned) {
            if (!m_arena.contains(c))
                cls_allocator().free_clause_memory(c);
        }

        m_clauses.swap(new_clauses);
        m_learned.swap(new_learned);
        m_arena.swap();
        m_cls_allocator[0].finalize();
        m_cls_allocator[1].finalize();

        reinit_assumptions();
    }


    void solver::set_learned(literal l1, literal l2, bool redundant) {
        set_learned1(l1, l2, redundant);
        set_learned1(l2, l1, redundant);
    }

    /**
       \brief Select a watch literal starting the search at the given position.
       This method is only used for clauses created during the search.

       I use the following rules to select a watch literal.

       1- select a literal l in idx >= starting_at such that value(l) = l_true,
       and for all l' in idx' >= starting_at . value(l') = l_true implies lvl(l) <= lvl(l')

       The purpose of this rule is to make the clause inactive for as long as possible. A clause
       is inactive when it contains a literal assigned to true.

       2- if there isn't a literal assigned to true, then select an unassigned literal l in idx >= starting_at

       3- if there isn't a literal l in idx >= starting_at such that value(l) = l_true or
       value(l) = l_undef (that is, all literals at positions >= starting_at are assigned
       to false), then peek the literal l such that for all l' starting at starting_at
       lvl(l) >= lvl(l')

       Without rule 3, boolean propagation is incomplete, that is, it may miss possible propagations.

       \remark The method select_lemma_watch_lit is used to select the watch literal for regular learned clauses.
    */
    unsigned solver::select_watch_lit(clause const & cls, unsigned starting_at) const {
        SASSERT(cls.size() >= 2);
        unsigned min_true_idx  = UINT_MAX;
        unsigned max_false_idx = UINT_MAX;
        unsigned unknown_idx   = UINT_MAX;
        unsigned n = cls.size();
        for (unsigned i = starting_at; i < n; ++i) {
            literal l   = cls[i];
            switch(value(l)) {
            case l_false:
                if (max_false_idx == UINT_MAX || lvl(l) > lvl(cls[max_false_idx]))
                    max_false_idx = i;
                break;
            case l_undef:
                unknown_idx = i;
                break;
            case l_true:
                if (min_true_idx == UINT_MAX || lvl(l) < lvl(cls[min_true_idx]))
                    min_true_idx = i;
                break;
            }
        }
        if (min_true_idx != UINT_MAX)
            return min_true_idx;
        if (unknown_idx != UINT_MAX)
            return unknown_idx;
        SASSERT(max_false_idx != UINT_MAX);
        return max_false_idx;
    }

    /**
       \brief The learned clauses (lemmas) produced by the SAT solver
       have the property that the first literal will be implied by it
       after backtracking. All other literals are assigned to (or
       implied to be) false when the learned clause is created. The
       first watch literal will always be the first literal.  The
       second watch literal is computed by this method. It should be
       the literal with the highest decision level.

       // TODO: do we really need this? strength the conflict resolution
    */
    unsigned solver::select_learned_watch_lit(clause const & cls) const {
        SASSERT(cls.size() >= 2);
        unsigned max_false_idx = UINT_MAX;
        unsigned num_lits = cls.size();
        for (unsigned i = 1; i < num_lits; ++i) {
            literal l    = cls[i];
            CTRACE(sat, value(l) != l_false, tout << l << ":=" << value(l););
            SASSERT(value(l) == l_false);
            if (max_false_idx == UINT_MAX || lvl(l) > lvl(cls[max_false_idx]))
                max_false_idx = i;
        }
        return max_false_idx;
    }

    template<bool lvl0>
    bool solver::simplify_clause_core(unsigned & num_lits, literal * lits) const {
        std::sort(lits, lits+num_lits);
        literal prev = null_literal;
        unsigned i = 0;
        unsigned j = 0;
        for (; i < num_lits; ++i) {
            literal curr = lits[i];
            lbool val = value(curr);
            if (!lvl0 && lvl(curr) > 0)
                val = l_undef;
            switch (val) {
            case l_false:
                break; // ignore literal
            case l_undef:
                if (curr == ~prev)
                    return false; // clause is equivalent to true
                if (curr != prev) {
                    prev = curr;
                    if (i != j)
                        std::swap(lits[j], lits[i]);
                    j++;
                }
                break;
            case l_true:
                return false; // clause is equivalent to true
            }
        }
        num_lits = j;
        return true;
    }

    bool solver::simplify_clause(unsigned & num_lits, literal * lits) const {
        if (at_base_lvl()) 
            return simplify_clause_core<true>(num_lits, lits);
        else
            return simplify_clause_core<false>(num_lits, lits);
    }

    void solver::detach_bin_clause(literal l1, literal l2, bool redundant) {
        get_bin_wlist(~l1).erase(watched(l2, redundant));
        get_bin_wlist(~l2).erase(watched(l1, redundant));
        if (m_config.m_drat) m_drat.del(l1, l2);
    }

    void solver::detach_clause(clause& c) {
        detach_nary_clause(c);
    }

    void solver::detach_nary_clause(clause & c) {
        clause_offset cls_off = get_offset(c);
        erase_clause_watch(get_wlist(~c[0]), cls_off);
        erase_clause_watch(get_wlist(~c[1]), cls_off);
    }

    // -----------------------
    //
    // Basic
    //
    // -----------------------

    void solver::set_conflict(justification c, literal not_l) {
        if (m_inconsistent)
            return;
        m_inconsistent = true;
        m_conflict = c;
        m_not_l    = not_l;
        TRACE(sat, display(display_justification(tout << "conflict " << not_l << " ", c) << "\n"));
    }

    void solver::assign_core(literal l, justification j) {
        SASSERT(value(l) == l_undef);
        // value(l) == l_undef already implies l is not on the trail; O(1) vs O(n) scan
        SASSERT(value(~l) == l_undef);
        TRACE(sat_assign_core, tout << l << " " << j << "\n";);
        if (j.level() == 0) {
            if (m_config.m_drat)
                drat_log_unit(l, j);
            if (!m_trim)
                j = justification(0); // erase justification for level 0
        }
        else {
            VERIFY(!at_base_lvl());
        }
        m_assignment[l.index()]    = l_true;
        m_assignment[(~l).index()] = l_false;
        bool_var v = l.var();
        m_justification[v]         = j;
        if (!m_is_probing)
            m_phase[v]             = !l.sign();
        m_assigned_since_gc[v]     = true;
        m_trail_pos[v]             = m_trail.size();
        m_trail.push_back(l);

        // CaDiCaL-style assignment-time watch list prefetch.
        // Issuing the prefetch here gives the DRAM controller maximum lead time:
        // all remaining watches of the CURRENT propagation literal must be processed
        // before this newly assigned literal is dequeued, giving many cycles for the
        // prefetch to complete. The propagation-loop prefetch (one step ahead) and
        // this complement each other -- this one targets L2 cache (hint=1) for the
        // longer latency path.
        if (m_config.m_propagate_prefetch) {
            unsigned idx = l.index();
#if defined(__GNUC__) || defined(__clang__)
            __builtin_prefetch(m_bin_watches[idx].data(), 0, 1);
            __builtin_prefetch(m_watches[idx].data(), 0, 1);
#else
    #if !defined(_M_ARM) && !defined(_M_ARM64)
            _mm_prefetch((const char*)(m_bin_watches[idx].data()), _MM_HINT_T1);
            _mm_prefetch((const char*)(m_watches[idx].data()), _MM_HINT_T1);
    #endif
#endif
        }

        switch (m_config.m_branching_heuristic) {
        case BH_VSIDS:
            break;
        case BH_CHB:
            m_last_propagation[v] = m_stats.m_conflict;
            break;
        default:
            break;
        }

        if (m_config.m_anti_exploration) {
            uint64_t age = m_stats.m_conflict - m_canceled[v];
            if (age > 0) {
                double decay = decay_pow095(age);
                set_activity(v, m_activity[v] * decay);
                m_canceled[v] = m_stats.m_conflict;
            }
        }
        
        SASSERT(m_is_probing || !l.sign() || !m_phase[v]);
        SASSERT(m_is_probing || l.sign()  || m_phase[v]);
        SASSERT(!l.sign() || value(v) == l_false);
        SASSERT(l.sign()  || value(v) == l_true);
        SASSERT(value(l) == l_true);
        SASSERT(value(~l) == l_false);
    }

    lbool solver::status(clause const & c) const {
        bool found_undef = false;
        for (literal lit : c) {
            switch (value(lit)) {
            case l_true:
                return l_true;
            case l_undef:
                found_undef = true;
                break;
            default:
                break;
            }
        }
        return found_undef ? l_undef : l_false;
    }

    // -----------------------
    //
    // Propagation
    //
    // -----------------------

    bool solver::propagate_core(bool update) {
        if (m_ext && (!is_probing() || at_base_lvl()))
            m_ext->unit_propagate();
        // CaDiCaL-style deferred statistics: accumulate in stack-local
        // counters during the entire propagation loop and write back
        // once at the end, avoiding cache-line pressure on the Stats struct.
        unsigned local_propagate = 0;
        unsigned local_bin_propagate = 0;
        unsigned prop_counter = 0;
        while (m_qhead < m_trail.size() && !m_inconsistent) {
            do {
                if ((prop_counter++ & 63) == 0)
                    checkpoint();
                m_cleaner.dec();
                literal l = m_trail[m_qhead];
                m_qhead++;
                if (m_config.m_propagate_prefetch && m_qhead < m_trail.size()) {
                    unsigned next_idx = m_trail[m_qhead].index();
#if defined(__GNUC__) || defined(__clang__)
                    __builtin_prefetch((const char*)((m_bin_watches[next_idx].data())));
                    __builtin_prefetch((const char*)((m_watches[next_idx].data())));
#else
    #if !defined(_M_ARM) && !defined(_M_ARM64)
                    _mm_prefetch((const char*)((m_bin_watches[next_idx].data())), _MM_HINT_T1);
                    _mm_prefetch((const char*)((m_watches[next_idx].data())), _MM_HINT_T1);
    #endif
#endif
                }
                if (!propagate_literal(l, update, local_propagate, local_bin_propagate)) {
                    m_stats.m_propagate += local_propagate;
                    m_stats.m_bin_propagate += local_bin_propagate;
                    return false;
                }
            } while (m_qhead < m_trail.size());

            if (m_ext && (!is_probing() || at_base_lvl()))
                m_ext->unit_propagate();
        }
        m_stats.m_propagate += local_propagate;
        m_stats.m_bin_propagate += local_bin_propagate;
        if (m_inconsistent)
            return false;

        SASSERT(m_qhead == m_trail.size());
        SASSERT(!m_inconsistent);
        return true;
    }

    bool solver::propagate(bool update) {
        unsigned qhead = m_qhead;
        bool r = propagate_core(update);
        // CaDiCaL-style tick accounting: each propagated literal is one tick
        // of search work.  CaDiCaL weighs by cache lines touched per watch
        // list; we approximate with a flat per-literal cost which is sufficient
        // to detect expensive propagation phases.
        m_search_ticks += (m_qhead - qhead);
        if (m_config.m_branching_heuristic == BH_CHB) {
            update_chb_activity(r, qhead);
        }
        CASSERT("sat_propagate", check_invariant());
        CASSERT("sat_missed_prop", check_missed_propagation());
        return r;
    }

    void solver::propagate_clause(clause& c, bool update, unsigned assign_level, clause_offset cls_off) {
        SASSERT(value(c[0]) == l_undef);
            c.mark_used();
            assign_core(c[0], justification(assign_level, cls_off));
            // Glue recomputation and tier promotion moved to conflict analysis
            // (CaDiCaL-style: keep the propagation loop tight, update glue only
            // when the clause is used as a reason during resolution).
    }

    void solver::set_watch(clause& c, unsigned idx, clause_offset cls_off) {
        std::swap(c[1], c[idx]);
        DEBUG_CODE(for (auto const& w : m_watches[(~c[1]).index()]) VERIFY(!w.is_clause() || w.get_clause_offset() != cls_off););
        m_watches[(~c[1]).index()].push_back(watched(c[0], cls_off));
    }

    bool solver::propagate_literal(literal l, bool update, unsigned& local_propagate, unsigned& local_bin_propagate) {
        bool keep;
        unsigned curr_level = lvl(l);
        TRACE(sat_propagate, tout << "propagating: " << l << "@" << curr_level << " " << m_justification[l.var()] << "\n"; );

        literal not_l = ~l;
        SASSERT(value(l) == l_true);
        SASSERT(value(not_l) == l_false);

        // Phase 1: propagate binary watches (tight inner loop, no pointer chasing)
        {
            watch_list& bin_wlist = m_bin_watches[l.index()];
            watch_list::iterator it  = bin_wlist.begin();
            watch_list::iterator end = bin_wlist.end();
            m_asymm_branch.dec(bin_wlist.size());
            m_probing.dec(bin_wlist.size());
            for (; it != end; ++it) {
                literal l1 = it->get_literal();
                switch (value(l1)) {
                case l_false:
                    set_conflict(justification(curr_level, not_l), ~l1);
                    return false;
                case l_undef:
                    local_bin_propagate++;
                    assign_core(l1, justification(curr_level, not_l));
                    break;
                default:
                    break;
                }
            }
        }

        // Phase 2: propagate clause and ext_constraint watches
        watch_list& wlist = m_watches[l.index()];
        m_asymm_branch.dec(wlist.size());
        m_probing.dec(wlist.size());
        watch_list::iterator it  = wlist.begin();
        watch_list::iterator it2 = it;
        watch_list::iterator end = wlist.end();
#define CONFLICT_CLEANUP() {                    \
                for (; it != end; ++it, ++it2)  \
                    *it2 = *it;                 \
                if (it2 != it)                  \
                    wlist.set_end(it2);         \
            }
        for (; it != end; ++it) {
            // Prefetch clause data for the next watch entry unconditionally.
            // Prefetch never faults, so if the next entry is not a clause
            // (ext_constraint), we just prefetch irrelevant memory harmlessly.
            if (it + 1 < end) {
                const char* next_cls = reinterpret_cast<const char*>((it + 1)->get_clause_offset());
#if defined(__GNUC__) || defined(__clang__)
                __builtin_prefetch(next_cls, 0, 1);
#elif !defined(_M_ARM) && !defined(_M_ARM64)
                _mm_prefetch(next_cls, _MM_HINT_T1);
#endif
            }
            switch (it->get_kind()) {
            case watched::BINARY:
                // Binary watches should not appear in m_watches; skip gracefully.
                UNREACHABLE();
                *it2 = *it;
                it2++;
                break;
            case watched::CLAUSE: {
                if (value(it->get_blocked_literal()) == l_true) {
                    TRACE(propagate_clause_bug, tout << "blocked literal " << it->get_blocked_literal() << "\n";
                    tout << get_clause(it) << "\n";);
                    *it2 = *it;
                    it2++;
                    break;
                }
                clause_offset cls_off = it->get_clause_offset();
                clause& c = get_clause(cls_off);
                TRACE(propagate_clause_bug, tout << "processing... " << c << "\nwas_removed: " << c.was_removed() << "\n";);
                if (c.was_removed() || c.size() == 1) {
                    *it2 = *it;
                    it2++;
                    break;
                }
                // Stale watch: neither watched literal is the false literal.
                if (c[0] != not_l && c[1] != not_l) {
                    *it2 = *it;
                    it2++;
                    break;
                }
                // Branchless XOR (CaDiCaL-style): compute the other watched
                // literal without a conditional branch or clause body write.
                // a^b^not_l == b when a==not_l, == a when b==not_l.
                literal other_watch = to_literal(c[0].to_uint() ^ c[1].to_uint() ^ not_l.to_uint());
                if (value(other_watch) == l_true) {
                    // Fast path: no clause body write -- avoids dirtying cache line.
                    it2->set_clause(other_watch, cls_off);
                    it2++;
                    break;
                }

                // Slow path: must scan for a replacement.  Materialize the
                // normalized watch positions now since set_watch and
                // propagate_clause read c[0] and c[1].
                c[0] = other_watch;
                c[1] = not_l;

                unsigned sz = c.size();

                if (value(other_watch) == l_undef) {
                    // Saved-position scan (Gent 2013 / CaDiCaL):
                    // Start scanning from the saved position instead of 2.
                    // This turns repeated scans of the same clause from O(n) to amortized O(1).
                    unsigned pos = c.pos();
                    if (pos >= sz) pos = 2; // guard against stale pos after shrink
                    // Scan from pos to end
                    for (unsigned i = pos; i < sz; ++i) {
                        literal lit = c[i];
                        lbool val = value(lit);
                        if (val == l_true) {
                            c.set_pos(i + 1);
                            it2->set_clause(lit, cls_off);
                            it2++;
                            goto end_clause_case;
                        }
                        if (val == l_undef) {
                            c.set_pos(i + 1);
                            set_watch(c, i, cls_off);
                            goto end_clause_case;
                        }
                    }
                    // Wrap around: scan from 2 to pos
                    for (unsigned i = 2; i < pos; ++i) {
                        literal lit = c[i];
                        lbool val = value(lit);
                        if (val == l_true) {
                            c.set_pos(i + 1);
                            it2->set_clause(lit, cls_off);
                            it2++;
                            goto end_clause_case;
                        }
                        if (val == l_undef) {
                            c.set_pos(i + 1);
                            set_watch(c, i, cls_off);
                            goto end_clause_case;
                        }
                    }
                    // No replacement found -- propagate c[0].
                    // CaDiCaL optimization: only scan for the true assignment level
                    // when chronological backtracking is enabled. Without chrono,
                    // scope_lvl() is always correct since NCB backtracks exactly.
                    unsigned assign_level;
                    if (m_config.m_chrono_level_lim < UINT_MAX) {
                        assign_level = curr_level;
                        unsigned max_index = 1;
                        for (unsigned i = 2; i < sz; ++i) {
                            unsigned level = lvl(c[i]);
                            if (level > assign_level) {
                                assign_level = level;
                                max_index = i;
                            }
                        }
                        if (max_index != 1) {
                            IF_VERBOSE(20, verbose_stream() << "swap watch for: " << c[1] << " " << c[max_index] << "\n");
                            set_watch(c, max_index, cls_off);
                        }
                        else {
                            *it2 = *it;
                            it2++;
                        }
                    }
                    else {
                        assign_level = scope_lvl();
                        *it2 = *it;
                        it2++;
                    }
                    local_propagate++;
                    propagate_clause(c, update, assign_level, cls_off);
                }
                else {
                    SASSERT(value(c[0]) == l_false);
                    unsigned undef_index = 0;
                    // CaDiCaL optimization: skip per-literal lvl() calls when
                    // chrono is disabled -- scope_lvl() is always correct with NCB.
                    bool track_levels = m_config.m_chrono_level_lim < UINT_MAX;
                    unsigned assign_level = track_levels ? std::max(curr_level, lvl(c[0])) : scope_lvl();
                    unsigned num_undef = 0;

                    // Saved-position scan for the false-c[0] branch too.
                    unsigned pos = c.pos();
                    if (pos >= sz) pos = 2;
                    // Phase 1: scan from pos to end
                    for (unsigned i = pos; i < sz && num_undef <= 1; ++i) {
                        literal lit = c[i];
                        lbool val = value(lit);
                        if (val == l_true) {
                            c.set_pos(i + 1);
                            it2->set_clause(lit, cls_off);
                            it2++;
                            goto end_clause_case;
                        }
                        if (val == l_undef) {
                            undef_index = i;
                            ++num_undef;
                        } else if (track_levels) {
                            unsigned level = lvl(lit);
                            if (level > assign_level) assign_level = level;
                        }
                    }
                    // Phase 2: wrap around from 2 to pos
                    for (unsigned i = 2; i < pos && num_undef <= 1; ++i) {
                        literal lit = c[i];
                        lbool val = value(lit);
                        if (val == l_true) {
                            c.set_pos(i + 1);
                            it2->set_clause(lit, cls_off);
                            it2++;
                            goto end_clause_case;
                        }
                        if (val == l_undef) {
                            undef_index = i;
                            ++num_undef;
                        } else if (track_levels) {
                            unsigned level = lvl(lit);
                            if (level > assign_level) assign_level = level;
                        }
                    }

                    if (undef_index != 0) {
                        set_watch(c, undef_index, cls_off);
                        if (num_undef == 1) {
                            std::swap(c[0], c[1]);
                            local_propagate++;
                            propagate_clause(c, update, assign_level, cls_off);
                        }
                        goto end_clause_case;
                    }

                    c.mark_used();
                    CONFLICT_CLEANUP();
                    set_conflict(justification(assign_level, cls_off));
                    return false;
                }
            end_clause_case:
                break;
            }
            case watched::EXT_CONSTRAINT:
                SASSERT(m_ext);
                keep = m_ext->propagated(l, it->get_ext_constraint_idx());
                if (m_inconsistent) {
                    if (!keep) {
                        ++it;
                    }
                    CONFLICT_CLEANUP();
                    return false;
                }
                if (keep) {
                    *it2 = *it;
                    it2++;
                }
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        if (it2 != it)
            wlist.set_end(it2);
        if (m_ext && m_external[l.var()] && (!is_probing() || at_base_lvl()))
            m_ext->asserted(l);

        return true;
    }


    // -----------------------------------------------------------------------
    // Dual-pointer probing propagation (CaDiCaL-style)
    //
    // During probing, binary clause propagation is much cheaper than long
    // clause propagation (no pointer chasing into clause memory). By draining
    // all binary implications to quiescence before touching any long clause,
    // we often find conflicts without ever paying the cost of long clause
    // watches. This is the key insight from the CaDiCaL/CPAIOR'13 paper on
    // tree-based look-ahead.
    //
    // m_qhead_binary: advances over trail entries for binary-only propagation
    // m_qhead:        advances over trail entries for long clause propagation
    //
    // Invariant: m_qhead <= m_qhead_binary <= m_trail.size()
    // -----------------------------------------------------------------------

    bool solver::propagate_binary_only(unsigned& local_bin_propagate) {
        while (m_qhead_binary < m_trail.size()) {
            literal l = m_trail[m_qhead_binary];
            m_qhead_binary++;
            literal not_l = ~l;
            unsigned curr_level = lvl(l);

            watch_list& bin_wlist = m_bin_watches[l.index()];
            m_probing.dec(bin_wlist.size());
            for (auto const& w : bin_wlist) {
                literal l1 = w.get_literal();
                switch (value(l1)) {
                case l_false:
                    set_conflict(justification(curr_level, not_l), ~l1);
                    return false;
                case l_undef:
                    local_bin_propagate++;
                    assign_core(l1, justification(curr_level, not_l));
                    break;
                default:
                    break;
                }
            }
        }
        return !m_inconsistent;
    }

    bool solver::propagate_long_one(unsigned& local_propagate) {
        SASSERT(m_qhead < m_trail.size());
        bool keep;

        literal l = m_trail[m_qhead];
        m_qhead++;
        literal not_l = ~l;
        unsigned curr_level = lvl(l);

        watch_list& wlist = m_watches[l.index()];
        m_probing.dec(wlist.size());
        watch_list::iterator it  = wlist.begin();
        watch_list::iterator it2 = it;
        watch_list::iterator end = wlist.end();
#define PROBE_CONFLICT_CLEANUP() {              \
            for (; it != end; ++it, ++it2)      \
                *it2 = *it;                     \
            if (it2 != it)                      \
                wlist.set_end(it2);             \
        }
        for (; it != end; ++it) {
            switch (it->get_kind()) {
            case watched::BINARY:
                UNREACHABLE();
                *it2 = *it;
                it2++;
                break;
            case watched::CLAUSE: {
                if (value(it->get_blocked_literal()) == l_true) {
                    *it2 = *it;
                    it2++;
                    break;
                }
                clause_offset cls_off = it->get_clause_offset();
                clause& c = get_clause(cls_off);
                if (c[0] == not_l)
                    std::swap(c[0], c[1]);

                if (c.was_removed() || c.size() == 1 || c[1] != not_l) {
                    *it2 = *it;
                    it2++;
                    break;
                }
                if (value(c[0]) == l_true) {
                    it2->set_clause(c[0], cls_off);
                    it2++;
                    break;
                }
                SASSERT(c[1] == not_l);

                unsigned sz = c.size();

                if (value(c[0]) == l_undef) {
                    for (unsigned i = 2; i < sz; ++i) {
                        literal lit = c[i];
                        switch (value(lit)) {
                        case l_true:
                            it2->set_clause(lit, cls_off);
                            it2++;
                            goto probe_end_clause_case;
                        case l_undef:
                            set_watch(c, i, cls_off);
                            goto probe_end_clause_case;
                        default:
                            break;
                        }
                    }
                    // CaDiCaL optimization: skip level scan when chrono is disabled.
                    unsigned assign_level;
                    if (m_config.m_chrono_level_lim < UINT_MAX) {
                        assign_level = curr_level;
                        unsigned max_index = 1;
                        for (unsigned i = 2; i < sz; ++i) {
                            unsigned level = lvl(c[i]);
                            if (level > assign_level) {
                                assign_level = level;
                                max_index = i;
                            }
                        }
                        if (max_index != 1) {
                            set_watch(c, max_index, cls_off);
                        }
                        else {
                            *it2 = *it;
                            it2++;
                        }
                    }
                    else {
                        assign_level = scope_lvl();
                        *it2 = *it;
                        it2++;
                    }
                    local_propagate++;
                    c.mark_used();
                    assign_core(c[0], justification(assign_level, cls_off));
                }
                else {
                    SASSERT(value(c[0]) == l_false);
                    unsigned undef_index = 0;
                    // CaDiCaL optimization: skip per-literal lvl() calls when
                    // chrono is disabled -- scope_lvl() is always correct with NCB.
                    bool track_levels = m_config.m_chrono_level_lim < UINT_MAX;
                    unsigned assign_level = track_levels ? std::max(curr_level, lvl(c[0])) : scope_lvl();
                    unsigned num_undef = 0;

                    for (unsigned i = 2; i < sz && num_undef <= 1; ++i) {
                        literal lit = c[i];
                        switch (value(lit)) {
                        case l_true:
                            it2->set_clause(lit, cls_off);
                            it2++;
                            goto probe_end_clause_case;
                        case l_undef:
                            undef_index = i;
                            ++num_undef;
                            break;
                        case l_false:
                            if (track_levels) {
                                unsigned level = lvl(lit);
                                if (level > assign_level) {
                                    assign_level = level;
                                }
                            }
                            break;
                        }
                    }

                    if (undef_index != 0) {
                        set_watch(c, undef_index, cls_off);
                        if (num_undef == 1) {
                            std::swap(c[0], c[1]);
                            local_propagate++;
                            c.mark_used();
                            assign_core(c[0], justification(assign_level, cls_off));
                        }
                        goto probe_end_clause_case;
                    }

                    c.mark_used();
                    PROBE_CONFLICT_CLEANUP();
                    set_conflict(justification(assign_level, cls_off));
                    return false;
                }
            probe_end_clause_case:
                break;
            }
            case watched::EXT_CONSTRAINT:
                SASSERT(m_ext);
                keep = m_ext->propagated(l, it->get_ext_constraint_idx());
                if (m_inconsistent) {
                    if (!keep) {
                        ++it;
                    }
                    PROBE_CONFLICT_CLEANUP();
                    return false;
                }
                if (keep) {
                    *it2 = *it;
                    it2++;
                }
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        if (it2 != it)
            wlist.set_end(it2);
#undef PROBE_CONFLICT_CLEANUP
        return true;
    }

    bool solver::propagate_probing() {
        m_qhead_binary = m_qhead;
        unsigned local_propagate = 0;
        unsigned local_bin_propagate = 0;
        while (true) {
            if (m_qhead_binary < m_trail.size()) {
                if (!propagate_binary_only(local_bin_propagate)) {
                    m_stats.m_propagate += local_propagate;
                    m_stats.m_bin_propagate += local_bin_propagate;
                    return false;
                }
            }
            else if (m_qhead < m_trail.size()) {
                if (!propagate_long_one(local_propagate)) {
                    m_stats.m_propagate += local_propagate;
                    m_stats.m_bin_propagate += local_bin_propagate;
                    return false;
                }
            }
            else {
                break;
            }
        }
        m_stats.m_propagate += local_propagate;
        m_stats.m_bin_propagate += local_bin_propagate;
        return !m_inconsistent;
    }

    void solver::display_lookahead_scores(std::ostream& out) {
        lookahead lh(*this);
        lh.display_lookahead_scores(out);
    }

    lbool solver::cube(bool_var_vector& vars, literal_vector& lits, unsigned backtrack_level) {
        bool is_first = !m_cuber;
        if (is_first) {
            m_cuber = alloc(lookahead, *this);
        }
        lbool result = m_cuber->cube(vars, lits, backtrack_level);
        m_cuber->update_cube_statistics(m_aux_stats);
        switch (result) {
        case l_false:
            dealloc(m_cuber);
            m_cuber = nullptr;
            if (is_first) {
                pop_to_base_level();
                set_conflict();
            }
            break;
        case l_true: {
            lits.reset();
            pop_to_base_level();
            model const& mdl = m_cuber->get_model();
            for (bool_var v = 0; v < mdl.size(); ++v) {
                if (value(v) != l_undef) {
                    continue;
                }
                literal l(v, false);
                if (mdl[v] != l_true) l.neg();
                if (inconsistent())
                    return l_undef;
                push();
                assign_core(l, justification(scope_lvl()));
                propagate(false);
            }
            mk_model();
            break;
        }
        default:
            break;
        }
        return result;
    }


    // -----------------------
    //
    // Search
    //
    // -----------------------
    lbool solver::check(unsigned num_lits, literal const* lits) {
        init_reason_unknown();
        // ILB (CaDiCaL-style): reuse trail when assumptions are identical.
        bool ilb_reused = try_ilb_reuse(num_lits, lits);
        if (!ilb_reused)
            pop_to_base_level();
        m_stats.m_units = init_trail_size();
        IF_VERBOSE(2, verbose_stream() << "(sat.solver)\n";);

        if (m_config.m_ddfw_search) {
            if (!at_base_lvl()) pop_to_base_level();
            m_cleaner(true);
            return do_ddfw_search(num_lits, lits);
        }
        if (m_config.m_prob_search) {
            if (!at_base_lvl()) pop_to_base_level();
            m_cleaner(true);
            return do_prob_search(num_lits, lits);
        }
        if (m_config.m_local_search) {
            if (!at_base_lvl()) pop_to_base_level();
            m_cleaner(true);
            return do_local_search(num_lits, lits);
        }
        if ((m_config.m_num_threads > 1 || m_config.m_ddfw_threads > 0) && !m_par && !m_ext) {
            if (!at_base_lvl()) pop_to_base_level();
            SASSERT(scope_lvl() == 0);
            return check_par(num_lits, lits);
        }
        if (m_config.m_local_search_threads > 0 && !m_par && (!m_ext || m_ext->is_pb())) {
            if (!at_base_lvl()) pop_to_base_level();
            SASSERT(scope_lvl() == 0);
            return check_par(num_lits, lits);
        }
        flet<bool> _searching(m_searching, true);
        m_clone = nullptr;
        if (m_mc.empty() && gparams::get_ref().get_bool("model_validate", false)) {

            m_clone = alloc(solver, m_no_drat_params, m_rlimit);
            m_clone->copy(*this);
            m_clone->set_extension(nullptr);
        }
        try {
            init_search();
            lbool result = l_undef;
            if (check_inconsistent()) { result = l_false; goto alog_solve; }
            propagate(false);
            if (check_inconsistent()) { result = l_false; goto alog_solve; }
            if (!ilb_reused) {
                init_assumptions(num_lits, lits);
                propagate(false);
                if (check_inconsistent()) { result = l_false; goto alog_solve; }
            } else {
                // ILB: assumptions already assigned; restore search_lvl.
                m_search_lvl = scope_lvl();
            }
            if (m_config.m_force_cleanup) do_cleanup(true);
            TRACE(sat, display(tout););
            TRACE(before_search, display(tout););

            if (m_config.m_gc_burst) {
                // force gc
                m_conflicts_since_gc = m_gc_threshold + 1;
                do_gc();
            }

            if (m_config.m_enable_pre_simplify) {
                do_simplify();
                if (check_inconsistent()) { result = l_false; goto alog_solve; }
            }

            if (m_config.m_max_conflicts == 0) {
                IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-conflicts = 0\")\n";);
                TRACE(sat, display(tout); m_mc.display(tout););
                result = l_undef;
                goto alog_solve;
            }

            // CaDiCaL-style lucky phase detection
            {
                lbool lucky = try_lucky_phases();
                if (lucky != l_undef) {
                    result = lucky;
                    goto alog_solve;
                }
            }

            if (m_config.m_phase == PS_LOCAL_SEARCH && m_ext) {
                bounded_local_search();
            }

            log_stats();
            if (m_config.m_max_conflicts > 0 && m_config.m_burst_search > 0) {
                m_restart_threshold = m_config.m_burst_search;
                result = bounded_search();
                log_stats();
                if (result != l_undef)
                    goto alog_solve;

                pop_reinit(scope_lvl());
                m_conflicts_since_restart = 0;
                m_ticks_at_last_restart = m_search_ticks;
                m_restart_threshold = m_config.m_restart_initial;
            }

            result = search();
            log_stats();

        alog_solve:
            ALOG(m_adaptive_log, "SOLVE")
                .s("result", result == l_false ? "unsat" : result == l_true ? "sat" : "unknown")
                .u("conflicts", m_conflicts_since_init)
                .u("restarts", m_restarts)
                .u("decisions", m_stats.m_decision)
                .u("props", m_stats.m_propagate)
                .u("learned", m_learned.size());
            return result;
        }
        catch (const abort_solver &) {
            IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort giveup\")\n";);
            return l_undef;
        }
    }

    bool solver::should_cancel() {
        if (limit_reached() || memory_exceeded() || m_solver_canceled) {
            return true;
        }
        if (m_config.m_restart_max <= m_restarts) {
            m_reason_unknown = "sat.max.restarts";
            IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-restarts\")\n";);
            return true;
        }
        if (m_config.m_inprocess_max <= m_simplifications) {
            m_reason_unknown = "sat.max.inprocess";
            IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-inprocess\")\n";);
            return true;
        }
        if (reached_max_conflicts()) {
            return true;
        }
        return false;
    }

    enum par_exception_kind {
        DEFAULT_EX,
        ERROR_EX
    };

    struct solver::scoped_ls {
        solver& s;
        scoped_ls(solver& s): s(s) {}
        ~scoped_ls() { 
            dealloc(s.m_local_search); 
            s.m_local_search = nullptr; 
        }
    };

    void solver::bounded_local_search() {
        // CaDiCaL-style warmup: propagate all variables using current phases
        // to give local search a propagation-consistent starting assignment.
        warmup_phases();

        if (m_ext) {
            IF_VERBOSE(0, verbose_stream() << "WARNING: local search with theories is in testing mode\n");
            do_restart(true);
            lbool r = m_ext->local_search(m_best_phase);
            verbose_stream() << r << "\n";
            if (r == l_true) {
                m_conflicts_since_restart = 0;
                m_ticks_at_last_restart = m_search_ticks;
                m_conflicts_since_gc = 0;
                m_next_simplify = std::max(m_next_simplify, m_conflicts_since_init + 1);
            }
            return;
        }
        literal_vector _lits;
        scoped_limits scoped_rl(rlimit());
        m_local_search = alloc(ddfw_wrapper);
        scoped_ls _ls(*this);
        SASSERT(m_local_search);
        m_local_search->add(*this);
        m_local_search->updt_params(m_params);
        m_local_search->set_seed(m_rand());
        scoped_rl.push_child(&(m_local_search->rlimit()));

        m_local_search_lim.inc(num_clauses());
        m_local_search->rlimit().push(m_local_search_lim.limit);

        m_local_search->reinit(*this, m_best_phase);
        lbool r = m_local_search->check(_lits.size(), _lits.data(), nullptr);
        auto const& mdl = m_local_search->get_model();
        if (mdl.size() == m_best_phase.size()) {
            for (unsigned i = 0; i < m_best_phase.size(); ++i)
                m_best_phase[i] = l_true == mdl[i];

            if (r == l_true) {
                m_conflicts_since_restart = 0;
                m_ticks_at_last_restart = m_search_ticks;
                m_conflicts_since_gc = 0;
                m_next_simplify = std::max(m_next_simplify, m_conflicts_since_init + 1);
            }
            do_restart(true);
#if 0
            // move higher priority variables to front
            // eg., move the first 10% variables to front
            svector<std::pair<double, bool_var>> priorities(mdl.size());
            for (unsigned i = 0; i < mdl.size(); ++i) 
                priorities[i] = { m_local_search->get_priority(i), i };
            std::sort(priorities.begin(), priorities.end(), [](auto& x, auto& y) { return x.first > y.first; });
            for (unsigned i = priorities.size() / 10; i-- > 0; ) {
                auto [priority, var] = priorities[i];
                move_to_front(var);
            }
#endif


            if (l_true == r) {
                for (clause const* cp : m_clauses) {
                    bool is_true = any_of(*cp, [&](auto lit) { return lit.sign() != m_best_phase[lit.var()]; });
                    if (!is_true) {
                        verbose_stream() << "clause is false " << *cp << "\n";
                    }
                }
            }
        }
    }

    // run_probsat() is defined later in the rephase section (CaDiCaL-style walker).

    lbool solver::invoke_local_search(unsigned num_lits, literal const* lits) {
        literal_vector _lits(num_lits, lits);
        for (literal lit : m_user_scope_literals) 
            _lits.push_back(~lit);
        scoped_ls _ls(*this);
        if (inconsistent()) 
            return l_false;
        scoped_limits scoped_rl(rlimit());
        SASSERT(m_local_search);
        m_local_search->add(*this);
        m_local_search->updt_params(m_params);
        scoped_rl.push_child(&(m_local_search->rlimit()));
        lbool r = m_local_search->check(_lits.size(), _lits.data(), nullptr);
        if (r == l_true) {
            m_model = m_local_search->get_model();
            m_model_is_current = true;
        }
        return r;
    }

    lbool solver::do_local_search(unsigned num_lits, literal const* lits) {
        SASSERT(!m_local_search);
        m_local_search = alloc(local_search);
        return invoke_local_search(num_lits, lits);
    }

    lbool solver::do_ddfw_search(unsigned num_lits, literal const* lits) {
        if (m_ext) return l_undef;
        SASSERT(!m_local_search);
        m_local_search = alloc(ddfw_wrapper);
        return invoke_local_search(num_lits, lits);
    }

    lbool solver::do_prob_search(unsigned num_lits, literal const* lits) {
        if (m_ext) return l_undef;
        if (num_lits > 0 || !m_user_scope_literals.empty()) return l_undef;
        SASSERT(!m_local_search);
        m_local_search = alloc(prob);
        return invoke_local_search(num_lits, lits);
    }

#ifdef SINGLE_THREAD
    lbool solver::check_par(unsigned num_lits, literal const* lits) {
        return l_undef;
    }
#else
    lbool solver::check_par(unsigned num_lits, literal const* lits) {
        if (!rlimit().inc()) {
            return l_undef;
        }
        if (m_ext && !m_ext->is_pb())
            return l_undef;


        int num_extra_solvers = m_config.m_num_threads - 1;
        int num_local_search  = static_cast<int>(m_config.m_local_search_threads);
        int num_ddfw      = m_ext ? 0 : static_cast<int>(m_config.m_ddfw_threads);
        int num_threads = num_extra_solvers + 1 + num_local_search + num_ddfw;        
        vector<reslimit> lims(num_ddfw);
        scoped_ptr_vector<i_local_search> ls;
        scoped_ptr_vector<solver> uw;
        for (int i = 0; i < num_local_search; ++i) {
            local_search* l = alloc(local_search);
            l->updt_params(m_params);
            l->add(*this);
            l->set_seed(m_config.m_random_seed + i);
            ls.push_back(l);
        }

           
        // set up ddfw search
        for (int i = 0; i < num_ddfw; ++i) {
            ddfw_wrapper* d = alloc(ddfw_wrapper);
            d->updt_params(m_params);
            d->set_seed(m_config.m_random_seed + i);
            d->add(*this);
            ls.push_back(d);
        }
        int local_search_offset = num_extra_solvers;
        int main_solver_offset = num_extra_solvers + num_local_search + num_ddfw;

#define IS_AUX_SOLVER(i)   (0 <= i && i < num_extra_solvers)
#define IS_LOCAL_SEARCH(i) (local_search_offset <= i && i < main_solver_offset)
#define IS_MAIN_SOLVER(i)  (i == main_solver_offset)

        sat::parallel par(*this);
        par.reserve(num_threads, 1 << 12);
        par.init_solvers(*this, num_extra_solvers);
        for (unsigned i = 0; i < ls.size(); ++i) {
            par.push_child(ls[i]->rlimit());
        }
        for (reslimit& rl : lims) {
            par.push_child(rl);
        }
        for (unsigned i = 0; i < uw.size(); ++i) {
            uw[i]->set_par(&par, 0);
        }
        int finished_id = -1;
        std::string        ex_msg;
        par_exception_kind ex_kind = DEFAULT_EX;
        unsigned error_code = 0;
        lbool result = l_undef;
        bool canceled = false;
        std::mutex mux;

        auto worker_thread = [&](int i) {
            try {
                lbool r = l_undef;
                if (IS_AUX_SOLVER(i)) {
                    r = par.get_solver(i).check(num_lits, lits);
                }
                else if (IS_LOCAL_SEARCH(i)) {
                    r = ls[i-local_search_offset]->check(num_lits, lits, &par);
                }
                else {
                    r = check(num_lits, lits);
                }
                bool first = false;
                {
                    std::lock_guard<std::mutex> lock(mux);
                    if (finished_id == -1) {
                        finished_id = i;
                        first = true;
                        result = r;
                    }
                }
                if (first) {
                    for (unsigned j = 0; j < ls.size(); ++j) {
                        ls[j]->rlimit().cancel();
                    }
                    for (auto& rl : lims) {
                        rl.cancel();
                    }
                    for (int j = 0; j < num_extra_solvers; ++j) {
                        if (i != j) {
                            par.cancel_solver(j);
                        }
                    }
                    if (!IS_MAIN_SOLVER(i)) {
                        canceled = !rlimit().inc();
                        if (!canceled) {
                            rlimit().cancel();
                        }
                    }
                }
            }
            catch (z3_error & err) {
                error_code = err.error_code();
                ex_kind = ERROR_EX;                
            }
            catch (z3_exception & ex) {
                ex_msg = ex.what();
                ex_kind = DEFAULT_EX;    
            }
        };

        if (!rlimit().inc()) {
            set_par(nullptr, 0);
            return l_undef;
        }

        vector<std::thread> threads(num_threads);
        for (int i = 0; i < num_threads; ++i) {
            threads[i] = std::thread([&, i]() { worker_thread(i); });
        }
        for (auto & th : threads) {
            th.join();
        }
        
        if (IS_AUX_SOLVER(finished_id)) {
            m_stats = par.get_solver(finished_id).m_stats;
        }
        if (result == l_true && IS_AUX_SOLVER(finished_id)) {
            set_model(par.get_solver(finished_id).get_model(), true);
        }
        else if (result == l_false && IS_AUX_SOLVER(finished_id)) {
            m_core.reset();
            m_core.append(par.get_solver(finished_id).get_core());
        }
        if (result == l_true && IS_LOCAL_SEARCH(finished_id)) {
            set_model(ls[finished_id - local_search_offset]->get_model(), true);
        }
        if (!canceled) {
            rlimit().reset_cancel();
        }
        par.reset();
        set_par(nullptr, 0);
        ls.reset();
        uw.reset();
        if (finished_id == -1) {
            switch (ex_kind) {
            case ERROR_EX: throw z3_error(error_code);
            default: throw default_exception(std::move(ex_msg));
            }
        }
        return result;

    }
#endif

    /*
      \brief import lemmas/units from parallel sat solvers.
     */
    void solver::exchange_par() {
        if (m_par && at_base_lvl() && m_config.m_num_threads > 1) m_par->get_clauses(*this);
        if (m_par && at_base_lvl() && m_config.m_num_threads > 1) {
            // SASSERT(scope_lvl() == search_lvl());
            // TBD: import also dependencies of assumptions.
            unsigned sz = init_trail_size();
            unsigned num_in = 0, num_out = 0;
            literal_vector in, out;
            for (unsigned i = m_par_limit_out; i < sz; ++i) {
                literal lit = m_trail[i];
                if (lit.var() < m_par_num_vars) {
                    ++num_out;
                    out.push_back(lit);
                }
            }
            m_par_limit_out = sz;
            m_par->exchange(*this, out, m_par_limit_in, in);
            for (unsigned i = 0; !inconsistent() && i < in.size(); ++i) {
                literal lit = in[i];
                SASSERT(lit.var() < m_par_num_vars);
                if (lvl(lit.var()) != 0 || value(lit) != l_true) {
                    ++num_in;
                    assign_unit(lit);
                }
            }
            if (num_in > 0 || num_out > 0) {
                IF_VERBOSE(2, verbose_stream() << "(sat-sync out: " << num_out << " in: " << num_in << ")\n";);
            }
        }
    }

    void solver::set_par(parallel* p, unsigned id) {
        m_par = p;
        m_par_num_vars = num_vars();
        m_par_limit_in = 0;
        m_par_limit_out = 0;
        m_par_id = id; 
        m_par_syncing_clauses = false;
    }

    bool_var solver::next_var() {
        bool_var next;

        // CaDiCaL-style random decision bursts (decide.cpp:40-117):
        // Instead of i.i.d. random decisions with fixed probability,
        // inject concentrated bursts at scheduled intervals.
        // Burst length grows as base * log(count + 10).
        // Interval grows as phases * log(phases) * interval_factor.
        if (m_randec_burst_remaining > 0 && num_vars() > 0) {
            // We're inside a burst — pick a random unassigned variable.
            for (unsigned attempts = 0; attempts < 100; ++attempts) {
                next = m_rand() % num_vars();
                if (value(next) == l_undef && !was_eliminated(next))
                    return next;
            }
            // Couldn't find one quickly; fall through to normal heuristic.
        }
        else if (!m_randec_burst_remaining && m_config.m_randec &&
                 m_stats.m_conflict >= m_randec_next_conflict &&
                 scope_lvl() <= m_search_lvl + 1) {
            // Time to start a new burst (only when near base level).
            ++m_randec_phases;
            m_randec_burst_remaining = static_cast<unsigned>(
                m_config.m_randec_length * std::log(m_randec_phases + 10));
            // Schedule next burst.
            double delta = m_randec_phases * std::log(static_cast<double>(m_randec_phases) + 1);
            m_randec_next_conflict = m_stats.m_conflict +
                static_cast<uint64_t>(delta * m_config.m_randec_interval);
            IF_VERBOSE(3, verbose_stream() << "(sat-randec burst phase=" << m_randec_phases
                       << " len=" << m_randec_burst_remaining
                       << " next=" << m_randec_next_conflict << ")\n";);
            // Pick first random decision of this burst.
            if (num_vars() > 0) {
                for (unsigned attempts = 0; attempts < 100; ++attempts) {
                    next = m_rand() % num_vars();
                    if (value(next) == l_undef && !was_eliminated(next))
                        return next;
                }
            }
        }
        else if (m_rand() < static_cast<int>(m_config.m_random_freq * random_gen::max_value())) {
            // Fallback: i.i.d. random decisions at low probability.
            if (num_vars() == 0)
                return null_bool_var;
            next = m_rand() % num_vars();
            if (value(next) == l_undef && !was_eliminated(next))
                return next;
        }

        // In focused mode, use the VMTF queue instead of the VSIDS heap.
        if (m_config.m_dual_mode && !m_stable_mode) {
            next = vmtf_next_decision();
            if (next != null_bool_var)
                return next;
            // Fall through to VSIDS if VMTF queue is exhausted (shouldn't happen).
        }

        while (!m_case_split_queue.empty()) {
            if (m_config.m_anti_exploration) {
                next = m_case_split_queue.min_var();
                auto age = m_stats.m_conflict - m_canceled[next];
                while (age > 0) {
                    set_activity(next, m_activity[next] * decay_pow095(age));
                    m_canceled[next] = m_stats.m_conflict;
                    next = m_case_split_queue.min_var();
                    age = m_stats.m_conflict - m_canceled[next];
                }
            }
            next = m_case_split_queue.next_var();
            if (value(next) == l_undef && !was_eliminated(next))
                return next;
        }

        return null_bool_var;
    }
    
    bool solver::guess(bool_var next) {
        lbool lphase = m_ext ? m_ext->get_phase(next) : l_undef;

        if (lphase != l_undef)
            return lphase == l_true;

        // Belief-derived phase: use polarity gradient signal from conflicts.
        // Positive belief → variable should be TRUE, negative → FALSE.
        // When belief is near zero (no signal), fall back to saved phase.
        if (m_config.m_phase_strategy == PHS_BELIEF) {
            double belief = m_polarity_belief[next];
            if (belief > 0.0)
                return true;
            if (belief < 0.0)
                return false;
            // belief == 0.0 (no signal yet): use saved phase as fallback
            return m_phase[next];
        }

        // CaDiCaL-style three-phase decision cascade (decide.cpp:138-154):
        //   Stable mode:  target -> best -> saved
        //   Focused mode: initial phase (negative polarity)
        // Target phase records the deepest conflict-free trail prefix and
        // provides guided restart: the solver rebuilds the same prefix and
        // extends it further each time.
        //
        // Critical: focused mode must NOT use saved phase -- using saved
        // phase defeats the exploration purpose of VMTF.  CaDiCaL uses the
        // initial phase (negative) so VMTF variable ordering is the sole
        // exploratory signal.
        lbool tp = m_target_phase.get(next, l_undef);
        bool stable = m_config.m_dual_mode ? m_stable_mode : (m_search_state == s_sat);
        bool focused = m_config.m_dual_mode && !m_stable_mode;

        switch (m_config.m_phase) {
        case PS_ALWAYS_TRUE:
            return true;
        case PS_ALWAYS_FALSE:
            return false;
        case PS_BASIC_CACHING:
            if (focused)
                return false;  // initial phase (negative polarity)
            if (stable && tp != l_undef)
                return tp == l_true;
            return m_phase[next];
        case PS_FROZEN:
            return m_best_phase[next];
        case PS_SAT_CACHING:
        case PS_LOCAL_SEARCH:
            if (focused)
                return false;  // initial phase (negative polarity)
            // CaDiCaL cascade: stable prefers target, then best.
            if (stable) {
                if (tp != l_undef)
                    return tp == l_true;
                return m_best_phase[next];
            }
            return m_phase[next];
        case PS_RANDOM:
            return (m_rand() % 2) == 0;
        default:
            UNREACHABLE();
            return false;
        }
    }

    bool solver::decide() {
        bool_var next;
        lbool phase = l_undef;
        bool is_pos;
        bool used_queue = false;
        if (!m_ext || !m_ext->get_case_split(next, phase)) {
            used_queue = true;
            next = next_var();
            if (next == null_bool_var)
                return false;
        }
        else {
            SASSERT(value(next) == l_undef);
        }
        push();
        m_stats.m_decision++;
        
        CTRACE(sat, m_best_phase[next] != guess(next), tout << "phase " << phase << " " << m_best_phase[next] << " " << guess(next) << "\n");

        if (phase == l_undef)
            phase = guess(next) ? l_true: l_false;
        
        literal next_lit(next, false);
        SASSERT(value(next_lit) == l_undef);
        
        if (m_ext && m_ext->decide(next, phase)) {

            if (used_queue)
                m_case_split_queue.unassign_var_eh(next);
            next_lit = literal(next, false);
            SASSERT(value(next_lit) == l_undef);
        }
                
        if (phase == l_undef)
            is_pos = guess(next);
        else
            is_pos = phase == l_true;

        if (!is_pos)
            next_lit.neg();

        TRACE(sat_decide, tout << scope_lvl() << ": next-case-split: " << next_lit << "\n";);
        // Phase timing: decide
        m_landscape.dynamics_phase_begin();
        assign_scoped(next_lit);
        m_landscape.on_decision(next_lit.var(), is_pos, scope_lvl(), m_trail.size());
        // Dynamics: propagation chain length + reversal detection
        m_landscape.dynamics_on_decision(m_trail.size());
        // A3: Phase flip detection — compare chosen polarity with phase cache.
        m_landscape.dynamics_on_phase_flip(is_pos != m_phase[next]);
        {
            // Reversal: check if polarity flipped vs last decision on this var
            bool_var bv = next_lit.var();
            auto& lp = m_landscape.last_decided_polarity();
            if (bv >= lp.size())
                lp.resize(bv + 1, 0);
            uint8_t prev = lp[bv];
            uint8_t cur = next_lit.sign() ? 1 : 2; // 1=negative(false), 2=positive(true)
            if (prev != 0 && prev != cur)
                m_landscape.dynamics_on_reversal();
            lp[bv] = cur;
            m_landscape.dynamics().reversal_window++;
        }
        m_landscape.dynamics_phase_end_decide();
        return true;
    }

    lbool solver::bounded_search() {
        flet<bool> _disable_simplify(m_simplify_enabled, false);
        flet<bool> _restart_enabled(m_restart_enabled, false);
        return search();
    }

    lbool solver::basic_search() {
        lbool is_sat = l_undef;
        while (is_sat == l_undef && !should_cancel()) {
            if (inconsistent()) {
                // Phase timing: conflict analysis
                m_landscape.dynamics_phase_begin();
                is_sat = resolve_conflict_core();
                m_landscape.dynamics_phase_end_conflict();
            }
            else if (should_propagate()) {
                // Phase timing: BCP
                m_landscape.dynamics_phase_begin();
                unsigned trail_before = m_trail.size();
                propagate(true);
                m_landscape.dynamics_phase_end_bcp();
                // Count BCP propagations for theory_prop_density denominator
                unsigned bcp_props = m_trail.size() - trail_before;
                m_landscape.dynamics().props_this_round += bcp_props;
            }
            else if (do_cleanup(false)) continue;
            else if (should_gc()) do_gc();
            else if (should_rephase()) do_rephase();
            else if (should_restart()) { if (!m_restart_enabled) return l_undef; do_restart(!m_config.m_restart_fast); }
            else if (should_simplify()) do_simplify();
            else if (!decide()) {
                // Phase timing: decide (final_check path = no decision was made)
                m_landscape.dynamics_phase_begin();
                is_sat = final_check();
                m_landscape.dynamics_phase_end_decide();
            }
        }
        return is_sat;
    }

    lbool solver::search() {
        if (!m_ext || !m_ext->tracking_assumptions())
            return basic_search();
        while (true) {
            pop_to_base_level();
            reinit_assumptions();
            lbool r = basic_search();
            if (r != l_false)
                return r;
            ensure_core_computed();
            if (!m_ext->should_research(m_core))
                return r;
        }
    }

    bool solver::should_propagate() const {        
        return !inconsistent() && (m_qhead < m_trail.size() || (m_ext && m_ext->can_propagate()));
    }

    lbool solver::final_check() {
        if (m_ext) {
            switch (m_ext->check()) {
            case check_result::CR_DONE:
                mk_model();
                return l_true;
            case check_result::CR_CONTINUE:
                break;
            case check_result::CR_GIVEUP:
                m_reason_unknown = m_ext->reason_unknown();                
                throw abort_solver();
            }
            return l_undef;
        }
        else {
            mk_model();
            return l_true;
        }
    }


    bool solver::check_inconsistent() {
        if (inconsistent()) {
            if (tracking_assumptions() && at_search_lvl())
                resolve_conflict();
            else if (m_config.m_drat && at_base_lvl())
                resolve_conflict();
            return true;
        }
        else {
            return false;
        }
    }    


    // ILB: Incremental Lazy Backtracking (CaDiCaL-style).
    // If the new assumptions are identical to the old ones, preserve the
    // assumption scope and skip the full pop/reassign cycle.
    bool solver::try_ilb_reuse(unsigned num_lits, literal const* lits) {
        if (at_base_lvl())
            return false;
        if (m_assumptions.empty() && m_user_scope_literals.empty())
            return false;
        if (!m_user_scope_literals.empty())
            return false;
        if (m_config.m_drat)
            return false;
        if (num_lits != m_assumptions.size())
            return false;
        for (unsigned i = 0; i < num_lits; ++i) {
            if (lits[i] != m_assumptions[i])
                return false;
        }
        // Assumptions match. Pop search scopes but keep assumption scope.
        if (scope_lvl() > m_search_lvl)
            pop(scope_lvl() - m_search_lvl);
        m_inconsistent = false;
        m_core_is_valid = false;
        m_conflict_at_search_lvl = false;
        m_stats.m_trail_reuse++;
        TRACE(sat, tout << "ILB: reused " << m_assumptions.size()
              << " assumptions, trail size " << m_trail.size() << "\n";);
        return true;
    }

    void solver::init_assumptions(unsigned num_lits, literal const* lits) {
        if (num_lits == 0 && m_user_scope_literals.empty())
            return;

        SASSERT(at_base_lvl());
        reset_assumptions();
        push();

        propagate(false);
        if (inconsistent())
            return;

        TRACE(sat,
              tout << literal_vector(num_lits, lits) << "\n";
              if (!m_user_scope_literals.empty())
                  tout << "user literals: " << m_user_scope_literals << "\n";
              m_mc.display(tout);
              );

        for (unsigned i = 0; !inconsistent() && i < m_user_scope_literals.size(); ++i) {
            literal nlit = ~m_user_scope_literals[i];
            assign_scoped(nlit);
        }

        for (unsigned i = 0; !inconsistent() && i < num_lits; ++i) {
            literal lit = lits[i];
            set_external(lit.var());
            SASSERT(is_external(lit.var()));
            add_assumption(lit);
            assign_scoped(lit);
        }

        m_search_lvl = scope_lvl();
        SASSERT(m_search_lvl == 1);
    }

    void solver::update_min_core() {
        if (!m_min_core_valid || m_core.size() < m_min_core.size()) {
            m_min_core.reset();
            m_min_core.append(m_core);
            m_min_core_valid = true;
        }
    }

    void solver::reset_assumptions() {
        // Melt variables frozen by previous assumptions (CaDiCaL-style).
        for (literal lit : m_assumptions)
            melt_assumption_var(lit.var());
        // Clear per-literal assumption flags.
        for (literal lit : m_assumptions) {
            unsigned idx = lit.index();
            if (idx < m_assumption_mark.size())
                m_assumption_mark[idx] = false;
        }
        m_assumptions.reset();
        m_assumption_set.reset();
        m_ext_assumption_set.reset();
        m_core_is_valid = false;
        m_conflict_at_search_lvl = false;
    }

    void solver::add_assumption(literal lit) {
        // O(1) dedup via per-literal flag (CaDiCaL-style).
        unsigned idx = lit.index();
        if (idx < m_assumption_mark.size() && m_assumption_mark[idx])
            return;
        while (m_assumption_mark.size() <= idx)
            m_assumption_mark.push_back(false);
        m_assumption_mark[idx] = true;
        m_assumption_set.insert(lit);
        m_assumptions.push_back(lit);
        set_external(lit.var());
        freeze_assumption_var(lit.var());
    }

    void solver::freeze_assumption_var(bool_var v) {
        while (m_frozen_refcount.size() <= v)
            m_frozen_refcount.push_back(0);
        if (m_frozen_refcount[v] < UINT_MAX)
            m_frozen_refcount[v]++;
    }

    void solver::melt_assumption_var(bool_var v) {
        if (v >= m_frozen_refcount.size()) return;
        if (m_frozen_refcount[v] == 0) return;
        if (m_frozen_refcount[v] < UINT_MAX)
            m_frozen_refcount[v]--;
    }

    // Lazy UNSAT core (CaDiCaL-style deferred failing analysis).
    void solver::ensure_core_computed() {
        if (m_core_is_valid) return;
        if (!m_conflict_at_search_lvl) return;
        // Clear flag BEFORE calling to prevent re-entrant recursion from MUS.
        m_conflict_at_search_lvl = false;
        m_conflict = m_saved_conflict;
        m_not_l = m_saved_not_l;
        m_conflict_lvl = m_saved_conflict_lvl;
        resolve_conflict_for_unsat_core();
        m_core_is_valid = true;
    }

    void solver::reassert_min_core() {
        SASSERT(m_min_core_valid);
        pop_to_base_level();
        push();
        reset_assumptions();
        TRACE(sat, tout << "reassert: " << m_min_core << "\n";);
        for (literal lit : m_min_core) {
            SASSERT(is_external(lit.var()));
            add_assumption(lit);
            assign_scoped(lit);
        }
        propagate(false);
        SASSERT(inconsistent());
    }

    void solver::reinit_assumptions() {
        if (tracking_assumptions() && at_base_lvl() && !inconsistent()) {
            TRACE(sat, tout << "assumptions: " << m_assumptions << " user scopes: " << m_user_scope_literals << "\n";);
            if (!propagate(false)) return;
            push();
            for (literal lit : m_user_scope_literals) {
                if (inconsistent()) break;
                assign_scoped(~lit);
            }
            for (literal lit : m_assumptions) {
                if (inconsistent()) break;
                assign_scoped(lit);
            }
            init_ext_assumptions();

            if (!inconsistent()) 
                propagate(false);
            TRACE(sat,
                  tout << "consistent: " << !inconsistent() << "\n";
                  for (literal a : m_assumptions) {
                      index_set s;
                      if (m_antecedents.find(a.var(), s)) 
                          tout << a << ": "; display_index_set(tout, s) << "\n";                      
                  }
                  for (literal lit : m_user_scope_literals) 
                      tout << "user " << lit << "\n";                   
                  );
        }
    }

    void solver::init_ext_assumptions() {
        if (m_ext && m_ext->tracking_assumptions()) {
            m_ext_assumption_set.reset();
            if (!inconsistent())
                m_ext->add_assumptions(m_ext_assumption_set);
        }
    }

    bool solver::tracking_assumptions() const {
        return !m_assumptions.empty() || !m_user_scope_literals.empty() || (m_ext && m_ext->tracking_assumptions());
    }

    bool solver::is_assumption(literal l) const {
        if (!tracking_assumptions()) return false;
        // Fast path: per-literal flag (O(1)) for SAT-level assumptions.
        unsigned idx = l.index();
        if (idx < m_assumption_mark.size() && m_assumption_mark[idx])
            return true;
        return m_ext_assumption_set.contains(l);
    }

    void solver::set_activity(bool_var v, double new_act) {
        double old_act = m_activity[v];
        m_activity[v] = new_act;
        if (!was_eliminated(v) && value(v) == l_undef && new_act != old_act) {
            m_case_split_queue.activity_changed_eh(v, new_act > old_act);
        }
    }

    bool solver::is_assumption(bool_var v) const {
        return is_assumption(literal(v, false)) || is_assumption(literal(v, true));
    }

    void solver::init_search() {
        // ------------------------------------------------------------------
        // Per-call state: always reset on every check() invocation.
        // ------------------------------------------------------------------
        m_model_is_current        = false;
        m_solver_canceled         = false;
        m_phase_counter           = 0;
        m_search_state            = s_unsat;
        m_search_unsat_conflicts  = m_config.m_search_unsat_conflicts;
        m_search_sat_conflicts    = m_config.m_search_sat_conflicts;
        m_search_next_toggle      = m_search_unsat_conflicts;
        m_best_phase_size         = 0;
        m_target_assigned         = 0;

        m_rephase.base            = m_config.m_rephase_base;
        m_rephase_lim             = 0;
        m_rephase_inc             = 0;
        m_conflicts_at_last_walk  = 0;

        m_conflicts_since_restart = 0;
        m_search_ticks            = 0;
        m_ticks_at_last_restart   = 0;
        m_search_ticks_backup     = 0;
        m_ticks_restart_backup    = 0;
        m_force_conflict_analysis = false;
        m_restart_threshold       = m_config.m_restart_initial;
        m_luby_idx                = 1;
        m_restarts                = 0;
        m_last_position_log       = 0;
        m_restart_logs            = 0;
        m_conflicts_since_init    = 0;
        m_next_simplify           = m_config.m_simplify_delay;
        m_min_d_tk                = 1.0;
        m_search_lvl              = 0;

        m_randec_burst_remaining  = 0;

        m_restart_next_out        = 0;
        m_asymm_branch.init_search();
        m_stopwatch.reset();
        m_stopwatch.start();
        m_core.reset();
        m_core_is_valid = false;
        m_conflict_at_search_lvl = false;
        m_min_core_valid = false;
        m_min_core.reset();
        m_simplifier.init_search();
        m_mc.init_search(*this);
        if (m_ext)
            m_ext->init_search();

        // Open adaptive log lazily on first search (smt.adaptive_log param).
        if (!m_adaptive_log) {
            smt_params_helper sp(m_params);
            const char* log_path = sp.adaptive_log();
            if (log_path && log_path[0]) {
                m_adaptive_log = fopen(log_path, "w");
                if (m_adaptive_log) {
                    setvbuf(m_adaptive_log, nullptr, _IOLBF, 0);
                    ALOG(m_adaptive_log, "INIT")
                        .s("version", "z3-adaptive-log-v1")
                        .s("solver", "sat")
                        .u("vars", num_vars())
                        .u("clauses", num_clauses());
                }
            }
        }

        // Initialize landscape map for spatial awareness.
        m_landscape.init_search();
        {
            unsigned nv = num_vars();
            unsigned nc = num_clauses();
            if (nv > 0) {
                m_landscape.ensure_var_profiles(nv);
                m_landscape.ensure_conflict_graph(nv);
            }
            if (nc > 0)
                m_landscape.ensure_clause_profiles(nc);
            // Build clause pointer → index reverse map for on_clause_antecedent.
            // Use m_clauses.size() (input clauses only), not nc (which includes
            // units, binaries, and learned clauses).
            {
                unsigned n_input = m_clauses.size();
                if (n_input > 0) {
                    m_landscape.ensure_clause_ptr_map(n_input);
                    for (unsigned ci = 0; ci < n_input; ++ci) {
                        clause* cls = m_clauses[ci];
                        if (cls)
                            m_landscape.register_clause_ptr(ci, reinterpret_cast<uintptr_t>(cls));
                    }
                }
            }
            // Compute clause_occurrence counts from input clauses.
            if (nv > 0 && nc > 0) {
                struct occ_ctx { solver* s; };
                occ_ctx octx{this};
                m_landscape.compute_clause_occurrences(
                    nv, nc,
                    [](unsigned ci, void* ctx) -> unsigned {
                        auto* oc = static_cast<occ_ctx*>(ctx);
                        if (ci >= oc->s->m_clauses.size()) return 0;
                        clause* c = oc->s->m_clauses[ci];
                        return c ? c->size() : 0;
                    },
                    [](unsigned ci, unsigned li, void* ctx) -> unsigned {
                        auto* oc = static_cast<occ_ctx*>(ctx);
                        if (ci >= oc->s->m_clauses.size()) return 0;
                        clause* c = oc->s->m_clauses[ci];
                        if (!c || li >= c->size()) return 0;
                        return (*c)[li].var();
                    },
                    &octx);
            }
            // Dynamics: binary clause ratio (datapoint 19)
            {
                unsigned given_bin = 0, learned_bin = 0;
                num_binary(given_bin, learned_bin);
                unsigned total_binary = given_bin + learned_bin;
                unsigned total_cls = nc + total_binary;
                m_landscape.dynamics_update_binary_ratio(total_binary, total_cls);
            }
        }

        // Incremental clause decay (CaDiCaL-style): age learned clauses from
        // previous check() calls by incrementing their glue.  This makes stale
        // clauses gradually eligible for GC if they are not useful in the new
        // assumption context.  Only fires when the watermark is non-zero (i.e.
        // not the very first check() call).
        if (m_config.m_incremental_decay && m_last_decay_clause_id > 0) {
            for (clause* cp : m_learned) {
                if (cp->id() < m_last_decay_clause_id && !cp->is_garbage() && cp->glue() < 255) {
                    cp->set_glue(cp->glue() + 1);
                }
            }
        }
        m_last_decay_clause_id = cls_allocator().id_range();

        // Initialize dual-mode (stable/focused) search state.
        if (m_config.m_dual_mode) {
            m_stable_mode = false;
            m_stab_phases = 0;
            m_stabilize_inc = 0;
            m_stabilize_last_ticks = 0;
            m_stabilize_last_decisions = m_stats.m_decision;
            m_stabilize_last_conflicts = 0;
            m_stabilize_limit = m_config.m_stabilize_initial;
            m_phase_glue_sum = 0;
            m_phase_conflict_count = 0;
            m_stable_avg_glue = 0;
            m_focused_avg_glue = 0;
            m_adaptive_has_stable = false;
            m_adaptive_has_focused = false;
            reluctant_enable();
        }

        // ------------------------------------------------------------------
        // Once-only state: slowly-evolving limits preserved across incremental
        // check() calls (CaDiCaL-style).  Resetting these after a long run
        // causes overly aggressive GC that deletes good learned clauses, and
        // discards tuned simplification schedules.
        // ------------------------------------------------------------------
        if (!m_search_initialized) {
            m_gc_threshold            = m_config.m_gc_initial;
            m_defrag_threshold        = 2;
            m_simplifications         = 0;
            m_conflicts_since_gc      = 0;

            // Dynamic tier boundary state.
            memset(m_glue_histogram, 0, sizeof(m_glue_histogram));
            m_tier1_glue_limit        = 2;
            m_tier2_glue_limit        = 6;
            m_tier_recompute_count    = 0;
            m_next_tier_recompute     = 1000;

            // Effort-based inprocessing state.
            m_props_at_last_simplify  = 0;

            // Backoff limits for inprocessing, reorder, local search.
            m_reorder.lo              = m_config.m_reorder_base;
            m_local_search_lim.base   = 500;

            // Random decision burst schedule.
            m_randec_phases           = 0;
            m_randec_next_conflict    = m_config.m_randec_initial;

            m_search_initialized      = true;
        }

        TRACE(sat, display(tout););
    }

    bool solver::should_simplify() const {
        return m_conflicts_since_init >= m_next_simplify && m_simplify_enabled;
    }

    // CaDiCaL-style density scaling: denser formulas (higher clause/variable
    // ratio) need more conflicts before inprocessing pays off.  Returns v
    // unchanged when ratio <= 2; otherwise multiplies by log2(ratio).
    double solver::scale_by_density(double v) const {
        double nc = static_cast<double>(m_clauses.size());
        double nv = static_cast<double>(num_vars());
        if (nv == 0) return v;
        double ratio = nc / nv;
        if (ratio <= 2.0) return v;
        double res = log2(ratio) * v;
        return res < 1.0 ? 1.0 : res;
    }

    /**
       \brief Apply all simplifications.
    */
    void solver::do_simplify() {
        if (!should_simplify()) {
            return;
        }
        log_stats();
        m_simplifications++;

        TRACE(sat, tout << "simplify\n";);

        pop(scope_lvl());
        struct report {
            solver&   s;
            stopwatch m_watch;
            report(solver& s):s(s) {
                s.m_profile_simplify.start();
                m_watch.start();
                s.log_stats();
                IF_VERBOSE(2, verbose_stream() << "(sat.simplify :simplifications " << s.m_simplifications << ")\n";);
            }
            ~report() {
                m_watch.stop();
                s.m_profile_simplify.stop();
                s.log_stats();
            }
        };
        report _rprt(*this);
        SASSERT(at_base_lvl());

        // Track propagation work between inprocessing rounds (CaDiCaL SET_EFFORT_LIMIT
        // infrastructure). Currently used for diagnostics; individual techniques use
        // their own doubling + AIMD-delay budgets.
        m_props_at_last_simplify = m_stats.m_propagate;

        // CaDiCaL-style -O optimization levels: add extra effort budget per round.
        // Level N adds 2^N million extra budget to each inprocessing technique.
        if (m_config.m_optimize_level > 0) {
            int64_t extra = static_cast<int64_t>(1000000) << m_config.m_optimize_level;
            m_probing.add_effort_budget(extra);
            m_asymm_branch.add_effort_budget(extra);
        }

        m_cleaner(m_config.m_force_cleanup);
        CASSERT("sat_simplify_bug", check_invariant());

        m_scc();
        CASSERT("sat_simplify_bug", check_invariant());

        // Lightweight binary deduplication right after SCC.
        // SCC's elim_eqs remaps and re-creates binary clauses, which can
        // introduce duplicates.  Cleaning them before the simplifier avoids
        // registering duplicates in the subsumption use-lists.
        dedup_bin_clauses();

        if (m_ext) {
            m_ext->pre_simplify();
        }

        // Simplifier with AIMD delay: skip if the technique has been
        // unproductive recently, but track progress to re-enable it.
        if (!m_simplifier_delay.should_delay()) {
            unsigned old_subsumed  = m_simplifier.m_num_subsumed;
            unsigned old_sub_res   = m_simplifier.m_num_sub_res;
            unsigned old_elim_vars = m_simplifier.m_num_elim_vars;

            m_simplifier(false);

            CASSERT("sat_simplify_bug", check_invariant());
            CASSERT("sat_missed_prop", check_missed_propagation());
            if (!m_learned.empty()) {
                m_simplifier(true);
                CASSERT("sat_missed_prop", check_missed_propagation());
                CASSERT("sat_simplify_bug", check_invariant());
            }

            bool simp_progress =
                m_simplifier.m_num_subsumed  > old_subsumed  ||
                m_simplifier.m_num_sub_res   > old_sub_res   ||
                m_simplifier.m_num_elim_vars > old_elim_vars;
            if (simp_progress)
                m_simplifier_delay.reduce();
            else
                m_simplifier_delay.bump();
        }
        sort_watch_lits();
        CASSERT("sat_simplify_bug", check_invariant());

        CASSERT("sat_missed_prop", check_missed_propagation());
        CASSERT("sat_simplify_bug", check_invariant());
        if (m_ext) {
            m_ext->clauses_modifed();
            m_ext->simplify();
        }

        // Probing with AIMD delay.
        if (!m_probing_delay.should_delay()) {
            uint64_t old_units = m_stats.m_units;
            uint64_t old_bins  = m_stats.m_mk_bin_clause;
            m_probing();
            CASSERT("sat_missed_prop", check_missed_propagation());
            CASSERT("sat_simplify_bug", check_invariant());
            if (m_stats.m_units > old_units)
                m_probing_delay.reduce();
            else
                m_probing_delay.bump();

            // CaDiCaL-style: run SCC after probing if new units or binary
            // clauses were produced. New units shrink the implication graph,
            // and new binaries can form equivalence cycles that SCC detects.
            if (!inconsistent() &&
                (m_stats.m_units > old_units || m_stats.m_mk_bin_clause > old_bins)) {
                m_scc();
                CASSERT("sat_simplify_bug", check_invariant());
            }
        }

        // Vivification (asymmetric branching) with AIMD delay.
        if (!m_asymm_delay.should_delay()) {
            unsigned old_lits = m_asymm_branch.m_elim_literals;
            unsigned old_learned_lits = m_asymm_branch.m_elim_learned_literals;
            uint64_t old_bins = m_stats.m_mk_bin_clause;
            m_asymm_branch(false);
            bool asymm_progress =
                m_asymm_branch.m_elim_literals > old_lits ||
                m_asymm_branch.m_elim_learned_literals > old_learned_lits;
            if (asymm_progress)
                m_asymm_delay.reduce();
            else
                m_asymm_delay.bump();

            // CaDiCaL-style: run SCC after vivification if clauses were
            // shrunk to binary. Vivification can reduce ternary clauses
            // to binary, creating new implication edges that form cycles.
            if (!inconsistent() && m_stats.m_mk_bin_clause > old_bins) {
                m_scc();
                CASSERT("sat_simplify_bug", check_invariant());
            }
        }

        if (m_config.m_lookahead_simplify && !m_ext) {
            lookahead lh(*this);
            lh.simplify(true);
            lh.collect_statistics(m_aux_stats);
        }

        reinit_assumptions();
        if (inconsistent()) return;

        // Variable compaction: remap variables to eliminate holes
        // left by variable elimination during simplification.
        if (should_compact()) {
            compact_vars();
        }

        // After heavy simplification (SCC, variable elimination, probing),
        // the VMTF bump timestamps are stale -- they reflect pre-simplification
        // conflict patterns, not the restructured formula.  Reinitialize the
        // queue so focused mode starts fresh with the new problem structure.
        vmtf_reinit_after_simplify();

        if (m_next_simplify == 0) {
            m_next_simplify = static_cast<unsigned>(scale_by_density(m_config.m_next_simplify1));
        }
        else {
            m_next_simplify = static_cast<unsigned>(m_conflicts_since_init * m_config.m_simplify_mult2);
            unsigned cap = static_cast<unsigned>(scale_by_density(m_config.m_simplify_max));
            if (m_next_simplify > m_conflicts_since_init + cap)
                m_next_simplify = m_conflicts_since_init + cap;
        }

        if (m_par) {
            m_par->from_solver(*this);
            m_par->to_solver(*this);
        }

        if (m_config.m_anf_simplify && m_simplifications > m_config.m_anf_delay && !inconsistent()) {
            anf_simplifier anf(*this);
            anf_simplifier::config cfg;
            cfg.m_enable_exlin = m_config.m_anf_exlin;
            anf();
            anf.collect_statistics(m_aux_stats);
            // TBD: throttle anf_delay based on yield
        }        

        if (m_config.m_inprocess_out.is_non_empty_string()) {
            std::ofstream fout(m_config.m_inprocess_out.str());
            if (fout) {
                display_dimacs(fout);
            }
            throw solver_exception("output generated");
        }
    }

    bool solver::set_root(literal l, literal r) {
        return !m_ext || m_ext->set_root(l, r);
    }

    void solver::flush_roots() {
        if (m_ext) m_ext->flush_roots();
    }

    void solver::sort_watch_lits() {
        // With separated binary watches, m_watches contains only clause/ext watches.
        // No sorting needed since binary watches are already separate.
    }

    unsigned solver::dedup_bin_clauses() {
        // Lightweight binary clause deduplication (CaDiCaL deduplicate.cpp).
        // For each literal, sort its binary watch list by the watched literal
        // (non-learned before learned for equal literals), then remove
        // consecutive duplicates.  When a pair exists as both learned and
        // non-learned, the sort order ensures the non-learned copy comes
        // first and the learned duplicate is the one removed.
        //
        // Each removed watch entry accounts for one side of the binary clause;
        // the matching entry in the other literal's watch list will be removed
        // when we process that list.  So total removed watches / 2 = clauses.
        unsigned removed = 0;
        for (watch_list& wlist : m_bin_watches) {
            if (wlist.size() < 2)
                continue;
            // Sort: primary key = watched literal index (ascending),
            //        secondary key = non-learned before learned.
            std::sort(wlist.begin(), wlist.end(),
                [](watched const& a, watched const& b) {
                    SASSERT(a.is_binary_clause() && b.is_binary_clause());
                    unsigned ai = a.get_literal().index();
                    unsigned bi = b.get_literal().index();
                    if (ai != bi) return ai < bi;
                    // non-learned (0) < learned (1)
                    return !a.is_learned() && b.is_learned();
                });
            // Remove consecutive duplicates (same literal).
            auto out = wlist.begin();
            literal prev = null_literal;
            for (auto it = wlist.begin(), end = wlist.end(); it != end; ++it) {
                if (it->get_literal() == prev) {
                    ++removed;
                }
                else {
                    prev = it->get_literal();
                    *out++ = *it;
                }
            }
            wlist.set_end(out);
        }
        unsigned clauses_removed = removed / 2;
        IF_VERBOSE(10, if (clauses_removed > 0)
            verbose_stream() << " (sat-dedup-bin :removed " << clauses_removed << ")\n";);
        return clauses_removed;
    }

    void solver::set_model(model const& mdl, bool is_current) {
        m_model.reset();
        m_model.append(mdl);
        m_model_is_current = is_current;
    }

    void solver::mk_model() {
        m_model.reset();
        m_model_is_current = true;
        unsigned num = num_vars();
        if (m_compact_old_num_vars > 0) {
            // After compaction, the model converter still references old
            // variable indices. Create a model large enough for both old
            // and new indices. Populate old-index slots for active vars
            // so the model converter can see correct values.
            // Disable solver reference in model converter to avoid
            // out-of-bounds access on is_assumption/is_external.
            m_mc.set_solver(nullptr);
            m_model.resize(m_compact_old_num_vars, l_undef);
            for (bool_var nv = 0; nv < num; ++nv) {
                if (!was_eliminated(nv)) {
                    lbool val = value(nv);
                    unsigned old_v = m_compact_new_to_old[nv];
                    if (old_v != UINT_MAX)
                        m_model[old_v] = val;
                    m_phase[nv] = val == l_true;
                    m_best_phase[nv] = val == l_true;
                }
            }
        }
        else {
            m_model.resize(num, l_undef);
            for (bool_var v = 0; v < num; ++v) {
                if (!was_eliminated(v)) {
                    m_model[v] = value(v);
                    m_phase[v] = value(v) == l_true;
                    m_best_phase[v] = value(v) == l_true;
                }
            }
        }
        TRACE(sat_mc_bug, m_mc.display(tout););

#if 0
        IF_VERBOSE(2, for (bool_var v = 0; v < num; ++v) verbose_stream() << v << ": " << m_model[v] << "\n";);
        for (auto [l1, l2] : big::s_del_bin) {
            if (value(l1) != l_true && value(l2) != l_true) {
                IF_VERBOSE(2, verbose_stream() << "binary violation: " << l1 << " " << l2 << "\n");
            }
        }
#endif

        // After compaction, model is indexed by old var indices for the model
        // converter. check_clauses uses new-index literals, so skip it.
        if (m_clone && m_compact_old_num_vars == 0) {
            IF_VERBOSE(10, verbose_stream() << "\"checking model\"\n";);
            if (!check_clauses(m_model)) {
                throw solver_exception("check model failed");
            }
        }

        if (m_config.m_drat) {
            m_drat.check_model(m_model);
        }

        m_mc(m_model);

        if (m_clone && m_compact_old_num_vars == 0 && !check_clauses(m_model)) {
            IF_VERBOSE(1, verbose_stream() << "failure checking clauses on transformed model\n";);
            IF_VERBOSE(10, m_mc.display(verbose_stream()));
            IF_VERBOSE(1, for (bool_var v = 0; v < num; ++v) verbose_stream() << v << ": " << m_model[v] << "\n";);

            throw solver_exception("check model failed");
        }

        TRACE(sat, for (bool_var v = 0; v < num; ++v) tout << v << ": " << m_model[v] << "\n";);

        if (m_clone) {
            IF_VERBOSE(1, verbose_stream() << "\"checking model (on original set of clauses)\"\n";);
            if (!m_clone->check_model(m_model)) {
                IF_VERBOSE(1, m_mc.display(verbose_stream()));
                IF_VERBOSE(1, display_units(verbose_stream()));
                throw solver_exception("check model failed (for cloned solver)");
            }
        }
    }

    bool solver::check_clauses(model const& m) const {
        bool ok = true;
        for (clause const* cp : m_clauses) {
            clause const & c = *cp;
            if (!c.satisfied_by(m)) {
                IF_VERBOSE(1, verbose_stream() << "failed clause " << c.id() << ": " << c << "\n";);
                TRACE(sat, tout << "failed: " << c << "\n";
                      tout << "assumptions: " << m_assumptions << "\n";
                      tout << "trail: " << m_trail << "\n";
                      tout << "model: " << m << "\n";
                      m_mc.display(tout);
                      );
                for (literal l : c) {
                    if (was_eliminated(l.var())) IF_VERBOSE(1, verbose_stream() << "eliminated: " << l << "\n";);
                }
                ok = false;
            }
        }
        unsigned l_idx = 0;
        for (watch_list const& wlist : m_bin_watches) {
            literal l = ~to_literal(l_idx);
            if (value_at(l, m) != l_true) {
                for (watched const& w : wlist) {
                    if (!w.is_binary_non_learned_clause())
                        continue;
                    literal l2 = w.get_literal();
                    if (l.index() > l2.index())
                        continue;
                    if (value_at(l2, m) != l_true) {
                        IF_VERBOSE(1, verbose_stream() << "failed binary: " << l << " := " << value_at(l, m) << " " << l2 <<  " := " << value_at(l2, m) << "\n");
                        IF_VERBOSE(1, verbose_stream() << "elim l1: " << was_eliminated(l.var()) << " elim l2: " << was_eliminated(l2) << "\n");
                        TRACE(sat, m_mc.display(tout << "failed binary: " << l << " " << l2 << "\n"););
                        ok = false;
                    }
                }
            }
            ++l_idx;
        }
        for (literal l : m_assumptions) {
            if (value_at(l, m) != l_true) {
                VERIFY(is_external(l.var()));
                IF_VERBOSE(1, verbose_stream() << "assumption: " << l << " does not model check " << value_at(l, m) << "\n";);
                TRACE(sat,
                      tout << l << " does not model check\n";
                      tout << "trail: " << m_trail << "\n";
                      tout << "model: " << m << "\n";
                      m_mc.display(tout);
                      );
                ok = false;
            }
        }
        if (m_ext && !m_ext->check_model(m)) {
            ok = false;
        }
        return ok;
    }

    bool solver::check_model(model const & m) const {
        bool ok = check_clauses(m);
        if (ok && !m_mc.check_model(m)) {
            ok = false;
            TRACE(sat, tout << "model: " << m << "\n"; m_mc.display(tout););
            IF_VERBOSE(0, verbose_stream() << "model check failed\n");
        }
        return ok;
    }

    bool solver::should_restart() {
        if (scope_lvl() < 2 + search_lvl()) return false;
        if (m_case_split_queue.empty()) return false;

        // Check for dual-mode switching before evaluating restart condition.
        // stabilizing() may toggle m_stable_mode and swap EMA averages.
        // If a mode switch occurs, force a restart so the solver starts
        // fresh in the new mode (CaDiCaL always restarts on mode switch).
        if (m_config.m_dual_mode) {
            bool was_stable = m_stable_mode;
            stabilizing();
            if (was_stable != m_stable_mode)
                return true;  // force restart on mode switch
        }

        // CaDiCaL-style tick-based restart forcing: if the total search work
        // (propagation + minimization) since the last restart greatly exceeds
        // what conflicts alone would suggest, force a restart.  This prevents
        // expensive minimization phases from silently delaying restarts and
        // phase switches.  The threshold is 64 ticks per expected conflict --
        // if we burn more than restart_threshold*64 ticks without enough
        // conflicts, the solver is doing expensive work that should trigger
        // a restart consideration.
        //
        // Exception: in focused mode with zero conflicts since last restart,
        // tick-forced restarts cause deterministic decision loops (VMTF picks
        // the same variables in the same order since nothing was bumped).
        // Suppress them so the solver explores deeper until it hits a conflict.
        uint64_t ticks_since_restart = m_search_ticks - m_ticks_at_last_restart;
        bool tick_forced = ticks_since_restart > static_cast<uint64_t>(m_restart_threshold) * 64;
        if (tick_forced && m_config.m_dual_mode && !m_stable_mode && m_conflicts_since_restart == 0)
            tick_forced = false;

        // In stable mode with dual-mode, use reluctant doubling for restart timing.
        if (m_config.m_dual_mode && m_stable_mode) {
            if (!tick_forced && !m_reluctant_triggered) return false;
            return true;
        }

        if (!tick_forced && m_conflicts_since_restart <= m_restart_threshold) return false;
        if (m_config.m_restart != RS_EMA) return true;
        double margin = (m_search_state == s_sat) ? m_config.m_restart_margin_sat : m_config.m_restart_margin;
        return
            m_fast_glue_avg + search_lvl() <= scope_lvl() &&
            margin * m_slow_glue_avg <= m_fast_glue_avg;
    }

    void solver::log_stats() {
        m_restart_logs++;
        
        std::stringstream strm;
        strm << "(sat.stats " << std::setw(6) << m_stats.m_conflict << " " 
             << std::setw(6) << m_stats.m_decision << " "
             << std::setw(4) << m_stats.m_restart 
             << mk_stat(*this)
             << " " << std::setw(6) << std::setprecision(2) << m_stopwatch.get_current_seconds() << ")\n";
        std::string str = std::move(strm).str();
        svector<size_t> nums;
        for (size_t i = 0; i < str.size(); ++i) {
            while (i < str.size() && str[i] != ' ') ++i;
            while (i < str.size() && str[i] == ' ') ++i;
            // position of first character after space
            if (i < str.size()) {
                nums.push_back(i);
            }
        }   
        bool same = m_last_positions.size() == nums.size();
        size_t diff = 0;
        for (unsigned i = 0; i < nums.size() && same; ++i) {
            if (m_last_positions[i] > nums[i]) diff += m_last_positions[i] - nums[i];
            if (m_last_positions[i] < nums[i]) diff += nums[i] - m_last_positions[i];
        }
        if (m_last_positions.empty() || 
            m_restart_logs >= 20 + m_last_position_log || 
            (m_restart_logs >= 6 + m_last_position_log && (!same || diff > 3))) {
            m_last_position_log = m_restart_logs;
            //           conflicts          restarts          learned            gc               time
            //                     decisions         clauses            units          memory
            int adjust[9] = { -3,      -3,      -3,      -1,      -3,      -2,   -1,     -2,       -1 };
            char const* tag[9]  = { ":conflicts ", ":decisions ", ":restarts ", ":clauses/bin ", ":learned/bin ", ":units ", ":gc ", ":memory ", ":time" };
            std::stringstream l1, l2;
            l1 << "(sat.stats ";
            l2 << "(sat.stats ";
            size_t p1 = 11, p2 = 11;
            SASSERT(nums.size() == 9);
            for (unsigned i = 0; i < 9 && i < nums.size(); ++i) {
                size_t p = nums[i];
                if (i & 0x1) {
                    // odd positions
                    for (; p2 < p + adjust[i]; ++p2) l2 << " ";
                    p2 += strlen(tag[i]);
                    l2 << tag[i];
                }
                else {
                    // even positions
                    for (; p1 < p + adjust[i]; ++p1) l1 << " ";
                    p1 += strlen(tag[i]);
                    l1 << tag[i];
                }                               
            }
            for (; p1 + 2 < str.size(); ++p1) l1 << " ";            
            for (; p2 + 2 < str.size(); ++p2) l2 << " ";            
            l1 << ")\n";
            l2 << ")\n";
            IF_VERBOSE(1, verbose_stream() << l1.str() << l2.str());
            m_last_positions.reset();
            m_last_positions.append(nums);
        }
        IF_VERBOSE(1, verbose_stream() << str);            
    }

    void solver::do_restart(bool to_base) {        
        m_stats.m_restart++;
        m_restarts++;
        if (m_conflicts_since_init >= m_restart_next_out && get_verbosity_level() >= 1) {
            if (0 == m_restart_next_out) {
                m_restart_next_out = 1;
            }
            else {
                m_restart_next_out = std::min(m_conflicts_since_init + 50000, (3*m_restart_next_out)/2 + 1); 
            }
            log_stats();
        }
        TRACE(sat, tout << "restart " << restart_level(to_base) << "\n";);
        IF_VERBOSE(30, display_status(verbose_stream()););
        TRACE(sat, tout << "restart " << restart_level(to_base) << "\n";);

        ALOG(m_adaptive_log, "RESTART")
            .u("r", m_restarts)
            .u("c", m_conflicts_since_init)
            .u("trail", m_trail.size())
            .d("fast_glue", static_cast<double>(m_fast_glue_avg))
            .d("slow_glue", static_cast<double>(m_slow_glue_avg));

        // Landscape: compute phase hash and health for region tracking.
        {
            unsigned nv = num_vars();
            uint64_t phase_hash = 0;
            // Sample every 64th variable to keep cost bounded.
            for (unsigned v = 0; v < nv; v += 64) {
                uint64_t bit = m_phase[v] ? 1ULL : 0ULL;
                phase_hash ^= fmix64(static_cast<uint64_t>(v) | (bit << 32));
            }
            // Health = conflicts_since_restart / trail_size (higher = more productive).
            float health = 0.0f;
            if (m_trail.size() > 0) {
                health = static_cast<float>(m_conflicts_since_restart) /
                         static_cast<float>(m_trail.size());
            }
            m_landscape.on_restart(phase_hash, health);
            // Update polarity history for sampled variables.
            for (unsigned v = 0; v < nv; v += 64) {
                m_landscape.update_polarity_history(v, m_phase[v]);
            }
            // Complete fanout for the last decision before restart.
            if (m_landscape.get_last_decision_var() != UINT32_MAX) {
                unsigned trail_now = m_trail.size();
                unsigned trail_prev = m_landscape.get_last_trail_pos();
                if (trail_now > trail_prev) {
                    unsigned fanout = trail_now - trail_prev - 1;
                    m_landscape.on_decision_fanout(m_landscape.get_last_decision_var(), fanout);
                }
                m_landscape.set_last_decision_var(UINT32_MAX);
            }
            // Dynamics: restart interval (datapoint 15) + theory prop density (18)
            m_landscape.dynamics_on_restart(m_conflicts_since_restart);

            // A4: Activity Gini — compute from VSIDS activity array.
            m_landscape.dynamics_compute_activity_gini(m_activity.data(), num_vars());

            // C1: Trail stability — fraction of vars that maintained assignment polarity.
            {
                unsigned nv = num_vars();
                unsigned step = (nv > 4096) ? (nv / 4096) : 1;
                unsigned same = 0, total = 0;
                auto& lp = m_landscape.last_decided_polarity();
                for (unsigned v = 0; v < nv; v += step) {
                    if (v >= lp.size()) break;
                    if (lp[v] == 0) continue;  // never decided
                    bool prev_pol = (lp[v] == 2);
                    if (prev_pol == m_phase[v]) same++;
                    total++;
                }
                if (total > 0) {
                    float stab = static_cast<float>(same) / static_cast<float>(total);
                    m_landscape.dynamics_update_trail_stability(stab);
                }
            }
        }

        pop_reinit(restart_level(to_base));
        set_next_restart();
    }

    unsigned solver::restart_level(bool to_base) {
        if (to_base || scope_lvl() == search_lvl())
            return scope_lvl() - search_lvl();

        // In focused mode, always restart to base -- VMTF trail reuse
        // requires careful handling of bumped timestamps vs. scope literals.
        // CaDiCaL does not reuse trail in focused (queue) mode.
        if (m_config.m_dual_mode && !m_stable_mode)
            return scope_lvl() - search_lvl();

        if (m_case_split_queue.empty())
            return scope_lvl() - search_lvl();

        bool_var next = m_case_split_queue.min_var();
        // Implementations of Marijn's idea of reusing the
        // trail when the next decision literal has lower precedence.
        // pop trail from top
#if 0
        unsigned n = 0;
        do {
            bool_var prev = scope_literal(scope_lvl() - n - 1).var();
            if (m_case_split_queue.more_active(prev, next)) break;
            ++n;
        }
        while (n < scope_lvl() - search_lvl());
        return n;
#endif
        // pop trail from bottom
        unsigned n = search_lvl();
        for (; n < scope_lvl() && m_case_split_queue.more_active(scope_literal(n).var(), next); ++n) {
        }
        return n - search_lvl();
    }

    void solver::update_activity(bool_var v, double p) {
        double new_act = num_vars() * m_config.m_activity_scale * p;
        set_activity(v, new_act);
    }

    void solver::set_next_restart() {
        m_conflicts_since_restart = 0;
        m_ticks_at_last_restart = m_search_ticks;
        // Consume the reluctant trigger after a restart in stable mode.
        if (m_config.m_dual_mode && m_stable_mode)
            m_reluctant_triggered = false;
        switch (m_config.m_restart) {
        case RS_GEOMETRIC:
            m_restart_threshold = static_cast<unsigned>(m_restart_threshold * m_config.m_restart_factor);
            break;
        case RS_LUBY:
            m_luby_idx++;
            m_restart_threshold = m_config.m_restart_initial * get_luby(m_luby_idx);
            break;
        case RS_EMA:
            m_restart_threshold = m_config.m_restart_initial;
            break;
        case RS_STATIC:
            break;
        default:
            UNREACHABLE();
            break;
        }
        CASSERT("sat_restart", check_invariant());
    }


    // -----------------------
    //
    // Conflict resolution
    //
    // -----------------------

    /**
     * Recompute dynamic tier boundaries from the glue usage histogram.
     *
     * CaDiCaL-style: iterate glue values from 1 upward, accumulating usage counts.
     * tier1 = glue where accumulated usage reaches 50% of total (top-half most-used).
     * tier2 = glue where accumulated usage reaches 90% of total.
     * Clamp: tier1 >= 2, tier2 >= tier1 + 1.
     *
     * After recomputation, double the interval (up to 2^16 = 65536 conflicts).
     */
    void solver::recompute_tier_boundaries() {
        m_tier_recompute_count++;

        // Schedule next recomputation with exponentially growing interval.
        unsigned delta = m_tier_recompute_count >= 16 ? (1u << 16) : (1u << m_tier_recompute_count);
        m_next_tier_recompute = m_conflicts_since_init + delta;

        // Sum total usage across all glue values.
        uint64_t total = 0;
        for (unsigned g = 0; g < 64; g++)
            total += m_glue_histogram[g];

        // If no usage data yet, keep defaults.
        if (total == 0) {
            m_tier1_glue_limit = 2;
            m_tier2_glue_limit = 6;
            return;
        }

        uint64_t tier1_threshold = total / 2;      // 50%
        uint64_t tier2_threshold = total * 9 / 10;  // 90%

        unsigned new_tier1 = 1;
        unsigned new_tier2 = 1;

        // Find tier1 boundary: glue where accumulated usage reaches 50%.
        uint64_t accumulated = m_glue_histogram[0];
        unsigned g = 1;
        for (; g < 64; g++) {
            accumulated += m_glue_histogram[g];
            if (accumulated >= tier1_threshold) {
                new_tier1 = g;
                break;
            }
        }

        // Continue past tier1 to find tier2 boundary at 90%.
        // Increment g to avoid double-counting the glue bucket where tier1 was found.
        for (++g; g < 64; g++) {
            accumulated += m_glue_histogram[g];
            if (accumulated >= tier2_threshold) {
                new_tier2 = g;
                break;
            }
        }

        // Clamp minimums.
        if (new_tier1 < 2)
            new_tier1 = 2;
        if (new_tier2 < new_tier1 + 1)
            new_tier2 = new_tier1 + 1;

        m_tier1_glue_limit = new_tier1;
        m_tier2_glue_limit = new_tier2;

        TRACE(sat, tout << "recompute_tier_boundaries: tier1=" << m_tier1_glue_limit
              << " tier2=" << m_tier2_glue_limit
              << " total_usage=" << total
              << " next_recompute=" << m_next_tier_recompute << "\n";);
    }

    bool solver::resolve_conflict() {
        while (true) {
            lbool r = resolve_conflict_core();
            CASSERT("sat_check_marks", check_marks());
            // after pop, clauses are reinitialized, this may trigger another conflict.
            if (r == l_false)
                return false;
            if (!inconsistent())
                return true;
        }
    }


    lbool solver::resolve_conflict_core() {
        m_conflicts_since_init++;
        m_conflicts_since_restart++;
        m_conflicts_since_gc++;
        m_stats.m_conflict++;
        if (m_step_size > m_config.m_step_size_min)
            m_step_size -= m_config.m_step_size_dec;

        // In stable mode, tick the reluctant doubling counter on every conflict.
        if (m_config.m_dual_mode && m_stable_mode)
            reluctant_tick();

        // Decrement random decision burst counter on conflict.
        if (m_randec_burst_remaining > 0)
            --m_randec_burst_remaining;

        // Periodically recompute dynamic tier boundaries from glue usage histogram.
        if (m_conflicts_since_init >= m_next_tier_recompute)
            recompute_tier_boundaries();

        // Adaptive log: periodic SAT snapshot every 100 conflicts.
        if (m_adaptive_log && m_conflicts_since_init > 0 && m_conflicts_since_init % 100 == 0) {
            ALOG(m_adaptive_log, "SAT")
                .u("c", m_conflicts_since_init)
                .u("decisions", m_stats.m_decision)
                .u("props", m_stats.m_propagate)
                .u("learned", m_learned.size())
                .u("clauses", m_clauses.size())
                .u("restarts", m_restarts)
                .u("vars", num_vars())
                .d("fast_glue", static_cast<double>(m_fast_glue_avg))
                .d("slow_glue", static_cast<double>(m_slow_glue_avg));
        }
        // Landscape: dump every 250 conflicts.
        if (m_conflicts_since_init > 0 && m_conflicts_since_init % 250 == 0) {
            // Causal signal batch update at LANDSCAPE dump cadence.
            // SAT solver: QI signals (A1, B1, C2-theory, C3) are always 0.
            double stress_gini = m_landscape.stress_concentration();
            m_landscape.dynamics_update_rates(
                0,                           // qi_inserts (no QI in SAT solver)
                m_stats.m_decision,           // decisions
                m_landscape.dynamics().theory_lemma_count,  // theory lemmas
                stress_gini);
            // C4: SAT solver has no agility metric; leave at 0.

            if (m_adaptive_log)
                m_landscape.dump_to_alog(m_adaptive_log, m_conflicts_since_init, num_vars());
        }
        // Landscape: periodic stress decay every 1000 conflicts.
        if (m_conflicts_since_init > 0 && m_conflicts_since_init % 1000 == 0) {
            m_landscape.decay_stress();
            // Periodic clause scan for saving literals.
            unsigned nc = m_clauses.size();
            for (unsigned ci = 0; ci < nc; ++ci) {
                clause* cls = m_clauses[ci];
                if (!cls || cls->is_learned()) continue;
                unsigned nlits = cls->size();
                unsigned false_count = 0;
                unsigned true_lit_pos = UINT32_MAX;
                for (unsigned li = 0; li < nlits; ++li) {
                    lbool val = value((*cls)[li]);
                    if (val == l_false) {
                        false_count++;
                    } else if (val == l_true && true_lit_pos == UINT32_MAX) {
                        true_lit_pos = li;
                    }
                }
                if (false_count == nlits - 1 && true_lit_pos != UINT32_MAX) {
                    m_landscape.on_clause_propagation(ci, (*cls)[true_lit_pos].index());
                }
            }
        }

        bool unique_max;
        m_conflict_lvl = get_max_lvl(m_not_l, m_conflict, unique_max);
        justification js = m_conflict;

        if (m_conflict_lvl <= 1 && (!m_assumptions.empty() ||
                                    !m_ext_assumption_set.empty() ||
                                    !m_user_scope_literals.empty())) {
            if (m_config.m_drat) {
                // DRAT mode: compute core eagerly so proof logging is correct.
                // drat_explain_conflict handles extension logging (scoped_drating)
                // and also calls resolve_conflict_for_unsat_core when m_ext != null.
                drat_explain_conflict();
                // When there is no extension, compute the core directly.
                if (!m_ext)
                    resolve_conflict_for_unsat_core();
                if (m_conflict_lvl == 0)
                    drat_log_clause(0, nullptr, sat::status::redundant());
                m_core_is_valid = true;
            }
            else {
                // CaDiCaL-style lazy failing: save conflict state, defer core
                // extraction until the first get_core() call.
                TRACE(sat, tout << "unsat core deferred (conflict_lvl=" << m_conflict_lvl
                      << " not_l=" << m_not_l << " conflict=" << m_conflict << ")\n";);
                m_saved_conflict         = m_conflict;
                m_saved_not_l            = m_not_l;
                m_saved_conflict_lvl     = m_conflict_lvl;
                m_conflict_at_search_lvl = true;
                m_core_is_valid          = false;
                m_core.reset();
            }
            return l_false;
        }

        if (m_conflict_lvl == 0) {
            drat_explain_conflict();
            if (m_config.m_drat)
                drat_log_clause(0, nullptr, sat::status::redundant());
            TRACE(sat, tout << "conflict level is 0\n";);
            return l_false;
        }

        // force_conflict_analysis is used instead of relying on normal propagation to assign m_not_l 
        // at the backtracking level. This is the case where the external theories miss propagations
        // that only get triggered after decisions.
        
        if (allow_backtracking() && unique_max && !m_force_conflict_analysis) {
            TRACE(sat, tout << "unique max " << js << " " << m_not_l << "\n";);
            pop_reinit(m_scope_lvl - m_conflict_lvl + 1);
            m_force_conflict_analysis = true;
            ++m_stats.m_backtracks;
            return l_undef;
        }
        m_force_conflict_analysis = false;

        updt_phase_of_vars();

        if (m_ext) {
            switch (m_ext->resolve_conflict()) {
            case l_true:                
                learn_lemma_and_backjump();
                reset_level_info();
                return l_undef;
            case l_undef:
                break;
            case l_false:
                // backjumping was taken care of internally.
                return l_undef;
            }
        }

        m_lemma.reset();

        unsigned idx = skip_literals_above_conflict_level();
        m_max_marked_trail = idx;

        // save space for first uip
        m_lemma.push_back(null_literal);

        TRACE(sat_conflict_detail, 
              tout << "resolve: " << m_not_l << " " 
              << " js: " << js 
              << " idx: " << idx 
              << " trail: " << m_trail.size() 
              << " @" << m_conflict_lvl << "\n";);

        unsigned num_marks = 0;
        literal consequent = null_literal;
        if (m_not_l != null_literal) {
            TRACE(sat_conflict_detail, tout << "not_l: " << m_not_l << "\n";);
            process_antecedent(m_not_l, num_marks);
            consequent = ~m_not_l;
        }

        do {
            TRACE(sat_conflict_detail, tout << "processing consequent: " << consequent << " @" << (consequent==null_literal?m_conflict_lvl:lvl(consequent)) << "\n";
                  tout << "num_marks: " << num_marks << "\n";
                  display_justification(tout, js) << "\n";);

            switch (js.get_kind()) {
            case justification::NONE:
                break;
            case justification::BINARY:
                process_antecedent(~(js.get_literal()), num_marks);
                break;
            case justification::CLAUSE: {
                clause & c = get_clause(js);
                // CaDiCaL-style: recompute glue for reason clauses during
                // conflict analysis (not during propagation) to keep the
                // propagation loop tight.  All literals in a reason clause
                // are assigned, so num_diff_levels_below is safe here.
                if (c.is_learned()) {
                    unsigned new_glue;
                    if (c.glue() > 2 &&
                        num_diff_levels_below(c.size(), c.begin(), c.glue() - 1, new_glue)) {
                        c.set_glue(new_glue);
                    }
                    // Tier promotion based on (possibly updated) glue.
                    unsigned g = c.glue();
                    if (g <= m_tier1_glue_limit && !c.is_core())
                        c.set_tier(clause::CORE);
                    else if (g <= m_tier2_glue_limit && c.is_tier2())
                        c.set_tier(clause::TIER1);
                    // Track glue usage for dynamic tier boundary recomputation.
                    m_glue_histogram[std::min(g, 63u)]++;
                }
                unsigned i = 0;
                if (consequent != null_literal) {
                    SASSERT(c[0] == consequent || c[1] == consequent);
                    if (c[0] == consequent) {
                        i = 1;
                    }
                    else {
                        process_antecedent(~c[0], num_marks);
                        i = 2;
                    }
                }
                unsigned sz = c.size();
                for (; i < sz; ++i)
                    process_antecedent(~c[i], num_marks);
                // OTFS: On-the-fly strengthening (CaDiCaL-style).
                // After resolving against this clause, check if the resolvent is
                // smaller than the antecedent. If so, the pivot literal is redundant
                // in the antecedent and can be removed.
                // resolvent_size = num_marks (conflict-level) + lemma.size()-1 (below-level)
                // antecedent_size must EXCLUDE level-0 literals (they are not part of
                // the resolvent since process_antecedent skips level-0 vars).
                // We only apply to the non-initial clauses (consequent != null_literal means
                // this is a reason clause, not the conflict clause itself) and non-binary clauses.
                // Skip when DRAT proofs are enabled (proof tracking for OTFS is complex).
                if (m_config.m_otfs && !m_config.m_drat &&
                    consequent != null_literal && sz > 2) {
                    // Compute antecedent_size excluding level-0 literals (matching CaDiCaL).
                    unsigned antecedent_size = 0;
                    for (unsigned k = 0; k < sz; ++k)
                        if (lvl(c[k]) > 0)
                            antecedent_size++;
                    unsigned resolvent_size = num_marks + (m_lemma.size() - 1);
                    if (antecedent_size > 2 && resolvent_size < antecedent_size) {
                        on_the_fly_strengthen(c, consequent, js.get_clause_offset());
                    }
                }
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                fill_ext_antecedents(consequent, js, false);
                TRACE(sat, tout << "ext antecedents: " << m_ext_antecedents << "\n";);
                for (literal l : m_ext_antecedents)                     
                    process_antecedent(l, num_marks);                
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
            
            // Theory-propagated antecedents may appear at trail positions
            // above idx (out-of-order trail). Bump idx to cover them.
            if (m_max_marked_trail > idx)
                idx = m_max_marked_trail;

            bool_var c_var;
            while (true) {
                consequent = m_trail[idx];
                c_var = consequent.var();
                if (is_marked(c_var)) {
                    if (lvl(c_var) == m_conflict_lvl) {
                        break;
                    }
                    SASSERT(lvl(c_var) < m_conflict_lvl);
                }
                CTRACE(sat, idx == 0,
                       tout << "conflict level " << m_conflict_lvl << "\n";
                       for (literal lit : m_trail)
                           if (is_marked(lit.var()))
                               tout << "missed " << lit << "@" << lvl(lit) << "\n";);
                CTRACE(sat, idx == 0, display(tout););
                if (idx == 0)
                    IF_VERBOSE(0, verbose_stream() << "num-conflicts: " << m_stats.m_conflict << "\n");
                VERIFY(idx > 0);
                idx--;
            }
            SASSERT(lvl(consequent) == m_conflict_lvl);
            js             = m_justification[c_var];
            idx--;
            num_marks--;
            reset_mark(c_var);

            TRACE(sat, display_justification(tout << consequent << " ", js) << "\n";);            
        }
        while (num_marks > 0);

        m_lemma[0] = ~consequent;
        learn_lemma_and_backjump();
        reset_level_info();

        return l_undef;
    }

    void solver::eager_subsume(clause& new_cls) {
        SASSERT(new_cls.is_learned());
        unsigned new_sz = new_cls.size();
        if (new_sz == 0) return;
        for (literal l : new_cls) m_lit_mark[l.index()] = true;
        unsigned limit = m_config.m_eager_subsume_limit;
        unsigned checked = 0;
        unsigned j = m_learned.size();
        for (unsigned i = m_learned.size(); i-- > 0 && checked < limit; ) {
            clause* d = m_learned[i];
            if (d == &new_cls) continue;
            ++checked;
            if (!d->is_learned() || !can_delete(*d)) continue;
            unsigned needed = new_sz;
            for (literal l : *d) {
                if (m_lit_mark[l.index()])
                    if (--needed == 0) break;
            }
            if (needed > 0) continue;
            TRACE(sat, tout << "eager subsume: " << new_cls << " subsumes " << *d << "\n";);
            ++m_stats.m_eager_subsumed;
            detach_clause(*d);
            del_clause(*d);
            --j;
            if (i < j) m_learned[i] = m_learned[j];
        }
        if (j < m_learned.size()) m_learned.shrink(j);
        for (literal l : new_cls) m_lit_mark[l.index()] = false;
    }

    void solver::learn_lemma_and_backjump() {
        TRACE(sat_lemma, tout << "new lemma size: " << m_lemma.size() << "\n" << m_lemma << "\n";);
        
        if (m_lemma.empty()) {
            pop_reinit(m_scope_lvl);
            mk_clause_core(0, nullptr, sat::status::redundant());
            return;
        }
        
        // Per-level UIP clause shrinking (CaDiCaL technique).
        if (m_config.m_shrink > 0 && m_lemma.size() > 2)
            shrink_lemma();

        if (m_config.m_minimize_lemmas) {
            minimize_lemma();
            reset_lemma_var_marks();
            if (m_config.m_dyn_sub_res)
                dyn_sub_res();
            TRACE(sat_lemma, tout << "new lemma (after minimization) size: " << m_lemma.size() << "\n" << m_lemma << "\n";);
        }
        else {
            reset_lemma_var_marks();
        }
        
        unsigned backtrack_lvl = lvl(m_lemma[0]);
        unsigned backjump_lvl  = 0;
        for (unsigned i = m_lemma.size(); i-- > 1;) {
            unsigned level = lvl(m_lemma[i]);
            backjump_lvl = std::max(level, backjump_lvl);
        }    
        // with scope tracking and chronological backtracking, 
        // consequent may not be at highest decision level.
        if (backtrack_lvl < backjump_lvl) {
            backtrack_lvl = backjump_lvl;
            for (unsigned i = m_lemma.size(); i-- > 1;) {
                if (lvl(m_lemma[i]) == backjump_lvl) {
                    TRACE(sat, tout << "swap " << m_lemma[0] << "@" << lvl(m_lemma[0]) << m_lemma[1] << "@" << backjump_lvl << "\n";);
                    std::swap(m_lemma[i], m_lemma[0]);
                    break;
                }
            }
        }
        
        unsigned glue = num_diff_levels(m_lemma.size(), m_lemma.data());
        // Populate per-conflict statistics for downstream consumers
        // (e.g. bump_reason_literals, activity scaling).
        m_conflict_glue           = glue;
        m_conflict_clause_size    = m_lemma.size();
        m_conflict_decision_level = m_conflict_lvl;

        // --- Landscape map: record conflict data ---
        {
            unsigned num_lits = m_lemma.size();
            unsigned var_buf[8];
            unsigned var_count = 0;
            for (unsigned i = 0; i < num_lits; ++i) {
                m_landscape.on_conflict_antecedent(m_lemma[i].index());
                if (var_count < 8)
                    var_buf[var_count++] = m_lemma[i].var();
            }
            m_landscape.on_learned_clause(var_count, var_buf);

            // Tier 1b: mark variables as conflict participants.
            for (unsigned i = 0; i < num_lits; ++i) {
                bool was_dec = (i == 0); // FUIP literal approximates the decision
                m_landscape.on_var_in_conflict(m_lemma[i].var(), was_dec);
            }

            // Tier 1a: bump antecedent count for reason clauses of learned-clause
            // literals. Records which input clauses contribute to conflict derivation.
            for (unsigned i = 0; i < num_lits; ++i) {
                bool_var v = m_lemma[i].var();
                justification js = m_justification[v];
                if (js.is_clause()) {
                    clause& c = get_clause(js);
                    unsigned cidx = m_landscape.find_clause_idx(
                        reinterpret_cast<uintptr_t>(&c));
                    if (cidx != UINT32_MAX)
                        m_landscape.on_clause_antecedent(cidx);
                }
            }

            // Tier 2b: full conflict metadata.
            uint64_t clause_hash = fmix64(static_cast<uint64_t>(num_lits));
            for (unsigned i = 0; i < num_lits && i < 8; ++i)
                clause_hash ^= fmix64(static_cast<uint64_t>(m_lemma[i].index()));

            unsigned backjump = (m_conflict_lvl > backjump_lvl)
                              ? (m_conflict_lvl - backjump_lvl) : 0;
            m_landscape.on_conflict_full(
                clause_hash, var_buf, var_count, glue,
                backjump, m_trail.size(),
                0 /* no theory in pure SAT */, num_lits);

            // Dynamics: conflict-time datapoints (8-11, 14, 16-17, 20)
            // In the pure SAT path, theory_conflict is always false.
            // When m_ext is present (euf_solver), check if the conflict
            // justification was an extension justification.
            bool th_conflict = m_conflict.is_ext_justification();
            m_landscape.dynamics_on_conflict(
                m_conflict_lvl, m_trail.size(),
                num_vars(), num_lits,
                glue, m_conflict_lvl, backjump_lvl, th_conflict);
        }

        // Muon-style per-conflict normalization: LBD weight * clause-size normalization.
        // Dividing by sqrt(clause_size) makes total activity injection per conflict
        // constant regardless of how many variables are bumped.
        {
            double glue_scale = 1.0 / std::max(static_cast<double>(m_slow_glue_avg), 1.0);
            double muon_scale = 1.0 / std::sqrt(std::max(static_cast<double>(m_conflict_clause_size), 1.0));
            m_conflict_bump_scale = glue_scale * muon_scale;
        }
        // E3: fast/slow EMAs of bump scale for gradient trend detection.
        m_bump_scale_fast = 0.03 * m_conflict_bump_scale + 0.97 * m_bump_scale_fast;
        m_bump_scale_slow = 0.0001 * m_conflict_bump_scale + 0.9999 * m_bump_scale_slow;
        m_fast_glue_avg.update(glue);
        m_slow_glue_avg.update(glue);
        m_phase_glue_sum += glue;
        ++m_phase_conflict_count;
    
        // CaDiCaL-style backtrack level determination with trail reuse.
        unsigned actual_bt_lvl = determine_backtrack_level(backjump_lvl);
        unsigned num_scopes = m_scope_lvl - actual_bt_lvl;
        if (actual_bt_lvl == backjump_lvl)
            ++m_stats.m_backjumps;
        else
            ++m_stats.m_backtracks;
        pop_reinit(num_scopes);
        clause * lemma = mk_clause_core(m_lemma.size(), m_lemma.data(), sat::status::redundant());
        if (lemma) {
            lemma->set_glue(glue);
            // Assign tier based on glue (LBD) using dynamic boundaries:
            //   glue <= tier1_glue_limit => CORE (never deleted)
            //   glue <= tier2_glue_limit => TIER1 (protected from routine GC)
            //   else                     => TIER2 (aggressively GC'd)
            if (glue <= m_tier1_glue_limit)
                lemma->set_tier(clause::CORE);
            else if (glue <= m_tier2_glue_limit)
                lemma->set_tier(clause::TIER1);
            else
                lemma->set_tier(clause::TIER2);
        }
        if (m_par && lemma) {
            m_par->share_clause(*this, *lemma);
        }
        if (lemma && m_config.m_eager_subsume) {
            eager_subsume(*lemma);
        }

        // Learned scorer removed: was tracking-only infrastructure (never used
        // for branching decisions).  extract_features + Adam-style train() per
        // lemma literal added measurable per-conflict overhead for zero benefit.

        m_lemma.reset();
        TRACE(sat_conflict_detail, tout << "consistent " << (!m_inconsistent) << " scopes: " << scope_lvl() << " backtrack: " << backtrack_lvl << " backjump: " << backjump_lvl << "\n";);
        decay_activity();
        if (m_config.m_branching_heuristic == BH_ADAM || m_config.m_branching_heuristic == BH_COMBINED)
            ++m_adam_step;
        updt_phase_counters();
    }

    bool solver::use_backjumping(unsigned num_scopes) const {
        return 
            num_scopes > 0 && 
            (num_scopes <= m_config.m_backtrack_scopes || !allow_backtracking());
    }

    bool solver::allow_backtracking() const {
        return m_conflicts_since_init > m_config.m_backtrack_init_conflicts;
    }

    unsigned solver::determine_backtrack_level(unsigned backjump_lvl) {
        unsigned current_lvl = m_scope_lvl;
        if (backjump_lvl >= current_lvl - 1) return backjump_lvl;
        if (!allow_backtracking()) {
            unsigned gap = current_lvl - backjump_lvl;
            return (gap <= m_config.m_backtrack_scopes) ? backjump_lvl : current_lvl - 1;
        }
        if (backjump_lvl < search_lvl()) return backjump_lvl;
        unsigned gap = current_lvl - backjump_lvl;
        if (gap > m_config.m_chrono_level_lim) {
            ++m_stats.m_chrono_backtracks;
            return current_lvl - 1;
        }
        if (m_config.m_chrono_reuse_trail && backjump_lvl + 1 < m_scopes.size()) {
            unsigned ts = m_scopes[backjump_lvl + 1].m_trail_lim;
            unsigned te = m_trail.size();
            if (ts < te) {
                double ba = -1.0; unsigned bp = ts;
                for (unsigned i = ts; i < te; ++i) {
                    double a = m_activity[m_trail[i].var()];
                    if (a > ba) { ba = a; bp = i; }
                }
                unsigned r = backjump_lvl;
                while (r < current_lvl - 1 && r + 1 < m_scopes.size() && m_scopes[r + 1].m_trail_lim <= bp) r++;
                if (r > backjump_lvl) { ++m_stats.m_trail_reuse; return r; }
            }
        }
        return backjump_lvl;
    }

    void solver::process_antecedent_for_unsat_core(literal antecedent) {
        bool_var var     = antecedent.var();
        SASSERT(var < num_vars());
        TRACE(sat, tout << antecedent << " " << (is_marked(var)?"+":"-") << "\n";);
        if (!is_marked(var)) {
            mark(var);
            m_unmark.push_back(var);
            if (is_assumption(antecedent)) {
                m_core.push_back(antecedent);
            }
        }
    }

    void solver::process_consequent_for_unsat_core(literal consequent, justification const& js) {
        TRACE(sat, tout << "processing consequent: ";
              if (consequent == null_literal) tout << "null\n";
              else tout << consequent << "\n";
              display_justification(tout << "js kind: ", js) << "\n";);
        switch (js.get_kind()) {
        case justification::NONE:
            break;
        case justification::BINARY:
            SASSERT(consequent != null_literal);
            process_antecedent_for_unsat_core(~(js.get_literal()));
            break;
        case justification::CLAUSE: {
            clause & c = get_clause(js);
            unsigned i = 0;
            if (consequent != null_literal) {
                SASSERT(c[0] == consequent || c[1] == consequent);
                if (c[0] == consequent) {
                    i = 1;
                }
                else {
                    process_antecedent_for_unsat_core(~c[0]);
                    i = 2;
                }
            }
            unsigned sz = c.size();
            for (; i < sz; ++i)
                process_antecedent_for_unsat_core(~c[i]);
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            fill_ext_antecedents(consequent, js, false);
            for (literal l : m_ext_antecedents) {
                process_antecedent_for_unsat_core(l);
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }

    void solver::resolve_conflict_for_unsat_core() {
        TRACE(sat_verbose, display(tout);
              unsigned level = 0;
              for (literal l : m_trail) {
                  if (level != lvl(l)) {
                      level = lvl(l);
                      tout << level << ": ";
                  }
                  tout << l;
                  if (m_mark[l.var()]) {
                      tout << "*";
                  }
                  tout << " ";
              }
              tout << "\n";
              tout << "conflict level: " << m_conflict_lvl << "\n";
              );

        m_core.reset();
        if (!m_config.m_drat && m_conflict_lvl == 0) {
            return;
        }
        SASSERT(m_unmark.empty());
        DEBUG_CODE({
                for (literal lit : m_trail) {
                    SASSERT(!is_marked(lit.var()));
                }});

        unsigned old_size = m_unmark.size();
        int idx = skip_literals_above_conflict_level();

        literal consequent = m_not_l;
        if (m_not_l != null_literal) {
            justification js = m_justification[m_not_l.var()];
            TRACE(sat, tout << "not_l: " << m_not_l << "\n";
                  display_justification(tout, js) << "\n";);

            process_antecedent_for_unsat_core(m_not_l);
            if (is_assumption(~m_not_l)) {
                m_core.push_back(~m_not_l);
            }
            else {
                process_consequent_for_unsat_core(m_not_l, js);
            }
            consequent = ~m_not_l;
        }

        justification js = m_conflict;

        int init_sz = init_trail_size();
        while (true) {
            process_consequent_for_unsat_core(consequent, js);
            while (idx >= init_sz) {
                consequent = m_trail[idx];
                if (is_marked(consequent.var()) && lvl(consequent) == m_conflict_lvl)
                    break;
                idx--;
            }
            if (idx < init_sz) {
                break;
            }
            SASSERT(lvl(consequent) == m_conflict_lvl);
            js = m_justification[consequent.var()];
            idx--;
        }
        reset_unmark(old_size);
        if (m_core.size() > 1) {
            unsigned j = 0;
            for (unsigned i = 0; i < m_core.size(); ++i) {
                if (lvl(m_core[i]) > 0) m_core[j++] = m_core[i];            
            }
            m_core.shrink(j);
        }

        if (m_config.m_core_minimize) {
            if (m_min_core_valid && m_min_core.size() < m_core.size()) {
                IF_VERBOSE(2, verbose_stream() << "(sat.updating core " << m_min_core.size() << " " << m_core.size() << ")\n";);
                m_core.reset();
                m_core.append(m_min_core);
            }
            // TBD:
            // apply optional clause minimization by detecting subsumed literals.
            // initial experiment suggests it has no effect.
            m_mus(); // ignore return value on cancelation.
            set_model(m_mus.get_model(), !m_mus.get_model().empty());
            IF_VERBOSE(2, verbose_stream() << "(sat.core: " << m_core << ")\n";);
        }
    }


    unsigned solver::get_max_lvl(literal not_l, justification js, bool& unique_max) {
        unique_max = true;
        unsigned level = 0;

        if (not_l != null_literal) {
            level = lvl(not_l);
        }      
        TRACE(sat, tout << "level " << not_l << " is " << level << " " << js << "\n");

        switch (js.get_kind()) {
        case justification::NONE:
            level = std::max(level, js.level());
            break;
        case justification::BINARY:
            level = update_max_level(js.get_literal(), level, unique_max);
            break;
        case justification::CLAUSE: 
            for (literal l : get_clause(js)) 
                level = update_max_level(l, level, unique_max);
            break;
        case justification::EXT_JUSTIFICATION:
            if (not_l != null_literal) 
                not_l.neg();
            fill_ext_antecedents(not_l, js, true);
            for (literal l : m_ext_antecedents) 
                level = update_max_level(l, level, unique_max);
            break;
        default:
            UNREACHABLE();
            break;
        }
        TRACE(sat, tout << "max-level " << level << " " << unique_max << "\n");
        return level;
    }

    /**
       \brief Skip literals from levels above m_conflict_lvl.
       It returns an index idx such that lvl(m_trail[idx]) <= m_conflict_lvl, and
       for all idx' > idx, lvl(m_trail[idx']) > m_conflict_lvl
    */
    unsigned solver::skip_literals_above_conflict_level() {
        unsigned idx = m_trail.size();
        if (idx == 0) {
            return idx;
        }
        idx--;
        // skip literals from levels above the conflict level
        while (lvl(m_trail[idx]) > m_conflict_lvl) {
            SASSERT(idx > 0);
            idx--;
        }
        return idx;
    }

    void solver::process_antecedent(literal antecedent, unsigned & num_marks) {
        bool_var var     = antecedent.var();
        unsigned var_lvl = lvl(var);
        SASSERT(var < num_vars());
        TRACE(sat_verbose, tout << "process " << var << "@" << var_lvl << " marked " << is_marked(var) << " conflict " << m_conflict_lvl << "\n";);
        if (!is_marked(var) && var_lvl > 0) {
            // Guard against unassigned antecedents: after OTFS clause
            // strengthening, a reason clause may contain a literal whose
            // variable was unassigned by backtracking.  Its stale lvl()
            // could match m_conflict_lvl, corrupting num_marks and
            // m_max_marked_trail.  Skip such variables safely — they
            // contribute no information to the resolvent.
            if (value(antecedent) == l_undef)
                return;
            mark(var);
            // Polarity gradient: only when belief-based phase or combined
            // heuristic will actually read the values.  Saves ~5ns/antecedent
            // of wasted FP math under the default VSIDS+caching config.
            if (m_config.m_phase_strategy == PHS_BELIEF ||
                m_config.m_branching_heuristic == BH_COMBINED) {
                double ps = (value(var) == l_true) ? -1.0 : 1.0;
                double& belief = m_polarity_belief[var];
                double old_belief = belief;
                belief = 0.95 * belief + 0.05 * ps * m_conflict_bump_scale;
                if (belief > 1.0) belief = 1.0;
                else if (belief < -1.0) belief = -1.0;
                double delta = belief - old_belief;
                m_belief_update_ema = 0.99 * m_belief_update_ema + 0.01 * delta * delta;
            }
            // CaDiCaL-style: focused mode bumps ONLY the VMTF queue (recency);
            // stable mode bumps ONLY VSIDS/CHB scores.  Bumping both corrupts
            // VSIDS scores with focused-mode exploration noise, destroying the
            // benefit of having two independent heuristics.
            if (m_config.m_dual_mode && !m_stable_mode) {
                vmtf_bump(var);
            }
            else {
                switch (m_config.m_branching_heuristic) {
                case BH_VSIDS:
                    inc_activity_scaled(var);
                    break;
                case BH_CHB:
                    m_last_conflict[var] = m_stats.m_conflict;
                    break;
                case BH_ADAM:
                    adam_bump(var);
                    break;
                case BH_COMBINED:
                    adam_bump(var);
                    {
                        // Combined score: importance * (0.5 + confidence)
                        double importance = std::abs(m_adam_m1[var]) / (std::sqrt(m_adam_m2[var]) + 0.01);
                        double confidence = std::abs(m_polarity_belief[var]);
                        set_activity(var, importance * (0.5 + confidence));
                    }
                    break;
                case BH_MUON:
                    // Muon uses scaled VSIDS bumps (same as BH_VSIDS with
                    // m_conflict_bump_scale normalization applied via inc_activity_scaled).
                    inc_activity_scaled(var);
                    break;
                }
            }

            // CaDiCaL-style per-level seen tracking for minimization early abort.
            if (var_lvl >= m_level_info.size())
                m_level_info.resize(var_lvl + 1);
            level_info& li = m_level_info[var_lvl];
            if (li.seen_count++ == 0)
                m_active_levels.push_back(var_lvl);
            unsigned tpos = m_trail_pos[var];
            if (tpos < li.min_trail)
                li.min_trail = tpos;

            if (var_lvl == m_conflict_lvl) {
                num_marks++;
                // Track max trail position of conflict-level marks to handle
                // theory-propagated antecedents at out-of-order trail positions.
                if (tpos > m_max_marked_trail)
                    m_max_marked_trail = tpos;
            }
            else
                m_lemma.push_back(~antecedent);
        }
    }


    /**
       \brief On-the-fly strengthening (OTFS): remove pivot from clause c
       during conflict analysis. When the resolvent is smaller than the
       antecedent clause c, the antecedent can be strengthened by removing
       the resolved-away pivot literal.
       Based on CaDiCaL's on_the_fly_strengthen (analyze.cpp:770-865).
    */
    void solver::on_the_fly_strengthen(clause& c, literal pivot, clause_offset cls_off) {
        SASSERT(c.size() > 2);
        SASSERT(c.contains(pivot));

        unsigned old_sz = c.size();

        // Find pivot position in clause.
        unsigned pivot_pos = UINT_MAX;
        for (unsigned i = 0; i < old_sz; ++i) {
            if (c[i] == pivot) {
                pivot_pos = i;
                break;
            }
        }
        SASSERT(pivot_pos != UINT_MAX);

        bool pivot_was_watched = (pivot_pos == 0 || pivot_pos == 1);

        if (old_sz == 3) {
            // Shrinking ternary to binary: collect remaining literals.
            literal remaining[2];
            unsigned j = 0;
            for (unsigned i = 0; i < 3; ++i) {
                if (i != pivot_pos)
                    remaining[j++] = c[i];
            }
            SASSERT(j == 2);

            // Remove clause watches for both watched literals.
            erase_clause_watch(get_wlist(~c[0]), cls_off);
            erase_clause_watch(get_wlist(~c[1]), cls_off);

            // Add binary watches.
            bool learned = c.is_learned();
            get_bin_wlist(~remaining[0]).push_back(watched(remaining[1], learned));
            get_bin_wlist(~remaining[1]).push_back(watched(remaining[0], learned));

            // Update justification: propagated literal now justified by binary clause.
            literal propagated = null_literal;
            for (unsigned i = 0; i < 2; ++i) {
                if (value(remaining[i]) == l_true) {
                    propagated = remaining[i];
                    break;
                }
            }
            if (propagated != null_literal) {
                literal other = (remaining[0] == propagated) ? remaining[1] : remaining[0];
                m_justification[propagated.var()] = justification(lvl(propagated), ~other);
            }

            c.set_removed(true);
            m_stats.m_otfs_strengthened++;
            return;
        }

        // General case: clause size > 3, shrinking by one literal.
        if (pivot_was_watched) {
            unsigned other_watched_pos = (pivot_pos == 0) ? 1 : 0;
            literal other_watched = c[other_watched_pos];

            // Remove watch from ~pivot's list.
            erase_clause_watch(get_wlist(~pivot), cls_off);

            // Pick highest-level non-watched literal as replacement.
            unsigned best_pos = 2;
            unsigned best_lvl = lvl(c[2]);
            for (unsigned i = 3; i < old_sz; ++i) {
                unsigned l = lvl(c[i]);
                if (l > best_lvl) {
                    best_lvl = l;
                    best_pos = i;
                }
            }

            literal replacement = c[best_pos];
            c[pivot_pos] = replacement;
            if (best_pos != old_sz - 1)
                c[best_pos] = c[old_sz - 1];
            c.shrink(old_sz - 1);

            // Add watch for ~replacement.
            literal block_lit = c[c.size() >> 1];
            get_wlist(~replacement).push_back(watched(block_lit, cls_off));

            // Update blocked literal in the other watch.
            watch_list& owlist = get_wlist(~other_watched);
            for (auto& w : owlist) {
                if (w.is_clause() && w.get_clause_offset() == cls_off) {
                    w.set_blocked_literal(block_lit);
                    break;
                }
            }
        }
        else {
            // Pivot not watched (position >= 2): swap with last and shrink.
            if (pivot_pos != old_sz - 1)
                std::swap(c[pivot_pos], c[old_sz - 1]);
            c.shrink(old_sz - 1);

            // Update blocked literal in both watch lists.
            literal new_block = c[c.size() >> 1];
            for (unsigned w = 0; w < 2; ++w) {
                watch_list& wl = get_wlist(~c[w]);
                for (auto& we : wl) {
                    if (we.is_clause() && we.get_clause_offset() == cls_off) {
                        we.set_blocked_literal(new_block);
                        break;
                    }
                }
            }
        }

        // CaDiCaL: clamp glue to size-1 after OTFS shrink.
        if (c.is_learned() && c.glue() >= c.size())
            c.set_glue(c.size() - 1);
        c.mark_used();
        m_stats.m_otfs_strengthened++;
    }

    /**
       \brief js is an external justification. Collect its antecedents and store at m_ext_antecedents.
    */
    void solver::fill_ext_antecedents(literal consequent, justification js, bool probing) {
        SASSERT(js.is_ext_justification());
        SASSERT(m_ext);
        auto idx = js.get_ext_justification_idx();
        m_ext_antecedents.reset();
        m_ext->get_antecedents(consequent, idx, m_ext_antecedents, probing);
    }

    bool solver::is_two_phase() const {
        return m_config.m_phase == PS_SAT_CACHING || m_config.m_phase == PS_LOCAL_SEARCH;
    }

    bool solver::is_sat_phase() const {
        return is_two_phase() && m_search_state == s_sat;
    }

    // CaDiCaL-style target and best phase update (analyze.cpp update_target_and_best).
    // Called at the start of conflict analysis, before backjumping.
    //
    // Uses the full trail size (all assigned variables at the moment of
    // conflict), matching CaDiCaL: every literal on the trail was propagated
    // without contradiction -- the conflict was found on the NEXT propagation.
    //
    // Target phase: deepest trail since last rephase (reset on rephase).
    // Best phase: deepest trail ever since last rephase (also reset on rephase).
    // Both provide "guided restart" memory for the solver.
    void solver::update_target_phase() {
        if (m_conflict_lvl == 0)
            return;
        unsigned assigned = m_trail.size();
        if (assigned > m_target_assigned) {
            m_target_assigned = assigned;
            for (unsigned i = 0; i < assigned; ++i) {
                literal  lit = m_trail[i];
                bool_var v   = lit.var();
                m_target_phase[v] = lit.sign() ? l_false : l_true;
            }
            IF_VERBOSE(12, verbose_stream() << "target trail: " << assigned << "\n");
        }
    }

    void solver::updt_phase_of_vars() {
        if (m_config.m_phase == PS_FROZEN)
            return;
        update_target_phase();
        unsigned from_lvl = m_conflict_lvl;
        unsigned head = from_lvl == 0 ? 0 : m_scopes[from_lvl - 1].m_trail_lim;
        unsigned sz   = m_trail.size();
        // Save current assignment as the "saved" phase for variables
        // at or above the conflict level (these will be unassigned).
        for (unsigned i = head; i < sz; ++i) {
            bool_var v = m_trail[i].var();
            m_phase[v] = !m_trail[i].sign();
        }
        // CaDiCaL unconditionally tracks the best (longest-ever) assignment
        // on every conflict (analyze.cpp update_target_and_best).
        // Uses full trail size, not just the prefix below conflict level.
        if (sz > m_best_phase_size) {
            m_best_phase_size = sz;
            IF_VERBOSE(12, verbose_stream() << "best trail: " << sz << "\n");
            for (unsigned i = 0; i < sz; ++i) {
                bool_var v = m_trail[i].var();
                m_best_phase[v] = !m_trail[i].sign();
            }
            set_has_new_best_phase(true);
        }
    }

    bool solver::should_toggle_search_state() {
        if (m_search_state == s_unsat) {
            m_trail_avg.update(m_trail.size());
        }
        return 
            (m_phase_counter >= m_search_next_toggle) &&
            (m_search_state == s_sat || m_trail.size() > 0.50*m_trail_avg);  
    }

    void solver::do_toggle_search_state() {

        if (is_two_phase()) {
            // In dual mode, stable/focused switching is handled by stabilizing()
            // and best phase should persist across mode switches (CaDiCaL never
            // resets best on mode switch). Only reset in legacy two-phase mode.
            if (!m_config.m_dual_mode)
                m_best_phase_size = 0;
            std::swap(m_fast_glue_backup, m_fast_glue_avg);
            std::swap(m_slow_glue_backup, m_slow_glue_avg);
            if (m_search_state == s_sat) {
                m_search_unsat_conflicts += m_config.m_search_unsat_conflicts;
            }
            else {
                m_search_sat_conflicts += m_config.m_search_sat_conflicts;
            }
        }

        if (m_search_state == s_unsat) {
            m_search_state = s_sat;
            m_search_next_toggle = m_search_sat_conflicts;
        }
        else {
            m_search_state = s_unsat;
            m_search_next_toggle = m_search_unsat_conflicts;
        }

        // Reset reluctant doubling on search state toggle so each
        // phase starts with a fresh Luby sequence.
        reluctant_enable();

        m_phase_counter = 0;
    }

    bool solver::should_rephase() {
        // Belief mode accumulates polarity signal from conflict gradients
        // and does not use the phase cache cascade (target/best/saved) for
        // decisions.  Rephasing mutates m_phase[] which is only a neutral
        // fallback for belief==0.0 variables -- overwriting it with random,
        // inverted, or best-phase values would fight the belief signal.
        // The expensive ProbSAT walk is also unnecessary.
        if (m_config.m_phase_strategy == PHS_BELIEF)
            return false;
        return m_conflicts_since_init > m_rephase_lim;
    }

    // -----------------------------------------------------------------------
    // CaDiCaL-style rephase strategies
    // -----------------------------------------------------------------------

    // Set all phases to the default initial value (false = negative polarity).
    char solver::rephase_original() {
        m_rephase_original++;
        for (auto& p : m_phase) p = false;
        IF_VERBOSE(12, verbose_stream() << "(rephase :type original :count " << m_rephase_original << ")\n");
        return 'O';
    }

    // Set all phases to the inverted default (true = positive polarity).
    char solver::rephase_inverted() {
        m_rephase_inverted++;
        for (auto& p : m_phase) p = true;
        IF_VERBOSE(12, verbose_stream() << "(rephase :type inverted :count " << m_rephase_inverted << ")\n");
        return 'I';
    }

    // Flip every phase individually.
    char solver::rephase_flipping() {
        m_rephase_flipping++;
        for (auto& p : m_phase) p = !p;
        IF_VERBOSE(12, verbose_stream() << "(rephase :type flipping :count " << m_rephase_flipping << ")\n");
        return 'F';
    }

    // Set all phases randomly.
    // Uses a local RNG seeded from the solver's RNG (like CaDiCaL's rephase_random
    // which creates a local Random from opts.seed + count) to avoid perturbing
    // the main solver RNG stream used by other heuristics.
    char solver::rephase_random() {
        m_rephase_random++;
        random_gen rng(m_rand());
        for (auto& p : m_phase) p = (rng() % 2) == 0;
        IF_VERBOSE(12, verbose_stream() << "(rephase :type random :count " << m_rephase_random << ")\n");
        return '#';
    }

    // Copy best-phase assignment into current phase (CaDiCaL: rephase_best).
    char solver::rephase_best() {
        m_rephase_best++;
        if (m_best_phase_size > 0) {
            for (unsigned i = 0; i < m_phase.size(); ++i)
                m_phase[i] = m_best_phase[i];
        }
        IF_VERBOSE(12, verbose_stream() << "(rephase :type best :count " << m_rephase_best
                   << " :best_depth " << m_best_phase_size << ")\n");
        return 'B';
    }

    // Run in-place ProbSAT walker with effort-proportional budget.
    // The walker writes results directly to m_phase and m_best_phase
    // via probsat::export_best.
    // When max_flips == 0 (default), compute budget from CDCL conflict delta.
    bool solver::run_probsat(unsigned max_flips) {
        if (max_flips == 0) {
            // Compute walk budget proportional to CDCL conflicts since last walk.
            // CaDiCaL uses walkeffort=80 (per mille): budget = delta_ticks * 0.08
            // Minimum 5000 to ensure meaningful exploration; max 500000 to bound latency.
            unsigned conflicts_delta = m_conflicts_since_init - m_conflicts_at_last_walk;
            m_conflicts_at_last_walk = m_conflicts_since_init;
            uint64_t raw_budget = static_cast<uint64_t>(conflicts_delta) * static_cast<uint64_t>(num_vars()) / 1000;
            max_flips = std::max(5000u, std::min(500000u,
                static_cast<unsigned>(std::min(raw_budget, static_cast<uint64_t>(UINT_MAX)))));
        }
        return m_probsat(*this, max_flips);
    }

    // Trigger local search 'walk' to find a phase assignment that minimizes
    // the number of falsified clauses. This is the CaDiCaL rephase_walk analog.
    //
    // CaDiCaL reference: rephase.cpp:100-109, walk.cpp:1048-1086
    //   - Backtracks to level 0
    //   - Runs walk_round with budget = delta_ticks * walkeffort * 1e-3
    //   - walk saves best assignment to phases.saved
    //
    // In Z3 we use the lightweight in-place ProbSAT walker (sat_probsat.cpp)
    // which operates directly on the solver's clause pool without copying.
    char solver::rephase_walk() {
        m_rephase_walk++;

        // Backtrack to decision level 0 (CaDiCaL's backtrack() in walk())
        if (scope_lvl() > search_lvl())
            pop_reinit(scope_lvl() - search_lvl());

        // Run ProbSAT walk -- writes results directly to m_phase and m_best_phase
        run_probsat();

        IF_VERBOSE(12, verbose_stream() << "(rephase :type walk :count " << m_rephase_walk << ")\n");
        return 'W';
    }

    void solver::do_rephase() {
        char type = 0;
        unsigned count = m_rephase.count;

        switch (m_config.m_phase) {
        case PS_ALWAYS_TRUE:
            for (auto& p : m_phase) p = true;
            type = 'T';
            break;
        case PS_ALWAYS_FALSE:
            for (auto& p : m_phase) p = false;
            type = '0';
            break;
        case PS_FROZEN:
            type = 'Z';
            break;
        case PS_RANDOM:
            type = rephase_random();
            break;

        case PS_BASIC_CACHING:
            // Rich rephase schedule interleaving "best" (most effective strategy
            // from CaDiCaL) with diversification strategies.
            //
            // 8-cycle: best, random, best, original, best, flipping, best, walk
            //
            // "Best" appears in every other slot because it exploits the solver's
            // memory of its deepest conflict-free assignment -- the single most
            // impactful rephase strategy. Between best slots, we cycle through
            // diversification: random (entropy), original (reset to negative),
            // flipping (complement), and walk (local search guidance).
            //
            // Best-phase tracking is unconditional in updt_phase_of_vars(),
            // and m_best_phase_size resets each rephase for PS_BASIC_CACHING.
            switch (count % 8) {
            case 0: type = rephase_best();     break;
            case 1: type = rephase_random();   break;
            case 2: type = rephase_best();     break;
            case 3: type = rephase_original(); break;
            case 4: type = rephase_best();     break;
            case 5: type = rephase_flipping(); break;
            case 6: type = rephase_best();     break;
            case 7: type = rephase_walk();     break;
            default: UNREACHABLE();            break;
            }
            break;

        case PS_SAT_CACHING:
        case PS_LOCAL_SEARCH:
            // Search-state-aware rephasing with walk integration.
            //
            // s_sat (stable): best-heavy 8-cycle with walk for guidance:
            //   best, walk, best, original, best, flipping, best, inverted
            //
            // s_unsat (focused): standard CaDiCaL schedule balancing
            // exploitation and exploration:
            //   original, inverted, (best, walk, original, best, walk, inverted)^w
            if (m_search_state == s_sat) {
                switch (count % 8) {
                case 0: type = rephase_best();     break;
                case 1: type = rephase_walk();     break;
                case 2: type = rephase_best();     break;
                case 3: type = rephase_original(); break;
                case 4: type = rephase_best();     break;
                case 5: type = rephase_flipping(); break;
                case 6: type = rephase_best();     break;
                case 7: type = rephase_inverted(); break;
                default: UNREACHABLE();            break;
                }
            }
            else {
                if (count == 0)
                    type = rephase_original();
                else if (count == 1)
                    type = rephase_inverted();
                else {
                    switch ((count - 2) % 6) {
                    case 0: type = rephase_best();     break;
                    case 1: type = rephase_walk();     break;
                    case 2: type = rephase_original(); break;
                    case 3: type = rephase_best();     break;
                    case 4: type = rephase_walk();     break;
                    case 5: type = rephase_inverted(); break;
                    default: UNREACHABLE();            break;
                    }
                }
            }
            break;

        default:
            UNREACHABLE();
            break;
        }

        IF_VERBOSE(12, verbose_stream() << "(rephase :round " << count << " :type " << type << ")\n");

        // CaDiCaL-style: shuffle variable activities after rephasing for
        // search diversification (rephase.cpp lines 397-399).
        if (m_config.m_rephase_shuffle)
            shuffle_activity_on_rephase();

        // Reset target phase depth on rephase to allow re-discovery of a new
        // deepest conflict-free assignment (following CaDiCaL's approach).
        m_target_assigned = 0;

        // For PS_BASIC_CACHING, also reset best-phase depth so the solver can
        // discover a new best assignment after rephasing. In two-phase modes
        // (PS_SAT_CACHING, PS_LOCAL_SEARCH) this reset happens in
        // do_toggle_search_state() when switching between stable/focused.
        if (m_config.m_phase == PS_BASIC_CACHING)
            m_best_phase_size = 0;

        // Arithmetically increasing rephase interval (CaDiCaL: delta = rephaseint * (total+1))
        m_rephase_inc += m_config.m_rephase_base;
        m_rephase_lim += m_rephase_inc;
        m_rephase.inc(m_conflicts_since_init, num_clauses());
    }

    // CaDiCaL-style activity perturbation after rephasing.
    // Multiplies each unassigned variable's activity by a random factor
    // in [0.9, 1.1), providing mild diversification of the variable
    // ordering without destroying the overall learned score ranking.
    // This is lighter than do_reorder() which does a full softmax
    // redistribution; here we just jitter the existing scores.
    void solver::shuffle_activity_on_rephase() {
        for (bool_var v = num_vars(); v-- > 0; ) {
            if (was_eliminated(v) || value(v) != l_undef)
                continue;
            // Generate a random factor in [0.9, 1.1):
            //   m_rand() returns [0, 0x7fff], so r/max is in [0,1].
            //   factor = 0.9 + 0.2 * (r / max_value)
            double r = static_cast<double>(m_rand()) / static_cast<double>(random_gen::max_value());
            double factor = 0.9 + 0.2 * r;
            double old_act = m_activity[v];
            double new_act = old_act * factor;
            if (new_act != old_act) {
                m_activity[v] = new_act;
                m_case_split_queue.activity_changed_eh(v, new_act > old_act);
            }
        }
    }

    bool solver::should_reorder() {
        return m_reorder.should_apply(m_conflicts_since_init);
    }

    void solver::do_reorder() {
        IF_VERBOSE(1, verbose_stream() << "(reorder)\n");
        m_activity_inc = 1.0;
        svector<bool_var> vars;
        for (bool_var v = num_vars(); v-- > 0; ) {
            if (!was_eliminated(v) && value(v) == l_undef) {            
                vars.push_back(v);
            }
        }
#if 1
        // 
        //   exp(logits[i]) / sum(exp(logits)) 
        // = 
        //   exp(log(exp(logits[i]) / sum(exp(logits)))) 
        // = 
        //   exp(log(exp(logits[i])) - log(sum(exp(logits)))) 
        // =
        //   exp(logits[i] - lse)
        svector<double> logits(vars.size(), 0.0);
        double itau = m_config.m_reorder_itau;
        double lse = 0;
        double mid = (double)(m_rand.max_value()/2);
        double max = 0;
        for (double& f : logits) {
            f = itau * (m_rand() - mid)/mid;
            if (f > max) max = f;
        }
        for (double f : logits) {
            lse += exp(f - max);
        }
        lse = max + log(lse);

        for (unsigned i = 0; i < vars.size(); ++i) {
            update_activity(vars[i], exp(logits[i] - lse));
        }
#else
        shuffle(vars.size(), vars.c_ptr(), m_rand);
        for (bool_var v : vars) {
            update_activity(v, m_rand(10)/10.0);
        }
#endif
        m_reorder.inc(m_conflicts_since_init, num_clauses());
    }

    void solver::updt_phase_counters() {
        m_phase_counter++;
        if (should_toggle_search_state()) {
            do_toggle_search_state();
        }
    }

    /**
       \brief Return the number of different levels in lits.
       All literals in lits must be assigned.
    */
    unsigned solver::num_diff_levels(unsigned num, literal const * lits) {
        m_diff_levels.reserve(scope_lvl() + 1, false);
        unsigned r = 0;
        for (unsigned i = 0; i < num; ++i) {
            SASSERT(value(lits[i]) != l_undef);
            unsigned lit_lvl = lvl(lits[i]);
            if (!m_diff_levels[lit_lvl]) {
                m_diff_levels[lit_lvl] = true;
                r++;
            }
        }
        // reset m_diff_levels.
        for (unsigned i = 0; i < num; ++i)
            m_diff_levels[lvl(lits[i])] = false;
        return r;
    }

    bool solver::num_diff_levels_below(unsigned num, literal const* lits, unsigned max_glue, unsigned& glue) {
        m_diff_levels.reserve(scope_lvl() + 1, false);
        glue = 0;
        unsigned i = 0;
        for (; i < num && glue < max_glue; ++i) {
            SASSERT(value(lits[i]) != l_undef);
            unsigned lit_lvl = lvl(lits[i]);
            if (!m_diff_levels[lit_lvl]) {
                m_diff_levels[lit_lvl] = true;
                glue++;
            }
        }       
        // reset m_diff_levels.
        for (; i-- > 0; )
            m_diff_levels[lvl(lits[i])] = false;
        return glue < max_glue;        
    }

    bool solver::num_diff_false_levels_below(unsigned num, literal const* lits, unsigned max_glue, unsigned& glue) {
        m_diff_levels.reserve(scope_lvl() + 1, false);
        glue = 0;
        unsigned i = 0;
        for (; i < num && glue < max_glue; ++i) {
            if (value(lits[i]) == l_false) {
                unsigned lit_lvl = lvl(lits[i]);
                if (!m_diff_levels[lit_lvl]) {
                    m_diff_levels[lit_lvl] = true;
                    glue++;
                }
            }
        }
        // reset m_diff_levels.
        for (; i-- > 0;) {
            literal lit = lits[i];
            if (value(lit) == l_false) {
                VERIFY(lvl(lit) < m_diff_levels.size());
                m_diff_levels[lvl(lit)] = false;
            }
        }
        return glue < max_glue;        
    }


    /**
       \brief Process an antecedent for lemma minimization.
    */
    bool solver::process_antecedent_for_minimization(literal antecedent) {
        bool_var var = antecedent.var();
        unsigned var_lvl = lvl(var);
        if (!is_marked(var) && var_lvl > 0) {
            // cached success: var already proven removable in this minimization round
            if (m_removable[var])
                return true;
            // cached failure: var already proven non-removable in this minimization round
            if (m_poison[var])
                return false;
            if (m_lvl_set.may_contain(var_lvl)) {
                mark(var);
                m_unmark.push_back(var);
                m_lemma_min_stack.push_back(antecedent);
            }
            else {
                return false;
            }
        }
        return true;
    }

    /**
       \brief Return true if lit is implied by other marked literals
       and/or literals assigned at the base level.
       The set lvl_set is used as an optimization.
       The idea is to stop the recursive search with a failure
       as soon as we find a literal assigned in a level that is not in lvl_set.
    */
    bool solver::implied_by_marked(literal lit) {
        m_lemma_min_stack.reset();
        unsigned old_size = m_unmark.size();
        bool_var initial_var = lit.var();

        // CaDiCaL early-abort heuristics A and B at depth 0.
        {
            unsigned v0_lvl = lvl(initial_var);
            if (v0_lvl > 0 && v0_lvl < m_level_info.size()) {
                level_info const& li = m_level_info[v0_lvl];
                // (A) Knuth: only one literal seen on this level => essential.
                if (li.seen_count < 2)
                    return false;
                // (B) Assigned at or before earliest seen => not implied.
                if (m_trail_pos[initial_var] <= li.min_trail)
                    return false;
            }
        }

        m_lemma_min_stack.push_back(lit);
        unsigned steps = 0;

        while (!m_lemma_min_stack.empty()) {
            // Heuristic C: work limit (CaDiCaL minimizedepth default 1000).
            if (steps++ > 1000)
                goto fail;
            // CaDiCaL-style tick: each variable explored during minimization
            // is one unit of search work (minimize.cpp:36 in CaDiCaL).
            ++m_search_ticks;
            lit = m_lemma_min_stack.back();
            bool_var var = lit.var();
            m_lemma_min_stack.pop_back();

            // Heuristic B at depth > 0.
            {
                unsigned var_lvl = lvl(var);
                if (var_lvl > 0 && var_lvl < m_level_info.size()) {
                    if (m_trail_pos[var] <= m_level_info[var_lvl].min_trail)
                        goto fail;
                }
            }

            justification const& js   = m_justification[var];
            switch(js.get_kind()) {
            case justification::NONE:
                if (lvl(var) > 0)
                    goto fail;
                break;
            case justification::BINARY:
                if (!process_antecedent_for_minimization(~(js.get_literal())))
                    goto fail;
                break;
            case justification::CLAUSE: {
                clause & c = get_clause(js);
                unsigned i   = 0;
                if (c[0].var() == var) {
                    i = 1;
                }
                else {
                    SASSERT(c[1].var() == var);
                    if (!process_antecedent_for_minimization(~c[0]))
                        goto fail;
                    i = 2;
                }
                unsigned sz = c.size();
                for (; i < sz; ++i) {
                    if (!process_antecedent_for_minimization(~c[i]))
                        goto fail;
                }
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                literal consequent(var, value(var) == l_false);
                fill_ext_antecedents(consequent, js, false);
                for (literal l : m_ext_antecedents) {
                    if (!process_antecedent_for_minimization(l))
                        goto fail;
                }
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
            TRACE(sat_conflict,
                  display_justification(tout << var << " ",js) << "\n";);
        }
        // success: cache all newly explored vars as removable
        for (unsigned i = old_size; i < m_unmark.size(); ++i) {
            bool_var v = m_unmark[i];
            if (!m_removable[v]) {
                m_removable[v] = true;
                m_minimized_vars.push_back(v);
            }
        }
        return true;

    fail:
        reset_unmark(old_size);
        if (!m_poison[initial_var]) {
            m_poison[initial_var] = true;
            m_minimized_vars.push_back(initial_var);
        }
        return false;
    }

    /**
       \brief Restore the size of m_unmark to old_size, and
       unmark variables at positions [old_size, m_unmark.size()).
    */
    void solver::reset_unmark(unsigned old_size) {
        unsigned curr_size = m_unmark.size();
        for(unsigned i = old_size; i < curr_size; ++i)
            reset_mark(m_unmark[i]);
        m_unmark.shrink(old_size);
    }


    void solver::reset_level_info() {
        for (unsigned lvl : m_active_levels)
            m_level_info[lvl].reset();
        m_active_levels.reset();
    }

    /**
       \brief Store the levels of the literals at m_lemma in the
       approximated set m_lvl_set.
    */
    void solver::updt_lemma_lvl_set() {
        m_lvl_set.reset();
        for (literal l : m_lemma) 
            m_lvl_set.insert(lvl(l));
    }

    /**
       \brief Minimize lemma using binary resolution
    */
    bool solver::minimize_lemma_binres() {
        SASSERT(!m_lemma.empty());
        SASSERT(m_unmark.empty());
        unsigned sz   = m_lemma.size();
        unsigned num_reduced = 0;
        for (unsigned i = 1; i < sz; ++i) {
            mark_lit(m_lemma[i]);            
        }
        watch_list const& bin_wlist = get_bin_wlist(m_lemma[0]);
        for (watched const& w : bin_wlist) {
            SASSERT(w.is_binary_clause());
            if (is_marked_lit(w.get_literal())) {
                unmark_lit(~w.get_literal());
                num_reduced++;
            }
        }
        if (num_reduced > 0) {
            unsigned j = 1;
            for (unsigned i = 1; i < sz; ++i) {
                if (is_marked_lit(m_lemma[i])) {
                    m_lemma[j++] = m_lemma[i];
                    unmark_lit(m_lemma[i]);
                }
            }
            m_lemma.shrink(j);
        }

        return num_reduced > 0;
    }

    // -----------------------------------------------------------------------
    // Per-level UIP clause shrinking (CaDiCaL technique)
    // -----------------------------------------------------------------------

    int solver::shrink_literal(literal lit, unsigned blevel, bool resolve_large) {
        bool_var v = lit.var();
        unsigned v_lvl = lvl(v);
        if (v_lvl == 0) return 0;
        if (m_shrinkable.get(v, false)) return 0;
        if (v_lvl != blevel) {
            // v_lvl < blevel: lower-level literal, check if implied by lemma.
            // v_lvl > blevel: can happen with chronological backtracking
            //   (out-of-order trail entries). Treat the same as lower-level.
            if (is_marked(v)) return 0;
            if (v_lvl < blevel && implied_by_marked(lit)) return 0;
            return -1;
        }
        m_shrinkable[v] = true;
        m_shrinkable_vars.push_back(v);
        return 1;
    }

    bool solver::shrink_block(unsigned block_begin, unsigned block_end) {
        SASSERT(block_end > block_begin);
        SASSERT(m_shrinkable_vars.empty());
        unsigned blevel = lvl(m_lemma[block_begin]);
        bool resolve_large = (m_config.m_shrink >= 2);
        unsigned max_tp = 0;
        unsigned open = 0;
        for (unsigned i = block_begin; i <= block_end; ++i) {
            bool_var v = m_lemma[i].var();
            unsigned tpos = m_trail_pos[v];
            if (tpos > max_tp) max_tp = tpos;
            m_shrinkable[v] = true;
            m_shrinkable_vars.push_back(v);
            open++;
        }
        bool failed = false;
        unsigned pos = max_tp;
        int uip_pos = -1;
        while (!failed) {
            while (pos < m_trail.size()) {
                bool_var v = m_trail[pos].var();
                if (m_shrinkable.get(v, false) && lvl(v) == blevel) break;
                if (pos == 0) { failed = true; break; }
                pos--;
            }
            if (failed) break;
            literal trail_lit = m_trail[pos];
            bool_var v = trail_lit.var();
            open--;
            if (open == 0) { uip_pos = pos; break; }
            justification js = m_justification[v];
            switch (js.get_kind()) {
            case justification::NONE:
                failed = true;
                break;
            case justification::BINARY: {
                int r = shrink_literal(~js.get_literal(), blevel, resolve_large);
                if (r < 0) failed = true;
                else if (r > 0) open++;
                break;
            }
            case justification::CLAUSE: {
                if (!resolve_large) { failed = true; break; }
                clause & c = get_clause(js);
                for (unsigned ci = 0; ci < c.size(); ++ci) {
                    if (c[ci] == trail_lit) continue;
                    int r = shrink_literal(~c[ci], blevel, resolve_large);
                    if (r < 0) { failed = true; break; }
                    if (r > 0) open++;
                }
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                if (!resolve_large) { failed = true; break; }
                fill_ext_antecedents(trail_lit, js, false);
                for (literal l : m_ext_antecedents) {
                    int r = shrink_literal(l, blevel, resolve_large);
                    if (r < 0) { failed = true; break; }
                    if (r > 0) open++;
                }
                break;
            }
            default: failed = true; break;
            }
            if (pos == 0 && !failed && open > 0) failed = true;
            if (!failed && pos > 0) pos--;
        }
        for (bool_var w : m_shrinkable_vars) m_shrinkable[w] = false;
        m_shrinkable_vars.reset();
        if (failed || uip_pos < 0) return false;
        literal uip = ~m_trail[uip_pos];
        bool_var old_begin_var = m_lemma[block_begin].var();
        m_lemma[block_begin] = uip;
        bool_var uip_var = uip.var();
        // Reset mark on the replaced block-begin literal if it's a different variable
        // than the UIP, since it will no longer appear in m_lemma.
        if (old_begin_var != uip_var && is_marked(old_begin_var))
            reset_mark(old_begin_var);
        if (!is_marked(uip_var)) mark(uip_var);
        unsigned shrunken = 0;
        for (unsigned i = block_begin + 1; i <= block_end; ++i) {
            literal old_lit = m_lemma[i];
            if (is_marked(old_lit.var())) reset_mark(old_lit.var());
            m_lemma[i] = null_literal;
            shrunken++;
        }
        m_stats.m_shrunken_lits += shrunken;
        return true;
    }

    void solver::shrink_lemma() {
        unsigned sz = m_lemma.size();
        if (sz <= 2) return;
        m_shrinkable.reserve(num_vars(), false);
        // Populate m_lvl_set so that implied_by_marked (called from
        // shrink_literal for lower-level literals) can use the level
        // filter in process_antecedent_for_minimization.
        updt_lemma_lvl_set();
        std::sort(m_lemma.data() + 1, m_lemma.data() + sz,
            [this](literal a, literal b) {
                unsigned la = lvl(a), lb = lvl(b);
                if (la != lb) return la > lb;
                return m_trail_pos[a.var()] > m_trail_pos[b.var()];
            });
        unsigned total_shrunken = 0;
        unsigned i = 1;
        while (i < sz) {
            unsigned blvl = lvl(m_lemma[i]);
            if (blvl == 0) break;
            unsigned bstart = i, bend = i;
            while (bend + 1 < sz && lvl(m_lemma[bend + 1]) == blvl) bend++;
            if (bend > bstart) {
                if (shrink_block(bstart, bend))
                    total_shrunken += (bend - bstart);
            }
            i = bend + 1;
        }
        // Clean up marks and memoization state accumulated by implied_by_marked
        // calls inside shrink_literal. Without this, minimize_lemma's
        // SASSERT(m_unmark.empty()) would fire, and stale removable/poison
        // flags would contaminate the subsequent minimization pass.
        reset_unmark(0);
        clear_minimized_lits();

        if (total_shrunken == 0) return;
        unsigned j = 1;
        for (i = 1; i < sz; ++i)
            if (m_lemma[i] != null_literal)
                m_lemma[j++] = m_lemma[i];
        m_lemma.shrink(j);
    }

    /**
       \brief Minimize the number of literals in m_lemma. The main idea is to remove
       literals that are implied by other literals in m_lemma and/or literals
       assigned at level 0.
    */
    bool solver::minimize_lemma() {
        SASSERT(!m_lemma.empty());
        SASSERT(m_unmark.empty());
        updt_lemma_lvl_set();

        unsigned sz   = m_lemma.size();

        // CaDiCaL-style: sort the learned clause by ascending trail position
        // before minimization.  Processing literals in trail order ensures that
        // antecedents of earlier-assigned literals are already marked when we
        // reach later ones, reducing the recursion depth of implied_by_marked.
        if (sz > 2) {
            std::sort(m_lemma.data() + 1, m_lemma.data() + sz,
                [this](literal a, literal b) {
                    return m_trail_pos[a.var()] < m_trail_pos[b.var()];
                });
        }

        unsigned i    = 1; // the first literal is the FUIP
        unsigned j    = 1;
        for (; i < sz; ++i) {
            literal l = m_lemma[i];
            if (implied_by_marked(l)) {
                m_unmark.push_back(l.var());
            }
            else {
                m_lemma[j++] = m_lemma[i];
            }
        }

        reset_unmark(0);
        clear_minimized_lits();
        m_lemma.shrink(j);
        m_stats.m_minimized_lits += sz - j;
        return j < sz;
    }

    /**
       \brief Bulk-clear poison and removable flags set during minimization.
    */
    void solver::clear_minimized_lits() {
        for (bool_var v : m_minimized_vars) {
            m_poison[v] = false;
            m_removable[v] = false;
        }
        m_minimized_vars.reset();
    }

    /**
       \brief Reset the mark of the variables in the current lemma.
    */
    void solver::reset_lemma_var_marks() {
        // Reason-side bumping applies to VSIDS, ADAM, and COMBINED.
        // bump_reason_literals() has its own heuristic guard internally.
        bump_reason_literals();        
        literal_vector::iterator it  = m_lemma.begin();
        literal_vector::iterator end = m_lemma.end();
        SASSERT(!is_marked((*it).var()));
        ++it;
        for(; it != end; ++it) {
            bool_var var = (*it).var();
            reset_mark(var);
        }
    }

    void solver::update_lrb_reasoned() {
        unsigned sz = m_lemma.size();
        SASSERT(!is_marked(m_lemma[0].var()));
        mark(m_lemma[0].var());
        for (unsigned i = m_lemma.size(); i-- > 0; ) {
            // CaDiCaL-style tick: reason-side bumping traverses clauses,
            // analogous to analyze.cpp:370 in CaDiCaL.
            ++m_search_ticks;
            justification js = m_justification[m_lemma[i].var()];
            switch (js.get_kind()) {
            case justification::NONE:
                break;
            case justification::BINARY:
                update_lrb_reasoned(js.get_literal());
                break;
            case justification::CLAUSE: {
                clause & c = get_clause(js);
                for (literal l : c) {
                    update_lrb_reasoned(l);
                }
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                fill_ext_antecedents(~m_lemma[i], js, true);
                for (literal l : m_ext_antecedents) {
                    update_lrb_reasoned(l);
                }
                break;
            }
            }
        }
        reset_mark(m_lemma[0].var());
        for (unsigned i = m_lemma.size(); i-- > sz; ) {
            reset_mark(m_lemma[i].var());
        }
        m_lemma.shrink(sz);
    }

    void solver::update_lrb_reasoned(literal lit) {
        bool_var v = lit.var();
        if (!is_marked(v)) {
            mark(v);
            m_reasoned[v]++;
            inc_activity(v);
            m_lemma.push_back(lit);
        }
    }

    // CaDiCaL-style reason-side literal bumping for VSIDS (analyze.cpp:342-424).
    void solver::bump_reason_literals() {
        if (!m_config.m_bump_reason ||
            (m_config.m_branching_heuristic != BH_VSIDS && m_config.m_branching_heuristic != BH_ADAM &&
             m_config.m_branching_heuristic != BH_COMBINED && m_config.m_branching_heuristic != BH_MUON) ||
            m_lemma.empty())
            return;
        // CaDiCaL-style: reason-side bumping is a VSIDS-only technique.
        // In focused mode, VMTF recency is the sole signal -- skip reason
        // bumping to avoid corrupting VSIDS scores and wasting time.
        if (m_config.m_dual_mode && !m_stable_mode)
            return;
        uint64_t decisions_this = m_stats.m_decision - m_decisions_at_last_conflict;
        m_decisions_at_last_conflict = m_stats.m_decision;
        m_decisions_per_conflict += 1e-4 * (decisions_this - m_decisions_per_conflict);
        if (m_decisions_per_conflict > m_config.m_bump_reason_rate)
            return;
        if (m_bump_reason_delay > 0) { m_bump_reason_delay--; return; }
        unsigned depth_limit = m_config.m_bump_reason_depth;
        SASSERT(depth_limit > 0);
        unsigned saved_sz = m_lemma.size();
        unsigned bump_limit = saved_sz * m_config.m_bump_reason_limit;
        unsigned bump_count = 0;
        SASSERT(!is_marked(m_lemma[0].var()));
        mark(m_lemma[0].var());
        for (unsigned i = 0; i < saved_sz && bump_count <= bump_limit; ++i)
            bump_reason_literals_recursive(m_lemma[i], depth_limit, bump_count, bump_limit);
        bool limit_exhausted = (bump_count > bump_limit);
        if (limit_exhausted) {
            for (unsigned i = m_lemma.size(); i-- > saved_sz; ) {
                SASSERT(is_marked(m_lemma[i].var()));
                reset_mark(m_lemma[i].var());
            }
            m_lemma.shrink(saved_sz);
            m_bump_reason_delay_interval++;
        } else {
            for (unsigned i = m_lemma.size(); i-- > saved_sz; ) {
                bool_var bv = m_lemma[i].var();
                if (m_config.m_branching_heuristic == BH_ADAM || m_config.m_branching_heuristic == BH_COMBINED)
                    adam_bump(bv);
                else
                    inc_activity_scaled(bv);
                // Polarity gradient for reason-side literals: only when
                // belief-based phase or combined heuristic consumes it.
                if (m_config.m_phase_strategy == PHS_BELIEF ||
                    m_config.m_branching_heuristic == BH_COMBINED) {
                    double ps = (value(bv) == l_true) ? -1.0 : 1.0;
                    double& belief = m_polarity_belief[bv];
                    double old_belief = belief;
                    belief = 0.95 * belief + 0.05 * ps * m_conflict_bump_scale;
                    if (belief > 1.0) belief = 1.0;
                    else if (belief < -1.0) belief = -1.0;
                    double delta = belief - old_belief;
                    m_belief_update_ema = 0.99 * m_belief_update_ema + 0.01 * delta * delta;
                }
                // Combined: overwrite activity with importance * (0.5 + confidence)
                if (m_config.m_branching_heuristic == BH_COMBINED) {
                    double importance = std::abs(m_adam_m1[bv]) / (std::sqrt(m_adam_m2[bv]) + 0.01);
                    double confidence = std::abs(m_polarity_belief[bv]);
                    set_activity(bv, importance * (0.5 + confidence));
                }
            }
            for (unsigned i = m_lemma.size(); i-- > saved_sz; ) {
                SASSERT(is_marked(m_lemma[i].var()));
                reset_mark(m_lemma[i].var());
            }
            m_lemma.shrink(saved_sz);
            m_bump_reason_delay_interval /= 2;
        }
        m_bump_reason_delay = m_bump_reason_delay_interval;
        reset_mark(m_lemma[0].var());
    }

    void solver::bump_reason_literals_recursive(literal lit, unsigned depth_limit,
                                                 unsigned& bump_count, unsigned bump_limit) {
        SASSERT(depth_limit > 0);
        // CaDiCaL-style tick: reason-side recursive bumping (analyze.cpp:370).
        ++m_search_ticks;
        bool_var v = lit.var();
        if (!lvl(v)) return;
        justification js = m_justification[v];
        switch (js.get_kind()) {
        case justification::NONE: return;
        case justification::BINARY: {
            literal other = js.get_literal();
            bool_var ov = other.var();
            if (!is_marked(ov) && lvl(ov) > 0) {
                mark(ov); m_lemma.push_back(other); bump_count++;
                if (depth_limit >= 2 && bump_count <= bump_limit)
                    bump_reason_literals_recursive(~other, depth_limit - 1, bump_count, bump_limit);
            }
            break;
        }
        case justification::CLAUSE: {
            clause & c = get_clause(js);
            for (literal l : c) {
                if (l == lit || l == ~lit) continue;
                bool_var lv = l.var();
                if (!is_marked(lv) && lvl(lv) > 0) {
                    mark(lv); m_lemma.push_back(l); bump_count++;
                    if (bump_count > bump_limit) break;
                    if (depth_limit >= 2)
                        bump_reason_literals_recursive(~l, depth_limit - 1, bump_count, bump_limit);
                    if (bump_count > bump_limit) break;
                }
            }
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            fill_ext_antecedents(~lit, js, true);
            for (literal l : m_ext_antecedents) {
                bool_var lv = l.var();
                if (!is_marked(lv) && lvl(lv) > 0) {
                    mark(lv); m_lemma.push_back(l); bump_count++;
                    if (bump_count > bump_limit) break;
                    if (depth_limit >= 2)
                        bump_reason_literals_recursive(~l, depth_limit - 1, bump_count, bump_limit);
                    if (bump_count > bump_limit) break;
                }
            }
            break;
        }
        default: break;
        }
    }

    /**
       \brief Apply dynamic subsumption resolution to new lemma.
       Only binary and ternary clauses are used.
    */
    bool solver::dyn_sub_res() {
        unsigned sz = m_lemma.size();
        for (unsigned i = 0; i < sz; ++i) {
            mark_lit(m_lemma[i]);
        }

        literal l0 = m_lemma[0];
        // l0 is the FUIP, and we never remove the FUIP.
        //
        // In the following loop, we use unmark_lit(l) to remove a
        // literal from m_lemma.

        for (unsigned i = 0; i < sz; ++i) {
            literal l = m_lemma[i];
            if (!is_marked_lit(l))
                continue; // literal was eliminated
            // first use binary watch lists
            watch_list const & bin_wlist = get_bin_wlist(~l);
            for (watched const& w : bin_wlist) {
                SASSERT(w.is_binary_clause());
                literal l2 = w.get_literal();
                if (is_marked_lit(~l2) && l0 != ~l2) {
                    // eliminate ~l2 from lemma because we have the clause l \/ l2
                    unmark_lit(~l2);
                }
            }
            // try to use cached implication if available
            literal_vector * implied_lits = m_probing.cached_implied_lits(~l);
            if (implied_lits) {
                for (literal l2 : *implied_lits) {
                    // Here, we must check l0 != ~l2.
                    // l \/ l2 is an implied binary clause.
                    // However, it may have been deduced using a lemma that has been deleted.
                    // For example, consider the following sequence of events:
                    //
                    // 1. Initial clause database:
                    //
                    //    l  \/ ~p1
                    //    p1 \/ ~p2
                    //    p2 \/ ~p3
                    //    p3 \/ ~p4
                    //    q1  \/ q2  \/ p1 \/ p2 \/ p3 \/ p4 \/ l2
                    //    q1  \/ ~q2 \/ p1 \/ p2 \/ p3 \/ p4 \/ l2
                    //    ~q1 \/ q2  \/ p1 \/ p2 \/ p3 \/ p4 \/ l2
                    //    ~q1 \/ ~q2 \/ p1 \/ p2 \/ p3 \/ p4 \/ l2
                    //    ...
                    //
                    // 2. Now suppose we learned the lemma
                    //
                    //    p1 \/ p2 \/ p3 \/ p4 \/ l2   (*)
                    //
                    // 3. Probing is executed and we notice hat (~l => l2) when we assign l to false.
                    //    That is, l \/ l2 is an implied clause. Note that probing does not add
                    //    this clause to the clause database (there are too many).
                    //
                    // 4. Lemma (*) is deleted (garbage collected).
                    //
                    // 5. l is decided to be false, p1, p2, p3 and p4 are propagated using BCP,
                    //    but l2 is not since the lemma (*) was deleted.
                    //
                    //    Probing module still "knows" that l \/ l2 is valid binary clause
                    //
                    // 6. A new lemma is created where ~l2 is the FUIP and the lemma also contains l.
                    //    If we remove l0 != ~l2 may try to delete the FUIP.
                    if (is_marked_lit(~l2) && l0 != ~l2) {
                        // eliminate ~l2 from lemma because we have the clause l \/ l2
                        unmark_lit(~l2);
                    }
                }
            }
        }

        // can't eliminate FUIP
        SASSERT(is_marked_lit(m_lemma[0]));

        unsigned j = 0;
        for (unsigned i = 0; i < sz; ++i) {
            literal l = m_lemma[i];
            if (is_marked_lit(l)) {
                unmark_lit(l);
                m_lemma[j] = l;
                j++;
            }
        }

        m_stats.m_dyn_sub_res += sz - j;

        SASSERT(j >= 1);
        m_lemma.shrink(j);
        return j < sz;
    }


    // -----------------------
    //
    // Backtracking
    //
    // -----------------------
    void solver::push() {
        SASSERT(!m_ext || !m_ext->can_propagate());
        SASSERT(!inconsistent());
        TRACE(sat_verbose, tout << "q:" << m_qhead << " trail: " << m_trail.size() << "\n";);
        SASSERT(m_qhead == m_trail.size());
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        m_scope_lvl++;
        s.m_trail_lim = m_trail.size();
        s.m_clauses_to_reinit_lim = m_clauses_to_reinit.size();
        s.m_inconsistent = m_inconsistent;
        if (m_ext) {
            m_vars_lim.push(m_active_vars.size());
            m_ext->push();
        }
    }

    void solver::pop_reinit(unsigned num_scopes) {
        pop(num_scopes);
        exchange_par();
        reinit_assumptions();
        m_stats.m_units = init_trail_size();
    }

    void solver::pop_vars(unsigned num_scopes) {
        //integrity_checker check(*this);
        //check.check_reinit_stack();
        m_vars_to_reinit.reset();
        unsigned old_num_vars = m_vars_lim.pop(num_scopes);
        if (old_num_vars == m_active_vars.size())
            return;
        unsigned sz = m_active_vars.size(), j = old_num_vars;
        unsigned new_lvl = m_scopes.size() - num_scopes;

        gc_reinit_stack(num_scopes);        

        // check.check_reinit_stack();
        init_visited();
        unsigned old_sz = m_scopes[new_lvl].m_clauses_to_reinit_lim;
        for (unsigned i = m_clauses_to_reinit.size(); i-- > old_sz; ) {
            clause_wrapper const& cw = m_clauses_to_reinit[i];
            for (unsigned j = cw.size(); j-- > 0; )
                mark_visited(cw[j].var());
        }
        for (literal lit : m_lemma)
           mark_visited(lit.var());

        auto is_active = [&](bool_var v) {
            return value(v) != l_undef && lvl(v) <= new_lvl;
        };

        for (unsigned i = old_num_vars; i < sz; ++i) {
            bool_var v = m_active_vars[i];
            if (is_external(v) || is_visited(v) || is_active(v)) {
                m_vars_to_reinit.push_back(v);
                m_active_vars[j++] = v;
                m_var_scope[v] = new_lvl;
            }
            else {
                set_eliminated(v, true);
                m_vars_to_free.push_back(v);                                   
            }
        }
        m_active_vars.shrink(j);

        auto cleanup_watch = [&](literal lit) {
            for ([[maybe_unused]] auto const& w : get_bin_wlist(lit)) {
                IF_VERBOSE(1, verbose_stream() << "cleanup: " << lit << " binary\n");
            }
            for ([[maybe_unused]] auto const& w : get_wlist(lit)) {
                IF_VERBOSE(1, verbose_stream() << "cleanup: " << lit << " clause/ext\n");
            }
        };
        for (bool_var v : m_vars_to_free) {
            cleanup_watch(literal(v, false));
            cleanup_watch(literal(v, true));
            
        }
        TRACE(sat,
            tout << "clauses to reinit: " << (m_clauses_to_reinit.size() - old_sz) << "\n";
            tout << "new level:         " << new_lvl << "\n";
            tout << "vars to reinit:    " << m_vars_to_reinit << "\n";
            tout << "free vars:         " << bool_var_vector(m_vars_to_free) << "\n";
            for (unsigned i = m_clauses_to_reinit.size(); i-- > old_sz; )
                tout << "reinit:           " << m_clauses_to_reinit[i] << "\n";
            display(tout););        
    }

    void solver::shrink_vars(unsigned v) {
        unsigned j = 0; 
        for (bool_var w : m_free_vars) 
            if (w < v)
                m_free_vars[j++] = w;
        m_free_vars.shrink(j);

        for (bool_var w = m_justification.size(); w-- > v;) {
            m_case_split_queue.del_var_eh(w);
            m_probing.reset_cache(literal(w, true));
            m_probing.reset_cache(literal(w, false));
        }
        m_watches.shrink(2*v);
        m_bin_watches.shrink(2*v);
        m_assignment.shrink(2*v);
        m_justification.shrink(v);
        m_trail_pos.shrink(v);
        m_decision.shrink(v);
        m_eliminated.shrink(v);
        m_external.shrink(v);
        m_var_scope.shrink(v);
        m_touched.shrink(v);
        m_activity.shrink(v);
        m_polarity_belief.shrink(v);
        if (m_config.m_branching_heuristic == BH_ADAM || m_config.m_branching_heuristic == BH_COMBINED) {
            m_adam_m1.shrink(v);
            m_adam_m2.shrink(v);
            m_adam_last_update.shrink(v);
        }
        m_mark.shrink(v);
        m_poison.shrink(v);
        m_removable.shrink(v);
        m_lit_mark.shrink(2*v);
        m_phase.shrink(v);
        m_best_phase.shrink(v);
        m_prev_phase.shrink(v);
        m_target_phase.shrink(v);
        m_assigned_since_gc.shrink(v);
        if (m_frozen_refcount.size() > v)
            m_frozen_refcount.shrink(v);
        if (m_assumption_mark.size() > 2*v)
            m_assumption_mark.shrink(2*v);
        m_simplifier.reset_todos();
    }

    void solver::pop(unsigned num_scopes) {
        if (num_scopes == 0)
            return;
        if (m_ext) {
            pop_vars(num_scopes);
            m_ext->pop(num_scopes);
        }
        SASSERT(num_scopes <= scope_lvl());
        unsigned new_lvl = scope_lvl() - num_scopes;
        scope & s        = m_scopes[new_lvl];
        m_inconsistent   = false; // TBD: use model seems to make this redundant: s.m_inconsistent;
        unassign_vars(s.m_trail_lim, new_lvl);
        for (bool_var v : m_vars_to_free)
            m_case_split_queue.del_var_eh(v);
        m_scope_lvl -= num_scopes;
        reinit_clauses(s.m_clauses_to_reinit_lim);
        m_scopes.shrink(new_lvl);
        if (m_ext) {
            m_ext->pop_reinit();
            m_free_vars.append(m_vars_to_free);
            m_vars_to_free.reset();
        }
    }

    void solver::unassign_vars(unsigned old_sz, unsigned new_lvl) {
        SASSERT(old_sz <= m_trail.size());
        SASSERT(m_replay_assign.empty());
        for (unsigned i = m_trail.size(); i-- > old_sz; ) {
            literal l  = m_trail[i];
            bool_var v = l.var();
            if (lvl(v) <= new_lvl) {
                m_replay_assign.push_back(l);
                continue;
            }
            m_assignment[l.index()]    = l_undef;
            m_assignment[(~l).index()] = l_undef;
            SASSERT(value(v) == l_undef);
            m_case_split_queue.unassign_var_eh(v);
            if (m_config.m_dual_mode)
                vmtf_update_search(v);
            if (m_config.m_anti_exploration) {
                m_canceled[v] = m_stats.m_conflict;
            }
        }
        m_trail.shrink(old_sz);        
        DEBUG_CODE(for (literal l : m_trail) SASSERT(lvl(l.var()) <= new_lvl););
        m_qhead = m_trail.size();
        m_qhead_binary = m_trail.size();
        if (!m_replay_assign.empty()) IF_VERBOSE(20, verbose_stream() << "replay assign: " << m_replay_assign.size() << "\n");
        CTRACE(sat, !m_replay_assign.empty(), tout << "replay-assign: " << m_replay_assign << "\n";);
        for (unsigned i = m_replay_assign.size(); i-- > 0; ) {
            literal lit = m_replay_assign[i];
            SASSERT(value(lit) == l_true);
            SASSERT(!m_trail.contains(lit) && !m_trail.contains(~lit));
            m_trail.push_back(lit);            
        }
        
        m_replay_assign.reset();
    }

    void solver::reinit_clauses(unsigned old_sz) {
        unsigned sz = m_clauses_to_reinit.size();
        SASSERT(old_sz <= sz);
        unsigned j = old_sz;
        for (unsigned i = old_sz; i < sz; ++i) {
            clause_wrapper cw = m_clauses_to_reinit[i];
            bool reinit = false;
            if (cw.is_binary()) {
                if (propagate_bin_clause(cw[0], cw[1]) && !at_base_lvl())
                    m_clauses_to_reinit[j++] = cw;
                else if (has_variables_to_reinit(cw[0], cw[1]) && !at_base_lvl())
                    m_clauses_to_reinit[j++] = cw;
            }
            else {
                clause & c = *(cw.get_clause());
                detach_clause(c);
                attach_clause(c, reinit);
                if (reinit && !at_base_lvl()) 
                    // clause propagated literal, must keep it in the reinit stack.
                    m_clauses_to_reinit[j++] = cw;                
                else if (has_variables_to_reinit(c) && !at_base_lvl())
                    m_clauses_to_reinit[j++] = cw;
                else 
                    c.set_reinit_stack(false);   
            }
        }
        m_clauses_to_reinit.shrink(j);
    }

    //
    // All new clauses that are added to the solver
    // are relative to the user-scope literals.
    //

    void solver::user_push() {
        pop_to_base_level();
        m_free_var_freeze.push_back(m_free_vars);
        m_free_vars.reset(); // resetting free_vars forces new variables to be assigned above new_v
        bool_var new_v = mk_var(true, false);
        SASSERT(new_v + 1 == m_justification.size()); // there are no active variables that have higher values
        literal lit = literal(new_v, false);
        m_user_scope_literals.push_back(lit);
        if (m_ext)
            m_ext->user_push();
        TRACE(sat, tout << "user_push: " << lit << "\n";);
    }

    void solver::user_pop(unsigned num_scopes) {
        if (m_user_scope_literals.empty())
            return;
        unsigned old_sz = m_user_scope_literals.size() - num_scopes;
        bool_var max_var = m_user_scope_literals[old_sz].var();        
        m_user_scope_literals.shrink(old_sz);

        pop_to_base_level();
        if (m_ext)
            m_ext->user_pop(num_scopes);
    
        gc_vars(max_var);
        TRACE(sat, display(tout););

        // Scope change invalidates evolved search limits; re-initialize on next check().
        m_search_initialized = false;

        m_qhead = 0;
        m_qhead_binary = 0;
        unsigned j = 0;
        for (bool_var v : m_free_vars)
            if (v < max_var)
                m_free_vars[j++] = v;
        m_free_vars.shrink(j);
        m_free_vars.append(m_free_var_freeze[old_sz]);
        m_free_var_freeze.shrink(old_sz);
        scoped_suspend_rlimit _sp(m_rlimit);
        propagate(false);
    }

    void solver::pop_to_base_level() {
        reset_assumptions();
        pop(scope_lvl());
    }

    // -----------------------
    //
    // Misc
    //
    // -----------------------

    void solver::updt_params(params_ref const & p) {
        m_params.append(p);
        m_config.updt_params(p);
        m_simplifier.updt_params(p);
        m_asymm_branch.updt_params(p);
        m_probing.updt_params(p);
        m_scc.updt_params(p);
        m_rand.set_seed(m_config.m_random_seed);
        m_step_size = m_config.m_step_size_init;
        m_drat.updt_config();
        m_fast_glue_avg.set_alpha(m_config.m_fast_glue_avg);
        m_slow_glue_avg.set_alpha(m_config.m_slow_glue_avg);
        m_fast_glue_backup.set_alpha(m_config.m_fast_glue_avg);
        m_slow_glue_backup.set_alpha(m_config.m_slow_glue_avg);
        m_trail_avg.set_alpha(m_config.m_slow_glue_avg);

        // Ensure Adam arrays are properly sized when switching to BH_ADAM/BH_COMBINED.
        // Variables created under a different heuristic won't have Adam entries --
        // grow the arrays now to prevent out-of-bounds access in adam_bump().
        if (m_config.m_branching_heuristic == BH_ADAM || m_config.m_branching_heuristic == BH_COMBINED) {
            unsigned nv = num_vars();
            while (m_adam_m1.size() < nv) {
                m_adam_m1.push_back(0.0);
                m_adam_m2.push_back(0.0);
                m_adam_last_update.push_back(m_adam_step);
            }
        }
    }

    void solver::collect_param_descrs(param_descrs & d) {
        config::collect_param_descrs(d);
        simplifier::collect_param_descrs(d);
        asymm_branch::collect_param_descrs(d);
        probing::collect_param_descrs(d);
        scc::collect_param_descrs(d);
    }

    void solver::collect_statistics(statistics & st) const {
        m_stats.collect_statistics(st);
        m_cleaner.collect_statistics(st);
        m_simplifier.collect_statistics(st);
        m_scc.collect_statistics(st);
        m_asymm_branch.collect_statistics(st);
        m_probing.collect_statistics(st);
        if (m_ext) m_ext->collect_statistics(st);
        if (m_local_search) m_local_search->collect_statistics(st);
        st.copy(m_aux_stats);
        // Per-phase profiling timers.
        st.update("sat time simplify", m_profile_simplify.get_seconds());
        st.update("sat time gc", m_profile_gc.get_seconds());
    }

    void solver::reset_statistics() {
        m_stats.reset();
        m_cleaner.reset_statistics();
        m_simplifier.reset_statistics();
        m_asymm_branch.reset_statistics();
        m_probing.reset_statistics();
        m_aux_stats.reset();
    }

    // -----------------------
    //
    // Activity related stuff
    //
    // -----------------------

    void solver::rescale_activity() {
        SASSERT(m_config.m_branching_heuristic == BH_VSIDS);
        double inv = 1e-100;
        for (double& act : m_activity) {
            act *= inv;
        }
        m_activity_inc *= inv;
    }

    // -------------------------------------------------------
    // Adam optimizer branching heuristic
    // -------------------------------------------------------
    // Uses the P4.1 lazy decay power tables (decay_pow095, decay_pow0999)
    // for timestamped moment decay, and the enriched gradient signal
    // m_conflict_bump_scale (LBD-weighted + Muon-normalized) from P1.2.

    void solver::adam_bump(bool_var v) {
        static constexpr double BETA1       = 0.95;
        static constexpr double BETA2       = 0.999;
        static constexpr double ONE_M_BETA1 = 1.0 - BETA1;   // 0.05
        static constexpr double ONE_M_BETA2 = 1.0 - BETA2;   // 0.001
        static constexpr double EPS         = 0.01;

        // Lazy decay: apply accumulated beta^dt since last update.
        uint64_t dt = m_adam_step - m_adam_last_update[v];
        if (dt > 0) {
            m_adam_m1[v] *= decay_pow095(dt);
            m_adam_m2[v] *= decay_pow0999(dt);
            m_adam_last_update[v] = m_adam_step;
        }
        // Enriched gradient: LBD-weighted + Muon-normalized per-conflict signal.
        double g = m_conflict_bump_scale;
        m_adam_m1[v] = BETA1 * m_adam_m1[v] + ONE_M_BETA1 * g;
        m_adam_m2[v] = BETA2 * m_adam_m2[v] + ONE_M_BETA2 * g * g;
        // Effective activity: m1 / (sqrt(m2) + eps).
        double act = m_adam_m1[v] / (std::sqrt(m_adam_m2[v]) + EPS);
        set_activity(v, act);
    }

    void solver::update_chb_activity(bool is_sat, unsigned qhead) {
        SASSERT(m_config.m_branching_heuristic == BH_CHB);
        double multiplier = m_config.m_reward_offset * (is_sat ? m_config.m_reward_multiplier : 1.0);
        for (unsigned i = qhead; i < m_trail.size(); ++i) {
            auto v = m_trail[i].var();
            auto d = m_stats.m_conflict - m_last_conflict[v] + 1;
            if (d == 0) d = 1;
            auto reward = multiplier / d;            
            double activity = m_activity[v];
            set_activity(v, m_step_size * reward + (1.0 - m_step_size) * activity);
        }
    }

    void solver::move_to_front(bool_var b) {
        if (b >= num_vars())
            return;
        if (m_case_split_queue.empty())
            return;
        bool_var next = m_case_split_queue.min_var();
        double next_act = m_activity[next];
        set_activity(b, next_act + m_activity_inc);
    }

    // -----------------------
    //
    // Iterators
    //
    // -----------------------
    void solver::collect_bin_clauses(svector<bin_clause> & r, bool redundant, bool learned_only) const {
        SASSERT(redundant || !learned_only);
        unsigned sz = m_bin_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l = to_literal(l_idx);
            l.neg();
            for (watched const& w : m_bin_watches[l_idx]) {
                SASSERT(w.is_binary_clause());
                if (!redundant && w.is_learned())
                    continue;
                else if (redundant && learned_only && !w.is_learned())
                    continue;
                literal l2 = w.get_literal();
                if (l.index() > l2.index())
                    continue;
                TRACE(cleanup_bug, tout << "collected: " << l << " " << l2 << "\n";);
                r.push_back(bin_clause(l, l2));
            }
        }
    }

    // -----------------------
    //
    // Debugging
    //
    // -----------------------
    bool solver::check_invariant() const {
        if (!m_rlimit.inc()) 
            return true;
        if (m_simplifier.need_cleanup())
            return true;
        integrity_checker checker(*this);
        VERIFY(checker());
        VERIFY(!m_ext || m_ext->validate());
        return true;
    }

    bool solver::check_marks() const {
        for (bool_var v = 0; v < num_vars(); ++v) {
            SASSERT(!is_marked(v));
        }
        return true;
    }

    std::ostream& solver::display_model(std::ostream& out) const {
        unsigned num = num_vars();
        for (bool_var v = 0; v < num; ++v) {
            out << v << ": " << m_model[v] << "\n";
        }
        return out;
}

    void solver::display_binary(std::ostream & out) const {
        unsigned sz = m_bin_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l = to_literal(l_idx);
            l.neg();
            for (watched const& w : m_bin_watches[l_idx]) {
                SASSERT(w.is_binary_clause());
                literal l2 = w.get_literal();
                if (l.index() > l2.index())
                    continue;
                out << "(" << l << " " << l2 << ")";
                if (w.is_learned()) out << "*";
                out << "\n";
            }
        }
    }

    void solver::display_units(std::ostream & out) const {
        unsigned level = 0;
        for (literal lit : m_trail) {            
            if (lvl(lit) > level) {
                level = lvl(lit);
                out << level << ": ";
            }
            else {
                out << "    ";
            }
            out << lit << " ";
            if (lvl(lit) < level) {
                out << "@" << lvl(lit) << " ";
            }
            display_justification(out, m_justification[lit.var()]) << "\n";
        }
    }

    void solver::display(std::ostream & out) const {
        out << "(sat\n";
        display_units(out);
        display_binary(out);
        out << m_clauses << m_learned;
        if (m_ext) {
            m_ext->display(out);
        }
        out << ")\n";
    }

    std::ostream& solver::display_justification(std::ostream & out, justification const& js) const {
        switch (js.get_kind()) {
        case justification::NONE:
            out << "none @" << js.level();
            break;
        case justification::BINARY:
            out << "binary " << js.get_literal() << "@" << lvl(js.get_literal());
            break;
        case justification::CLAUSE: {
            out << "(";
            bool first = true;
            for (literal l : get_clause(js)) {
                if (first) first = false; else out << " ";
                out << l << "@" << lvl(l);
            }
            out << ")";
            break;
        }
        case justification::EXT_JUSTIFICATION:
            if (m_ext) 
                m_ext->display_justification(out << "ext ", js.get_ext_justification_idx());            
            break;
        default:
            break;
        }
        return out;
    }


    unsigned solver::num_clauses() const {
        unsigned num_cls = m_trail.size(); // units;
        unsigned l_idx = 0;
        for (auto const& wl : m_bin_watches) {
            literal l = ~to_literal(l_idx++);
            for (auto const& w : wl) {
                if (w.is_binary_clause() && l.index() < w.get_literal().index())
                    num_cls++;
            }
        }
        return num_cls + m_clauses.size() + m_learned.size();
    }

    void solver::num_binary(unsigned& given, unsigned& redundant) const {
        given = redundant = 0;
        unsigned l_idx = 0;
        for (auto const& wl : m_bin_watches) {
            literal l = ~to_literal(l_idx++);
            for (auto const& w : wl) {
                SASSERT(w.is_binary_clause());
                if (l.index() < w.get_literal().index()) {
                    if (w.is_learned()) ++redundant; else ++given;
                }
            }
        }
    }

    void solver::display_dimacs(std::ostream & out) const {
        out << "p cnf " << num_vars() << " " << num_clauses() << "\n";
        for (literal lit : m_trail) {
            out << dimacs_lit(lit) << " 0\n";
        }
        unsigned l_idx = 0;
        for (auto const& wlist : m_bin_watches) {
            literal l = ~to_literal(l_idx++);
            for (auto const& w : wlist) {
                SASSERT(w.is_binary_clause());
                if (l.index() < w.get_literal().index())
                    out << dimacs_lit(l) << " " << dimacs_lit(w.get_literal()) << " 0\n";
            }
        }
        clause_vector const * vs[2] = { &m_clauses, &m_learned };
        for (unsigned i = 0; i < 2; ++i) {
            clause_vector const & cs = *(vs[i]);
            for (auto cp : cs) {
                for (literal l : *cp) {
                    out << dimacs_lit(l) << " ";
                }
                out << "0\n";
            }
        }
    }

    void solver::display_wcnf(std::ostream & out, unsigned sz, literal const* lits, unsigned const* weights) const {
        unsigned max_weight = 0;
        for (unsigned i = 0; i < sz; ++i) 
            max_weight += weights[i];
        ++max_weight;

        if (m_ext)
            throw default_exception("wcnf is only supported for pure CNF problems");

        out << "p wcnf " << num_vars() << " " << num_clauses() + sz << " " << max_weight << "\n";
        out << "c soft " << sz << "\n";

        for (literal lit : m_trail) 
            out << max_weight << " " << dimacs_lit(lit) << " 0\n";
        unsigned l_idx = 0;
        for (watch_list const& wlist : m_bin_watches) {
            literal l = ~to_literal(l_idx);
            for (watched const& w : wlist) {
                if (w.is_binary_clause() && l.index() < w.get_literal().index())
                    out << max_weight << " " << dimacs_lit(l) << " " << dimacs_lit(w.get_literal()) << " 0\n";
            }
            ++l_idx;
        }
        clause_vector const * vs[2] = { &m_clauses, &m_learned };
        for (unsigned i = 0; i < 2; ++i) {
            clause_vector const & cs = *(vs[i]);
            for (clause const* cp : cs) {
                clause const & c = *cp;
                out << max_weight << " ";
                for (literal l : c)
                    out << dimacs_lit(l) << " ";
                out << "0\n";
            }
        }
        for (unsigned i = 0; i < sz; ++i) {
            out << weights[i] << " " << lits[i] << " 0\n";
        }
        out.flush();
    }

    void solver::display_watches(std::ostream & out, literal lit) const {
        display_watch_list(out << lit << " bin: ", get_bin_wlist(lit)) << "\n";
        display_watch_list(out << lit << " cls: ", get_wlist(lit)) << "\n";
    }

    void solver::display_watches(std::ostream & out) const {
        for (unsigned l_idx = 0; l_idx < m_watches.size(); ++l_idx) {
            literal l = to_literal(l_idx);
            watch_list const& bwl = m_bin_watches[l_idx];
            watch_list const& cwl = m_watches[l_idx];
            if (!bwl.empty())
                display_watch_list(out << l << " bin: ", bwl) << "\n";
            if (!cwl.empty())
                display_watch_list(out << l << " cls: ", cwl) << "\n";
        }
    }

    std::ostream& solver::display_watch_list(std::ostream& out, watch_list const& wl) const {
        return sat::display_watch_list(out, cls_allocator(), wl, m_ext.get());
    }

    void solver::display_assignment(std::ostream & out) const {
        out << m_trail << "\n";
    }

    /**
       \brief Return true, if c is a clause containing one unassigned literal.
    */
    bool solver::is_unit(clause const & c) const {
        bool found_undef = false;
        for (literal l : c) {
            switch (value(l)) {
            case l_undef:
                if (found_undef)
                    return false;
                found_undef = true;
                break;
            case l_true:
                return false;
            case l_false:
                break;
            }
        }
        return found_undef;
    }

    /**
       \brief Return true, if all literals in c are assigned to false.
    */
    bool solver::is_empty(clause const & c) const {
        for (literal lit : c) 
            if (value(lit) != l_false)
                return false;
        return true;
    }

    bool solver::check_missed_propagation(clause_vector const & cs) const {
        for (clause* cp : cs) {
            clause const & c = *cp;
            if (c.frozen())
                continue;
            if (is_empty(c) || is_unit(c)) {
                TRACE(sat_missed_prop, tout << "missed_propagation: " << c << "\n";
                      for (literal l : c) tout << l << ": " << value(l) << "\n";);
                UNREACHABLE();
            }
            SASSERT(!is_empty(c));
            SASSERT(!is_unit(c));
        }
        return true;
    }

    bool solver::check_missed_propagation() const {
        if (inconsistent())
            return true;
        return check_missed_propagation(m_clauses) && check_missed_propagation(m_learned);
    }

    // -----------------------
    //
    // Simplification
    //
    // -----------------------
    bool solver::do_cleanup(bool force) {
        if (m_conflicts_since_init == 0 && !force)
            return false;
        if (at_base_lvl() && !inconsistent() && m_cleaner(force)) {
            if (m_ext)
                m_ext->clauses_modifed();
            return true;
        }
        return false;
    }

    void solver::simplify(bool redundant) {
        if (!at_base_lvl() || inconsistent())
            return;
        m_simplifier(redundant);
        m_simplifier.finalize();
        if (m_ext)
            m_ext->clauses_modifed();
    }

    unsigned solver::scc_bin() {
        if (!at_base_lvl() || inconsistent())
            return 0;
        unsigned r = m_scc();
        if (r > 0 && m_ext)
            m_ext->clauses_modifed();
        return r;
    }

    // -----------------------
    //
    // Extraction of mutexes
    //
    // -----------------------

    struct neg_literal {
        unsigned negate(unsigned idx) {
            return (~to_literal(idx)).index();
        }
    };

    lbool solver::find_mutexes(literal_vector const& lits, vector<literal_vector> & mutexes) {
        max_cliques<neg_literal> mc;
        m_user_bin_clauses.reset();
        // m_binary_clause_graph.reset();
        collect_bin_clauses(m_user_bin_clauses, true, false);
        hashtable<literal_pair, pair_hash<literal_hash, literal_hash>, default_eq<literal_pair> > seen_bc;
        for (auto const& [l1, l2] : m_user_bin_clauses) {
            literal_pair p(l1, l2);
            if (!seen_bc.contains(p)) {
                seen_bc.insert(p);
                mc.add_edge(l1.index(), l2.index());
            }
        }
        vector<unsigned_vector> _mutexes;
        literal_vector _lits(lits);
        if (m_ext) {
            m_ext->find_mutexes(_lits, mutexes);
        }
        unsigned_vector ps;
        for (literal lit : _lits) 
            ps.push_back(lit.index());
        mc.cliques2(ps, _mutexes);
        vector<vector<literal_vector>> sorted;
        for (auto const& mux : _mutexes) {
            literal_vector clique;
            sorted.reserve(mux.size() + 1);
            for (auto const& idx : mux) 
                clique.push_back(to_literal(idx));
            sorted[mux.size()].push_back(clique);
        }
        for (unsigned i = sorted.size(); i-- > 0; ) 
            mutexes.append(sorted[i]);
        return l_true;
    }

    // -----------------------
    //
    // Consequence generation.
    //
    // -----------------------

    static void prune_unfixed(sat::literal_vector& lambda, sat::model const& m) {
        for (unsigned i = 0; i < lambda.size(); ++i) {
            if ((m[lambda[i].var()] == l_false) != lambda[i].sign()) {
                lambda[i] = lambda.back();
                lambda.pop_back();
                --i;
            }
        }
    }

    // Algorithm 7: Corebased Algorithm with Chunking

    static void back_remove(sat::literal_vector& lits, sat::literal l) {
        for (unsigned i = lits.size(); i > 0; ) {
            --i;
            if (lits[i] == l) {
                lits[i] = lits.back();
                lits.pop_back();
                return;
            }
        }
        UNREACHABLE();
    }

    static void brute_force_consequences(sat::solver& s, sat::literal_vector const& asms, sat::literal_vector const& gamma, vector<sat::literal_vector>& conseq) {
        for (literal lit : gamma) {
            sat::literal_vector asms1(asms);
            asms1.push_back(~lit);
            lbool r = s.check(asms1.size(), asms1.data());
            if (r == l_false) {
                conseq.push_back(s.get_core());
            }
        }
    }

    static lbool core_chunking(sat::solver& s, model const& m, sat::bool_var_vector const& vars, sat::literal_vector const& asms, vector<sat::literal_vector>& conseq, unsigned K) {
        sat::literal_vector lambda;
        for (bool_var v : vars) {
            lambda.push_back(sat::literal(v, m[v] == l_false));
        }
        while (!lambda.empty()) {
            IF_VERBOSE(1, verbose_stream() << "(sat-backbone-core " << lambda.size() << " " << conseq.size() << ")\n";);
            unsigned k = std::min(K, lambda.size());
            sat::literal_vector gamma, omegaN;
            for (unsigned i = 0; i < k; ++i) {
                sat::literal l = lambda[lambda.size() - i - 1];
                gamma.push_back(l);
                omegaN.push_back(~l);
            }
            while (true) {
                sat::literal_vector asms1(asms);
                asms1.append(omegaN);
                lbool r = s.check(asms1.size(), asms1.data());
                if (r == l_true) {
                    IF_VERBOSE(1, verbose_stream() << "(sat) " << omegaN << "\n";);
                    prune_unfixed(lambda, s.get_model());
                    break;
                }
                sat::literal_vector const& core = s.get_core();
                sat::literal_vector occurs;
                IF_VERBOSE(1, verbose_stream() << "(core " << core.size() << ")\n";);
                for (unsigned i = 0; i < omegaN.size(); ++i) {
                    if (core.contains(omegaN[i])) {
                        occurs.push_back(omegaN[i]);
                    }
                }
                if (occurs.size() == 1) {
                    sat::literal lit = occurs.back();
                    sat::literal nlit = ~lit;
                    conseq.push_back(core);
                    back_remove(lambda, ~lit);
                    back_remove(gamma, ~lit);
                    s.mk_clause(1, &nlit);
                }
                for (unsigned i = 0; i < omegaN.size(); ++i) {
                    if (occurs.contains(omegaN[i])) {
                        omegaN[i] = omegaN.back();
                        omegaN.pop_back();
                        --i;
                    }
                }
                if (omegaN.empty() && occurs.size() > 1) {
                    brute_force_consequences(s, asms, gamma, conseq);
                    for (unsigned i = 0; i < gamma.size(); ++i) {
                        back_remove(lambda, gamma[i]);
                    }
                    break;
                }
            }
        }
        return l_true;
    }


    lbool solver::get_consequences(literal_vector const& asms, bool_var_vector const& vars, vector<literal_vector>& conseq) {
        literal_vector lits;
        lbool is_sat = l_true;

        if (m_config.m_restart_max != UINT_MAX && !m_model_is_current) {
            return get_bounded_consequences(asms, vars, conseq);
        }
        if (!m_model_is_current) {
            is_sat = check(asms.size(), asms.data());
        }
        if (is_sat != l_true) {
            return is_sat;
        }
        model mdl = get_model();
        for (unsigned i = 0; i < vars.size(); ++i) {
            bool_var v = vars[i];
            switch (get_model()[v]) {
            case l_true: lits.push_back(literal(v, false)); break;
            case l_false: lits.push_back(literal(v, true)); break;
            default: break;
            }
        }

        if (false && asms.empty()) {
            is_sat = core_chunking(*this, mdl, vars, asms, conseq, 100);
        }
        else {
            is_sat = get_consequences(asms, lits, conseq);
        }
        set_model(mdl, !mdl.empty());
        return is_sat;
    }

    void solver::fixup_consequence_core() {
        index_set s;
        TRACE(sat, tout << m_core << "\n";);
        for (unsigned i = 0; i < m_core.size(); ++i) {
            TRACE(sat, tout << m_core[i] << ": "; display_index_set(tout, m_antecedents.find(m_core[i].var())) << "\n";);
            s |= m_antecedents.find(m_core[i].var());
        }
        m_core.reset();
        for (unsigned idx : s) {
            m_core.push_back(to_literal(idx));
        }
        TRACE(sat, tout << m_core << "\n";);
    }

    bool solver::reached_max_conflicts() {
        if (m_config.m_max_conflicts == 0 || m_conflicts_since_init > m_config.m_max_conflicts) {
            if (m_reason_unknown != "sat.max.conflicts") {
                m_reason_unknown = "sat.max.conflicts";
                IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-conflicts = " << m_conflicts_since_init << "\")\n";);
            }
            return !inconsistent();
        }
        return false;
    }


    lbool solver::get_bounded_consequences(literal_vector const& asms, bool_var_vector const& vars, vector<literal_vector>& conseq) {
        bool_var_set unfixed_vars;
        unsigned num_units = 0;
        for (bool_var v : vars) {
            unfixed_vars.insert(v);
        }
        TRACE(sat, tout << asms << "\n";);
        m_antecedents.reset();
        pop_to_base_level();
        if (inconsistent()) return l_false;
        flet<bool> _searching(m_searching, true);
        init_search();
        propagate(false);
        if (inconsistent()) return l_false;
        if (asms.empty()) {
            bool_var v = mk_var(true, false);
            literal lit(v, false);
            init_assumptions(1, &lit);
        }
        else {
            init_assumptions(asms.size(), asms.data());
        }
        propagate(false);
        if (check_inconsistent()) return l_false;

        extract_fixed_consequences(num_units, asms, unfixed_vars, conseq);

        do_simplify();
        if (check_inconsistent()) {
            fixup_consequence_core();
            return l_false;
        }

        while (true) {
            SASSERT(!inconsistent());

            lbool r = bounded_search();
            if (r != l_undef) {
                fixup_consequence_core();
                return r;
            }

            extract_fixed_consequences(num_units, asms, unfixed_vars, conseq);

            do_restart(true);
            do_simplify();
            if (check_inconsistent()) {
                fixup_consequence_core();
                return l_false;
            }
            do_gc();

            if (should_cancel()) {
                return l_undef;
            }
        }
    }

    lbool solver::get_consequences(literal_vector const& asms, literal_vector const& lits, vector<literal_vector>& conseq) {
        TRACE(sat, tout << asms << "\n";);
        m_antecedents.reset();
        literal_set unfixed_lits(lits), assumptions(asms);
        bool_var_set unfixed_vars;
        for (literal lit : lits) {
            unfixed_vars.insert(lit.var());
        }

        pop_to_base_level();
        if (inconsistent()) return l_false;
        init_search();
        propagate(false);
        if (inconsistent()) return l_false;
        if (asms.empty()) {
            bool_var v = mk_var(true, false);
            literal lit(v, false);
            init_assumptions(1, &lit);
        }
        else {
            init_assumptions(asms.size(), asms.data());
        }
        propagate(false);
        if (check_inconsistent()) return l_false;
        SASSERT(search_lvl() == 1);

        unsigned num_iterations = 0;
        extract_fixed_consequences(unfixed_lits, assumptions, unfixed_vars, conseq);
        update_unfixed_literals(unfixed_lits, unfixed_vars);
        while (!unfixed_lits.empty()) {
            if (scope_lvl() > search_lvl()) {
                pop(scope_lvl() - search_lvl());
            }
            propagate(false);
            ++num_iterations;
            checkpoint();
            unsigned num_resolves = 0;
            unsigned num_fixed = 0;
            lbool is_sat = l_true;
            for (literal lit : unfixed_lits) {
                if (value(lit) != l_undef) {
                    ++num_fixed;
                    if (lvl(lit) <= 1 && value(lit) == l_true) {
                        extract_fixed_consequences(lit, assumptions, unfixed_vars, conseq);
                    }
                    continue;
                }
                push();
                assign_scoped(~lit);
                propagate(false);
                while (inconsistent()) {
                    if (!resolve_conflict()) {
                        TRACE(sat, display(tout << "inconsistent\n"););
                        m_inconsistent = false;
                        is_sat = l_undef;
                        break;
                    }
                    propagate(false);
                    ++num_resolves;
                }
            }

            extract_fixed_consequences(unfixed_lits, assumptions, unfixed_vars, conseq);

            if (is_sat == l_true) {
                if (scope_lvl() == search_lvl() && num_resolves > 0) {
                    IF_VERBOSE(1, verbose_stream() << "(sat.get-consequences backjump)\n";);
                    is_sat = l_undef;
                }
                else {
                    is_sat = bounded_search();
                    if (is_sat == l_undef) {
                        do_restart(true);                        
                        propagate(false);
                    }
                    extract_fixed_consequences(unfixed_lits, assumptions, unfixed_vars, conseq);
                }
            }
            if (is_sat == l_false) {
                TRACE(sat, tout << "unsat\n";);
                m_inconsistent = false;
            }
            if (is_sat == l_true) {
                delete_unfixed(unfixed_lits, unfixed_vars);
            }
            update_unfixed_literals(unfixed_lits, unfixed_vars);
            IF_VERBOSE(1, verbose_stream() << "(sat.get-consequences"
                       << " iterations: " << num_iterations
                       << " variables: " << unfixed_lits.size()
                       << " fixed: " << conseq.size()
                       << " status: " << is_sat
                       << " pre-assigned: " << num_fixed
                       << " unfixed: " << lits.size() - conseq.size() - unfixed_lits.size()
                       << ")\n";);

            if (!unfixed_lits.empty() && m_config.m_restart_max <= num_iterations) {
                return l_undef;
            }
        }
        return l_true;
    }

    void solver::delete_unfixed(literal_set& unfixed_lits, bool_var_set& unfixed_vars) {
        literal_set to_keep;
        for (literal lit : unfixed_lits) {
            if (value(lit) == l_true) {
                to_keep.insert(lit);
            }
            else {
                unfixed_vars.remove(lit.var());
            }
        }
        unfixed_lits = to_keep;
    }

    void solver::update_unfixed_literals(literal_set& unfixed_lits, bool_var_set& unfixed_vars) {
        literal_vector to_delete;
        for (literal lit : unfixed_lits) {
            if (!unfixed_vars.contains(lit.var())) {
                to_delete.push_back(lit);
            }
        }
        for (unsigned i = 0; i < to_delete.size(); ++i) {
            unfixed_lits.remove(to_delete[i]);
        }
    }


    void solver::extract_fixed_consequences(unsigned& start, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq) {
        SASSERT(!inconsistent());
        unsigned sz = m_trail.size();
        for (unsigned i = start; i < sz && lvl(m_trail[i]) <= 1; ++i) {
            extract_fixed_consequences(m_trail[i], assumptions, unfixed, conseq);
        }
        start = sz;
    }

    void solver::extract_fixed_consequences(literal_set const& unfixed_lits, literal_set const& assumptions, bool_var_set& unfixed_vars, vector<literal_vector>& conseq) {
        for (literal lit: unfixed_lits) {
            TRACE(sat, tout << "extract: " << lit << " " << value(lit) << " " << lvl(lit) << "\n";);
            if (lvl(lit) <= 1 && value(lit) == l_true) {
                extract_fixed_consequences(lit, assumptions, unfixed_vars, conseq);
            }
        }
    }

    bool solver::check_domain(literal lit, literal lit2) {
        if (!m_antecedents.contains(lit2.var())) {
            SASSERT(value(lit2) == l_true);
            SASSERT(m_todo_antecedents.empty() || m_todo_antecedents.back() != lit2);
            m_todo_antecedents.push_back(lit2);
            return false;
        }
        else {
            return true;
        }
    }

    bool solver::extract_assumptions(literal lit, index_set& s) {
        justification js = m_justification[lit.var()];
        TRACE(sat, tout << lit << " " << js << "\n";);
        bool all_found = true;
        switch (js.get_kind()) {
        case justification::NONE:
            break;
        case justification::BINARY:
            if (!check_domain(lit, ~js.get_literal())) 
                return false;
            s |= m_antecedents.find(js.get_literal().var());
            break;
        case justification::CLAUSE: {
            clause & c = get_clause(js);
            for (literal l : c) {
                if (l != lit) {
                    if (check_domain(lit, ~l) && all_found) 
                        s |= m_antecedents.find(l.var());                    
                    else 
                        all_found = false;                    
                }
            }
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            fill_ext_antecedents(lit, js, true);
            for (literal l : m_ext_antecedents) {
                if (check_domain(lit, l) && all_found) {
                    s |= m_antecedents.find(l.var());
                }
                else {
                    all_found = false;
                }
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
        TRACE(sat, display_index_set(tout << lit << ": " , s) << "\n";);
        return all_found;
    }

    std::ostream& solver::display_index_set(std::ostream& out, index_set const& s) const {
        for (unsigned idx : s) {
            out << to_literal(idx) << " ";
        }
        return out;
    }


    bool solver::extract_fixed_consequences1(literal lit, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq) {
        index_set s;
        if (m_antecedents.contains(lit.var())) 
            return true;
        
        if (assumptions.contains(lit)) 
            s.insert(lit.index());        
        else {
            if (!extract_assumptions(lit, s)) {
                SASSERT(!m_todo_antecedents.empty());
                return false;
            }
            add_assumption(lit);
        }
        if (unfixed.contains(lit.var())) {
            literal_vector cons;
            cons.push_back(lit);
            for (unsigned idx : s) {
                cons.push_back(to_literal(idx));
            }
            unfixed.remove(lit.var());
            conseq.push_back(std::move(cons));
        }
        m_antecedents.insert(lit.var(), std::move(s));
        return true;
    }

    void solver::extract_fixed_consequences(literal lit, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq) {
        SASSERT(m_todo_antecedents.empty());
        m_todo_antecedents.push_back(lit);
        while (!m_todo_antecedents.empty()) {
            auto lit = m_todo_antecedents.back();
            if (extract_fixed_consequences1(lit, assumptions, unfixed, conseq)) 
                m_todo_antecedents.pop_back();
        }
    }

    // -----------------------
    //
    // Statistics
    //
    // -----------------------

    void solver::display_status(std::ostream & out) const {
        unsigned num_bin = 0;
        unsigned num_ext = 0;
        unsigned num_lits = 0;
        unsigned l_idx = 0;
        for (watch_list const& wlist : m_bin_watches) {
            literal l = ~to_literal(l_idx++);
            for (watched const& w : wlist) {
                if (w.is_binary_clause() && l.index() < w.get_literal().index()) {
                    num_lits += 2;
                    num_bin++;
                }
            }
        }
        for (watch_list const& wlist : m_watches) {
            for (watched const& w : wlist) {
                if (w.is_ext_constraint())
                    num_ext++;
            }
        }
        unsigned num_elim = 0;
        for (bool_var v = 0; v < num_vars(); ++v) {
            if (m_eliminated[v])
                num_elim++;
        }
        unsigned num_ter  = 0;
        unsigned num_cls  = 0;
        clause_vector const * vs[2] = { &m_clauses, &m_learned };
        for (unsigned i = 0; i < 2; ++i) {
            clause_vector const & cs = *(vs[i]);
            for (clause* cp : cs) {
                clause & c = *cp;
                if (c.size() == 3)
                    num_ter++;
                else
                    num_cls++;
                num_lits += c.size();
            }
        }
        unsigned total_cls = num_cls + num_ter + num_bin + num_ext;
        double mem = static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024);
        out << "(sat-status\n";
        out << "  :inconsistent    " << (m_inconsistent ? "true" : "false") << "\n";
        out << "  :vars            " << num_vars() << "\n";
        out << "  :elim-vars       " << num_elim << "\n";
        out << "  :lits            " << num_lits << "\n";
        out << "  :assigned        " << m_trail.size() << "\n";
        out << "  :binary-clauses  " << num_bin << "\n";
        out << "  :ternary-clauses " << num_ter << "\n";
        out << "  :clauses         " << num_cls << "\n";
        out << "  :del-clause      " << m_stats.m_del_clause << "\n";
        out << "  :avg-clause-size " << (total_cls == 0 ? 0.0 : static_cast<double>(num_lits) / static_cast<double>(total_cls)) << "\n";
        out << "  :memory          " << std::fixed << std::setprecision(2) << mem << ")" << std::endl;
    }

    void stats::collect_statistics(statistics & st) const {
        st.update("sat mk clause 2ary", m_mk_bin_clause);
        st.update("sat mk clause 3ary", m_mk_ter_clause);
        st.update("sat mk clause nary", m_mk_clause);
        st.update("sat mk var", m_mk_var);
        st.update("sat gc clause", m_gc_clause);
        st.update("sat del clause", m_del_clause);
        st.update("sat conflicts", m_conflict);
        st.update("sat decisions", m_decision);
        st.update("sat propagations 2ary", m_bin_propagate);
        st.update("sat propagations 3ary", m_ter_propagate);
        st.update("sat propagations nary", m_propagate);
        st.update("sat restarts", m_restart);
        st.update("sat minimized lits", m_minimized_lits);
        st.update("sat shrunken lits", m_shrunken_lits);
        st.update("sat subs resolution dyn", m_dyn_sub_res);
        st.update("sat blocked correction sets", m_blocked_corr_sets);
        st.update("sat units", m_units);
        st.update("sat elim bool vars res", m_elim_var_res);
        st.update("sat elim bool vars bdd", m_elim_var_bdd);
        st.update("sat backjumps", m_backjumps);
        st.update("sat backtracks", m_backtracks);
        st.update("sat chrono backtracks", m_chrono_backtracks);
        st.update("sat trail reuse", m_trail_reuse);
        st.update("sat elim eqs inplace", m_elim_eqs_inplace);
        st.update("sat eager subsumed", m_eager_subsumed);
        st.update("sat otfs strengthened", m_otfs_strengthened);
    }

    void stats::reset() {
        memset(this, 0, sizeof(*this));
    }

    void mk_stat::display(std::ostream & out) const {
        unsigned given, redundant;
        m_solver.num_binary(given, redundant);
        out << " " << std::setw(5) << m_solver.m_clauses.size() + given << "/" << given;
        out << " " << std::setw(5) << (m_solver.m_learned.size() + redundant - m_solver.m_num_frozen) << "/" << redundant;
        out << " " << std::setw(3)  << m_solver.init_trail_size();
        out << " " << std::setw(7)  << m_solver.m_stats.m_gc_clause << " ";
        out << " " << std::setw(7)  << mem_stat();
    }

    std::ostream & operator<<(std::ostream & out, mk_stat const & stat) {
        stat.display(out);
        return out;
    }

    bool solver::all_distinct(literal_vector const& lits) {
        init_visited();
        for (literal l : lits) {
            if (is_visited(l.var())) {
                return false;
            }
            mark_visited(l.var());
        }
        return true;
    }

    bool solver::all_distinct(clause const& c) {
        init_visited();
        for (literal l : c) {
            if (is_visited(l.var())) {
                return false;
            }
            mark_visited(l.var());
        }
        return true;
    }

};
