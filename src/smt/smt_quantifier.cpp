/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_quantifier.cpp

Abstract:

    Quantifier reasoning support for smt::context.

Author:

    Leonardo de Moura (leonardo) 2012-02-16.

Revision History:

--*/
#include <cmath>
#include <iomanip>
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/quantifier_stat.h"
#include "smt/smt_quantifier.h"
#include "smt/smt_context.h"
#include "smt/smt_model_finder.h"
#include "smt/smt_model_checker.h"
#include "smt/smt_quick_checker.h"
#include "smt/mam.h"
#include "smt/qi_queue.h"
#include "smt/adaptive_log.h"
#include "util/obj_hashtable.h"

namespace smt {

    quantifier_manager_plugin * mk_default_plugin();

    void log_single_justification(std::ostream & out, enode *en, obj_hashtable<enode> &visited, context &ctx, ast_manager &m);

    /**
         \brief Ensures that all relevant proof steps to explain why the enode is equal to the root of its
        equivalence class are in the log and up-to-date.
    */
    void quantifier_manager::log_justification_to_root(std::ostream & out, enode *en, obj_hashtable<enode> &visited, context &ctx, ast_manager &m) {
        enode *root = en->get_root();
        for (enode *it = en; it != root; it = it->get_trans_justification().m_target) {
            if (visited.find(it) == visited.end()) visited.insert(it);
            else break;

            if (!it->m_proof_is_logged) {
                log_single_justification(out, it, visited, ctx, m);
                it->m_proof_is_logged = true;
            } else if (it->get_trans_justification().m_justification.get_kind() == smt::eq_justification::kind::CONGRUENCE) {

                // When the justification of an argument changes m_proof_is_logged is not reset => We need to check if the proofs of all arguments are logged.
                const unsigned num_args = it->get_num_args();
                enode *target = it->get_trans_justification().m_target;

                for (unsigned i = 0; i < num_args; ++i) {
                    log_justification_to_root(out, it->get_arg(i), visited, ctx, m);
                    log_justification_to_root(out, target->get_arg(i), visited, ctx, m);
                }
                it->m_proof_is_logged = true;
            }
        }
        if (!root->m_proof_is_logged) {
            out << "[eq-expl] #" << root->get_owner_id() << " root\n";
            root->m_proof_is_logged = true;
        }
    }

    /**
         \brief Logs a single equality explanation step and, if necessary, recursively calls log_justification_to_root to log
        equalities needed by the step (e.g. argument equalities for congruence steps).
    */
    void log_single_justification(std::ostream & out, enode *en, obj_hashtable<enode> &visited, context &ctx, ast_manager &m) {
        smt::literal lit;
        unsigned num_args;
        enode *target = en->get_trans_justification().m_target;
        theory_id th_id;

        switch (en->get_trans_justification().m_justification.get_kind()) {
        case smt::eq_justification::kind::EQUATION:
            lit = en->get_trans_justification().m_justification.get_literal();
            out << "[eq-expl] #" << en->get_owner_id() << " lit #" << ctx.bool_var2expr(lit.var())->get_id() << " ; #" << target->get_owner_id() << "\n";
            break;
        case smt::eq_justification::kind::AXIOM:
            out << "[eq-expl] #" << en->get_owner_id() << " ax ; #" << target->get_owner_id() << "\n";
            break;
        case smt::eq_justification::kind::CONGRUENCE:
            if (!en->get_trans_justification().m_justification.used_commutativity()) {
                num_args = en->get_num_args();

                for (unsigned i = 0; i < num_args; ++i) {
                    quantifier_manager::log_justification_to_root(out, en->get_arg(i), visited, ctx, m);
                    quantifier_manager::log_justification_to_root(out, target->get_arg(i), visited, ctx, m);
                }

                out << "[eq-expl] #" << en->get_owner_id() << " cg";
                for (unsigned i = 0; i < num_args; ++i) {
                    out << " (#" << en->get_arg(i)->get_owner_id() << " #" << target->get_arg(i)->get_owner_id() << ")";
                }
                out << " ; #" << target->get_owner_id() << "\n";

                break;
            } else {

                // The e-graph only supports commutativity for binary functions
                out << "[eq-expl] #" << en->get_owner_id()
                    << " cg (#" << en->get_arg(0)->get_owner_id() << " #" << target->get_arg(1)->get_owner_id()
                    << ") (#" << en->get_arg(1)->get_owner_id() << " #" << target->get_arg(0)->get_owner_id()
                    << ") ; #" << target->get_owner_id() << "\n";
                break;
            }
        case smt::eq_justification::kind::JUSTIFICATION:
            th_id = en->get_trans_justification().m_justification.get_justification()->get_from_theory();
            if (th_id != null_theory_id) {
                symbol const theory = m.get_family_name(th_id);
                out << "[eq-expl] #" << en->get_owner_id() << " th " << theory.str() << " ; #" << target->get_owner_id() << "\n";
            } else {
                out << "[eq-expl] #" << en->get_owner_id() << " unknown ; #" << target->get_owner_id() << "\n";
            }
            break;
        default:
            out << "[eq-expl] #" << en->get_owner_id() << " unknown ; #" << target->get_owner_id() << "\n";
            break;
        }
    }

    struct quantifier_manager::imp {
        quantifier_manager &                   m_wrapper;
        context &                              m_context;
        smt_params &                           m_params;
        qi_queue                               m_qi_queue;
        obj_map<quantifier, q::quantifier_stat *> m_quantifier_stat;
        q::quantifier_stat_gen                    m_qstat_gen;
        ptr_vector<quantifier>                 m_quantifiers;
        scoped_ptr<quantifier_manager_plugin>  m_plugin;
        unsigned                               m_num_instances = 0;
        unsigned                               m_qc_skip_count = 0;
        unsigned                               m_qc_skip_threshold = 0;

        // MAM matching / fingerprint dedup counters for adaptive trace
        unsigned                               m_mam_match_total = 0;
        unsigned                               m_fp_hit_total = 0;
        unsigned                               m_fp_miss_total = 0;

        // E12: QI dependency graph — 1-ply successor lookup.
        // trigger_map: func_decl -> quantifiers triggered by it.
        // successors:  Q -> quantifiers whose triggers use func_decls from Q's body.
        // chain_scores: Q -> cached 1-ply chain score.
        obj_map<func_decl, ptr_vector<quantifier>*>  m_trigger_map;
        obj_map<quantifier, ptr_vector<quantifier>*> m_successors;
        obj_map<quantifier, float>                   m_chain_scores;
        unsigned                                      m_chain_score_restart = UINT_MAX;
        unsigned                                      m_restart_counter = 0;
        bool                                          m_dep_graph_built = false;
        ptr_vector<ptr_vector<quantifier>>            m_dep_allocs; // owned allocations for cleanup

        imp(quantifier_manager & wrapper, context & ctx, smt_params & p, quantifier_manager_plugin * plugin):
            m_wrapper(wrapper),
            m_context(ctx),
            m_params(p),
            m_qi_queue(m_wrapper, ctx, p),
            m_qstat_gen(ctx.get_manager(), ctx.get_region()),
            m_plugin(plugin) {
            m_qi_queue.setup();
        }

        ~imp() {
            // Free heap-allocated ptr_vectors stored in m_dep_allocs.
            // ptr_vector's destructor only frees its own storage, not pointed-to objects.
            for (auto * v : m_dep_allocs)
                dealloc(v);
        }

        ast_manager& m() const { return m_context.get_manager(); }
        bool has_trace_stream() const { return m().has_trace_stream(); }
        std::ostream & trace_stream() { return m().trace_stream(); }

        q::quantifier_stat * get_stat(quantifier * q) const {
            return m_quantifier_stat.find(q);
        }

        unsigned get_generation(quantifier * q) const {
            return get_stat(q)->get_generation();
        }

        void add(quantifier * q, unsigned generation) {
            q::quantifier_stat * stat = m_qstat_gen(q, generation);
            m_quantifier_stat.insert(q, stat);
            m_quantifiers.push_back(q);
            m_plugin->add(q);
        }

        bool has_quantifiers() const { return !m_quantifiers.empty(); }

        /**
         * E12.1: Build the static QI dependency graph.
         * For each quantifier Q: collect uninterpreted func_decls in body,
         * build trigger_map (func_decl -> triggered quantifiers), then
         * build successors (Q -> quantifiers whose triggers overlap Q's body).
         * Self-loops excluded. Called once per search in init_search_eh().
         */
        void build_dep_graph() {
            // Clean up previous graph allocations.
            for (auto * v : m_dep_allocs)
                dealloc(v);
            m_dep_allocs.reset();
            m_trigger_map.reset();
            m_successors.reset();
            m_chain_scores.reset();
            m_dep_graph_built = false;

            if (m_quantifiers.empty())
                return;

            // Step 1: Build trigger_map — func_decl* -> quantifiers triggered by it.
            for (quantifier * q : m_quantifiers) {
                unsigned npats = q->get_num_patterns();
                for (unsigned p = 0; p < npats; ++p) {
                    expr * pat = q->get_pattern(p);
                    // Walk the pattern tree to collect trigger func_decls.
                    ptr_buffer<expr, 32> todo;
                    todo.push_back(pat);
                    while (!todo.empty()) {
                        expr * e = todo.back();
                        todo.pop_back();
                        if (!is_app(e)) continue;
                        app * a = to_app(e);
                        func_decl * fd = a->get_decl();
                        if (fd->get_family_id() == null_family_id) {
                            // Uninterpreted func_decl — register as trigger.
                            ptr_vector<quantifier> * vec = nullptr;
                            if (!m_trigger_map.find(fd, vec)) {
                                vec = alloc(ptr_vector<quantifier>);
                                m_dep_allocs.push_back(vec);
                                m_trigger_map.insert(fd, vec);
                            }
                            // Avoid duplicates within same quantifier.
                            if (vec->empty() || vec->back() != q)
                                vec->push_back(q);
                        }
                        unsigned na = a->get_num_args();
                        for (unsigned i = 0; i < na; ++i)
                            todo.push_back(a->get_arg(i));
                    }
                }
            }

            // Step 2: Build successors — Q -> quantifiers whose triggers overlap Q's body.
            for (quantifier * q : m_quantifiers) {
                expr * body = q->get_expr();
                // Collect uninterpreted func_decls in body.
                ptr_buffer<expr, 64> todo;
                todo.push_back(body);
                unsigned visited = 0;
                ptr_vector<quantifier> * succ = nullptr;

                while (!todo.empty() && visited < 256) {
                    expr * e = todo.back();
                    todo.pop_back();
                    visited++;
                    if (!is_app(e)) continue;
                    app * a = to_app(e);
                    func_decl * fd = a->get_decl();
                    if (fd->get_family_id() == null_family_id) {
                        ptr_vector<quantifier> * triggered = nullptr;
                        if (m_trigger_map.find(fd, triggered)) {
                            for (quantifier * q2 : *triggered) {
                                if (q2 == q) {
                                    // Self-loop: Q's body produces terms matching Q's own trigger.
                                    q::quantifier_stat * stat = get_stat(q);
                                    if (stat) stat->set_self_loop(true);
                                    continue; // skip for dep graph edges
                                }
                                if (!succ) {
                                    succ = alloc(ptr_vector<quantifier>);
                                    m_dep_allocs.push_back(succ);
                                }
                                // Avoid duplicates.
                                bool found = false;
                                for (quantifier * s : *succ) {
                                    if (s == q2) { found = true; break; }
                                }
                                if (!found)
                                    succ->push_back(q2);
                            }
                        }
                    }
                    unsigned na = a->get_num_args();
                    for (unsigned i = 0; i < na; ++i)
                        todo.push_back(a->get_arg(i));
                }

                if (succ)
                    m_successors.insert(q, succ);
            }

            m_dep_graph_built = true;
            m_chain_score_restart = UINT_MAX; // force first recompute

            TRACE(qi_queue,
                  tout << "E12: dep graph built, " << m_quantifiers.size() << " quantifiers, "
                       << m_successors.size() << " with successors\n";
                  for (auto const & kv : m_successors) {
                      tout << "  " << kv.m_key->get_qid() << " -> " << kv.m_value->size() << " successors\n";
                  });
        }

        /**
         * E12.2: Recompute chain scores from successor rewards.
         * 1-ply: score = 0.7 * max(successor rewards) + 0.3 * avg(successor rewards).
         * Called every 5 restarts.
         */
        void recompute_chain_scores() {
            m_chain_scores.reset();
            if (!m_dep_graph_built) return;

            for (auto const & kv : m_successors) {
                quantifier * q = kv.m_key;
                ptr_vector<quantifier> const * succs = kv.m_value;
                if (!succs || succs->empty()) continue;

                double max_reward = 0.0;
                double sum_reward = 0.0;
                unsigned count = 0;

                for (quantifier * q2 : *succs) {
                    q::quantifier_stat * st = nullptr;
                    if (m_quantifier_stat.find(q2, st) && st) {
                        double r = st->get_reward();
                        if (r > max_reward) max_reward = r;
                        sum_reward += r;
                        count++;
                    }
                }

                if (count > 0) {
                    double avg_reward = sum_reward / count;
                    float score = static_cast<float>(0.7 * max_reward + 0.3 * avg_reward);
                    if (score > 0.001f)
                        m_chain_scores.insert(q, score);
                }
            }

            TRACE(qi_queue,
                  tout << "E12: recomputed chain scores for " << m_chain_scores.size() << " quantifiers\n";
                  for (auto const & kv : m_chain_scores) {
                      tout << "  " << kv.m_key->get_qid() << " = " << kv.m_value << "\n";
                  });
        }

        float get_chain_score(quantifier * q) const {
            float s = 0.0f;
            m_chain_scores.find(q, s);
            return s;
        }

        void display_stats(std::ostream & out, quantifier * q) {
            q::quantifier_stat * s     = get_stat(q);
            unsigned num_instances  = s->get_num_instances();
            unsigned num_instances_simplify_true = s->get_num_instances_simplify_true();
            unsigned num_instances_checker_sat  = s->get_num_instances_checker_sat();
            unsigned max_generation = s->get_max_generation();
            unsigned num_conflicts  = s->get_num_conflicts();
            float max_cost          = s->get_max_cost();
            if (num_instances > 0 || num_instances_simplify_true>0 || num_instances_checker_sat>0) {
                out << "[quantifier_instances] ";
                out.width(10);
                out << q->get_qid().str() << " : ";
                out.width(6);
                out << num_instances << " : ";
                out.width(3);
                out << num_instances_simplify_true << " : ";
                out.width(3);
                out << num_instances_checker_sat << " : ";
                out.width(3);
                out << max_generation << " : " << max_cost;
                out << " : " << num_conflicts;
                out << " : " << std::fixed << std::setprecision(4) << s->get_reward() << "\n";
            }
        }

        void del(quantifier * q) {
            if (m_params.m_qi_profile) {
                display_stats(verbose_stream(), q);
            }
            m_quantifiers.pop_back();
            m_quantifier_stat.erase(q);
        }

        bool empty() const {
            return m_quantifiers.empty();
        }

        bool is_shared(enode * n) const {
            return m_plugin->is_shared(n);
        }

        void log_causality(
            fingerprint* f,
            app * pat,
            vector<std::tuple<enode *, enode *>> & used_enodes) {

            if (pat != nullptr) {
                if (used_enodes.size() > 0) {
                    STRACE(causality, tout << "New-Match: "<< static_cast<void*>(f););
                    STRACE(triggers,  tout <<", Pat: "<< expr_ref(pat, m()););
                    STRACE(causality, tout <<", Father:";);
                }
                for (auto n : used_enodes) {
                    enode *orig = std::get<0>(n);
                    enode *substituted = std::get<1>(n);
                    (void) substituted;
                    if (orig == nullptr) {
                        STRACE(causality, tout << " #" << substituted->get_owner_id(););
                    }
                    else {
                        STRACE(causality, tout << " (#" << orig->get_owner_id() << " #" << substituted->get_owner_id() << ")";);
                    }
                }
                if (used_enodes.size() > 0) {
                    STRACE(causality, tout << "\n";);
                }
            }
        }

        void log_add_instance(
             fingerprint* f,
             quantifier * q, app * pat,
             unsigned num_bindings,
             enode * const * bindings,
             vector<std::tuple<enode *, enode *>> & used_enodes) {

            if (pat == nullptr) {
                trace_stream() << "[inst-discovered] MBQI " << f->get_data_hash() << " #" << q->get_id();
                for (unsigned i = 0; i < num_bindings; ++i) {
                    trace_stream() << " #" << bindings[num_bindings - i - 1]->get_owner_id();
                }
                trace_stream() << "\n";
            } else {
                std::ostream & out = trace_stream();

                obj_hashtable<enode> already_visited;

                // In the term produced by the quantifier instantiation the root of the equivalence class of the terms bound to the quantified variables
                // is used. We need to make sure that all of these equalities appear in the log.
                for (unsigned i = 0; i < num_bindings; ++i) {
                    log_justification_to_root(out, bindings[i], already_visited, m_context, m());
                }

                for (auto n : used_enodes) {
                    enode *orig = std::get<0>(n);
                    enode *substituted = std::get<1>(n);
                    if (orig != nullptr) {
                        log_justification_to_root(out, orig, already_visited, m_context, m());
                        log_justification_to_root(out, substituted, already_visited, m_context, m());
                    }
                }

                // At this point all relevant equalities for the match are logged.
                out << "[new-match] " << f->get_data_hash() << " #" << q->get_id() << " #" << pat->get_id();
                for (unsigned i = 0; i < num_bindings; ++i) {
                    // I don't want to use mk_pp because it creates expressions for pretty printing.
                    // This nasty side-effect may change the behavior of Z3.
                    out << " #" << bindings[num_bindings - i - 1]->get_owner_id();
                }
                out << " ;";
                for (auto n : used_enodes) {
                    enode *orig = std::get<0>(n);
                    enode *substituted = std::get<1>(n);
                    if (orig == nullptr)
                        out << " #" << substituted->get_owner_id();
                    else {
                        out << " (#" << orig->get_owner_id() << " #" << substituted->get_owner_id() << ")";
                    }
                }
                out << "\n";
            }
        }

        bool add_instance(quantifier * q, app * pat,
                          unsigned num_bindings,
                          enode * const * bindings,
                          expr* def,
                          unsigned max_generation,
                          unsigned min_top_generation,
                          unsigned max_top_generation,
                          vector<std::tuple<enode *, enode *>> & used_enodes) {

            // Fast-reject: skip fingerprint + insert for quantifiers whose
            // Bayesian surprisal proves they are in a matching loop.
            //
            // The threshold is 2× the eager cost threshold (default 14.0).
            // This blocks at ~640K zero-conflict inserts — well above any
            // productive quantifier (max observed: 9.2K per-quantifier in
            // solved UFLIA queries) and well below any matching loop
            // (min observed: 1.8M in timeout queries, 130× gap).
            //
            // Using lazy_threshold (20.0) here was too permissive: it allowed
            // 5.12M inserts before blocking. Using eager_threshold (7.0)
            // was too aggressive: it blocked at 56K, starving F* definitional
            // axioms that need up to 165K zero-conflict inserts.
            q::quantifier_stat * stat = get_stat(q);
            if (stat) {
                unsigned ni = stat->get_inserts_total();
                // Use current-search conflicts, not lifetime total.
                // A quantifier that had conflicts in earlier check-sat calls
                // but zero in the current search is currently unproductive —
                // historical productivity should not permanently protect
                // against matching loop suppression.
                unsigned nc = stat->get_num_conflicts_curr_search();
                if (nc == 0 && ni > 5000) {
                    double coeff = 2.0;
                    double surprisal = coeff * std::log2(static_cast<double>(ni) / 5000.0);
                    if (surprisal > m_params.m_qi_eager_threshold * 1.05) {
                        return false;
                    }
                }
            }

            // Skip multi-trigger instances if single-trigger already produced
            // instances for this quantifier. Single-trigger matches are more
            // precise; multi-trigger matches are expensive fallbacks.
            if (pat && pat->get_num_args() > 1 && get_stat(q)->had_unary_instance()) {
                TRACE(qi_queue, tout << "skipping multi-trigger instance (single-trigger active): " << q->get_qid() << "\n";);
                return false;
            }

            max_generation = std::max(max_generation, get_generation(q));

            get_stat(q)->update_max_generation(max_generation);
            fingerprint * f = m_context.add_fingerprint(q, q->get_id(), num_bindings, bindings, def);

            // MAM/fingerprint pipeline counters for adaptive trace
            ++m_mam_match_total;
            if (f) {
                ++m_fp_miss_total;  // new fingerprint = miss (not seen before)
                if (pat && pat->get_num_args() == 1)
                    get_stat(q)->set_had_unary_instance();
                if (is_trace_enabled(TraceTag::causality)) {
                    log_causality(f,pat,used_enodes);
                }
                if (has_trace_stream()) {
                    log_add_instance(f, q, pat, num_bindings, bindings, used_enodes);
                }
                m_qi_queue.insert(f, pat, max_generation, min_top_generation, max_top_generation); // TODO
                m_num_instances++;
            }
            else {
                ++m_fp_hit_total;   // duplicate fingerprint = hit (already seen)
            }

            // Periodic MAM pipeline summary (every 10000 matches)
            if (m_mam_match_total > 0 && (m_mam_match_total % 10000) == 0) {
                ALOG(m_context.get_adaptive_log(), "MAM")
                    .u("matches", m_mam_match_total)
                    .u("fp_hit", m_fp_hit_total)
                    .u("fp_miss", m_fp_miss_total);
            }

            CTRACE(bindings, f != nullptr,
                  tout << expr_ref(q, m()) << "\n";
                  for (unsigned i = 0; i < num_bindings; ++i) {
                      tout << expr_ref(bindings[i]->get_expr(), m()) << " [r " << bindings[i]->get_root()->get_owner_id() << "] ";
                  }
                  tout << "\n";
                  );

            return f != nullptr;
        }

        void init_search_eh() {
            m_num_instances = 0;
            m_qc_skip_count = 0;
            m_qc_skip_threshold = 0;
            for (quantifier * q : m_quantifiers) {
                get_stat(q)->reset_num_instances_curr_search();
            }
            m_qi_queue.init_search_eh();
            m_plugin->init_search_eh();
            // E12: Build dependency graph once all quantifiers are registered.
            if (m_params.m_qi_feedback && !m_dep_graph_built)
                build_dep_graph();
            TRACE(smt_params, m_params.display(tout); );
        }

        void assign_eh(quantifier * q) {
            m_plugin->assign_eh(q);
        }

        void add_eq_eh(enode * n1, enode * n2) {
            m_plugin->add_eq_eh(n1, n2);
        }

        void register_on_binding(std::function<bool(quantifier*, expr*)>& on_binding) {
            m_qi_queue.register_on_binding(on_binding);
        }

        void relevant_eh(enode * n) {
            m_plugin->relevant_eh(n);
        }

        void restart_eh() {
            m_plugin->restart_eh();
            m_restart_counter++;
            // Refresh per-quantifier MAM match budgets
            for (quantifier * q : m_quantifiers) {
                q::quantifier_stat * stat = get_stat(q);
                if (stat) stat->refresh_match_budget();
            }
            // E12: Recompute chain scores every 5 restarts.
            if (m_params.m_qi_feedback && m_dep_graph_built) {
                if (m_restart_counter >= m_chain_score_restart + 5 || m_chain_score_restart == UINT_MAX) {
                    recompute_chain_scores();
                    m_chain_score_restart = m_restart_counter;
                }
            }
        }

        void push() {
            m_plugin->push();
            m_qi_queue.push_scope();
        }

        void pop(unsigned num_scopes) {
            m_plugin->pop(num_scopes);
            m_qi_queue.pop_scope(num_scopes);
        }

        bool can_propagate() {
            return m_qi_queue.has_work() || m_plugin->can_propagate();
        }

        void propagate() {
            m_plugin->propagate();
            m_qi_queue.instantiate();
        }

        bool check_quantifier(quantifier* q) {
            return m_context.is_relevant(q) && m_context.get_assignment(q) == l_true;
        }

        bool quick_check_quantifiers() {
            if (m_params.m_qi_quick_checker == MC_NO)
                return true;
            if (m_quantifiers.empty())
                return true;
            // Exponential back-off: skip invocations that are unlikely to find
            // new instances, avoiding repeated overhead on hard queries.
            if (m_qc_skip_count < m_qc_skip_threshold) {
                ++m_qc_skip_count;
                return true;
            }
            m_qc_skip_count = 0;
            IF_VERBOSE(10, verbose_stream() << "quick checking quantifiers (unsat)...\n";);
            quick_checker mc(m_context);
            bool result = true;
            for (quantifier* q : m_quantifiers) {
                if (!mc.has_budget())
                    break;
                if (check_quantifier(q) && mc.instantiate_unsat(q))
                    result = false;
            }
            if (m_params.m_qi_quick_checker == MC_UNSAT || !result) {
                if (!result)
                    m_qc_skip_threshold = 0;
                else
                    m_qc_skip_threshold = std::min(m_qc_skip_threshold + 1, 16u);
                m_qi_queue.instantiate();
                return result;
            }
            // MC_NO_SAT is too expensive (it creates too many irrelevant instances).
            // we should use MBQI=true instead.
            IF_VERBOSE(10, verbose_stream() << "quick checking quantifiers (not sat)...\n";);
            for (quantifier* q : m_quantifiers) {
                if (!mc.has_budget())
                    break;
                if (check_quantifier(q) && mc.instantiate_not_sat(q))
                    result = false;
            }
            if (!result)
                m_qc_skip_threshold = 0;
            else
                m_qc_skip_threshold = std::min(m_qc_skip_threshold + 1, 16u);
            m_qi_queue.instantiate();
            return result;
        }

        final_check_status final_check_eh(bool full) {
            if (full) {
                IF_VERBOSE(100, if (!m_quantifiers.empty()) verbose_stream() << "(smt.final-check \"quantifiers\")\n";);
                final_check_status result  = m_qi_queue.final_check_eh() ? FC_DONE : FC_CONTINUE;
                final_check_status presult = m_plugin->final_check_eh(full);
                if (presult != FC_DONE)
                    result = presult;
                if (m_context.can_propagate())
                    result = FC_CONTINUE;
                if (result == FC_DONE && m_params.m_qi_quick_checker != MC_NO && !quick_check_quantifiers())
                    result = FC_CONTINUE;
                return result;
            }
            else {
                return m_plugin->final_check_eh(false);
            }
        }

        check_model_result check_model(proto_model * m, obj_map<enode, app *> const & root2value) {
            if (empty())
                return SAT;
            return m_plugin->check_model(m, root2value);
        }

    };

    quantifier_manager::quantifier_manager(context & ctx, smt_params & fp, params_ref const & p) {
        m_imp = alloc(imp, *this, ctx, fp, mk_default_plugin());
        m_imp->m_plugin->set_manager(*this);
        m_lazy_scopes = 0;
        m_lazy = true;
        
    }

    quantifier_manager::~quantifier_manager() {
        dealloc(m_imp);
    }

    context & quantifier_manager::get_context() const {
        return m_imp->m_context;
    }

    void quantifier_manager::add(quantifier * q, unsigned generation) {
        if (m_lazy) {
            while (m_lazy_scopes > 0) { --m_lazy_scopes; m_imp->push(); }
            m_lazy = false;
        }
        m_imp->add(q, generation);
    }

    void quantifier_manager::del(quantifier * q) {
        m_imp->del(q);
    }

    bool quantifier_manager::empty() const {
        return m_imp->empty();
    }

    bool quantifier_manager::is_shared(enode * n) const {
        return m_imp->is_shared(n);
    }

    q::quantifier_stat * quantifier_manager::get_stat(quantifier * q) const {
        return m_imp->get_stat(q);
    }

    unsigned quantifier_manager::get_generation(quantifier * q) const {
        return m_imp->get_generation(q);
    }

    bool quantifier_manager::add_instance(quantifier * q, app * pat,
                                          unsigned num_bindings,
                                          enode * const * bindings,
                                          expr* def,
                                          unsigned max_generation,
                                          unsigned min_top_generation,
                                          unsigned max_top_generation,
                                          vector<std::tuple<enode *, enode *>> & used_enodes) {
        return m_imp->add_instance(q, pat, num_bindings, bindings, def, max_generation, min_top_generation, max_top_generation, used_enodes);
    }

    bool quantifier_manager::add_instance(quantifier * q, unsigned num_bindings, enode * const * bindings, expr* def, unsigned generation) {
        vector<std::tuple<enode *, enode *>> tmp;
        return add_instance(q, nullptr, num_bindings, bindings, def, generation, generation, generation, tmp);
    }

    void quantifier_manager::init_search_eh() {
        m_imp->init_search_eh();
    }

    void quantifier_manager::assign_eh(quantifier * q) {
        m_imp->assign_eh(q);
    }

    void quantifier_manager::add_eq_eh(enode * n1, enode * n2) {
        m_imp->add_eq_eh(n1, n2);
    }

    void quantifier_manager::register_on_binding(std::function<bool(quantifier*, expr*)>& on_binding) {
        m_imp->register_on_binding(on_binding);
    }

    void quantifier_manager::inc_global_qi_conflicts() {
        m_imp->m_qi_queue.inc_global_qi_conflicts();
    }

    unsigned quantifier_manager::get_qi_conflicts() const {
        return m_imp->m_qi_queue.get_qi_conflicts();
    }

    void quantifier_manager::mark_binding_useful(uint64_t h) {
        m_imp->m_qi_queue.mark_binding_useful(h);
    }

    void quantifier_manager::record_binding_failure(uint64_t h) {
        m_imp->m_qi_queue.record_binding_failure(h);
    }

    void quantifier_manager::record_binding_success(uint64_t h) {
        m_imp->m_qi_queue.record_binding_success(h);
    }

    void quantifier_manager::on_conflict_failure_decay() {
        m_imp->m_qi_queue.on_conflict_failure_decay();
    }

    void quantifier_manager::attribute_qi_failures_on_restart() {
        // E5.3: At each restart, quantifiers that produced instances
        // in the current search but never contributed to a conflict
        // have their recent binding hashes recorded as failures.
        for (quantifier * q : m_imp->m_quantifiers) {
            q::quantifier_stat * stat = get_stat(q);
            if (!stat) continue;
            if (stat->get_num_instances_curr_search() > 0 &&
                stat->get_num_conflicts_curr_search() == 0) {
                stat->for_each_recent_binding_hash([this](uint64_t h) {
                    m_imp->m_qi_queue.record_binding_failure(h);
                });
            }
        }
    }

    float quantifier_manager::get_chain_score(quantifier * q) const {
        return m_imp->get_chain_score(q);
    }

    unsigned quantifier_manager::get_fp_hit_total() const {
        return m_imp->m_fp_hit_total;
    }

    unsigned quantifier_manager::get_fp_miss_total() const {
        return m_imp->m_fp_miss_total;
    }

    unsigned quantifier_manager::get_qi_velocity_inserts() const {
        return m_imp->m_qi_queue.get_qi_velocity_inserts();
    }

    float quantifier_manager::get_egraph_growth_rate_ema() const {
        return m_imp->m_qi_queue.get_egraph_growth_rate_ema();
    }

    void quantifier_manager::set_eager_threshold(double t) {
        m_imp->m_qi_queue.set_eager_threshold(t);
    }

    void quantifier_manager::relevant_eh(enode * n) {
        m_imp->relevant_eh(n);
    }

    final_check_status quantifier_manager::final_check_eh(bool full) {
        return m_imp->final_check_eh(full);
    }

    void quantifier_manager::restart_eh() {
        m_imp->restart_eh();
    }

    bool quantifier_manager::can_propagate() const {
        return m_imp->can_propagate();
    }

    void quantifier_manager::propagate() {
        m_imp->propagate();
    }

    bool quantifier_manager::model_based() const {
        return m_imp->m_plugin->model_based();
    }

    bool quantifier_manager::has_quantifiers() const {
        return m_imp->has_quantifiers();
    }

    bool quantifier_manager::mbqi_enabled(quantifier *q) const {
        return m_imp->m_plugin->mbqi_enabled(q);
    }

    void quantifier_manager::adjust_model(proto_model * m) {
        m_imp->m_plugin->adjust_model(m);
    }

    quantifier_manager::check_model_result quantifier_manager::check_model(proto_model * m, obj_map<enode, app *> const & root2value) {
        return m_imp->check_model(m, root2value);
    }

    void quantifier_manager::push() {        
        if (m_lazy) 
            ++m_lazy_scopes;
        else 
            m_imp->push();
    }

    void quantifier_manager::pop(unsigned num_scopes) {
        if (m_lazy)
            m_lazy_scopes -= num_scopes;
        else
            m_imp->pop(num_scopes);
    }

    void quantifier_manager::reset() {
        context & ctx        = m_imp->m_context;
        smt_params & p = m_imp->m_params;
        quantifier_manager_plugin * plugin = m_imp->m_plugin->mk_fresh();
        m_imp->~imp();
        m_imp = new (m_imp) imp(*this, ctx, p, plugin);
        plugin->set_manager(*this);
    }

    void quantifier_manager::display(std::ostream & out) const {
    }

    void quantifier_manager::collect_statistics(::statistics & st) const {
        m_imp->m_qi_queue.collect_statistics(st);
    }

    void quantifier_manager::reset_statistics() {
    }

    void quantifier_manager::display_stats(std::ostream & out, quantifier * q) const {
        m_imp->display_stats(out, q);
    }

    ptr_vector<quantifier>::const_iterator quantifier_manager::begin_quantifiers() const {
        return m_imp->m_quantifiers.begin();
    }

    ptr_vector<quantifier>::const_iterator quantifier_manager::end_quantifiers() const {
        return m_imp->m_quantifiers.end();
    }

    unsigned quantifier_manager::num_quantifiers() const {
        return m_imp->m_quantifiers.size();
    }

    // The default plugin uses E-matching, MBQI and quick-checker
    class default_qm_plugin : public quantifier_manager_plugin {
        quantifier_manager *        m_qm;
        smt_params *                m_fparams;
        context *                   m_context;
        scoped_ptr<mam>             m_mam;
        scoped_ptr<mam>             m_lazy_mam;
        scoped_ptr<model_finder>    m_model_finder;
        scoped_ptr<model_checker>   m_model_checker;
        unsigned                    m_new_enode_qhead;
        unsigned                    m_lazy_matching_idx;
        bool                        m_active;
    public:
        default_qm_plugin():
            m_qm(nullptr),
            m_context(nullptr),
            m_new_enode_qhead(0),
            m_lazy_matching_idx(0),
            m_active(false) {
        }

        void set_manager(quantifier_manager & qm) override {
            SASSERT(m_qm == nullptr);
            m_qm            = &qm;
            m_context       = &(qm.get_context());
            m_fparams       = &(m_context->get_fparams());
            ast_manager & m = m_context->get_manager();

            m_mam           = mk_mam(*m_context);
            m_lazy_mam      = mk_mam(*m_context);
            m_model_finder  = alloc(model_finder, m);
            m_model_checker = alloc(model_checker, m, *m_fparams, *(m_model_finder.get()));

            m_model_finder->set_context(m_context);
            m_model_checker->set_qm(qm);
        }

        quantifier_manager_plugin * mk_fresh() override { return alloc(default_qm_plugin); }

        bool model_based() const override { return m_fparams->m_mbqi; }

        bool mbqi_enabled(quantifier *q) const override {
            if (!m_fparams->m_mbqi_id) return true;
            const symbol &s = q->get_qid();
            size_t len = strlen(m_fparams->m_mbqi_id);
            if (s == symbol::null || s.is_numerical())
                return len == 0;
            return strncmp(s.bare_str(), m_fparams->m_mbqi_id, len) == 0;
        }

        /* Quantifier id's must begin with the prefix specified by parameter
           mbqi.id to be instantiated with MBQI. The default value is the
           empty string, so all quantifiers are instantiated. */
        void add(quantifier * q) override {
            TRACE(model_finder, tout << "add " << q->get_id() << ": " << q << " " << m_fparams->m_mbqi << " " << mbqi_enabled(q) << "\n";);
            if (m_fparams->m_mbqi && mbqi_enabled(q)) {
                m_active = true;
                m_model_finder->register_quantifier(q);
            }
        }

        void del(quantifier * q) override { }

        void push() override {
            m_mam->push_scope();
            m_lazy_mam->push_scope();
            m_model_finder->push_scope();            
        }

        void pop(unsigned num_scopes) override {
            m_mam->pop_scope(num_scopes);
            m_lazy_mam->pop_scope(num_scopes);
            m_model_finder->pop_scope(num_scopes);            
        }

        void init_search_eh() override {
            m_lazy_matching_idx = 0;
            m_model_finder->init_search_eh();
            m_model_checker->init_search_eh();            
        }

        void assign_eh(quantifier * q) override {
            m_active = true;
            ast_manager& m = m_context->get_manager();
            (void)m;
            if (!m_fparams->m_ematching) {
                return;
            }
            bool has_unary_pattern = false;
            unsigned num_patterns = q->get_num_patterns();
            for (unsigned i = 0; i < num_patterns; ++i) {
                app * mp = to_app(q->get_pattern(i));
                if (mp->get_num_args() == 1) {
                    has_unary_pattern = true;
                    break;
                }
            }
            unsigned num_eager_multi_patterns = m_fparams->m_qi_max_eager_multipatterns;
            if (!has_unary_pattern)
                num_eager_multi_patterns++;
            for (unsigned i = 0, j = 0; i < num_patterns; ++i) {
                app * mp = to_app(q->get_pattern(i));
                SASSERT(m.is_pattern(mp));
                bool unary = (mp->get_num_args() == 1);
                if (!unary && j >= num_eager_multi_patterns) {
                    TRACE(quantifier, tout << "delaying (too many multipatterns):\n" << mk_ismt2_pp(mp, m) << "\n"
                          << "j: " << j << " unary: " << unary << " m_params.m_qi_max_eager_multipatterns: " << m_fparams->m_qi_max_eager_multipatterns
                          << " num_eager_multi_patterns: " << num_eager_multi_patterns << "\n";);
                    m_lazy_mam->add_pattern(q, mp);
                }
                else {
                    TRACE(quantifier, tout << "adding:\n" << expr_ref(mp, m) << "\n";);
                    m_mam->add_pattern(q, mp);
                }
                if (!unary)
                    j++;
            }
        }

        bool use_ematching() const {
            return m_fparams->m_ematching && !m_qm->empty();
        }

        void add_eq_eh(enode * e1, enode * e2) override {
            if (use_ematching())
                m_mam->add_eq_eh(e1, e2);
        }

        void relevant_eh(enode * e) override {
            if (use_ematching()) {
                m_mam->relevant_eh(e, false);
                m_lazy_mam->relevant_eh(e, true);
            }
        }

        bool can_propagate() const override {
            return m_active && m_mam->has_work();
        }

        void restart_eh() override {
            if (m_fparams->m_mbqi) {
                m_model_finder->restart_eh();
                m_model_checker->restart_eh();
            }
            TRACE(mam_stats, m_mam->display(tout););
        }

        bool is_shared(enode * n) const override {
            return m_active && (m_mam->is_shared(n) || m_lazy_mam->is_shared(n));
        }

        void adjust_model(proto_model * m) override {
            if (m_fparams->m_mbqi) {
                m_model_finder->fix_model(m);
            }
        }

        void propagate() override {
            if (!m_active)
                return;
            m_mam->match();
            if (!m_context->relevancy() && use_ematching()) {
                ptr_vector<enode>::const_iterator it  = m_context->begin_enodes();
                ptr_vector<enode>::const_iterator end = m_context->end_enodes();
                unsigned sz = static_cast<unsigned>(end - it);
                if (sz > m_new_enode_qhead) {
                    m_context->push_trail(value_trail<unsigned>(m_new_enode_qhead));
                    it += m_new_enode_qhead;
                    while (m_new_enode_qhead < sz) {
                        enode * e = *it;
                        m_mam->relevant_eh(e, false);
                        m_lazy_mam->relevant_eh(e, true);
                        m_new_enode_qhead++;
                        it++;
                    }
                }
            }
        }

        quantifier_manager::check_model_result
        check_model(proto_model * m, obj_map<enode, app *> const & root2value) override {
            if (m_fparams->m_mbqi) {
                IF_VERBOSE(10, verbose_stream() << "(smt.mbqi)\n";);
                if (m_model_checker->check(m, root2value)) {
                    return quantifier_manager::SAT;
                }
                else if (m_model_checker->has_new_instances()) {
                    return quantifier_manager::RESTART;
                }
            }
            return quantifier_manager::UNKNOWN;
        }

        final_check_status final_check_eh(bool full) override {
            if (!full) {
                if (m_fparams->m_qi_lazy_instantiation)
                    return final_check_quant();
                return FC_DONE;
            }
            else {
                return final_check_quant();
            }
        }

        /**
           \brief Final check related with quantifiers...
        */
        final_check_status final_check_quant() {
            if (use_ematching()) {
                if (m_lazy_matching_idx < m_fparams->m_qi_max_lazy_multipattern_matching) {
                    m_lazy_mam->rematch();
                    m_context->push_trail(value_trail<unsigned>(m_lazy_matching_idx));
                    m_lazy_matching_idx++;
                }
            }
            return FC_DONE;
        }

    };

    quantifier_manager_plugin * mk_default_plugin() {
        return alloc(default_qm_plugin);
    }

};
