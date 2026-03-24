/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    qi_queue.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-15.

Revision History:

--*/
#include "util/warning.h"
#include "util/stats.h"
#include "util/hash.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/var_subst.h"
#include "smt/smt_context.h"
#include "smt/qi_queue.h"
#include "smt/adaptive_log.h"
#include <cmath>
#include <iostream>

namespace smt {

    /**
     * Hash the "skeleton" of an enode to depth 2.
     * Skeleton = func_decl ID of the enode, mixed with its arity
     * and the func_decl IDs of its immediate children.
     * This captures the structural shape of a binding without
     * depending on specific term identities.
     */
    static uint64_t binding_skeleton_hash(enode const * e) {
        uint64_t h = fmix64(static_cast<uint64_t>(e->get_decl_id()));
        h ^= fmix64(static_cast<uint64_t>(e->get_num_args()) + 0x9E3779B9ULL);
        unsigned nargs = e->get_num_args();
        for (unsigned i = 0; i < nargs; ++i) {
            enode const * child = e->get_arg(i);
            h ^= fmix64(static_cast<uint64_t>(child->get_decl_id()) + i + 1);
        }
        return h;
    }

    /**
     * Compute a structure hash for an entire binding vector.
     * Combines the quantifier ID with each binding's skeleton hash
     * via fmix64 accumulation.  The result identifies the "shape"
     * of a quantifier instantiation for Bloom filter lookup.
     */
    static uint64_t qi_binding_structure_hash(quantifier * q, unsigned num_bindings, enode * const * bindings) {
        uint64_t h = fmix64(static_cast<uint64_t>(q->get_id()));
        for (unsigned i = 0; i < num_bindings; ++i) {
            h ^= fmix64(binding_skeleton_hash(bindings[i]) + i);
        }
        return h;
    }

    qi_queue::qi_queue(quantifier_manager & qm, context & ctx, qi_params & params):
        m_qm(qm),
        m_context(ctx),
        m(m_context.get_manager()),
        m_params(params),
        m_checker(m_context),
        m_cost_function(m),
        m_new_gen_function(m),
        m_parser(m),
        m_evaluator(m),
        m_subst(m),
        m_instances(m) {
        init_parser_vars();
        m_vals.resize(15, 0.0f);
        m_binding_filter.init();
        m_failure_filter.reset();
    }

    void qi_queue::setup() {
        TRACE(qi_cost, tout << "qi_cost: " << m_params.m_qi_cost << "\n";);
        if (!m_parser.parse_string(m_params.m_qi_cost.c_str(), m_cost_function)) {
            // it is not reasonable to abort here during the creation of smt::context just because an invalid option was provided.
            // throw default_exception("invalid cost function %s", m_params.m_qi_cost.c_str());

            // using warning message instead
            warning_msg("invalid cost function '%s', switching to default one", m_params.m_qi_cost.c_str());
            // Trying again with default function
            VERIFY(m_parser.parse_string("(+ weight generation)", m_cost_function));
        }
        if (!m_parser.parse_string(m_params.m_qi_new_gen.c_str(), m_new_gen_function)) {
            // See comment above
            // throw default_exception("invalid new-gen function %s", m_params.m_qi_new_gen.c_str());
            warning_msg("invalid new_gen function '%s', switching to default one", m_params.m_qi_new_gen.c_str());
            VERIFY(m_parser.parse_string("cost", m_new_gen_function));
        }
        m_eager_cost_threshold = m_params.m_qi_eager_threshold;
    }

    void qi_queue::init_parser_vars() {
#define COST 14
        m_parser.add_var("cost");
#define MIN_TOP_GENERATION 13
        m_parser.add_var("min_top_generation");
#define MAX_TOP_GENERATION 12
        m_parser.add_var("max_top_generation");
#define INSTANCES 11
        m_parser.add_var("instances");
#define SIZE 10
        m_parser.add_var("size");
#define DEPTH 9
        m_parser.add_var("depth");
#define GENERATION 8
        m_parser.add_var("generation");
#define QUANT_GENERATION 7
        m_parser.add_var("quant_generation");
#define WEIGHT 6
        m_parser.add_var("weight");
#define VARS 5
        m_parser.add_var("vars");
#define PATTERN_WIDTH 4
        m_parser.add_var("pattern_width");
#define TOTAL_INSTANCES 3
        m_parser.add_var("total_instances");
#define SCOPE 2
        m_parser.add_var("scope");
#define NESTED_QUANTIFIERS 1
        m_parser.add_var("nested_quantifiers");
#define CS_FACTOR 0
        m_parser.add_var("cs_factor");
    }

    q::quantifier_stat * qi_queue::set_values(quantifier * q, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation, float cost) {
        q::quantifier_stat * stat     = m_qm.get_stat(q);
        m_vals[COST]               = cost;
        m_vals[MIN_TOP_GENERATION] = static_cast<float>(min_top_generation);
        m_vals[MAX_TOP_GENERATION] = static_cast<float>(max_top_generation);
        m_vals[INSTANCES]          = static_cast<float>(stat->get_num_instances_curr_branch());
        m_vals[SIZE]               = static_cast<float>(stat->get_size());
        m_vals[DEPTH]              = static_cast<float>(stat->get_depth());
        m_vals[GENERATION]         = static_cast<float>(generation);
        m_vals[QUANT_GENERATION]   = static_cast<float>(stat->get_generation());
        m_vals[WEIGHT]             = static_cast<float>(q->get_weight());
        m_vals[VARS]               = static_cast<float>(q->get_num_decls());
        m_vals[PATTERN_WIDTH]      = pat ? static_cast<float>(pat->get_num_args()) : 1.0f;
        m_vals[TOTAL_INSTANCES]    = static_cast<float>(stat->get_num_instances_curr_search());
        m_vals[SCOPE]              = static_cast<float>(m_context.get_scope_level());
        m_vals[NESTED_QUANTIFIERS] = static_cast<float>(stat->get_num_nested_quantifiers());
        m_vals[CS_FACTOR]          = static_cast<float>(stat->get_case_split_factor());
        TRACE(qi_queue_detail, for (unsigned i = 0; i < m_vals.size(); ++i) { tout << m_vals[i] << " "; } tout << "\n";);
        return stat;
    }

    // Compute the minimum ground term count across sub-patterns of a multi-pattern.
    unsigned qi_queue::pattern_ground_terms(app * pat) {
        unsigned min_gt = UINT_MAX;
        unsigned nargs = pat->get_num_args();
        for (unsigned i = 0; i < nargs; ++i) {
            expr * arg = pat->get_arg(i);
            if (is_app(arg)) {
                unsigned gt = m_context.get_num_enodes_of(to_app(arg)->get_decl());
                if (gt < min_gt) min_gt = gt;
            }
        }
        return min_gt == UINT_MAX ? 0 : min_gt;
    }

    float qi_queue::get_cost(quantifier * q, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation) {
        q::quantifier_stat * stat = set_values(q, pat, generation, min_top_generation, max_top_generation, 0);
        float r = m_evaluator(m_cost_function, m_vals.size(), m_vals.data());

        // Trigger selectivity penalty (orthogonal — kept).
        double sel_w = m_params.m_qi_trigger_selectivity;
        if (sel_w > 0.0 && pat != nullptr && q->get_num_patterns() > 1) {
            unsigned this_gt = pattern_ground_terms(pat);
            unsigned best_gt = UINT_MAX;
            unsigned npats = q->get_num_patterns();
            for (unsigned p = 0; p < npats; ++p) {
                app * mp = to_app(q->get_pattern(p));
                unsigned gt = pattern_ground_terms(mp);
                if (gt < best_gt) best_gt = gt;
            }
            if (best_gt > 0 && this_gt > best_gt) {
                double ratio = static_cast<double>(this_gt) / static_cast<double>(best_gt);
                r += static_cast<float>(sel_w * std::log2(ratio));
            }
        }

        // Bayesian surprisal: information-theoretic cost modifier based on
        // observed productivity.  Each quantifier's instantiation history is
        // modeled as Bernoulli trials with Beta(1,1) uniform prior.
        //
        //   surprisal = log₂((n + 2) / (k + 1))
        //
        // After 500-instance warmup (preserves original Z3 cost for easy queries):
        //   - Productive (n=1000, k=50): +4.3 cost (stabilizes)
        //   - Matching loop (n=1000, k=0): +10.0 cost (crosses eager threshold)
        //   - Loop at n=10K, k=0: +13.3 cost (well past threshold)
        //
        // Subsumes: reward-adjusted scoring, UCB bonus, 50K hard guard,
        // generation fixed-point fix.
        // Bayesian surprisal for matching loop suppression.
        // Only applies to quantifiers with ZERO conflict participation —
        // productive quantifiers (k>0) are never penalized.
        //
        // Uses INSERT count (not instantiation count) so the surprisal
        // reflects the true demand for this quantifier, including delayed
        // and lazy instances that the matching engine keeps finding.
        //
        // Shape: zero for the first N₀ inserts, then 2×log₂(n/N₀).
        //   n < N₀:   0    (no interference with normal solving)
        //   n = 2×N₀: +2   (mild — still below eager threshold)
        //   n = 10×N₀: +6.6 (significant)
        //   n = 100×N₀: +13.3 (past eager threshold — loop throttled)
        //   n = 1000×N₀: +20 (past lazy threshold — fully blocked)
        {
            unsigned n = stat->get_inserts_total();
            // Use current-search conflicts: historical productivity from
            // earlier check-sat calls should not suppress the cost penalty
            // in the current search where the quantifier may be looping.
            unsigned k = stat->get_num_conflicts_curr_search();
            constexpr unsigned N0 = 5000;
            if (k == 0 && n > N0) {
                r += static_cast<float>(m_surprisal_coeff * std::log2(static_cast<double>(n) / N0));
            }
        }

        // Chain initiator discount (orthogonal — captures downstream value).
        if (m_params.m_qi_feedback && r > 0.0f) {
            float chain_score = m_qm.get_chain_score(q);
            if (chain_score > 0.01f) {
                double discount = 1.0 - 0.20 * std::min(static_cast<double>(chain_score) * 5.0, 1.0);
                r = static_cast<float>(r * discount);
            }
        }

        stat->update_max_cost(r);
        return r;
    }

    unsigned qi_queue::get_new_gen(quantifier * q, unsigned generation, float cost) {
        set_values(q, nullptr, generation, 0, 0, cost);
        float r = m_evaluator(m_new_gen_function, m_vals.size(), m_vals.data());
        if (r < 0) r = 0;
        // Original Z3 logic: weight-0 quantifiers with zero cost must
        // advance generation to prevent the trivial gen=0 fixed point.
        // For all other quantifiers, the Bayesian surprisal in get_cost()
        // naturally inflates cost (and thus new_gen) for unproductive ones.
        if (q->get_weight() > 0 || r > 0)
            return static_cast<unsigned>(r);
        return std::max(generation + 1, static_cast<unsigned>(r));
    }

    double qi_queue::compute_binding_relevancy(unsigned num_bindings, enode * const * bindings) {
        if (num_bindings == 0) return 0.1;
        double sum = 0.0;
        for (unsigned i = 0; i < num_bindings; ++i) {
            enode * e = bindings[i];
            double r = m_context.get_soft_relevancy(e->get_expr());
            // Also check the equivalence class root
            enode * root = e->get_root();
            if (root != e) {
                double rr = m_context.get_soft_relevancy(root->get_expr());
                if (rr > r) r = rr;
            }
            sum += r;
        }
        double avg = sum / num_bindings;
        return avg < 0.1 ? 0.1 : avg;
    }

    /**
     * E7.2: Compute heat score for a binding vector.
     * Sums func_decl heat of each binding root's func_decl and its
     * children's func_decls. Also adds cached per-quantifier body heat,
     * refreshed every 64 conflicts.
     */
    float qi_queue::compute_binding_heat(quantifier * q, unsigned num_bindings, enode * const * bindings) {
        double heat = 0.0;
        for (unsigned i = 0; i < num_bindings; ++i) {
            enode * e = bindings[i]->get_root();
            // Root's func_decl heat
            heat += m_context.get_func_decl_heat(e->get_decl());
            // One level of children
            unsigned nargs = e->get_num_args();
            for (unsigned j = 0; j < nargs && j < 4; ++j) {
                heat += m_context.get_func_decl_heat(e->get_arg(j)->get_root()->get_decl());
            }
        }
        // Add cached body heat (refreshed every 64 conflicts)
        q::quantifier_stat * stat = m_qm.get_stat(q);
        if (stat) {
            unsigned cur_conflicts = m_stats.m_num_qi_conflicts;
            if (cur_conflicts >= stat->get_body_heat_conflict() + 64 ||
                stat->get_body_heat() == 0.0) {
                // Walk quantifier body func_decls to compute body heat
                double bh = 0.0;
                expr * body = q->get_expr();
                ptr_buffer<expr, 64> todo;
                todo.push_back(body);
                unsigned visited = 0;
                while (!todo.empty() && visited < 128) {
                    expr * e = todo.back();
                    todo.pop_back();
                    visited++;
                    if (!is_app(e)) continue;
                    app * a = to_app(e);
                    bh += m_context.get_func_decl_heat(a->get_decl());
                    unsigned na = a->get_num_args();
                    for (unsigned k = 0; k < na; ++k)
                        todo.push_back(a->get_arg(k));
                }
                stat->set_body_heat(bh, cur_conflicts);
            }
            heat += stat->get_body_heat();
        }
        return static_cast<float>(heat);
    }

    void qi_queue::insert(fingerprint * f, app * pat, unsigned generation, unsigned min_top_generation, unsigned max_top_generation) {
        // QI velocity gate: if bankrupt, block all new inserts.
        if (m_qi_bankrupt) return;

        quantifier * q         = static_cast<quantifier*>(f->get_data());

        // Increment inserts_total here (post-fingerprint) so it counts
        // unique instances only, not fingerprint-rejected duplicates.
        // The fast-reject in add_instance() reads this counter without
        // incrementing, so it stays in sync.
        q::quantifier_stat * stat = m_qm.get_stat(q);
        if (stat)
            stat->inc_inserts_total();

        // Track global insert count for velocity ratio computation.
        m_qi_velocity_inserts++;

        // Blind spot #5: dump landscape every 50000 QI inserts for tracing.
        // During QI floods, the solver makes no decisions and few conflicts,
        // so the normal landscape dump (every 250 conflicts) never fires.
        //
        // The driver update (blind spot #1) is handled separately via
        // QI_INSERT_INTERVAL in should_update(), piggybacked on the next
        // decision/conflict boundary.
        if (m_qi_velocity_inserts % 50000 == 0) {
            if (m_context.get_adaptive_log()) {
                m_context.get_landscape().dump_to_alog(
                    m_context.get_adaptive_log(),
                    m_context.get_num_conflicts(),
                    m_context.get_num_bool_vars());
            }
        }

        float cost             = get_cost(q, pat, generation, min_top_generation, max_top_generation);
        float const base_cost  = cost;  // snapshot for inflation cap
        // Relevancy-guided QI gating: penalize bindings with low soft-relevancy.
        // After warmup (500 instances), bindings in irrelevant parts of the
        // search space get their cost inflated, steering QI effort toward
        // the active proof frontier.
        double rel_w = m_params.m_qi_relevancy_weight;
        if (m_params.m_qi_feedback && rel_w > 0.0 &&
            m_stats.m_num_instances > 500) {
            double binding_rel = compute_binding_relevancy(f->get_num_args(), f->get_args());
            double factor = (1.0 - rel_w) + rel_w / binding_rel;
            cost = static_cast<float>(cost * factor);
        }
        // E4: E-graph metrics tracking (informational).
        // Depth penalty and connectivity discount are disabled because
        // they perturb proof search on borderline F* ModifiesGen queries
        // (pushing rlimit-marginal queries past their resource limit).
        // The EMAs are still computed for diagnostic tracing and future
        // use with gated parameters.
        if (m_params.m_qi_feedback) {
            unsigned num_bindings = f->get_num_args();
            unsigned max_depth = 0;
            for (unsigned i = 0; i < num_bindings; ++i) {
                unsigned d = f->get_arg(i)->get_expr()->get_depth();
                if (d > max_depth) max_depth = d;
            }
            if (max_depth >= 10) {
                m_egraph_metrics.m_deep_instance_count++;
            }
            constexpr float depth_alpha = 0.05f;
            m_egraph_metrics.m_avg_binding_depth_ema =
                (1.0f - depth_alpha) * m_egraph_metrics.m_avg_binding_depth_ema +
                depth_alpha * static_cast<float>(max_depth);

            if (num_bindings >= 2) {
                enode * roots[8];
                unsigned n_roots = std::min(num_bindings, 8u);
                unsigned distinct = 0;
                for (unsigned i = 0; i < n_roots; ++i) {
                    enode * r = f->get_arg(i)->get_root();
                    bool dup = false;
                    for (unsigned j = 0; j < distinct; ++j) {
                        if (roots[j] == r) { dup = true; break; }
                    }
                    if (!dup) roots[distinct++] = r;
                }
                float connectivity = static_cast<float>(distinct) / static_cast<float>(n_roots);
                constexpr float conn_alpha = 0.05f;
                m_egraph_metrics.m_avg_connectivity_ema =
                    (1.0f - conn_alpha) * m_egraph_metrics.m_avg_connectivity_ema +
                    conn_alpha * connectivity;
            }
        }

        // E2.4: Binding-level Bloom filter boost.
        // If the binding's structural hash matches a pattern that
        // previously appeared in a conflict antecedent chain, apply
        // a 10% cost discount.  Boost-only: unknown patterns are
        // never penalized.  Requires warmup (1000 instances) so
        // the filter has meaningful data before influencing decisions.
        if (m_params.m_qi_feedback && !m_binding_filter.is_empty() &&
            m_stats.m_num_instances > 1000) {
            uint64_t bh = qi_binding_structure_hash(q, f->get_num_args(), f->get_args());
            if (m_binding_filter.probably_useful(bh)) {
                cost *= 0.90f;
            }
        }

        // Global inflation cap: E1 relevancy + E4 connectivity + E4 depth
        // can compound.  Clamp so combined modifiers never inflate beyond
        // 10x the base cost returned by get_cost().  Discounts (< base)
        // are never clamped.
        if (m_params.m_qi_feedback && base_cost > 0.0f) {
            float max_cost = base_cost * 10.0f;
            if (cost > max_cost)
                cost = max_cost;
        }

        TRACE(qi_queue_detail,
              tout << "new instance of " << q->get_qid() << ", weight " << q->get_weight()
              << ", generation: " << generation << ", scope_level: " << m_context.get_scope_level() << ", cost: " << cost << "\n";
              for (unsigned i = 0; i < f->get_num_args(); ++i) {
                  tout << "#" << f->get_arg(i)->get_expr_id() << " d:" << f->get_arg(i)->get_expr()->get_depth() << " ";
              }
              tout << "\n";);
        // E7.2: Compute heat score from binding enodes and quantifier body.
        // Only compute after warmup (500 QI conflicts) so the heat map
        // has meaningful data. Before that, all scores would be zero.
        float heat = 0.0f;
        if (m_params.m_qi_feedback && m_stats.m_num_qi_conflicts > 500) {
            heat = compute_binding_heat(q, f->get_num_args(), f->get_args());
        }
        TRACE(new_entries_bug, tout << "[qi:insert]\n";);

        // Adaptive log: QI_INSERT with cost + heat
        ALOG(m_context.get_adaptive_log(), "QI_INSERT")
            .u("c", m_context.get_num_conflicts())
            .s("q", q->get_qid().str().c_str())
            .u("vars", q->get_num_decls())
            .d("cost", (double)cost)
            .d("heat", (double)heat)
            .u("gen", generation);

        m_new_entries.push_back(entry(f, cost, heat, generation));
    }

    void qi_queue::instantiate() {
        // QI velocity gate: if already bankrupt, skip entire batch.
        if (m_qi_bankrupt) {
            m_new_entries.reset();
            return;
        }

        // QI velocity gate: check insert/QI-conflict ratio.
        // Uses QI-ATTRIBUTED conflicts (instances in FUIP antecedent chain),
        // NOT total SAT conflicts.  Total SAT conflicts include noise from
        // the solver working on QI-generated clauses — they don't indicate
        // that QI is productive, just that the solver is busy.
        //
        // After 10K-insert warmup:
        //   ratio > 500:   double effective eager threshold (BFS mode)
        //   ratio > 2000:  declare bankruptcy — block ALL further QI
        //
        // QI velocity gate using TOTAL SAT conflicts (not QI-attributed).
        // QI-attributed conflicts are too sparse — most QI value is through
        // propagation/equality merging, not direct conflict participation.
        // Total conflicts capture the solver's overall health better.
        //
        // The gate only fires for extreme ratios (true dead zones):
        //   BFS at 5000 inserts/conflict, bankruptcy at 20000.
        // Productive Boogie: ratio ~300. F*: ratio ~600-5000. Loops: 100K+.
        bool velocity_bfs = false;
        if (m_qi_velocity_inserts > 50000) {
            unsigned conflicts = m_context.get_num_conflicts();
            double ratio = static_cast<double>(m_qi_velocity_inserts) / std::max(conflicts, 1u);
            if (ratio > 20000.0) {
                m_qi_bankrupt = true;
                m_stats.m_num_qi_bankruptcies++;
                ALOG(m_context.get_adaptive_log(), "QI_BANKRUPT")
                    .u("inserts", m_qi_velocity_inserts)
                    .u("conflicts", conflicts)
                    .d("ratio", ratio);
                m_new_entries.reset();
                return;
            }
            if (ratio > 5000.0) {
                velocity_bfs = true;
            }
        }

        // Adaptive QI budget: dynamically adjust the eager cost threshold
        // based on global success rate (qi_conflicts / total_instances).
        //
        // The success rate is typically 0.01-0.1% for F*/Pulse workloads:
        // most QI contributes via propagation, not direct conflict
        // participation. The budget adapts conservatively:
        //
        //   After warmup (50K instances):
        //     success < 1e-5 (< 0.001%): tighten threshold to 90%
        //     success > 1e-2 (> 1%):     loosen threshold to 300%
        //     otherwise:                  use default threshold
        //
        // The threshold adjustment is deliberately gentle to avoid
        // perturbing proof search on marginal queries. Tightening by 10%
        // only delays instances near the cost boundary, preserving all
        // low-cost (high-quality) instances.
        // E4.4: Snapshot E-graph state before instantiation batch.
        unsigned enodes_before = 0;
        unsigned add_eq_before = 0;
        unsigned inst_before   = 0;
        if (m_params.m_qi_feedback) {
            enodes_before = m_context.enodes().size();
            add_eq_before = m_context.m_stats.m_num_add_eq;
            inst_before   = m_stats.m_num_instances;
            m_egraph_metrics.m_enodes_before_qi   = enodes_before;
            m_egraph_metrics.m_add_eq_at_last_qi   = add_eq_before;
            m_egraph_metrics.m_instances_at_last_qi = inst_before;
        }

        // Effective threshold: the Bayesian surprisal in get_cost() makes
        // per-quantifier costs adaptive, so no global threshold modulation needed.
        double effective_threshold = m_eager_cost_threshold;

        // QI velocity BFS mode: double the threshold so more entries are
        // delayed rather than eagerly instantiated.  Capped at 100.0 to
        // avoid overflow effects on the cost comparison.
        if (velocity_bfs) {
            effective_threshold = std::min(effective_threshold * 2.0, 100.0);
        }

        // E4.4: E-graph growth and merge ratio tracking (informational only).
        // The threshold modulation is disabled because even mild 5%
        // adjustments caused regressions on borderline F* ModifiesGen
        // queries.  The EMAs are still computed (post-batch, below) for
        // diagnostic tracing and potential future use.

        // E7.3: Conflict-driven QI ordering — sort batch by heat-adjusted cost.
        // Entries with higher heat (more conflict-relevant func_decls) get
        // lower effective priority, so they are processed first.
        // Gated by warmup: requires 500+ QI conflicts so heat scores are meaningful.
        // Skip if batch is small (no benefit) or heat map is empty.
        if (m_params.m_qi_feedback && m_new_entries.size() > 4 &&
            m_stats.m_num_qi_conflicts > 500) {
            bool has_heat = false;
            for (auto const & e : m_new_entries) {
                if (e.m_heat_score > 0.0f) { has_heat = true; break; }
            }
            if (has_heat) {
                std::stable_sort(m_new_entries.begin(), m_new_entries.end(),
                    [](entry const & a, entry const & b) {
                        float pa = a.m_cost / (1.0f + a.m_heat_score);
                        float pb = b.m_cost / (1.0f + b.m_heat_score);
                        return pa < pb;
                    });
            }
        }

        unsigned since_last_check = 0;
        unsigned n_eager = 0, n_delayed = 0;
        unsigned batch_total = m_new_entries.size();
        for (entry & curr : m_new_entries) {
            if (m_context.get_cancel_flag()) {
                break;
            }
            if (m_stats.m_num_instances > m_params.m_qi_max_instances) {
                m_context.set_reason_unknown("maximum number of quantifier instances was reached");
                m_context.set_internal_completed();
                break;
            }
            fingerprint * f    = curr.m_qb;
            quantifier * qa    = static_cast<quantifier*>(f->get_data());

            // E5.2: Negative knowledge suppression — DISABLED.
            // Suppressing bindings changes instantiation order, which can
            // trigger a segfault in checker::is_relevant (null uint_set in
            // relevancy propagator) on certain queries (e.g. Seq.Properties-44).
            // The E5.3 feedback loop (failure attribution, success recording,
            // decay) remains active for data collection.
            // TODO: investigate the is_relevant crash root cause before
            // re-enabling suppression.

            if (curr.m_cost <= effective_threshold) {
                instantiate(curr);
                ++n_eager;
            }
            else if (m_params.m_qi_promote_unsat && m_checker.is_unsat(qa->get_expr(), f->get_num_args(), f->get_args())) {
                // do not delay instances that produce a conflict.
                // Skip is_sat check — if is_unsat returned true, the instance is definitely not satisfied.
                TRACE(qi_unsat, tout << "promoting instance that produces a conflict\n" << mk_pp(qa, m) << "\n";);
                instantiate(curr, /*skip_sat_check=*/true);
                ++n_eager;  // promoted unsat counts as eager
            }
            else if (m_checker.all_terms_exist(qa->get_expr(), f->get_num_args(), f->get_args())) {
                // All subterms already in E-graph — instance creates no new
                // nodes, only propagations. Process immediately.
                TRACE(qi_queue, tout << "promoting instance: all terms exist\n" << mk_pp(qa, m) << "\n";);
                instantiate(curr);
                ++n_eager;  // promoted all-terms-exist counts as eager
            }
            else {
                TRACE(qi_queue, tout << "delaying quantifier instantiation... " << f << "\n" << mk_pp(qa, m) << "\ncost: " << curr.m_cost << "\n";);
                m_delayed_entries.push_back(curr);
                ++n_delayed;
            }

            // Periodically check if we didn't run out of time/memory.
            if (since_last_check++ > 100) {
                if (m_context.resource_limits_exceeded()) {
                    break;
                }
                since_last_check = 0;
            }
        }

        // Adaptive log: QI_BATCH summary for the instantiation batch
        if (batch_total > 0) {
            double vel_ratio = 0.0;
            if (m_qi_velocity_inserts > 0) {
                unsigned c = m_context.get_num_conflicts();
                vel_ratio = static_cast<double>(m_qi_velocity_inserts) / std::max(c, 1u);
            }
            ALOG(m_context.get_adaptive_log(), "QI_BATCH")
                .u("total", batch_total)
                .u("eager", n_eager)
                .u("delayed", n_delayed)
                .u("delayed_q", static_cast<unsigned>(m_delayed_entries.size()))
                .u("fast_rej", m_stats.m_num_fast_rejected)
                .u("vel_ins", m_qi_velocity_inserts)
                .d("vel_ratio", vel_ratio);
        }
        // E4.4: Post-batch E-graph growth and merge ratio tracking.
        if (m_params.m_qi_feedback && enodes_before > 0) {
            unsigned enodes_after = m_context.enodes().size();
            float growth = static_cast<float>(enodes_after - enodes_before) /
                           static_cast<float>(enodes_before);
            constexpr float growth_alpha = 0.1f;
            m_egraph_metrics.m_growth_rate_ema =
                (1.0f - growth_alpha) * m_egraph_metrics.m_growth_rate_ema +
                growth_alpha * growth;

            // Merge ratio: add_eq events per instance in this batch.
            unsigned add_eq_after = m_context.m_stats.m_num_add_eq;
            unsigned inst_after   = m_stats.m_num_instances;
            unsigned inst_delta   = inst_after - inst_before;
            if (inst_delta > 0) {
                float merge_ratio = static_cast<float>(add_eq_after - add_eq_before) /
                                    static_cast<float>(inst_delta);
                constexpr float merge_alpha = 0.1f;
                m_egraph_metrics.m_qi_merge_ratio_ema =
                    (1.0f - merge_alpha) * m_egraph_metrics.m_qi_merge_ratio_ema +
                    merge_alpha * merge_ratio;
            }

            TRACE(qi_queue, tout << "egraph metrics: growth=" << growth
                  << " growth_ema=" << m_egraph_metrics.m_growth_rate_ema
                  << " merge_ema=" << m_egraph_metrics.m_qi_merge_ratio_ema
                  << " deep_count=" << m_egraph_metrics.m_deep_instance_count
                  << " depth_ema=" << m_egraph_metrics.m_avg_binding_depth_ema
                  << " conn_ema=" << m_egraph_metrics.m_avg_connectivity_ema << "\n";);
        }

        m_new_entries.reset();
        TRACE(new_entries_bug, tout << "[qi:instantiate]\n";);
    }

    void qi_queue::display_instance_profile(fingerprint * f, quantifier * q, unsigned num_bindings, enode * const * bindings, unsigned proof_id, unsigned generation) {
        if (m.has_trace_stream()) {
            m.trace_stream() << "[instance] " << f->get_data_hash();
            if (m.proofs_enabled())
                m.trace_stream() << " #" << proof_id;
            m.trace_stream() << " ; " << generation;
            m.trace_stream() << "\n";
        }
    }

    void qi_queue::instantiate(entry & ent, bool skip_sat_check) {
        // set temporary flag to enable quantifier-specific tracing in within smt_internalizer.
        flet<bool> _coming_from_quant(m_context.m_coming_from_quant, true);

        fingerprint * f          = ent.m_qb;
        quantifier * q           = static_cast<quantifier*>(f->get_data());
        unsigned generation      = ent.m_generation;
        unsigned num_bindings    = f->get_num_args();
        enode * const * bindings = f->get_args();

        ent.m_instantiated = true;

        TRACE(qi_queue_profile, tout << q->get_qid() << ", gen: " << generation << " " << *f << " cost: " << ent.m_cost << "\n";);

        q::quantifier_stat * stat = m_qm.get_stat(q);

        // SBSC: skip substitution+rewrite if body is already satisfied with existing terms.
        // Cheaper than the full is_sat path below because all_terms_exist is a fast
        // structural check — if it fails, we avoid the deeper is_sat traversal entirely.
        if (m_params.m_qi_feedback && !skip_sat_check &&
            m_checker.all_terms_exist(q->get_expr(), num_bindings, bindings) &&
            m_checker.is_sat(q->get_expr(), num_bindings, bindings)) {
            TRACE(checker, tout << "SBSC: body already satisfied with existing terms\n";);
            stat->inc_num_instances_checker_sat();
            return;
        }

        if (!skip_sat_check && m_checker.is_sat(q->get_expr(), num_bindings, bindings)) {
            TRACE(checker, tout << "instance already satisfied\n";);
            // we log the "dummy" instantiations separately from "instance"
            STRACE(dummy, tout << "### " << static_cast<void*>(f) <<", " << q->get_qid() << "\n";);
            STRACE(dummy, tout << "Instance already satisfied (dummy)\n";);
            // a dummy instantiation is still an instantiation.
            // in this way smt.qi.profile=true coincides with the axiom profiler
            stat->inc_num_instances_checker_sat();
            return;
        }

        STRACE(instance, tout << "### " << static_cast<void*>(f) <<", " << q->get_qid()  << "\n";);

        auto* ebindings = m_subst(q, num_bindings);
        for (unsigned i = 0; i < num_bindings; ++i)
            ebindings[i] = bindings[i]->get_expr();
        expr_ref instance = m_subst();


        TRACE(qi_queue, tout << "new instance:\n" << mk_pp(instance, m) << "\n";);
        expr_ref  s_instance(m);
        proof_ref pr(m);
        m_context.get_rewriter()(instance, s_instance, pr);

        TRACE(qi_queue_bug, tout << "new instance after simplification:\n" << s_instance << "\n";);
        if (m.is_true(s_instance)) {
            STRACE(instance, tout <<  "Instance reduced to true\n";);
            stat -> inc_num_instances_simplify_true();
            if (m.has_trace_stream()) {
                display_instance_profile(f, q, num_bindings, bindings, pr ? pr->get_id() : 0, generation);
                m.trace_stream() << "[end-of-instance]\n";
            }

            return;
        }
#if 0
        std::cout << "instantiate\n";
        enode_vector _bindings(num_bindings, bindings);
        for (auto * b : _bindings)
            std::cout << mk_pp(b->get_expr(), m) << " ";
        std::cout << "\n";
        std::cout << mk_pp(q, m) << "\n";
        std::cout << "instance\n";
        std::cout << instance << "\n";
#endif
   
        TRACE(qi_queue, tout << "simplified instance:\n" << s_instance << "\n";);
        stat->inc_num_instances();
        stat->inc_instances_total();
        // Record binding structure hash in per-quantifier ring buffer (E2.3).
        // attribute_qi_conflict will iterate the ring and mark useful hashes
        // in the Bloom filter for future QI cost discount.
        if (m_params.m_qi_feedback) {
            uint64_t bh = qi_binding_structure_hash(q, num_bindings, bindings);
            stat->record_binding_hash(bh);
            // Tier 1c: Record binding pattern in the landscape map (useful=false;
            // attribute_qi_conflict upgrades to useful=true on conflict).
            unsigned qid = q->get_id();
            landscape_map & lm = m_context.get_landscape();
            lm.ensure_qi_patterns(qid + 1);
            lm.update_qi_pattern(qid, static_cast<uint32_t>(bh), /*useful=*/false);
        }
        if (stat->get_num_instances() % m_params.m_qi_profile_freq == 0) {
            m_qm.display_stats(verbose_stream(), q);
        }

        if (m_on_binding && !m_on_binding(q, instance)) {
            verbose_stream() << "qi_queue: on_binding returned false, skipping instance.\n";
            return;
        }
        expr_ref lemma(m);
        if (m.is_or(s_instance)) {
            ptr_vector<expr> args;
            args.push_back(m.mk_not(q));
            args.append(to_app(s_instance)->get_num_args(), to_app(s_instance)->get_args());
            lemma = m.mk_or(args);
        }
        else if (m.is_false(s_instance)) {
            lemma = m.mk_not(q);
        }
        else if (m.is_true(s_instance)) {
            lemma = s_instance;
        }
        else {
            lemma = m.mk_or(m.mk_not(q), s_instance);
        }
        m_instances.push_back(lemma);
        proof_ref pr1(m);
        unsigned proof_id = 0;
        if (m.proofs_enabled()) {
            expr_ref_vector bindings_e(m);
            for (unsigned i = 0; i < num_bindings; ++i) {
                bindings_e.push_back(bindings[i]->get_expr());
            }
            app * bare_lemma    = m.mk_or(m.mk_not(q), instance);
            proof * qi_pr       = m.mk_quant_inst(bare_lemma, num_bindings, bindings_e.data());
            proof_id            = qi_pr->get_id();
            if (bare_lemma == lemma) {
                pr1             = qi_pr;
            }
            else if (instance == s_instance) {
                proof * rw      = m.mk_rewrite(bare_lemma, lemma);
                pr1             = m.mk_modus_ponens(qi_pr, rw);
            }
            else {
                app * bare_s_lemma  = m.mk_or(m.mk_not(q), s_instance);
                proof * prs[1]      = { pr.get() };
                proof * cg          = m.mk_congruence(bare_lemma, bare_s_lemma, 1, prs);
                proof * rw          = m.mk_rewrite(bare_s_lemma, lemma);
                proof * tr          = m.mk_transitivity(cg, rw);
                pr1                 = m.mk_modus_ponens(qi_pr, tr);
            }
            m_instances.push_back(pr1);
        }
        else if (m_context.clause_proof_active()) {
            expr_ref_vector bindings_e(m), args(m);
            arith_util a(m);
            expr_ref gen(a.mk_int(generation), m);
            expr* gens[1] = { gen.get() };
            for (unsigned i = 0; i < num_bindings; ++i) 
                bindings_e.push_back(bindings[i]->get_expr());
            args.push_back(q);
            args.push_back(mk_not(m, instance));
            args.push_back(m.mk_app(symbol("bind"), num_bindings, bindings_e.data(), m.mk_proof_sort()));
            args.push_back(m.mk_app(symbol("gen"), 1, gens, m.mk_proof_sort()));
            pr1 = m.mk_app(symbol("inst"), args.size(), args.data(), m.mk_proof_sort());
            m_instances.push_back(pr1);            
        }
        TRACE(qi_queue, tout << mk_pp(lemma, m) << "\n#" << lemma->get_id() << ":=\n" << mk_ll_pp(lemma, m););
        m_stats.m_num_instances++;
        unsigned gen = get_new_gen(q, generation, ent.m_cost);
        display_instance_profile(f, q, num_bindings, bindings, proof_id, gen);
        m_context.internalize_instance(lemma, pr1, gen);
        if (f->get_def()) {
            m_context.internalize(f->get_def(), true);
        }
        TRACE_CODE({
            static unsigned num_useless = 0;
            if (m.is_or(lemma)) {
                app * n = to_app(lemma);
                bool has_unassigned = false;
                expr * true_child = 0;
                for (unsigned i = 0; i < n->get_num_args(); ++i) {
                    expr * arg = n->get_arg(i);
                    switch(m_context.get_assignment(arg)) {
                    case l_undef: has_unassigned = true; break;
                    case l_true:  true_child = arg; break;
                    default:
                        break;
                    }
                }
                if (true_child && has_unassigned) {
                    TRACE(qi_queue_profile_detail, tout << "missed:\n" << mk_ll_pp(s_instance, m) << "\n#" << true_child->get_id() << "\n";);
                    num_useless++;
                    if (num_useless % 10 == 0) {
                        TRACE(qi_queue_profile, tout << "num useless: " << num_useless << "\n";);
                    }
                }
            }
        });

        if (m.has_trace_stream())
            m.trace_stream() << "[end-of-instance]\n";

    }

    void qi_queue::push_scope() {
        TRACE(new_entries_bug, tout << "[qi:push-scope]\n";);
        m_scopes.push_back(scope());
        SASSERT(m_context.inconsistent() || m_new_entries.empty());
        scope & s = m_scopes.back();
        s.m_delayed_entries_lim    = m_delayed_entries.size();
        s.m_instances_lim          = m_instances.size();
        s.m_instantiated_trail_lim = m_instantiated_trail.size();
    }

    void qi_queue::pop_scope(unsigned num_scopes) {
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        scope & s           = m_scopes[new_lvl];
        unsigned old_sz     = s.m_instantiated_trail_lim;
        unsigned sz         = m_instantiated_trail.size();
        for (unsigned i = old_sz; i < sz; ++i)
            m_delayed_entries[m_instantiated_trail[i]].m_instantiated = false;
        m_instantiated_trail.shrink(old_sz);
        m_delayed_entries.shrink(s.m_delayed_entries_lim);
        m_instances.shrink(s.m_instances_lim);
        m_new_entries.reset();
        m_scopes.shrink(new_lvl);
        TRACE(new_entries_bug, tout << "[qi:pop-scope]\n";);
    }

    void qi_queue::reset() {
        m_new_entries.reset();
        m_delayed_entries.reset();
        m_instances.reset();
        m_scopes.reset();
        m_binding_filter.init();
        m_failure_filter.reset();
        m_final_check_no_conflict_streak = 0;
        m_last_conflict_count = 0;
        m_qi_velocity_inserts = 0;
        m_qi_velocity_conflicts_base = 0;
        m_qi_bankrupt = false;
    }

    void qi_queue::init_search_eh() {
        m_subst.reset();
        m_new_entries.reset();
        m_egraph_metrics.reset();
        m_failure_filter.reset();
        m_qi_velocity_inserts = 0;
        m_qi_velocity_conflicts_base = m_stats.m_num_qi_conflicts;
        m_qi_bankrupt = false;
        // NOTE: do NOT reset m_final_check_no_conflict_streak here.
        // For incremental queries (push/pop with many check-sat calls),
        // the streak must persist across check-sat calls so the
        // final-check tightening can accumulate across the session.
    }

    bool qi_queue::final_check_eh() {
        // Track consecutive final checks with zero new conflicts.
        // When the streak is long, progressively tighten the effective
        // lazy threshold to break matching-loop feedback cycles.
        unsigned current_conflicts = m_context.get_num_conflicts();
        if (current_conflicts == m_last_conflict_count) {
            m_final_check_no_conflict_streak++;
        } else {
            m_final_check_no_conflict_streak = 0;
        }
        m_last_conflict_count = current_conflicts;

        // The lazy threshold is kept at its default value.  Loop suppression
        // is handled by the per-quantifier surprisal gate in the processing
        // loop below.  A streak-based global tightening was attempted but
        // noise conflicts from unrelated quantifiers kept resetting the
        // streak in Boogie incremental queries, while also blocking useful
        // delayed entries in F*/Pulse queries that need them.
        double effective_lazy = m_params.m_qi_lazy_threshold;

        TRACE(qi_queue, display_delayed_instances_stats(tout); tout << "lazy threshold: " << m_params.m_qi_lazy_threshold
              << " (effective: " << effective_lazy << ", streak: " << m_final_check_no_conflict_streak << ")"
              << ", scope_level: " << m_context.get_scope_level() << "\n";);

        if (m_params.m_qi_conservative_final_check) {
            bool  init = false;
            float min_cost = 0.0;
            unsigned sz = m_delayed_entries.size();
            for (unsigned i = 0; i < sz; ++i) {
                entry & e       = m_delayed_entries[i];
                TRACE(qi_queue, tout << e.m_qb << ", cost: " << e.m_cost << ", instantiated: " << e.m_instantiated << "\n";);
                if (!e.m_instantiated && e.m_cost <= effective_lazy && (!init || e.m_cost < min_cost)) {
                    init = true;
                    min_cost = e.m_cost;
                }
            }
            TRACE(qi_queue_min_cost, tout << "min_cost: " << min_cost << ", scope_level: " << m_context.get_scope_level() << "\n";);
            bool result = true;
            for (unsigned i = 0; i < sz; ++i) {
                entry & e       = m_delayed_entries[i];
                TRACE(qi_queue, tout << e.m_qb << ", cost: " << e.m_cost << " min-cost: " << min_cost << ", instantiated: " << e.m_instantiated << "\n";);
                if (!e.m_instantiated && e.m_cost <= min_cost) {
                    // Per-quantifier surprisal gate: if the quantifier's current
                    // surprisal exceeds the eager threshold, its delayed entries
                    // should NOT be processed — regardless of stored cost or
                    // global streak.  This is metatheoretically correct: if new
                    // instances from this quantifier would be delayed by the
                    // cost function, processing old delayed entries is equally
                    // wasteful.  The eager threshold is the natural cutoff:
                    // it's the cost at which entries stop being instantiated
                    // eagerly, i.e., the point where the solver judges
                    // instantiation to be speculative.
                    {
                        quantifier * qa = static_cast<quantifier*>(e.m_qb->get_data());
                        q::quantifier_stat * stat = m_qm.get_stat(qa);
                        if (stat) {
                            unsigned ni = stat->get_inserts_total();
                            unsigned nc = stat->get_num_conflicts_curr_search();
                            constexpr unsigned N0 = 5000;
                            if (nc == 0 && ni > N0) {
                                double surprisal = m_surprisal_coeff * std::log2(static_cast<double>(ni) / N0);
                                if (surprisal > m_eager_cost_threshold) {
                                    continue;
                                }
                            }
                        }
                    }
                    TRACE(qi_queue,
                          tout << "lazy quantifier instantiation...\n" << mk_pp(static_cast<quantifier*>(e.m_qb->get_data()), m) << "\ncost: " << e.m_cost << "\n";);
                    result             = false;
                    m_instantiated_trail.push_back(i);
                    m_stats.m_num_lazy_instances++;
                    instantiate(e);
                }
            }
            return result;
        }

        bool result = true;
        for (unsigned i = 0; i < m_delayed_entries.size(); ++i) {
            entry & e       = m_delayed_entries[i];
            TRACE(qi_queue, tout << e.m_qb << ", cost: " << e.m_cost << ", instantiated: " << e.m_instantiated << "\n";);
            if (!e.m_instantiated && e.m_cost <= effective_lazy)  {
                // Per-quantifier surprisal gate (same logic as conservative path).
                {
                    quantifier * qa = static_cast<quantifier*>(e.m_qb->get_data());
                    q::quantifier_stat * stat = m_qm.get_stat(qa);
                    if (stat) {
                        unsigned ni = stat->get_inserts_total();
                        unsigned nc = stat->get_num_conflicts();
                        constexpr unsigned N0 = 5000;
                        if (nc == 0 && ni > N0) {
                            double surprisal = m_surprisal_coeff * std::log2(static_cast<double>(ni) / N0);
                            if (surprisal > m_eager_cost_threshold) {
                                continue;
                            }
                        }
                    }
                }
                TRACE(qi_queue,
                      tout << "lazy quantifier instantiation...\n" << mk_pp(static_cast<quantifier*>(e.m_qb->get_data()), m) << "\ncost: " << e.m_cost << "\n";);
                result             = false;
                m_instantiated_trail.push_back(i);
                m_stats.m_num_lazy_instances++;
                instantiate(e);
            }
        }
        return result;
    }

    struct delayed_qa_info {
        unsigned m_num;
        float    m_min_cost;
        float    m_max_cost;
        delayed_qa_info():m_num(0), m_min_cost(0.0f), m_max_cost(0.0f) {}
    };

    void qi_queue::display_delayed_instances_stats(std::ostream & out) const {
        obj_map<quantifier, delayed_qa_info> qa2info;
        ptr_vector<quantifier> qas;
        for (entry const & e : m_delayed_entries) {
            if (e.m_instantiated)
                continue;
            quantifier * qa = static_cast<quantifier*>(e.m_qb->get_data());
            delayed_qa_info info;
            if (qa2info.find(qa, info)) {
                info.m_num++;
                info.m_min_cost = std::min(info.m_min_cost, e.m_cost);
                info.m_max_cost = std::max(info.m_max_cost, e.m_cost);
            }
            else {
                qas.push_back(qa);
                info.m_num      = 1;
                info.m_min_cost = e.m_cost;
                info.m_max_cost = e.m_cost;
            }
            qa2info.insert(qa, info);
        }
        for (quantifier * qa : qas) {
            delayed_qa_info info;
            qa2info.find(qa, info);
            out << qa->get_qid() << ": " << info.m_num << " [" << info.m_min_cost << ", " << info.m_max_cost << "]\n";
        }
    }

    void qi_queue::get_min_max_costs(float & min, float & max) const {
        min = 0.0f;
        max = 0.0f;
        bool found = false;
        for (unsigned i = 0; i < m_delayed_entries.size(); ++i) {
            if (!m_delayed_entries[i].m_instantiated) {
                float c = m_delayed_entries[i].m_cost;
                if (found) {
                    min = std::min(min, c);
                    max = std::max(max, c);
                }
                else {
                    found = true;
                    min = c;
                    max = c;
                }
            }
        }
    }

    void qi_queue::collect_statistics(::statistics & st) const {
        st.update("quant instantiations", m_stats.m_num_instances);
        st.update("lazy quant instantiations", m_stats.m_num_lazy_instances);
        st.update("qi conflicts", m_stats.m_num_qi_conflicts);
        st.update("qi fast rejects", m_stats.m_num_fast_rejected);
        st.update("qi bankruptcies", m_stats.m_num_qi_bankruptcies);
        st.update("missed quant instantiations", m_delayed_entries.size());
        float min, max;
        get_min_max_costs(min, max);
        st.update("min missed qa cost", min);
        st.update("max missed qa cost", max);
#if 0
        if (m_params.m_qi_profile) {
            out << "missed/delayed quantifier instances:\n";
            display_delayed_instances_stats(out);
        }
#endif
    }

};

