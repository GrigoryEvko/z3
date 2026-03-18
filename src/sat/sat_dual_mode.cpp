/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_dual_mode.cpp

Abstract:

    CaDiCaL-style dual-mode search: alternates between focused mode
    (VMTF queue + aggressive Glucose restarts) and stable mode
    (VSIDS heap + reluctant doubling restarts).

    VMTF queue: doubly-linked list ordered by bump timestamp.
    Mode switching: geometrically doubling intervals.
    Each mode has its own EMA averages for restart decisions.

Author:

    Z3 contributors

--*/

#include "sat/sat_solver.h"

namespace sat {

    // -----------------------
    //
    // VMTF queue operations
    //
    // -----------------------

    void solver::vmtf_dequeue(bool_var v) {
        SASSERT(v < m_vmtf_links.size());
        vmtf_link& lk = m_vmtf_links[v];
        if (lk.prev != null_bool_var)
            m_vmtf_links[lk.prev].next = lk.next;
        else
            m_vmtf_queue_head = lk.next;
        if (lk.next != null_bool_var)
            m_vmtf_links[lk.next].prev = lk.prev;
        else
            m_vmtf_queue_tail = lk.prev;
    }

    void solver::vmtf_enqueue(bool_var v) {
        SASSERT(v < m_vmtf_links.size());
        vmtf_link& lk = m_vmtf_links[v];
        lk.prev = m_vmtf_queue_tail;
        lk.next = null_bool_var;
        if (m_vmtf_queue_tail != null_bool_var)
            m_vmtf_links[m_vmtf_queue_tail].next = v;
        else
            m_vmtf_queue_head = v;
        m_vmtf_queue_tail = v;
    }

    void solver::vmtf_init_var(bool_var v) {
        while (m_vmtf_links.size() <= v) {
            m_vmtf_links.push_back(vmtf_link());
            m_vmtf_bumped.push_back(0);
        }
        m_vmtf_bumped[v] = ++m_vmtf_counter;
        vmtf_enqueue(v);
        vmtf_update_search(v);
    }

    void solver::vmtf_update_search(bool_var v) {
        if (value(v) == l_undef) {
            if (m_vmtf_search == null_bool_var ||
                m_vmtf_bumped[v] > m_vmtf_bumped[m_vmtf_search])
                m_vmtf_search = v;
        }
    }

    void solver::vmtf_bump(bool_var v) {
        if (v == null_bool_var || v >= m_vmtf_links.size())
            return;
        // Already at tail (most recently bumped)? Nothing to do.
        if (m_vmtf_links[v].next == null_bool_var)
            return;
        vmtf_dequeue(v);
        m_vmtf_bumped[v] = ++m_vmtf_counter;
        vmtf_enqueue(v);
        if (value(v) == l_undef)
            m_vmtf_search = v;
    }

    bool_var solver::vmtf_next_decision() {
        // Walk backwards from search hint toward head,
        // looking for the first unassigned, non-eliminated variable.
        bool_var res = m_vmtf_search;
        while (res != null_bool_var &&
               (value(res) != l_undef || was_eliminated(res))) {
            res = m_vmtf_links[res].prev;
        }
        if (res != null_bool_var)
            m_vmtf_search = res;
        return res;
    }

    void solver::vmtf_reinit_after_simplify() {
        // After simplification (variable elimination, SCC, etc.), the VMTF
        // bump timestamps reflect pre-simplification conflict patterns and
        // are meaningless for the post-simplification formula.  Reset all
        // timestamps to a uniform sequential order so focused mode starts
        // fresh.  This mirrors CaDiCaL's behavior where the queue is
        // effectively reinitialized after inprocessing.
        if (!m_config.m_dual_mode || m_vmtf_links.empty())
            return;

        unsigned nv = num_vars();
        m_vmtf_counter = 0;

        // Rebuild the queue from scratch in variable-ID order.
        // Variable-ID order is a reasonable default: variables created
        // later by bit-blasting tend to be structurally deeper and often
        // more useful for focused-mode decisions.
        m_vmtf_links.reset();
        m_vmtf_links.resize(nv);
        m_vmtf_bumped.reset();
        m_vmtf_bumped.resize(nv, 0);
        m_vmtf_queue_head = null_bool_var;
        m_vmtf_queue_tail = null_bool_var;
        m_vmtf_search = null_bool_var;
        for (bool_var v = 0; v < static_cast<bool_var>(nv); ++v) {
            if (was_eliminated(v))
                continue;
            m_vmtf_bumped[v] = ++m_vmtf_counter;
            vmtf_enqueue(v);
            if (value(v) == l_undef)
                m_vmtf_search = v;
        }

        IF_VERBOSE(3, verbose_stream() << "(sat.vmtf-reinit :vars " << nv
                   << " :counter " << m_vmtf_counter << ")\n");
    }

    // -----------------------
    //
    // Dual-mode switching
    //
    // -----------------------

    // Checks whether it's time to switch modes. If so, performs the switch
    // and returns the new value of m_stable_mode.
    //
    // Adaptive variant of CaDiCaL's Internal::stabilizing(): instead of
    // unconditional geometric doubling, the interval growth is governed by
    // per-mode learning quality (average LBD/glue).
    //
    // If stable mode consistently produces higher-glue (worse) clauses than
    // focused mode, the interval shrinks — the solver spends less time in
    // stable mode.  If stable mode is competitive, normal doubling proceeds.
    // This self-tunes: pure-SAT/BV problems (where VSIDS+reluctant hurts)
    // automatically converge to mostly-focused search, while SMT problems
    // (where stable mode helps) get the standard CaDiCaL behavior.
    bool solver::stabilizing() {
        if (!m_config.m_dual_mode)
            return false;

        // Primary trigger: conflict count exceeds limit.
        bool conflict_trigger = m_conflicts_since_init > m_stabilize_limit;

        // Fallback trigger: if the solver has done many decisions without
        // generating any new conflicts (stuck in VMTF deterministic loop),
        // force a mode switch based on decision count.
        bool decision_trigger = false;
        if (!m_stable_mode && !conflict_trigger) {
            uint64_t decisions_in_mode = m_stats.m_decision - m_stabilize_last_decisions;
            uint64_t conflicts_in_mode = m_conflicts_since_init -
                (m_stabilize_last_conflicts > m_conflicts_since_init ? 0 : m_stabilize_last_conflicts);
            if (conflicts_in_mode == 0 &&
                decisions_in_mode > 2 * static_cast<uint64_t>(m_config.m_stabilize_initial))
                decision_trigger = true;
        }

        if (!conflict_trigger && !decision_trigger)
            return m_stable_mode;

        // Record learning quality for the just-completed phase.
        // Require a minimum sample size to avoid noisy adaptation.
        if (m_phase_conflict_count >= 100) {
            double avg = static_cast<double>(m_phase_glue_sum) / m_phase_conflict_count;
            if (m_stable_mode) {
                m_stable_avg_glue = avg;
                m_adaptive_has_stable = true;
            } else {
                m_focused_avg_glue = avg;
                m_adaptive_has_focused = true;
            }
        }
        m_phase_glue_sum = 0;
        m_phase_conflict_count = 0;

        if (m_stabilize_inc == 0)
            m_stabilize_inc = m_config.m_stabilize_initial;
        if (m_stabilize_inc == 0)
            m_stabilize_inc = 1000;

        uint64_t next_delta = m_stabilize_inc;
        bool next_stable = !m_stable_mode;
        m_stabilize_limit = m_conflicts_since_init + next_delta;
        m_stabilize_last_ticks = m_conflicts_since_init;
        m_stabilize_last_decisions = m_stats.m_decision;
        m_stabilize_last_conflicts = m_conflicts_since_init;
        m_stable_mode = next_stable;

        if (m_stable_mode) {
            m_stab_phases++;
            // Adaptive interval growth based on relative learning quality.
            // ratio = stable_avg_glue / focused_avg_glue:
            //   > 1.3  → stable much worse: shrink interval (min = initial)
            //   > 1.1  → stable slightly worse: stagnate (no growth)
            //   <= 1.1 → stable competitive: normal doubling
            uint64_t min_inc = std::max(static_cast<uint64_t>(m_config.m_stabilize_initial),
                                        uint64_t(500));
            if (m_adaptive_has_stable && m_adaptive_has_focused && m_focused_avg_glue > 0) {
                double ratio = m_stable_avg_glue / m_focused_avg_glue;
                if (ratio > 1.3)
                    m_stabilize_inc = std::max(m_stabilize_inc / 2, min_inc);
                else if (ratio <= 1.1)
                    m_stabilize_inc = std::min(m_stabilize_inc * 2, static_cast<uint64_t>(1u << 20));
                // else: stagnate (no growth, no shrink)
            } else {
                // No comparison data yet → normal doubling.
                m_stabilize_inc = std::min(m_stabilize_inc * 2, static_cast<uint64_t>(1u << 20));
            }
            reluctant_enable();
        }

        // Each mode gets its own EMA averages and tick counters.
        std::swap(m_fast_glue_avg, m_fast_glue_backup);
        std::swap(m_slow_glue_avg, m_slow_glue_backup);
        std::swap(m_search_ticks, m_search_ticks_backup);
        std::swap(m_ticks_at_last_restart, m_ticks_restart_backup);

        IF_VERBOSE(2, verbose_stream() << "(sat.dual-mode :mode "
                   << (m_stable_mode ? "stable" : "focused")
                   << " :phase " << m_stab_phases
                   << " :conflicts " << m_conflicts_since_init
                   << " :next-limit " << m_stabilize_limit
                   << " :inc " << m_stabilize_inc;
                   if (m_adaptive_has_stable && m_adaptive_has_focused)
                       verbose_stream() << " :ratio "
                           << (m_focused_avg_glue > 0 ? m_stable_avg_glue / m_focused_avg_glue : 0.0);
                   verbose_stream() << ")\n");

        return m_stable_mode;
    }

    // -----------------------
    //
    // Reluctant doubling (Knuth/Luby) for stable-mode restarts
    //
    // -----------------------

    void solver::reluctant_enable() {
        m_reluctant_u = 1;
        m_reluctant_v = 1;
        m_reluctant_period = 1024;
        m_reluctant_countdown = m_reluctant_period;
        m_reluctant_triggered = false;
    }

    void solver::reluctant_tick() {
        if (m_reluctant_triggered) return;
        if (--m_reluctant_countdown > 0) return;
        // Knuth's reluctant doubling sequence (DK)
        if ((m_reluctant_u & (~m_reluctant_u + 1)) == m_reluctant_v) {
            m_reluctant_u++;
            m_reluctant_v = 1;
        } else {
            m_reluctant_v *= 2;
        }
        // Cap at 1048576 conflicts to prevent indefinite non-restarting.
        static constexpr uint64_t MAX_RELUCTANT_PERIOD = 1048576;
        uint64_t next = m_reluctant_v * m_reluctant_period;
        m_reluctant_countdown = std::min(next, MAX_RELUCTANT_PERIOD);
        m_reluctant_triggered = true;
    }

    bool solver::reluctant_triggered() {
        if (!m_reluctant_triggered) return false;
        m_reluctant_triggered = false;
        return true;
    }

}
