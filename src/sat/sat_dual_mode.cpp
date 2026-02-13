/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_dual_mode.cpp

Abstract:

    CaDiCaL-style dual-mode search: alternates between focused mode
    (VMTF queue + aggressive Glucose restarts) and stable mode
    (VSIDS heap + reluctant doubling restarts).

    VMTF queue: doubly-linked list ordered by bump timestamp.
    Mode switching: quadratically increasing intervals.
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

    // -----------------------
    //
    // Dual-mode switching
    //
    // -----------------------

    // Checks whether it's time to switch modes. If so, performs the switch
    // and returns the new value of m_stable_mode.
    // Modeled on CaDiCaL's Internal::stabilizing().
    bool solver::stabilizing() {
        if (!m_config.m_dual_mode)
            return false;
        if (m_conflicts_since_init <= m_stabilize_limit)
            return m_stable_mode;

        // Time to switch modes.
        uint64_t delta = m_conflicts_since_init > m_stabilize_last_ticks
                       ? m_conflicts_since_init - m_stabilize_last_ticks : 1;
        if (m_stabilize_inc == 0)
            m_stabilize_inc = delta;
        if (m_stabilize_inc == 0)
            m_stabilize_inc = 1;

        // Quadratic scaling of phase duration.
        uint64_t next_delta = m_stabilize_inc;
        uint64_t sp = static_cast<uint64_t>(m_stab_phases) + 1;
        next_delta *= sp * sp;

        bool next_stable = !m_stable_mode;
        m_stabilize_limit = m_conflicts_since_init + next_delta;
        m_stabilize_last_ticks = m_conflicts_since_init;
        m_stable_mode = next_stable;

        if (m_stable_mode) {
            m_stab_phases++;
            reluctant_enable();
        }

        // Each mode gets its own EMA averages.
        std::swap(m_fast_glue_avg, m_fast_glue_backup);
        std::swap(m_slow_glue_avg, m_slow_glue_backup);

        IF_VERBOSE(2, verbose_stream() << "(sat.dual-mode :mode "
                   << (m_stable_mode ? "stable" : "focused")
                   << " :phase " << m_stab_phases
                   << " :conflicts " << m_conflicts_since_init
                   << " :next-limit " << m_stabilize_limit << ")\n");

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
        m_reluctant_period = 512;
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
        m_reluctant_countdown = m_reluctant_v * m_reluctant_period;
        m_reluctant_triggered = true;
    }

    bool solver::reluctant_triggered() {
        if (!m_reluctant_triggered) return false;
        m_reluctant_triggered = false;
        return true;
    }

}
