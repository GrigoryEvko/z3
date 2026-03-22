/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    negative_knowledge.h

Abstract:

    4-bit counting Bloom filter for tracking failed QI bindings.
    Records binding structure hashes that produced instances without
    contributing to conflicts.  When a counter reaches the suppression
    threshold, the binding pattern is presumed wasteful and skipped.

    Decay: every DECAY_INTERVAL conflicts, all counters are halved
    via nibble-parallel right-shift.  This prevents stale negative
    knowledge from permanently suppressing patterns that become
    useful later in the search.

Author:

    Z3 contributors

--*/
#pragma once

#include <cstring>
#include <cstdint>

namespace smt {

    struct binding_failure_filter {
        // 16K slots x 4 bits = 8KB storage.
        // Packed as uint64_t words: 16 nibbles per word.
        static constexpr unsigned NUM_SLOTS      = 16384;
        static constexpr unsigned NUM_WORDS      = NUM_SLOTS / 16;  // 1024 words
        static constexpr unsigned SUPPRESS_THRESH = 8;  // min counter to suppress
        static constexpr unsigned DECAY_INTERVAL  = 10000;  // conflicts between decays

        // k=3 multiplicative hash constants (golden ratio derivatives).
        static constexpr uint64_t K1 = 0x9E3779B97F4A7C15ULL;
        static constexpr uint64_t K2 = 0x517CC1B727220A95ULL;
        static constexpr uint64_t K3 = 0x6C62272E07BB0142ULL;

        uint64_t m_data[NUM_WORDS];
        unsigned m_conflict_count;

        void reset() {
            memset(m_data, 0, sizeof(m_data));
            m_conflict_count = 0;
        }

        // Map a hash to 3 slot indices (0..NUM_SLOTS-1).
        void slot_indices(uint64_t h, unsigned & s1, unsigned & s2, unsigned & s3) const {
            s1 = static_cast<unsigned>((h * K1) >> 50) & (NUM_SLOTS - 1);
            s2 = static_cast<unsigned>((h * K2) >> 50) & (NUM_SLOTS - 1);
            s3 = static_cast<unsigned>((h * K3) >> 50) & (NUM_SLOTS - 1);
        }

        // Read the 4-bit counter at slot s.
        unsigned get_nibble(unsigned s) const {
            unsigned word = s >> 4;        // s / 16
            unsigned nib  = s & 15;        // s % 16
            return (m_data[word] >> (nib * 4)) & 0xFULL;
        }

        // Set the 4-bit counter at slot s to val (0..15).
        void set_nibble(unsigned s, unsigned val) {
            unsigned word = s >> 4;
            unsigned nib  = s & 15;
            unsigned shift = nib * 4;
            m_data[word] = (m_data[word] & ~(0xFULL << shift))
                         | (static_cast<uint64_t>(val & 0xF) << shift);
        }

        // Increment 3 counters (saturate at 15).
        void record_failure(uint64_t h) {
            unsigned s1, s2, s3;
            slot_indices(h, s1, s2, s3);
            unsigned v1 = get_nibble(s1); if (v1 < 15) set_nibble(s1, v1 + 1);
            unsigned v2 = get_nibble(s2); if (v2 < 15) set_nibble(s2, v2 + 1);
            unsigned v3 = get_nibble(s3); if (v3 < 15) set_nibble(s3, v3 + 1);
        }

        // Decrement 3 counters (floor at 0).
        void record_success(uint64_t h) {
            unsigned s1, s2, s3;
            slot_indices(h, s1, s2, s3);
            unsigned v1 = get_nibble(s1); if (v1 > 0) set_nibble(s1, v1 - 1);
            unsigned v2 = get_nibble(s2); if (v2 > 0) set_nibble(s2, v2 - 1);
            unsigned v3 = get_nibble(s3); if (v3 > 0) set_nibble(s3, v3 - 1);
        }

        // True when all 3 counters >= SUPPRESS_THRESH.
        bool should_suppress(uint64_t h) const {
            unsigned s1, s2, s3;
            slot_indices(h, s1, s2, s3);
            return get_nibble(s1) >= SUPPRESS_THRESH
                && get_nibble(s2) >= SUPPRESS_THRESH
                && get_nibble(s3) >= SUPPRESS_THRESH;
        }

        // Halve all counters via nibble-parallel right-shift.
        // For each uint64_t word: shift right by 1, then mask off
        // the bit that leaked from the neighboring nibble.
        void decay() {
            constexpr uint64_t MASK = 0x7777777777777777ULL;
            for (unsigned i = 0; i < NUM_WORDS; ++i) {
                m_data[i] = (m_data[i] >> 1) & MASK;
            }
        }

        // Call from resolve_conflict; triggers decay every DECAY_INTERVAL conflicts.
        void on_conflict() {
            if (++m_conflict_count >= DECAY_INTERVAL) {
                decay();
                m_conflict_count = 0;
            }
        }
    };

}
