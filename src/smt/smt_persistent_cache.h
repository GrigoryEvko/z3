/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    smt_persistent_cache.h

Abstract:

    Binary file format for persisting proof strategy cache across sessions.
    Stores top-K quantifier strategies and failure records keyed by
    assertion hash, enabling cross-session warm-start of QI heuristics.

    File layout:
      [file_header]
      [strategy_header + entry_record[] + seq_entry_record[]] * num_strategies
      [failure_record] * num_failures

Author:

    Z3 contributors

--*/
#pragma once

#include <cstdint>
#include <cstring>
#include <string>
#include <unordered_map>
#include "smt/smt_context.h"

namespace smt {

    // Magic bytes: "Z3LC" (Z3 Learning Cache)
    static constexpr uint32_t PERSISTENT_CACHE_MAGIC   = 0x5A334C43;
    static constexpr uint32_t PERSISTENT_CACHE_VERSION = 1;

    // On-disk caps
    static constexpr unsigned MAX_DISK_STRATEGIES = 256;
    static constexpr unsigned MAX_DISK_FAILURES   = 128;

    /**
     * File header: 32 bytes, fixed at file offset 0.
     */
    struct file_header {
        uint32_t magic;           // 0x5A334C43
        uint32_t version;         // 1
        uint32_t flags;           // reserved
        uint32_t num_strategies;  // number of strategy blocks following
        uint32_t num_failures;    // number of failure records at end
        uint32_t generation;      // monotonic generation counter
        uint32_t reserved;        // padding
        uint32_t checksum;        // XOR of all preceding 7 uint32_t fields
    };
    static_assert(sizeof(file_header) == 32, "file_header must be 32 bytes");

    /**
     * Strategy header: 44 bytes, precedes its entry_record[] and seq_entry_record[].
     */
    struct strategy_header {
        uint64_t assertion_hash;          // key into proof_cache
        double   effective_qi_threshold;  // cached solver config
        uint32_t effective_relevancy;
        uint32_t effective_ematching;     // bool stored as uint32
        uint32_t effective_mbqi;          // bool stored as uint32
        uint32_t num_entries;             // count of entry_record following
        uint32_t num_seq_entries;         // count of seq_entry_record following
        uint32_t conflicts_to_solve;
    };
    static_assert(sizeof(strategy_header) == 40, "strategy_header must be 40 bytes");

    /**
     * Single quantifier reward entry: 16 bytes.
     */
    struct entry_record {
        uint64_t signature;  // quantifier_signature hash
        double   reward;     // reward EMA
    };
    static_assert(sizeof(entry_record) == 16, "entry_record must be 16 bytes");

    /**
     * Single proof-sequence entry: 16 bytes.
     */
    struct seq_entry_record {
        uint64_t quantifier_sig;
        uint32_t position;
        uint32_t _pad;
    };
    static_assert(sizeof(seq_entry_record) == 16, "seq_entry_record must be 16 bytes");

    /**
     * Failure record: 16 bytes.
     */
    struct failure_record {
        uint64_t assertion_hash;
        uint32_t fail_count;
        uint32_t _pad;
    };
    static_assert(sizeof(failure_record) == 16, "failure_record must be 16 bytes");

    /**
     * Static load/save interface for persistent cache.
     * All I/O errors are silently ignored (best-effort persistence).
     */
    class persistent_cache {
    public:
        /**
         * Load strategies and failures from a binary cache file.
         * Merges into the provided maps: for strategies, the entry with
         * highest confidence wins on key collision.
         */
        static void load(
            std::string const & path,
            std::unordered_map<uint64_t, proof_strategy> & strategies,
            std::unordered_map<uint64_t, unsigned> & failures);

        /**
         * Save strategies and failures to a binary cache file.
         * Writes to path + ".tmp", then atomically renames.
         * Caps at MAX_DISK_STRATEGIES / MAX_DISK_FAILURES.
         */
        static void save(
            std::string const & path,
            std::unordered_map<uint64_t, proof_strategy> const & strategies,
            std::unordered_map<uint64_t, unsigned> const & failures,
            uint32_t generation);
    };

}
