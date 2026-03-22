/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    smt_persistent_cache.cpp

Abstract:

    Binary serialization for cross-session proof strategy cache.
    See smt_persistent_cache.h for file format documentation.

    Design constraints:
      - All I/O errors silently ignored (best-effort persistence).
      - Atomic write via .tmp + rename to prevent corruption.
      - On-disk caps: 256 strategies, 128 failures.
      - Merge policy on load: highest confidence wins.

Author:

    Z3 contributors

--*/
#include "smt/smt_persistent_cache.h"
#include <cstdio>
#include <algorithm>
#include <vector>

namespace smt {

    // Compute XOR checksum over the first 7 uint32_t fields of file_header.
    static uint32_t compute_checksum(file_header const & h) {
        uint32_t const * words = reinterpret_cast<uint32_t const *>(&h);
        uint32_t cs = 0;
        for (unsigned i = 0; i < 7; ++i)
            cs ^= words[i];
        return cs;
    }

    void persistent_cache::load(
        std::string const & path,
        std::unordered_map<uint64_t, proof_strategy> & strategies,
        std::unordered_map<uint64_t, unsigned> & failures)
    {
        FILE * f = fopen(path.c_str(), "rb");
        if (!f) return;

        file_header hdr;
        if (fread(&hdr, sizeof(hdr), 1, f) != 1)               { fclose(f); return; }
        if (hdr.magic != PERSISTENT_CACHE_MAGIC)                { fclose(f); return; }
        if (hdr.version != PERSISTENT_CACHE_VERSION)            { fclose(f); return; }
        if (hdr.checksum != compute_checksum(hdr))              { fclose(f); return; }
        if (hdr.num_strategies > MAX_DISK_STRATEGIES)           { fclose(f); return; }
        if (hdr.num_failures > MAX_DISK_FAILURES)               { fclose(f); return; }

        // Read strategies
        for (uint32_t i = 0; i < hdr.num_strategies; ++i) {
            strategy_header sh;
            if (fread(&sh, sizeof(sh), 1, f) != 1)             { fclose(f); return; }
            if (sh.num_entries > proof_strategy::TOP_K)         { fclose(f); return; }
            if (sh.num_seq_entries > proof_strategy::MAX_PROOF_SEQ) { fclose(f); return; }

            proof_strategy ps;
            ps.m_effective_qi_threshold = sh.effective_qi_threshold;
            ps.m_effective_relevancy    = sh.effective_relevancy;
            ps.m_effective_ematching    = (sh.effective_ematching != 0);
            ps.m_effective_mbqi         = (sh.effective_mbqi != 0);
            ps.m_conflicts_to_solve     = sh.conflicts_to_solve;
            ps.m_confidence             = 0.8; // loaded strategies start at moderate confidence

            // Read entry records
            for (uint32_t j = 0; j < sh.num_entries; ++j) {
                entry_record er;
                if (fread(&er, sizeof(er), 1, f) != 1)         { fclose(f); return; }
                proof_strategy::entry e;
                e.m_signature = er.signature;
                e.m_reward    = er.reward;
                ps.m_entries.push_back(e);
            }

            // Read proof sequence records
            for (uint32_t j = 0; j < sh.num_seq_entries; ++j) {
                seq_entry_record ser;
                if (fread(&ser, sizeof(ser), 1, f) != 1)       { fclose(f); return; }
                proof_strategy::seq_entry se;
                se.m_quantifier_sig = ser.quantifier_sig;
                se.m_position       = ser.position;
                ps.m_proof_sequence.push_back(se);
            }

            // Merge: highest confidence wins on collision
            auto it = strategies.find(sh.assertion_hash);
            if (it == strategies.end() || ps.m_confidence > it->second.m_confidence)
                strategies[sh.assertion_hash] = std::move(ps);
        }

        // Read failure records
        for (uint32_t i = 0; i < hdr.num_failures; ++i) {
            failure_record fr;
            if (fread(&fr, sizeof(fr), 1, f) != 1)             { fclose(f); return; }
            auto it = failures.find(fr.assertion_hash);
            if (it == failures.end() || fr.fail_count > it->second)
                failures[fr.assertion_hash] = fr.fail_count;
        }

        fclose(f);
    }

    void persistent_cache::save(
        std::string const & path,
        std::unordered_map<uint64_t, proof_strategy> const & strategies,
        std::unordered_map<uint64_t, unsigned> const & failures,
        uint32_t generation)
    {
        std::string tmp_path = path + ".tmp";
        FILE * f = fopen(tmp_path.c_str(), "wb");
        if (!f) return;

        // Collect strategies sorted by confidence (descending), capped
        struct ranked {
            uint64_t hash;
            proof_strategy const * ps;
            double confidence;
        };
        std::vector<ranked> ranked_strats;
        ranked_strats.reserve(strategies.size());
        for (auto const & kv : strategies)
            ranked_strats.push_back({kv.first, &kv.second, kv.second.m_confidence});
        std::sort(ranked_strats.begin(), ranked_strats.end(),
                  [](ranked const & a, ranked const & b) { return a.confidence > b.confidence; });
        if (ranked_strats.size() > MAX_DISK_STRATEGIES)
            ranked_strats.resize(MAX_DISK_STRATEGIES);

        // Collect failures, capped
        std::vector<std::pair<uint64_t, unsigned>> fail_vec(failures.begin(), failures.end());
        if (fail_vec.size() > MAX_DISK_FAILURES)
            fail_vec.resize(MAX_DISK_FAILURES);

        // Build and write header
        file_header hdr;
        memset(&hdr, 0, sizeof(hdr));
        hdr.magic          = PERSISTENT_CACHE_MAGIC;
        hdr.version        = PERSISTENT_CACHE_VERSION;
        hdr.flags          = 0;
        hdr.num_strategies = static_cast<uint32_t>(ranked_strats.size());
        hdr.num_failures   = static_cast<uint32_t>(fail_vec.size());
        hdr.generation     = generation;
        hdr.reserved       = 0;
        hdr.checksum       = compute_checksum(hdr);

        if (fwrite(&hdr, sizeof(hdr), 1, f) != 1) { fclose(f); return; }

        // Write each strategy block
        for (auto const & rs : ranked_strats) {
            proof_strategy const & ps = *rs.ps;

            strategy_header sh;
            memset(&sh, 0, sizeof(sh));
            sh.assertion_hash         = rs.hash;
            sh.effective_qi_threshold = ps.m_effective_qi_threshold;
            sh.effective_relevancy    = ps.m_effective_relevancy;
            sh.effective_ematching    = ps.m_effective_ematching ? 1u : 0u;
            sh.effective_mbqi         = ps.m_effective_mbqi ? 1u : 0u;
            sh.num_entries            = static_cast<uint32_t>(ps.m_entries.size());
            sh.num_seq_entries        = static_cast<uint32_t>(ps.m_proof_sequence.size());
            sh.conflicts_to_solve     = ps.m_conflicts_to_solve;

            if (fwrite(&sh, sizeof(sh), 1, f) != 1) { fclose(f); return; }

            for (auto const & e : ps.m_entries) {
                entry_record er;
                er.signature = e.m_signature;
                er.reward    = e.m_reward;
                if (fwrite(&er, sizeof(er), 1, f) != 1) { fclose(f); return; }
            }

            for (auto const & se : ps.m_proof_sequence) {
                seq_entry_record ser;
                ser.quantifier_sig = se.m_quantifier_sig;
                ser.position       = se.m_position;
                ser._pad           = 0;
                if (fwrite(&ser, sizeof(ser), 1, f) != 1) { fclose(f); return; }
            }
        }

        // Write failure records
        for (auto const & kv : fail_vec) {
            failure_record fr;
            fr.assertion_hash = kv.first;
            fr.fail_count     = kv.second;
            fr._pad           = 0;
            if (fwrite(&fr, sizeof(fr), 1, f) != 1) { fclose(f); return; }
        }

        fclose(f);

        // Atomic rename
        rename(tmp_path.c_str(), path.c_str());
    }

}
