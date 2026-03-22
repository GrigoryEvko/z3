/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    adaptive_log.h

Abstract:

    Zero-cost structured JSONL logger for the adaptive QI engine.
    When the log file is null, every method compiles to a branch-on-null
    that the CPU perfectly predicts. When active, writes one JSON object
    per line to the file for offline analysis.

    Usage:
        ALOG(m_adaptive_log, "QI_INSERT")
            .u("c", conflicts).s("q", name).d("cost", 8.3);
        // writes: {"t":"QI_INSERT","c":12,"q":"loc_includes","cost":8.3000}\n

    Analysis:
        python3 tools/z3_adaptive_summary.py trace.jsonl
        jq 'select(.t=="CONFLICT")' trace.jsonl

Author:

    Z3 contributors

--*/
#pragma once
#include <cstdio>
#include <cstdarg>

namespace smt {

class adaptive_log_event {
    FILE* m_f;
public:
    explicit adaptive_log_event(FILE* f, const char* type) : m_f(f) {
        if (!f) return;
        fprintf(f, "{\"t\":\"%s\"", type);
    }

    ~adaptive_log_event() {
        if (m_f) fprintf(m_f, "}\n");
    }

    adaptive_log_event(adaptive_log_event const&) = delete;
    adaptive_log_event& operator=(adaptive_log_event const&) = delete;

    adaptive_log_event& i(const char* k, int v) {
        if (m_f) fprintf(m_f, ",\"%s\":%d", k, v);
        return *this;
    }
    adaptive_log_event& u(const char* k, unsigned v) {
        if (m_f) fprintf(m_f, ",\"%s\":%u", k, v);
        return *this;
    }
    adaptive_log_event& u64(const char* k, uint64_t v) {
        if (m_f) fprintf(m_f, ",\"%s\":%lu", k, v);
        return *this;
    }
    adaptive_log_event& d(const char* k, double v) {
        if (m_f) fprintf(m_f, ",\"%s\":%.4f", k, v);
        return *this;
    }
    adaptive_log_event& s(const char* k, const char* v) {
        if (m_f) fprintf(m_f, ",\"%s\":\"%s\"", k, v);
        return *this;
    }
    adaptive_log_event& b(const char* k, bool v) {
        if (m_f) fprintf(m_f, ",\"%s\":%s", k, v ? "true" : "false");
        return *this;
    }
    adaptive_log_event& hex(const char* k, unsigned v) {
        if (m_f) fprintf(m_f, ",\"%s\":\"%08x\"", k, v);
        return *this;
    }

    // Raw JSON fragment (caller responsible for correctness)
    adaptive_log_event& raw(const char* k, const char* json) {
        if (m_f) fprintf(m_f, ",\"%s\":%s", k, json);
        return *this;
    }
};

#define ALOG(file, type) ::smt::adaptive_log_event((file), (type))

} // namespace smt
