/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    sat_arena.h

Abstract:

    Contiguous arena allocator for SAT clauses, inspired by CaDiCaL's arena.

    Provides a moving garbage collector with two semi-spaces (from/to).
    During GC, surviving clauses are copied into 'to' space in an order
    that places clauses watched by the same literal contiguously.
    After GC, 'from' is freed and 'to' becomes the new 'from'.

    This dramatically improves cache locality during propagation since
    clauses accessed together (sharing a watched literal) are physically
    adjacent in memory.

Author:

    SAT solver optimization, 2025.

Revision History:

--*/
#pragma once

#include <cstring>
#include <cstdlib>
#include "util/debug.h"

namespace sat {

    class arena {
        struct space {
            char* start;
            char* top;
            char* end;

            space() : start(nullptr), top(nullptr), end(nullptr) {}

            size_t used() const { return static_cast<size_t>(top - start); }
            size_t capacity() const { return static_cast<size_t>(end - start); }
        };

        space m_from;
        space m_to;

        static size_t align_up(size_t n, size_t alignment) {
            return (n + alignment - 1) & ~(alignment - 1);
        }

    public:
        arena() {}

        ~arena() {
            if (m_from.start) free(m_from.start);
            if (m_to.start) free(m_to.start);
        }

        // No copy/move.
        arena(arena const&) = delete;
        arena& operator=(arena const&) = delete;

        // Returns true if pointer p belongs to this arena (either space).
        bool contains(void const* p) const {
            char const* c = static_cast<char const*>(p);
            return (m_from.start && m_from.start <= c && c < m_from.top) ||
                   (m_to.start && m_to.start <= c && c < m_to.top);
        }

        // Returns true if the arena has any allocated space.
        bool active() const { return m_from.start != nullptr; }

        // Total bytes currently used in the 'from' space.
        size_t used() const { return m_from.used(); }

        // Prepare 'to' space to hold the given number of bytes.
        // Precondition: 'to' space must be empty.
        // Extra padding is added for alignment.
        void prepare(size_t bytes) {
            SASSERT(m_to.start == nullptr);
            // Add generous alignment padding (8 bytes per clause worst case).
            size_t alloc_bytes = bytes + bytes / 4 + 4096;
            m_to.start = static_cast<char*>(malloc(alloc_bytes));
            if (!m_to.start) throw default_exception("arena: out of memory");
            m_to.top = m_to.start;
            m_to.end = m_to.start + alloc_bytes;
        }

        // Copy 'bytes' bytes from source into 'to' space with pointer alignment.
        // Returns pointer to the new location in 'to' space.
        char* copy(char const* src, size_t bytes) {
            SASSERT(m_to.start != nullptr);
            // Align to pointer size for proper clause access.
            size_t offset = align_up(static_cast<size_t>(m_to.top - m_to.start), alignof(void*));
            char* dst = m_to.start + offset;
            m_to.top = dst + bytes;
            SASSERT(m_to.top <= m_to.end);
            memcpy(dst, src, bytes);
            return dst;
        }

        // Free 'from' space, then swap: 'to' becomes the new 'from'.
        void swap() {
            if (m_from.start)
                free(m_from.start);
            m_from = m_to;
            m_to.start = m_to.top = m_to.end = nullptr;
        }

        // Release all memory.
        void finalize() {
            if (m_from.start) { free(m_from.start); m_from.start = m_from.top = m_from.end = nullptr; }
            if (m_to.start) { free(m_to.start); m_to.start = m_to.top = m_to.end = nullptr; }
        }
    };

}
