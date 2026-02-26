/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    region.h

Abstract:

    Region/Arena memory manager

Author:

    Leonardo de Moura (leonardo) 2006-09-13.

Revision History:

--*/
#pragma once
#include<cstdlib>
#include<cstdint>
#include<ostream>

#ifdef Z3DEBUG

#include "util/vector.h"

class region {
    ptr_vector<char> m_chunks;
    unsigned_vector  m_scopes;
public:
    ~region() {
        reset();
    }


    void * allocate(size_t size);

    void reset();

    void push_scope() {
        m_scopes.push_back(m_chunks.size());
    }

    void pop_scope();
    
    void pop_scope(unsigned num_scopes) {
        for (unsigned i = 0; i < num_scopes; ++i) {
            pop_scope();
        }
    }

    void display_mem_stats(std::ostream & out) const;
};

#else

/**
\brief Implement explicit region memory manager.
*/
class region {
    struct mark {
        char * m_curr_page;
        char * m_curr_ptr;
        mark * m_prev_mark;
        mark(char * page, char * ptr, mark * m):m_curr_page(page), m_curr_ptr(ptr), m_prev_mark(m) {}
    };
    char *   m_curr_page;
    char *   m_curr_ptr;     //!< Next free space in the current page.
    char *   m_curr_end_ptr; //!< Point to the end of the current page.
    char *   m_free_pages;
    mark *   m_mark;
    void allocate_page();
    void recycle_curr_page();
    __attribute__((noinline)) void * allocate_slow(size_t size);
public:
    region();
    ~region();
    void * allocate(size_t size) {
        // Inline fast path: bump pointer within current page
        // Alignment: round up to next pointer-aligned boundary
        char * new_curr_ptr = m_curr_ptr + size;
        if (__builtin_expect(new_curr_ptr <= m_curr_end_ptr, 1)) {
            char * result = m_curr_ptr;
            m_curr_ptr = reinterpret_cast<char*>(
                (reinterpret_cast<uintptr_t>(new_curr_ptr) + (sizeof(void*) - 1)) & ~(sizeof(void*) - 1));
            return result;
        }
        return allocate_slow(size);
    }
    void reset();
    void push_scope();
    void pop_scope();
    void pop_scope(unsigned num_scopes) {
        for (unsigned i = 0; i < num_scopes; ++i) {
            pop_scope();
        }
    }
    void display_mem_stats(std::ostream & out) const;
};

static_assert(sizeof(region) <= 64,
              "region allocator exceeds 1 cache line — check field layout");

#endif

inline void * operator new(size_t s, region & r) { return r.allocate(s); }

inline void * operator new[](size_t s, region & r) { return r.allocate(s); }

inline void operator delete(void *, region & ) { /* do nothing */ }

inline void operator delete[](void *, region & ) { /* do nothing */ }


