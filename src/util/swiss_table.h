/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    swiss_table.h

Abstract:

    SIMD-accelerated Swiss table (flat hash set with metadata probing).
    Drop-in replacement for chashtable with significantly better probe
    performance: one SIMD instruction checks 16/32/64 slots simultaneously
    vs. chashtable's sequential pointer-chain walk.

    Design adapted from Google's SwissTable / Abseil flat_hash_set.
    SIMD group operations ported from crucible's SwissTable.h.

    Five SIMD paths selected at compile time:
      AVX-512BW:  64 bytes/group  — _mm512_cmpeq_epi8_mask → __mmask64
      AVX2:       32 bytes/group  — _mm256_cmpeq_epi8      → movemask
      SSE2:       16 bytes/group  — _mm_cmpeq_epi8         → movemask
      NEON:       16 bytes/group  — vceqq_s8 + vpaddl      → bitmask
      Portable:   16 bytes/group  — SWAR (SIMD Within A Register)

    Control byte encoding:
      0x80 (kEmpty)    — slot unoccupied
      0xFE (kDeleted)  — tombstone (slot erased, skip during probe)
      0x00..0x7F       — H2 tag (top 7 bits of hash), slot occupied

    H2 tags are always non-negative as int8_t; kEmpty/kDeleted are negative.
    match_empty_or_deleted() exploits the sign bit directly via movemask,
    avoiding cmpeq+set1. match_empty() must use cmpeq since kDeleted also
    has bit 7 set.

    Group-aligned probing (ported from crucible's ExprPool):
      base = (hash * kGroupWidth) & slot_mask
    This ensures every SIMD load starts at a group boundary, so reads
    never exceed the allocated ctrl array. No sentinel bytes needed.

--*/
#pragma once

#include "util/memory_manager.h"
#include "util/debug.h"
#include "util/hash.h"
#include <cstring>
#include <cstdint>
#include <utility>
#include <type_traits>

// ISA detection: check widest first (AVX-512 ⊃ AVX2 ⊃ SSE2).
#if defined(__AVX512BW__)
#include <immintrin.h>
#elif defined(__AVX2__)
#include <immintrin.h>
#elif defined(__SSE2__)
#include <emmintrin.h>
#elif defined(__aarch64__)
#include <arm_neon.h>
#endif

// ─── SIMD group operations ──────────────────────────────────────────
namespace swiss_detail {

static constexpr int8_t kEmpty   = static_cast<int8_t>(0x80);
static constexpr int8_t kDeleted = static_cast<int8_t>(0xFE);

#if defined(__AVX512BW__)
static constexpr size_t kGroupWidth = 64;
#elif defined(__AVX2__)
static constexpr size_t kGroupWidth = 32;
#else
static constexpr size_t kGroupWidth = 16;
#endif

// H2 tag: top 7 bits of 32-bit hash → [0, 127].
// Always non-negative as int8_t (bit 7 cleared).
// Independent from H1 (lower bits used for position) due to hash avalanche.
inline int8_t h2_tag(unsigned hash) {
    return static_cast<int8_t>((hash >> 25) & 0x7F);
}

// Bitmask of matching positions within a group.
// Each set bit corresponds to a slot offset (0..kGroupWidth-1).
// Iterate: while (m) { use m.lowest(); m.clear_lowest(); }
struct BitMask {
    uint64_t mask = 0;

    explicit operator bool() const { return mask != 0; }

    // Index of lowest set bit. Undefined if mask == 0.
    unsigned lowest() const {
#if defined(__GNUC__) || defined(__clang__)
        return static_cast<unsigned>(__builtin_ctzll(mask));
#elif defined(_MSC_VER)
        unsigned long idx;
        _BitScanForward64(&idx, static_cast<unsigned long long>(mask));
        return idx;
#else
        unsigned n = 0;
        uint64_t m = mask;
        while (!(m & 1)) { m >>= 1; ++n; }
        return n;
#endif
    }

    // Clear lowest set bit (branchless: Blsr on x86).
    void clear_lowest() { mask &= mask - 1; }
};

// SIMD group: compare kGroupWidth control bytes in parallel.
//
// load()                -- read kGroupWidth bytes from group start
// match(h2)            -- bitmask of slots matching the H2 tag
// match_empty()        -- bitmask of empty slots (cmpeq against kEmpty)
// match_empty_or_deleted() -- bitmask of non-occupied slots (sign-bit extraction)
struct CtrlGroup {

#if defined(__AVX512BW__)
    // ── AVX-512BW: 64 bytes/group ──────────────────────────────────
    __m512i ctrl;

    static CtrlGroup load(const int8_t* pos) {
        return { _mm512_loadu_si512(reinterpret_cast<const __m512i*>(pos)) };
    }

    BitMask match(int8_t h2) const {
        return { _mm512_cmpeq_epi8_mask(ctrl, _mm512_set1_epi8(h2)) };
    }

    // cmpeq against kEmpty to distinguish from kDeleted.
    BitMask match_empty() const {
        return { _mm512_cmpeq_epi8_mask(ctrl, _mm512_set1_epi8(kEmpty)) };
    }

    // kEmpty (0x80) and kDeleted (0xFE) both have bit 7 set.
    // _mm512_movepi8_mask extracts bit 7 of each byte directly.
    BitMask match_empty_or_deleted() const {
        return { _mm512_movepi8_mask(ctrl) };
    }

#elif defined(__AVX2__)
    // ── AVX2: 32 bytes/group ───────────────────────────────────────
    __m256i ctrl;

    static CtrlGroup load(const int8_t* pos) {
        return { _mm256_loadu_si256(reinterpret_cast<const __m256i*>(pos)) };
    }

    BitMask match(int8_t h2) const {
        auto cmp = _mm256_cmpeq_epi8(ctrl, _mm256_set1_epi8(h2));
        // Double-cast prevents sign-extension of negative int
        return { static_cast<uint64_t>(
            static_cast<uint32_t>(_mm256_movemask_epi8(cmp))) };
    }

    BitMask match_empty() const {
        auto cmp = _mm256_cmpeq_epi8(ctrl, _mm256_set1_epi8(kEmpty));
        return { static_cast<uint64_t>(
            static_cast<uint32_t>(_mm256_movemask_epi8(cmp))) };
    }

    // Both kEmpty (0x80) and kDeleted (0xFE) have bit 7 set.
    // movemask extracts bit 7 of each byte directly.
    BitMask match_empty_or_deleted() const {
        return { static_cast<uint64_t>(
            static_cast<uint32_t>(_mm256_movemask_epi8(ctrl))) };
    }

#elif defined(__SSE2__)
    // ── SSE2: 16 bytes/group ───────────────────────────────────────
    __m128i ctrl;

    static CtrlGroup load(const int8_t* pos) {
        return { _mm_loadu_si128(reinterpret_cast<const __m128i*>(pos)) };
    }

    BitMask match(int8_t h2) const {
        auto cmp = _mm_cmpeq_epi8(ctrl, _mm_set1_epi8(h2));
        return { static_cast<uint64_t>(
            static_cast<uint16_t>(_mm_movemask_epi8(cmp))) };
    }

    BitMask match_empty() const {
        auto cmp = _mm_cmpeq_epi8(ctrl, _mm_set1_epi8(kEmpty));
        return { static_cast<uint64_t>(
            static_cast<uint16_t>(_mm_movemask_epi8(cmp))) };
    }

    BitMask match_empty_or_deleted() const {
        return { static_cast<uint64_t>(
            static_cast<uint16_t>(_mm_movemask_epi8(ctrl))) };
    }

#elif defined(__aarch64__)
    // ── NEON: 16 bytes/group ───────────────────────────────────────
    int8x16_t ctrl;

    static CtrlGroup load(const int8_t* pos) {
        return { vld1q_s8(pos) };
    }

    BitMask match(int8_t h2) const {
        uint8x16_t cmp = vceqq_s8(ctrl, vdupq_n_s8(h2));
        return { neon_movemask(cmp) };
    }

    BitMask match_empty() const {
        uint8x16_t cmp = vceqq_s8(ctrl, vdupq_n_s8(kEmpty));
        return { neon_movemask(cmp) };
    }

    // vcltzq_s8 tests sign bit directly — 1 for kEmpty and kDeleted, 0 for H2 tags.
    BitMask match_empty_or_deleted() const {
        uint8x16_t neg = vreinterpretq_u8_s8(vcltzq_s8(ctrl));
        return { neon_movemask(neg) };
    }

    // Synthesize movemask on NEON via vpaddl reduction chain.
    // Takes a byte comparison result (0xFF or 0x00 per lane) and produces
    // a 16-bit bitmask with one bit per byte.
    static uint64_t neon_movemask(uint8x16_t cmp) {
        static constexpr uint8_t kBits[16] = {
            0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80,
            0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80 };
        uint8x16_t bits = vld1q_u8(kBits);
        uint8x16_t masked = vandq_u8(cmp, bits);
        // Pairwise widening add: 16xu8 → 8xu16 → 4xu32 → 2xu64
        uint64x2_t sum = vpaddlq_u32(vpaddlq_u16(vpaddlq_u8(masked)));
        // Lane 0 = bits 0-7 (bytes 0-7), lane 1 = bits 8-15 (bytes 8-15)
        return vgetq_lane_u64(sum, 0) | (vgetq_lane_u64(sum, 1) << 8);
    }

#else
    // ── Portable fallback: SWAR (SIMD Within A Register) ───────────
    //
    // Instead of 16 individual byte comparisons (branches), we load
    // 8 bytes at a time into a uint64_t and use the "has zero byte" trick
    // to detect matches in parallel. Two 8-byte chunks cover 16 bytes.
    //
    // The "has zero byte" trick (from Hacker's Delight):
    //   Given v = data ^ broadcast(target), bytes that matched are now 0.
    //   ((v - 0x0101...) & ~v & 0x8080...) has bit 7 set in each zero byte.
    //   Extract those bits via multiply-shift to form a bitmask.
    int8_t bytes[16] = {};

    static CtrlGroup load(const int8_t* pos) {
        CtrlGroup g;
        std::memcpy(g.bytes, pos, 16);
        return g;
    }

    BitMask match(int8_t h2) const {
        return { swar_match(h2) };
    }

    BitMask match_empty() const {
        // kEmpty = 0x80. Use SWAR match for exact byte comparison.
        return { swar_match(kEmpty) };
    }

    // kEmpty (0x80) and kDeleted (0xFE) both have bit 7 set.
    // H2 tags (0x00..0x7F) have bit 7 clear.
    // Extract bit 7 from each byte via SWAR.
    BitMask match_empty_or_deleted() const {
        uint64_t lo = 0, hi = 0;
        std::memcpy(&lo, bytes, 8);
        std::memcpy(&hi, bytes + 8, 8);
        uint64_t mask = extract_highbits(lo) | (extract_highbits(hi) << 8);
        return { mask };
    }

private:
    // Extract bit 7 from each of 8 bytes packed in a uint64_t.
    // Returns bits 0..7, one per byte, indicating which bytes have bit 7 set.
    // Uses the multiply-shift trick: carefully chosen constant gathers
    // bits 7,15,23,31,39,47,55,63 into the top byte.
    static uint64_t extract_highbits(uint64_t v) {
        constexpr uint64_t hi_mask = 0x8080808080808080ULL;
        uint64_t bits = v & hi_mask;
        bits *= 0x0002040810204080ULL;
        return bits >> 56;
    }

    // SWAR match: find all bytes in the 16-byte group that equal h2.
    // Uses the zero-byte detection trick from Hacker's Delight.
    uint64_t swar_match(int8_t h2) const {
        uint64_t lo = 0, hi = 0;
        std::memcpy(&lo, bytes, 8);
        std::memcpy(&hi, bytes + 8, 8);

        // Broadcast h2 to all 8 bytes
        uint64_t needle =
            static_cast<uint64_t>(static_cast<uint8_t>(h2)) * 0x0101010101010101ULL;

        // XOR: matching bytes become 0x00
        uint64_t xor_lo = lo ^ needle;
        uint64_t xor_hi = hi ^ needle;

        // "Has zero byte" detection:
        //   For each byte b in v: b==0 iff ((b - 0x01) & ~b & 0x80) != 0
        constexpr uint64_t lo_magic = 0x0101010101010101ULL;
        constexpr uint64_t hi_magic = 0x8080808080808080ULL;

        uint64_t zero_lo = (xor_lo - lo_magic) & ~xor_lo & hi_magic;
        uint64_t zero_hi = (xor_hi - lo_magic) & ~xor_hi & hi_magic;

        // Extract bit 7 from each zero-detected byte into bitmask positions
        return extract_highbits(zero_lo) | (extract_highbits(zero_hi) << 8);
    }
#endif
};

} // namespace swiss_detail

// ─── Swiss table ────────────────────────────────────────────────────
//
// Drop-in replacement for chashtable<T, HashProc, EqProc>.
// Stores T values in a flat array with a separate 1-byte control
// array for SIMD metadata probing.
//
// Group-aligned probing (crucible pattern):
//   base = (hash * kGroupWidth) & slot_mask
// Every SIMD load lands on a group boundary → always within bounds,
// no sentinel bytes or cloned tail needed.
//
// Single-pass find+insert: during the existence check, the first
// free slot (empty or deleted) is tracked. If the element is absent,
// we insert at the tracked position — no second probe pass needed.
//
// Differences from crucible's ExprPool (insert-only):
//   - Supports erase() via tombstone (kDeleted = 0xFE)
//   - match_empty() must use cmpeq (kDeleted also has bit 7 set)
//   - Rehash triggered by occupied + tombstones > 7/8 capacity
//
template<typename T, typename HashProc, typename EqProc>
class swiss_table : private HashProc, private EqProc {
    static_assert(std::is_trivially_copyable<T>::value,
                  "swiss_table requires trivially copyable element type");
    static_assert(std::is_trivially_destructible<T>::value,
                  "swiss_table requires trivially destructible element type");

    static constexpr size_t G = swiss_detail::kGroupWidth;

public:
    static constexpr unsigned default_init_slots  = static_cast<unsigned>(G);
    static constexpr unsigned default_init_cellar = 2; // ignored, for chashtable compat

    swiss_table(HashProc const& h = HashProc(),
                EqProc const& e = EqProc(),
                unsigned init_slots  = default_init_slots,
                unsigned             = default_init_cellar /* ignored */)
        : HashProc(h), EqProc(e),
          m_init_capacity(round_up(init_slots < G ? G : init_slots)) {
        alloc_tables(m_init_capacity);
    }

    ~swiss_table() {
        free_tables();
    }

    swiss_table(swiss_table const&) = delete;
    swiss_table& operator=(swiss_table const&) = delete;

    swiss_table(swiss_table&& other) noexcept
        : HashProc(static_cast<HashProc&&>(other)),
          EqProc(static_cast<EqProc&&>(other)),
          m_ctrl(other.m_ctrl), m_slots(other.m_slots),
          m_capacity(other.m_capacity), m_size(other.m_size),
          m_tombstones(other.m_tombstones), m_init_capacity(other.m_init_capacity) {
        other.m_ctrl = nullptr;
        other.m_slots = nullptr;
        other.m_capacity = 0;
        other.m_size = 0;
        other.m_tombstones = 0;
    }

    // ── Core operations ──

    // Insert or overwrite.
    void insert(T const& d) {
        if (needs_rehash()) [[unlikely]] rehash_grow();
        unsigned h = get_hash(d);
        int8_t tag = swiss_detail::h2_tag(h);
        size_t mask = m_capacity - 1;
        size_t base = (static_cast<size_t>(h) * G) & mask;
        size_t probe = 0;
        size_t insert_at = SIZE_MAX;

        while (true) {
            auto group = swiss_detail::CtrlGroup::load(&m_ctrl[base]);

            auto matches = group.match(tag);
            while (matches) {
                size_t idx = base + matches.lowest();
                if (equals(m_slots[idx], d)) {
                    m_slots[idx] = d; // overwrite
                    return;
                }
                matches.clear_lowest();
            }

            // Track first free slot for insertion
            if (insert_at == SIZE_MAX) {
                auto free_slots = group.match_empty_or_deleted();
                if (free_slots)
                    insert_at = base + free_slots.lowest();
            }

            if (group.match_empty()) [[likely]]
                break; // not in table
            ++probe;
            base = (base + probe * G) & mask;
        }

        SASSERT(insert_at != SIZE_MAX);
        if (m_ctrl[insert_at] == swiss_detail::kDeleted)
            --m_tombstones;
        m_ctrl[insert_at] = tag;
        m_slots[insert_at] = d;
        ++m_size;
    }

    // Insert without checking for duplicates (caller guarantees uniqueness).
    void insert_fresh(T const& d) {
        if (needs_rehash()) [[unlikely]] rehash_grow();
        unsigned h = get_hash(d);
        int8_t tag = swiss_detail::h2_tag(h);
        size_t mask = m_capacity - 1;
        size_t base = (static_cast<size_t>(h) * G) & mask;
        size_t probe = 0;

        while (true) {
            auto group = swiss_detail::CtrlGroup::load(&m_ctrl[base]);
            auto free_slots = group.match_empty_or_deleted();
            if (free_slots) [[likely]] {
                size_t idx = base + free_slots.lowest();
                if (m_ctrl[idx] == swiss_detail::kDeleted)
                    --m_tombstones;
                m_ctrl[idx] = tag;
                m_slots[idx] = d;
                ++m_size;
                return;
            }
            ++probe;
            base = (base + probe * G) & mask;
        }
    }

    // Insert if not present. Returns reference to existing or newly inserted element.
    T& insert_if_not_there(T const& d) {
        if (needs_rehash()) [[unlikely]] rehash_grow();
        unsigned h = get_hash(d);
        int8_t tag = swiss_detail::h2_tag(h);
        size_t mask = m_capacity - 1;
        size_t base = (static_cast<size_t>(h) * G) & mask;
        size_t probe = 0;
        size_t insert_at = SIZE_MAX;

        while (true) {
            auto group = swiss_detail::CtrlGroup::load(&m_ctrl[base]);

            auto matches = group.match(tag);
            while (matches) {
                size_t idx = base + matches.lowest();
                if (equals(m_slots[idx], d))
                    return m_slots[idx];
                matches.clear_lowest();
            }

            if (insert_at == SIZE_MAX) {
                auto free_slots = group.match_empty_or_deleted();
                if (free_slots)
                    insert_at = base + free_slots.lowest();
            }

            if (group.match_empty()) [[likely]]
                break;
            ++probe;
            base = (base + probe * G) & mask;
        }

        SASSERT(insert_at != SIZE_MAX);
        if (m_ctrl[insert_at] == swiss_detail::kDeleted)
            --m_tombstones;
        m_ctrl[insert_at] = tag;
        m_slots[insert_at] = d;
        ++m_size;
        return m_slots[insert_at];
    }

    // Insert if not present. Returns true if inserted, false if already exists.
    bool insert_if_not_there2(T const& d) {
        if (needs_rehash()) [[unlikely]] rehash_grow();
        unsigned h = get_hash(d);
        int8_t tag = swiss_detail::h2_tag(h);
        size_t mask = m_capacity - 1;
        size_t base = (static_cast<size_t>(h) * G) & mask;
        size_t probe = 0;
        size_t insert_at = SIZE_MAX;

        while (true) {
            auto group = swiss_detail::CtrlGroup::load(&m_ctrl[base]);

            auto matches = group.match(tag);
            while (matches) {
                size_t idx = base + matches.lowest();
                if (equals(m_slots[idx], d))
                    return false;
                matches.clear_lowest();
            }

            if (insert_at == SIZE_MAX) {
                auto free_slots = group.match_empty_or_deleted();
                if (free_slots)
                    insert_at = base + free_slots.lowest();
            }

            if (group.match_empty()) [[likely]]
                break;
            ++probe;
            base = (base + probe * G) & mask;
        }

        SASSERT(insert_at != SIZE_MAX);
        if (m_ctrl[insert_at] == swiss_detail::kDeleted)
            --m_tombstones;
        m_ctrl[insert_at] = tag;
        m_slots[insert_at] = d;
        ++m_size;
        return true;
    }

    bool contains(T const& d) const {
        unsigned h = get_hash(d);
        int8_t tag = swiss_detail::h2_tag(h);
        size_t mask = m_capacity - 1;
        size_t base = (static_cast<size_t>(h) * G) & mask;
        size_t probe = 0;

        while (true) {
            auto group = swiss_detail::CtrlGroup::load(&m_ctrl[base]);
            auto matches = group.match(tag);
            while (matches) {
                size_t idx = base + matches.lowest();
                if (equals(m_slots[idx], d))
                    return true;
                matches.clear_lowest();
            }
            if (group.match_empty())
                return false;
            ++probe;
            base = (base + probe * G) & mask;
        }
    }

    T* find_core(T const& d) const {
        unsigned h = get_hash(d);
        int8_t tag = swiss_detail::h2_tag(h);
        size_t mask = m_capacity - 1;
        size_t base = (static_cast<size_t>(h) * G) & mask;
        size_t probe = 0;

        while (true) {
            auto group = swiss_detail::CtrlGroup::load(&m_ctrl[base]);
            auto matches = group.match(tag);
            while (matches) {
                size_t idx = base + matches.lowest();
                if (equals(m_slots[idx], d))
                    return const_cast<T*>(&m_slots[idx]);
                matches.clear_lowest();
            }
            if (group.match_empty())
                return nullptr;
            ++probe;
            base = (base + probe * G) & mask;
        }
    }

    bool find(T const& d, T& r) const {
        T* p = find_core(d);
        if (p) { r = *p; return true; }
        return false;
    }

    void erase(T const& d) {
        unsigned h = get_hash(d);
        int8_t tag = swiss_detail::h2_tag(h);
        size_t mask = m_capacity - 1;
        size_t base = (static_cast<size_t>(h) * G) & mask;
        size_t probe = 0;

        while (true) {
            auto group = swiss_detail::CtrlGroup::load(&m_ctrl[base]);
            auto matches = group.match(tag);
            while (matches) {
                size_t idx = base + matches.lowest();
                if (equals(m_slots[idx], d)) {
                    m_ctrl[idx] = swiss_detail::kDeleted;
                    --m_size;
                    ++m_tombstones;
                    return;
                }
                matches.clear_lowest();
            }
            if (group.match_empty())
                return;
            ++probe;
            base = (base + probe * G) & mask;
        }
    }

    // ── Accessors ──

    unsigned size() const { return static_cast<unsigned>(m_size); }
    unsigned capacity() const { return static_cast<unsigned>(m_capacity); }
    bool empty() const { return m_size == 0; }

    void reset() {
        if (m_size == 0 && m_tombstones == 0)
            return;
        if (m_capacity > m_init_capacity * 4) {
            free_tables();
            alloc_tables(m_init_capacity);
        } else {
            std::memset(m_ctrl, static_cast<unsigned char>(swiss_detail::kEmpty), m_capacity);
            m_size = 0;
            m_tombstones = 0;
        }
    }

    void finalize() {
        free_tables();
        alloc_tables(m_init_capacity);
    }

    void swap(swiss_table& other) noexcept {
        std::swap(m_ctrl, other.m_ctrl);
        std::swap(m_slots, other.m_slots);
        std::swap(m_capacity, other.m_capacity);
        std::swap(m_size, other.m_size);
        std::swap(m_tombstones, other.m_tombstones);
        std::swap(m_init_capacity, other.m_init_capacity);
    }

    unsigned used_slots() const { return static_cast<unsigned>(m_size); }
    unsigned collisions() const { return 0; }

    // ── Iterator ──

    class iterator {
        int8_t const* m_ctrl;
        T const*      m_slots;
        size_t        m_pos;
        size_t        m_cap;

        void advance() {
            while (m_pos < m_cap && m_ctrl[m_pos] < 0) // skip empty/deleted (bit 7 set)
                ++m_pos;
        }

    public:
        iterator() : m_ctrl(nullptr), m_slots(nullptr), m_pos(0), m_cap(0) {}
        iterator(int8_t const* c, T const* s, size_t pos, size_t cap)
            : m_ctrl(c), m_slots(s), m_pos(pos), m_cap(cap) { advance(); }

        T& operator*() const { return const_cast<T&>(m_slots[m_pos]); }
        T const* operator->() const { return &m_slots[m_pos]; }

        iterator& operator++() { ++m_pos; advance(); return *this; }
        iterator operator++(int) { auto tmp = *this; ++*this; return tmp; }

        bool operator!=(iterator const& o) const { return m_pos != o.m_pos; }
        bool operator==(iterator const& o) const { return m_pos == o.m_pos; }
    };

    iterator begin() const { return iterator(m_ctrl, m_slots, 0, m_capacity); }
    iterator end() const { return iterator(m_ctrl, m_slots, m_capacity, m_capacity); }

private:
    unsigned get_hash(T const& d) const { return HashProc::operator()(d); }
    bool equals(T const& a, T const& b) const { return EqProc::operator()(a, b); }

    static size_t round_up(size_t n) {
        size_t v = G;
        while (v < n) v <<= 1;
        return v;
    }

    bool needs_rehash() const {
        // Rehash when occupied + tombstones exceed 7/8 of capacity.
        return (m_size + m_tombstones) * 8 >= m_capacity * 7;
    }

    void alloc_tables(size_t cap) {
        m_capacity = cap;
        m_ctrl = static_cast<int8_t*>(memory::allocate(cap));
        std::memset(m_ctrl, static_cast<unsigned char>(swiss_detail::kEmpty), cap);
        m_slots = static_cast<T*>(memory::allocate(cap * sizeof(T)));
        m_size = 0;
        m_tombstones = 0;
    }

    void free_tables() {
        if (m_ctrl) {
            memory::deallocate(m_ctrl);
            m_ctrl = nullptr;
        }
        if (m_slots) {
            memory::deallocate(m_slots);
            m_slots = nullptr;
        }
        m_size = 0;
        m_tombstones = 0;
    }

    void rehash_grow() {
        size_t new_cap = (m_capacity < G) ? G : m_capacity * 2;
        rehash_to(new_cap);
    }

    void rehash_to(size_t new_cap) {
        int8_t* old_ctrl  = m_ctrl;
        T*      old_slots = m_slots;
        size_t  old_cap   = m_capacity;

        m_capacity = new_cap;
        m_ctrl = static_cast<int8_t*>(memory::allocate(new_cap));
        std::memset(m_ctrl, static_cast<unsigned char>(swiss_detail::kEmpty), new_cap);
        m_slots = static_cast<T*>(memory::allocate(new_cap * sizeof(T)));
        m_size = 0;
        m_tombstones = 0;

        // Rehash: group-aligned insertion into fresh table (no tombstones).
        size_t mask = new_cap - 1;
        for (size_t i = 0; i < old_cap; ++i) {
            if (old_ctrl[i] >= 0) { // occupied (H2 tag: 0x00..0x7F)
                unsigned h  = get_hash(old_slots[i]);
                int8_t  tag = swiss_detail::h2_tag(h);
                size_t  base = (static_cast<size_t>(h) * G) & mask;
                size_t  probe = 0;

                while (true) {
                    auto group = swiss_detail::CtrlGroup::load(&m_ctrl[base]);
                    auto empties = group.match_empty();
                    if (empties) {
                        size_t idx = base + empties.lowest();
                        m_ctrl[idx] = tag;
                        m_slots[idx] = old_slots[i];
                        ++m_size;
                        break;
                    }
                    ++probe;
                    base = (base + probe * G) & mask;
                }
            }
        }

        memory::deallocate(old_ctrl);
        memory::deallocate(old_slots);
    }

    int8_t* m_ctrl         = nullptr;
    T*      m_slots        = nullptr;
    size_t  m_capacity     = 0;
    size_t  m_size         = 0;
    size_t  m_tombstones   = 0;
    size_t  m_init_capacity = G;
};
