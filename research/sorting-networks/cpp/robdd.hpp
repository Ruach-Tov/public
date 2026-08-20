// robdd.hpp — Reduced Ordered Binary Decision Diagram
// Port of order_only.py's ROBDD class to C++.
// Same 8-method interface: FALSE, TRUE, var, AND, OR, DIFF, size, witness.
//
// Uses open-addressing hash tables for the unique table and apply cache.
// No pointer chasing, no heap allocation per entry, cache-line friendly.
// Nodes are identified by integer handles (NodeId), same as the Python version.
//
// Ruach Tov Collective, 2026. CC BY 4.0.

#pragma once

#include <cstdint>
#include <vector>
#include <optional>
#include <unordered_map>
#include <cassert>
#include <cstring>

namespace ruachtov {

using NodeId = int32_t;

// ============================================================
// Partitioned open-addressing hash map: 3 int32 keys → int32 value
// 16 sub-tables indexed by 4 LSBs of the first key (variable number).
// Each sub-table: power-of-2, linear probing, ~70% load factor.
// The partition step is O(1) direct addressing (fits in 2 cache lines),
// reducing probe chain length by 16x.
// ============================================================

class FlatHash3 {
public:
    static constexpr int NBUCKETS = 32;
    static constexpr int32_t EMPTY = INT32_MIN;

    struct Entry {
        int32_t k0, k1, k2, val;
    };

    FlatHash3() { reset(256); }

    void reset(uint32_t total_capacity) {
        uint32_t per_bucket = total_capacity / NBUCKETS;
        if (per_bucket < 16) per_bucket = 16;
        // Round up to power of 2
        uint32_t cap = 1;
        while (cap < per_bucket) cap <<= 1;
        for (int i = 0; i < NBUCKETS; i++) {
            buckets_[i].cap = cap;
            buckets_[i].mask = cap - 1;
            buckets_[i].count = 0;
            buckets_[i].entries.assign(cap, Entry{EMPTY, 0, 0, 0});
        }
    }

    /// Lookup or insert. Returns pointer to the value slot.
    int32_t* probe(int32_t k0, int32_t k1, int32_t k2, int32_t missing_val = -1) {
        auto& b = buckets_[k0 & (NBUCKETS - 1)];
        uint32_t h = hash(k0, k1, k2) & b.mask;
        for (;;) {
            auto& e = b.entries[h];
            if (e.k0 == EMPTY) {
                if (++b.count * 10 > b.cap * 7) {
                    grow_bucket(k0 & (NBUCKETS - 1));
                    return probe(k0, k1, k2, missing_val);
                }
                e = {k0, k1, k2, missing_val};
                return &e.val;
            }
            if (e.k0 == k0 && e.k1 == k1 && e.k2 == k2) {
                return &e.val;
            }
            h = (h + 1) & b.mask;
        }
    }

    /// Lookup only. Returns nullptr if absent.
    int32_t* find(int32_t k0, int32_t k1, int32_t k2) {
        auto& b = buckets_[k0 & (NBUCKETS - 1)];
        uint32_t h = hash(k0, k1, k2) & b.mask;
        for (;;) {
            auto& e = b.entries[h];
            if (e.k0 == EMPTY) return nullptr;
            if (e.k0 == k0 && e.k1 == k1 && e.k2 == k2) return &e.val;
            h = (h + 1) & b.mask;
        }
    }

    /// Insert or update.
    void set(int32_t k0, int32_t k1, int32_t k2, int32_t val) {
        int32_t* slot = probe(k0, k1, k2, val);
        *slot = val;
    }

    void clear() {
        for (int i = 0; i < NBUCKETS; i++) {
            buckets_[i].count = 0;
            for (auto& e : buckets_[i].entries) e.k0 = EMPTY;
        }
    }

private:
    struct Bucket {
        uint32_t cap = 0;
        uint32_t mask = 0;
        uint32_t count = 0;
        std::vector<Entry> entries;
    };

    static uint32_t hash(int32_t a, int32_t b, int32_t c) {
        uint32_t h = static_cast<uint32_t>(a) * 2654435761u;
        h ^= static_cast<uint32_t>(b) * 2246822519u;
        h ^= static_cast<uint32_t>(c) * 3266489917u;
        return h;
    }

    void grow_bucket(int idx) {
        auto& b = buckets_[idx];
        auto old = std::move(b.entries);
        b.cap <<= 1;
        b.mask = b.cap - 1;
        b.count = 0;
        b.entries.assign(b.cap, Entry{EMPTY, 0, 0, 0});
        for (auto& e : old) {
            if (e.k0 != EMPTY) {
                set(e.k0, e.k1, e.k2, e.val);
            }
        }
    }

    Bucket buckets_[NBUCKETS];
};

// ============================================================
// ROBDD implementation
// ============================================================

class ROBDD {
public:
    static constexpr NodeId FALSE_NODE = 0;
    static constexpr NodeId TRUE_NODE  = 1;

    explicit ROBDD(int nvars)
        : nvars_(nvars)
    {
        // Reserve terminal nodes at indices 0 and 1
        // nodes_ stores (var, lo, hi) as flat arrays for cache friendliness
        node_var_.push_back(nvars_);  // FALSE
        node_lo_.push_back(FALSE_NODE);
        node_hi_.push_back(FALSE_NODE);
        node_var_.push_back(nvars_);  // TRUE
        node_lo_.push_back(TRUE_NODE);
        node_hi_.push_back(TRUE_NODE);

        unique_table_.reset(1024);
        apply_cache_.reset(2048);
    }

    /// Create a BDD variable node: x_i ? TRUE : FALSE
    NodeId var(int i) {
        return mk(i, FALSE_NODE, TRUE_NODE);
    }

    /// Conjunction: a AND b
    NodeId AND(NodeId a, NodeId b) {
        return apply(OpTag::AND, a, b);
    }

    /// Disjunction: a OR b
    NodeId OR(NodeId a, NodeId b) {
        return apply(OpTag::OR, a, b);
    }

    /// Difference: a AND (NOT b)
    NodeId DIFF(NodeId a, NodeId b) {
        return apply(OpTag::DIFF, a, b);
    }

    /// Number of non-terminal nodes
    int size() const {
        return static_cast<int>(node_var_.size()) - 2;
    }

    /// Top variable of a node (nvars for terminals)
    int top(NodeId n) const {
        return (n <= 1) ? nvars_ : node_var_[n];
    }

    /// Find a satisfying assignment, or std::nullopt if node == FALSE
    std::optional<std::unordered_map<int, int>> witness(NodeId node) const {
        if (node == FALSE_NODE) return std::nullopt;

        std::unordered_map<int, int> assignment;
        NodeId cur = node;
        while (cur > 1) {
            int v = node_var_[cur];
            NodeId hi = node_hi_[cur];
            if (hi != FALSE_NODE) {
                assignment[v] = 1;
                cur = hi;
            } else {
                assignment[v] = 0;
                cur = node_lo_[cur];
            }
        }
        return assignment;
    }

    // Public constants matching the Python interface
    static constexpr NodeId FALSE_ID = FALSE_NODE;
    static constexpr NodeId TRUE_ID  = TRUE_NODE;

private:
    /// Unique-table insert/lookup: ensures one node per (var, lo, hi)
    NodeId mk(int var, NodeId lo, NodeId hi) {
        if (lo == hi) return lo; // Reduction rule

        int32_t* slot = unique_table_.probe(var, lo, hi, -1);
        if (*slot != -1) return *slot;

        NodeId id = static_cast<NodeId>(node_var_.size());
        node_var_.push_back(var);
        node_lo_.push_back(lo);
        node_hi_.push_back(hi);
        *slot = id;
        return id;
    }

    enum class OpTag { AND, OR, DIFF };

    /// Apply a binary operation with memoization
    NodeId apply(OpTag op, NodeId a, NodeId b) {
        // Terminal cases
        switch (op) {
        case OpTag::AND:
            if (a == FALSE_NODE || b == FALSE_NODE) return FALSE_NODE;
            if (a == TRUE_NODE)  return b;
            if (b == TRUE_NODE)  return a;
            if (a == b)          return a;
            break;
        case OpTag::OR:
            if (a == TRUE_NODE || b == TRUE_NODE) return TRUE_NODE;
            if (a == FALSE_NODE) return b;
            if (b == FALSE_NODE) return a;
            if (a == b)          return a;
            break;
        case OpTag::DIFF:
            if (a == FALSE_NODE) return FALSE_NODE;
            if (b == TRUE_NODE)  return FALSE_NODE;
            if (b == FALSE_NODE) return a;
            if (a == b)          return FALSE_NODE;
            break;
        }

        // Commutative normalization for AND and OR
        if (op != OpTag::DIFF && a > b) std::swap(a, b);

        // Combine op+a into one key slot to keep 3 keys
        int32_t k0 = (static_cast<int32_t>(op) << 28) | (a & 0x0FFFFFFF);

        // Cache lookup
        int32_t* cached = apply_cache_.find(k0, b, 0);
        if (cached) return *cached;

        // Shannon decomposition on the top variable
        int va = top(a), vb = top(b);
        int v = std::min(va, vb);

        NodeId a_lo = (va == v) ? node_lo_[a] : a;
        NodeId a_hi = (va == v) ? node_hi_[a] : a;
        NodeId b_lo = (vb == v) ? node_lo_[b] : b;
        NodeId b_hi = (vb == v) ? node_hi_[b] : b;

        NodeId r_lo = apply(op, a_lo, b_lo);
        NodeId r_hi = apply(op, a_hi, b_hi);

        NodeId result = mk(v, r_lo, r_hi);
        apply_cache_.set(k0, b, 0, result);
        return result;
    }

    int nvars_;
    // Flat node storage — SoA for cache friendliness
    std::vector<int>    node_var_;
    std::vector<NodeId> node_lo_;
    std::vector<NodeId> node_hi_;
    // Partitioned open-addressing hash tables
    FlatHash3 unique_table_;
    FlatHash3 apply_cache_;
};

/// Verify that a comparator network sorts all inputs (0-1 principle).
/// Returns true if the network sorts, false otherwise.
inline bool verify_sorts(int n, const std::vector<std::pair<int, int>>& comparators) {
    ROBDD bdd(n);
    std::vector<NodeId> w(n);
    for (int i = 0; i < n; ++i)
        w[i] = bdd.var(i);

    for (auto [lo, hi] : comparators) {
        NodeId new_lo = bdd.AND(w[lo], w[hi]);
        NodeId new_hi = bdd.OR(w[lo], w[hi]);
        w[lo] = new_lo;
        w[hi] = new_hi;
    }

    for (int k = 0; k < n - 1; ++k) {
        NodeId bad = bdd.DIFF(w[k], w[k + 1]);
        if (bad != ROBDD::FALSE_ID)
            return false;
    }
    return true;
}

} // namespace ruachtov
