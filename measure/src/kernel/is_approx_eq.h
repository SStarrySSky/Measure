/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include "kernel/approx_eq.h"
#include "kernel/epsilon_tracker.h"
#include <unordered_map>
#include <functional>
#include <string>
#include <cstdint>

namespace lean {

/// Cache key for approximate equivalence lookups.
/// Pairs of expression hashes, order-normalized.
struct approx_cache_key {
    uint64_t m_lhs_hash;
    uint64_t m_rhs_hash;

    bool operator==(approx_cache_key const & o) const {
        return m_lhs_hash == o.m_lhs_hash
            && m_rhs_hash == o.m_rhs_hash;
    }
};

struct approx_cache_key_hash {
    size_t operator()(approx_cache_key const & k) const {
        // FNV-1a style combine
        size_t h = 14695981039346656037ULL;
        h ^= k.m_lhs_hash; h *= 1099511628211ULL;
        h ^= k.m_rhs_hash; h *= 1099511628211ULL;
        return h;
    }
};

/// Cached result of an approximate equivalence check.
struct approx_cache_entry {
    bool        m_is_approx_eq = false;
    epsilon_val m_epsilon;
    uint64_t    m_proof_node = 0;
};

/// Approximate equivalence cache, extending equiv_manager.
/// Stores previously computed approx-eq results for reuse.
class approx_equiv_manager {
    using cache_map = std::unordered_map<
        approx_cache_key, approx_cache_entry,
        approx_cache_key_hash>;
    cache_map m_cache;

public:
    /// Look up a cached result. Returns nullptr if not found.
    approx_cache_entry const * find(
        uint64_t lhs_hash, uint64_t rhs_hash) const;

    /// Insert a result into the cache.
    void insert(uint64_t lhs_hash, uint64_t rhs_hash,
                approx_cache_entry const & entry);

    /// Clear the cache.
    void clear();

    size_t size() const;
};

/// Configuration for approximate equality checking.
struct approx_eq_config {
    /// Maximum epsilon allowed for the entire judgment.
    epsilon_val m_max_epsilon = epsilon_val::inf();
    /// Whether to enable numeric approximation for literals.
    bool m_enable_numeric_approx = true;
    /// Whether to enable per-argument app node approximation.
    bool m_enable_app_approx = true;
    /// Relative tolerance for numeric literal comparison.
    /// Two floats a, b are approx-eq if |a-b| <= rel_tol * max(|a|,|b|)
    double m_numeric_rel_tol = 1e-10;
    /// Absolute tolerance for numeric literal comparison.
    double m_numeric_abs_tol = 1e-15;
};

/// Core approximate equality checker.
/// This is the Phase 2 extension to the type checker.
/// Called as a fallback when is_def_eq returns false.
class approx_eq_checker {
    epsilon_tracker      m_tracker;
    approx_equiv_manager m_cache;
    approx_eq_config     m_config;

public:
    explicit approx_eq_checker(approx_eq_config const & cfg = {});

    /// Main entry point: check if two expressions are approximately equal.
    /// Returns the result with epsilon bound and proof tree node.
    ///
    /// `lhs_hash` / `rhs_hash`: expression hashes for caching.
    /// `is_numeric_lit`: callback to test if an expr hash is a numeric literal.
    /// `get_numeric_val`: callback to extract Float64 value from a literal.
    /// `get_app_fn_hash`: callback to get the function hash of an app node.
    /// `get_app_args`: callback to get argument hashes of an app node.
    /// `is_app`: callback to test if an expr hash is an application.
    approx_eq_result is_approx_eq_core(
        uint64_t lhs_hash, uint64_t rhs_hash,
        std::function<bool(uint64_t)> is_numeric_lit,
        std::function<double(uint64_t)> get_numeric_val,
        std::function<bool(uint64_t)> is_app,
        std::function<uint64_t(uint64_t)> get_app_fn_hash,
        std::function<std::vector<uint64_t>(uint64_t)> get_app_args);

    /// Try numeric approximation for two literal expressions.
    approx_eq_result try_numeric_approx(
        double val_a, double val_b,
        std::string const & hint = "");

    /// Try per-argument approximation for two application nodes.
    /// Requires same function head; checks each argument pair.
    approx_eq_result is_approx_eq_app(
        uint64_t fn_hash,
        std::vector<uint64_t> const & args_a,
        std::vector<uint64_t> const & args_b,
        std::function<bool(uint64_t)> is_numeric_lit,
        std::function<double(uint64_t)> get_numeric_val,
        std::function<bool(uint64_t)> is_app,
        std::function<uint64_t(uint64_t)> get_app_fn_hash,
        std::function<std::vector<uint64_t>(uint64_t)> get_app_args);

    /// Access the epsilon tracker for diagnostics.
    epsilon_tracker const & tracker() const;
    epsilon_tracker & tracker();

    /// Access the cache.
    approx_equiv_manager const & cache() const;

    /// Reset all state.
    void reset();
};

} // namespace lean
