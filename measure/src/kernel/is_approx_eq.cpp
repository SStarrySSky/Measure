/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/is_approx_eq.h"
#include <cmath>
#include <algorithm>

namespace lean {

// --- approx_equiv_manager ---

approx_cache_entry const * approx_equiv_manager::find(
    uint64_t lhs_hash, uint64_t rhs_hash) const
{
    // Normalize key order for symmetric lookup
    approx_cache_key key;
    if (lhs_hash <= rhs_hash) {
        key = {lhs_hash, rhs_hash};
    } else {
        key = {rhs_hash, lhs_hash};
    }
    auto it = m_cache.find(key);
    return it != m_cache.end() ? &it->second : nullptr;
}

void approx_equiv_manager::insert(
    uint64_t lhs_hash, uint64_t rhs_hash,
    approx_cache_entry const & entry)
{
    approx_cache_key key;
    if (lhs_hash <= rhs_hash) {
        key = {lhs_hash, rhs_hash};
    } else {
        key = {rhs_hash, lhs_hash};
    }
    m_cache[key] = entry;
}

void approx_equiv_manager::clear() { m_cache.clear(); }
size_t approx_equiv_manager::size() const { return m_cache.size(); }

// --- approx_eq_checker ---

approx_eq_checker::approx_eq_checker(approx_eq_config const & cfg)
    : m_config(cfg) {}

void approx_eq_checker::reset() {
    m_tracker.reset();
    m_cache.clear();
}

epsilon_tracker const & approx_eq_checker::tracker() const {
    return m_tracker;
}

epsilon_tracker & approx_eq_checker::tracker() {
    return m_tracker;
}

approx_equiv_manager const & approx_eq_checker::cache() const {
    return m_cache;
}

// --- Numeric approximation ---

/// Convert a double difference to a rational epsilon_val.
/// Uses a fixed denominator for precision (1e15).
static epsilon_val double_to_epsilon(double diff) {
    if (diff <= 0.0) return epsilon_val::zero();
    if (std::isinf(diff) || std::isnan(diff))
        return epsilon_val::inf();
    constexpr uint64_t DENOM = 1000000000000000ULL; // 1e15
    double scaled = diff * static_cast<double>(DENOM);
    if (scaled >= static_cast<double>(UINT64_MAX))
        return epsilon_val::inf();
    uint64_t num = static_cast<uint64_t>(std::ceil(scaled));
    return epsilon_val::make(num, DENOM);
}

approx_eq_result approx_eq_checker::try_numeric_approx(
    double val_a, double val_b, std::string const & hint)
{
    double abs_diff = std::fabs(val_a - val_b);
    double max_abs = std::fmax(std::fabs(val_a), std::fabs(val_b));

    // Check absolute tolerance
    bool abs_ok = abs_diff <= m_config.m_numeric_abs_tol;
    // Check relative tolerance
    bool rel_ok = (max_abs > 0.0)
        ? (abs_diff / max_abs <= m_config.m_numeric_rel_tol)
        : abs_ok;

    if (!abs_ok && !rel_ok) {
        return {false, epsilon_val::inf(), 0};
    }

    auto eps = double_to_epsilon(abs_diff);

    // Check against max allowed epsilon
    if (!eps.leq(m_config.m_max_epsilon)) {
        return {false, eps, 0};
    }

    auto node_id = m_tracker.mk_literal(eps, hint);
    return {true, eps, node_id};
}

// --- Application node approximation ---

approx_eq_result approx_eq_checker::is_approx_eq_app(
    uint64_t fn_hash,
    std::vector<uint64_t> const & args_a,
    std::vector<uint64_t> const & args_b,
    std::function<bool(uint64_t)> is_numeric_lit,
    std::function<double(uint64_t)> get_numeric_val,
    std::function<bool(uint64_t)> is_app,
    std::function<uint64_t(uint64_t)> get_app_fn_hash,
    std::function<std::vector<uint64_t>(uint64_t)> get_app_args)
{
    if (args_a.size() != args_b.size()) {
        return {false, epsilon_val::inf(), 0};
    }
    if (args_a.empty()) {
        // Same function, no args: exactly equal
        return {true, epsilon_val::zero(), 0};
    }

    // Check each argument pair, accumulate via max rule
    uint64_t combined_node = 0;

    for (size_t i = 0; i < args_a.size(); ++i) {
        if (args_a[i] == args_b[i]) continue; // identical arg

        auto arg_result = is_approx_eq_core(
            args_a[i], args_b[i],
            is_numeric_lit, get_numeric_val,
            is_app, get_app_fn_hash, get_app_args);

        if (!arg_result.m_is_approx_eq) {
            return {false, epsilon_val::inf(), 0};
        }

        if (combined_node == 0) {
            combined_node = arg_result.m_proof_node_id;
        } else {
            combined_node = m_tracker.mk_max(
                combined_node, arg_result.m_proof_node_id,
                "app-arg-" + std::to_string(i));
        }
    }

    if (combined_node == 0) {
        // All args identical
        return {true, epsilon_val::zero(), 0};
    }

    auto eps = m_tracker.get_epsilon(combined_node);
    return {true, eps, combined_node};
}

// --- Main entry point ---

approx_eq_result approx_eq_checker::is_approx_eq_core(
    uint64_t lhs_hash, uint64_t rhs_hash,
    std::function<bool(uint64_t)> is_numeric_lit,
    std::function<double(uint64_t)> get_numeric_val,
    std::function<bool(uint64_t)> is_app,
    std::function<uint64_t(uint64_t)> get_app_fn_hash,
    std::function<std::vector<uint64_t>(uint64_t)> get_app_args)
{
    // Identical expressions are exactly equal
    if (lhs_hash == rhs_hash) {
        return {true, epsilon_val::zero(), 0};
    }

    // Check cache first
    auto cached = m_cache.find(lhs_hash, rhs_hash);
    if (cached) {
        return {cached->m_is_approx_eq,
                cached->m_epsilon,
                cached->m_proof_node};
    }

    approx_eq_result result = {false, epsilon_val::inf(), 0};

    // Strategy 1: numeric literal approximation
    if (m_config.m_enable_numeric_approx
        && is_numeric_lit(lhs_hash)
        && is_numeric_lit(rhs_hash))
    {
        double va = get_numeric_val(lhs_hash);
        double vb = get_numeric_val(rhs_hash);
        result = try_numeric_approx(va, vb, "numeric-lit");
    }

    // Strategy 2: application node per-argument approximation
    if (!result.m_is_approx_eq
        && m_config.m_enable_app_approx
        && is_app(lhs_hash) && is_app(rhs_hash))
    {
        uint64_t fn_a = get_app_fn_hash(lhs_hash);
        uint64_t fn_b = get_app_fn_hash(rhs_hash);
        // Same function head required
        if (fn_a == fn_b) {
            auto args_a = get_app_args(lhs_hash);
            auto args_b = get_app_args(rhs_hash);
            result = is_approx_eq_app(
                fn_a, args_a, args_b,
                is_numeric_lit, get_numeric_val,
                is_app, get_app_fn_hash, get_app_args);
        }
    }

    // Store in cache
    m_cache.insert(lhs_hash, rhs_hash,
        {result.m_is_approx_eq,
         result.m_epsilon,
         result.m_proof_node_id});

    return result;
}

} // namespace lean
