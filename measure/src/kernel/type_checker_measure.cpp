/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/type_checker_measure.h"
#include <sstream>

namespace lean {

type_checker_measure::type_checker_measure(
    type_checker_measure_config const & cfg)
    : m_approx_checker(cfg.m_approx_config)
    , m_config(cfg) {}

void type_checker_measure::reset() {
    m_approx_checker.reset();
}

// ── Approx fallback ─────────────────────────────────────────────

def_eq_ext_result type_checker_measure::try_approx_fallback(
    uint64_t lhs_hash, uint64_t rhs_hash,
    std::function<bool(uint64_t)> is_numeric_lit,
    std::function<double(uint64_t)> get_numeric_val,
    std::function<bool(uint64_t)> is_app,
    std::function<uint64_t(uint64_t)> get_app_fn_hash,
    std::function<std::vector<uint64_t>(uint64_t)> get_app_args)
{
    if (m_config.m_eq_mode != eq_mode::approx) {
        return {false, false, epsilon_val::inf(), 0,
                "eq_mode is exact; approx fallback disabled"};
    }

    auto result = m_approx_checker.is_approx_eq_core(
        lhs_hash, rhs_hash,
        is_numeric_lit, get_numeric_val,
        is_app, get_app_fn_hash, get_app_args);

    if (!result.m_is_approx_eq) {
        return {false, true, result.m_epsilon, 0,
                "approx fallback attempted but failed"};
    }

    // Check epsilon against configured maximum
    if (!result.m_epsilon.leq(m_config.m_max_epsilon)) {
        return {false, true, result.m_epsilon, result.m_proof_node_id,
                "approx match found but epsilon exceeds max allowed"};
    }

    std::ostringstream diag;
    diag << "approx equality accepted: eps = "
         << result.m_epsilon.to_string();
    if (m_approx_checker.tracker().has_overflow()) {
        diag << " [WARNING: epsilon overflow detected]";
    }

    return {true, true, result.m_epsilon,
            result.m_proof_node_id, diag.str()};
}

// ── Dimensional approx ──────────────────────────────────────────

def_eq_ext_result type_checker_measure::try_dim_approx(
    dim7 const & dim_lhs, dim7 const & dim_rhs)
{
    auto dr = dim_approx_eq(
        dim_lhs, dim_rhs, m_config.m_natural_units_active);

    switch (dr) {
    case dim_eq_result::exact:
        return {true, false, epsilon_val::zero(), 0,
                "dimensions exactly equal"};
    case dim_eq_result::natural_equiv:
        return {true, true, epsilon_val::zero(), 0,
                "dimensions equivalent under natural units"};
    case dim_eq_result::mismatch:
        return {false, false, epsilon_val::inf(), 0,
                "dimensional mismatch"};
    }
    return {false, false, epsilon_val::inf(), 0, "unknown"};
}

// ── Combined check ──────────────────────────────────────────────

def_eq_ext_result type_checker_measure::check_def_eq_ext(
    uint64_t lhs_hash, uint64_t rhs_hash,
    std::function<bool()> exact_eq_fn,
    std::function<bool(uint64_t)> is_numeric_lit,
    std::function<double(uint64_t)> get_numeric_val,
    std::function<bool(uint64_t)> is_app,
    std::function<uint64_t(uint64_t)> get_app_fn_hash,
    std::function<std::vector<uint64_t>(uint64_t)> get_app_args)
{
    // Step 1: try exact equality (standard Lean4 path)
    if (exact_eq_fn()) {
        return {true, false, epsilon_val::zero(), 0,
                "exact definitional equality"};
    }

    // Step 2: if exact mode, stop here
    if (m_config.m_eq_mode == eq_mode::exact) {
        return {false, false, epsilon_val::inf(), 0,
                "is_def_eq failed; eq_mode=exact"};
    }

    // Step 3: try approximate fallback
    return try_approx_fallback(
        lhs_hash, rhs_hash,
        is_numeric_lit, get_numeric_val,
        is_app, get_app_fn_hash, get_app_args);
}

} // namespace lean
