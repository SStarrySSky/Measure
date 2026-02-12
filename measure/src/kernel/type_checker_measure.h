/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Type checker integration for Measure approximate equality.
Provides the fallback path: when is_def_eq returns false,
try is_approx_eq_core if the current eq_mode is Approx.

See ARCHITECTURE.md Section 3.2 and docs/kernel-modification.md.
*/
#pragma once
#include "kernel/is_approx_eq.h"
#include "kernel/natural_units.h"
#include "kernel/rigor_propagation.h"
#include <functional>
#include <string>
#include <cstdint>

namespace lean {

// ── Equality mode ───────────────────────────────────────────────

enum class eq_mode : uint8_t {
    exact,    // standard Lean4 behavior: is_def_eq only
    approx   // Measure extension: fallback to is_approx_eq_core
};

// ── Type checker Measure extension ──────────────────────────────

/// Configuration for the Measure type checker extension.
struct type_checker_measure_config {
    eq_mode m_eq_mode = eq_mode::exact;
    approx_eq_config m_approx_config;
    bool m_natural_units_active = false;
    epsilon_val m_max_epsilon = epsilon_val::inf();
};

/// Result of the extended definitional equality check.
struct def_eq_ext_result {
    bool m_is_eq = false;
    bool m_used_approx = false;
    epsilon_val m_epsilon;
    uint64_t m_proof_node = 0;
    std::string m_diagnostic;
};

/// Measure extension to the Lean4 type checker.
/// Wraps the standard is_def_eq with an approximate fallback path.
///
/// Usage in the modified type_checker.cpp:
///   1. Call standard is_def_eq(lhs, rhs)
///   2. If it returns true, done (exact equality)
///   3. If it returns false AND eq_mode == approx:
///      a. Call try_approx_fallback(lhs_hash, rhs_hash, ...)
///      b. If approx succeeds, accept with epsilon annotation
///      c. If approx fails, report original failure
class type_checker_measure {
    approx_eq_checker m_approx_checker;
    type_checker_measure_config m_config;

public:
    explicit type_checker_measure(
        type_checker_measure_config const & cfg = {});

    /// Main fallback entry point.
    /// Called when is_def_eq returns false and eq_mode == approx.
    ///
    /// Parameters mirror the approx_eq_checker callbacks:
    ///   - lhs_hash, rhs_hash: expression hashes
    ///   - Callbacks for inspecting expression structure
    ///
    /// Returns a result indicating whether approximate equality holds.
    def_eq_ext_result try_approx_fallback(
        uint64_t lhs_hash, uint64_t rhs_hash,
        std::function<bool(uint64_t)> is_numeric_lit,
        std::function<double(uint64_t)> get_numeric_val,
        std::function<bool(uint64_t)> is_app,
        std::function<uint64_t(uint64_t)> get_app_fn_hash,
        std::function<std::vector<uint64_t>(uint64_t)> get_app_args);

    /// Dimensional approximate equality check.
    /// Used when comparing Quantity types with different SI dimensions
    /// that may be equivalent under natural units.
    def_eq_ext_result try_dim_approx(
        dim7 const & dim_lhs, dim7 const & dim_rhs);

    /// Combined check: first try exact, then approx if enabled.
    /// `exact_eq_fn` is the standard is_def_eq callback.
    def_eq_ext_result check_def_eq_ext(
        uint64_t lhs_hash, uint64_t rhs_hash,
        std::function<bool()> exact_eq_fn,
        std::function<bool(uint64_t)> is_numeric_lit,
        std::function<double(uint64_t)> get_numeric_val,
        std::function<bool(uint64_t)> is_app,
        std::function<uint64_t(uint64_t)> get_app_fn_hash,
        std::function<std::vector<uint64_t>(uint64_t)> get_app_args);

    // ── Configuration ────────────────────────────────────────

    eq_mode get_eq_mode() const { return m_config.m_eq_mode; }
    void set_eq_mode(eq_mode mode) { m_config.m_eq_mode = mode; }

    bool natural_units_active() const {
        return m_config.m_natural_units_active;
    }
    void set_natural_units(bool active) {
        m_config.m_natural_units_active = active;
    }

    // ── Diagnostics ──────────────────────────────────────────

    approx_eq_checker const & approx_checker() const {
        return m_approx_checker;
    }
    approx_eq_checker & approx_checker() {
        return m_approx_checker;
    }

    void reset();
};

} // namespace lean
