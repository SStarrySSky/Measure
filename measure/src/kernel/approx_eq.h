/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <cstdint>
#include <string>

namespace lean {

/// Rational epsilon value for approximate equality judgments.
/// Represents a non-negative rational number num/den.
/// Invariant: den > 0, gcd(num, den) == 1 (after simplify).
struct epsilon_val {
    uint64_t m_numerator = 0;
    uint64_t m_denominator = 1;

    // Construction
    static epsilon_val zero();
    static epsilon_val one();
    static epsilon_val inf();
    static epsilon_val make(uint64_t num, uint64_t den);

    // Predicates
    bool is_zero() const;
    bool is_inf() const;

    // Comparison (cross-multiplication, overflow-safe)
    bool leq(epsilon_val const & other) const;
    bool eq(epsilon_val const & other) const;

    // Arithmetic (results are simplified)
    epsilon_val add(epsilon_val const & other) const;
    epsilon_val mul(epsilon_val const & other) const;
    epsilon_val max(epsilon_val const & other) const;

    // Simplification via GCD
    epsilon_val simplify() const;

    // Overflow detection
    static bool would_overflow_mul(uint64_t a, uint64_t b);
    static bool cross_leq_safe(uint64_t a, uint64_t b,
                                uint64_t c, uint64_t d);

    // Serialization
    std::string to_string() const;
};

/// Result of an approximate equality check.
struct approx_eq_result {
    bool        m_is_approx_eq = false;
    epsilon_val m_epsilon;
    uint64_t    m_proof_node_id = 0;  // proof tree node (Phase 2)
};

// Utility: GCD for uint64_t
uint64_t gcd_u64(uint64_t a, uint64_t b);

} // namespace lean
