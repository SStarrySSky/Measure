/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Natural unit system kernel: NaturalDim4, projection matrix P,
dim_approx_eq, kernel membership test.
See docs/type-system.md Section 7.
*/
#pragma once
#include "kernel/approx_eq.h"
#include <cstdint>
#include <string>
#include <array>

namespace lean {

// Forward: QExp-like rational for dimension exponents.
// We reuse int64 numerator / uint64 denominator pairs inline
// since the kernel Dim is represented as 7 such pairs.

/// A single rational exponent (signed numerator, positive denominator).
struct dim_exp {
    int64_t  num = 0;
    uint64_t den = 1;

    static dim_exp zero() { return {0, 1}; }

    bool is_zero() const { return num == 0; }

    bool operator==(dim_exp const & o) const {
        // a/b == c/d  iff  a*d == c*b  (both den > 0)
        return static_cast<__int128>(num) * o.den
            == static_cast<__int128>(o.num) * den;
    }
    bool operator!=(dim_exp const & o) const { return !(*this == o); }

    dim_exp operator+(dim_exp const & o) const {
        // a/b + c/d = (a*d + c*b) / (b*d)
        int64_t  n = num * static_cast<int64_t>(o.den)
                   + o.num * static_cast<int64_t>(den);
        uint64_t d = den * o.den;
        return simplify({n, d});
    }

    dim_exp operator-(dim_exp const & o) const {
        int64_t  n = num * static_cast<int64_t>(o.den)
                   - o.num * static_cast<int64_t>(den);
        uint64_t d = den * o.den;
        return simplify({n, d});
    }

    dim_exp operator-() const { return {-num, den}; }

    std::string to_string() const;

private:
    static dim_exp simplify(dim_exp e);
};

/// 7-dimensional SI dimension vector.
struct dim7 {
    dim_exp L, M, T, I, Theta, N, J;

    static dim7 zero() {
        return {dim_exp::zero(), dim_exp::zero(), dim_exp::zero(),
                dim_exp::zero(), dim_exp::zero(), dim_exp::zero(),
                dim_exp::zero()};
    }

    bool operator==(dim7 const & o) const {
        return L == o.L && M == o.M && T == o.T && I == o.I
            && Theta == o.Theta && N == o.N && J == o.J;
    }
    bool operator!=(dim7 const & o) const { return !(*this == o); }

    dim7 operator-(dim7 const & o) const {
        return {L - o.L, M - o.M, T - o.T, I - o.I,
                Theta - o.Theta, N - o.N, J - o.J};
    }

    bool is_zero() const {
        return L.is_zero() && M.is_zero() && T.is_zero()
            && I.is_zero() && Theta.is_zero() && N.is_zero()
            && J.is_zero();
    }
};

/// 4-dimensional natural-unit dimension vector.
/// Projection of 7D SI space via P matrix (hbar=c=k_B=1).
///   E = M - L - T + Theta
///   I = I
///   N = N
///   J = J
struct natural_dim4 {
    dim_exp E, I, N, J;

    static natural_dim4 zero() {
        return {dim_exp::zero(), dim_exp::zero(),
                dim_exp::zero(), dim_exp::zero()};
    }

    bool operator==(natural_dim4 const & o) const {
        return E == o.E && I == o.I && N == o.N && J == o.J;
    }
    bool operator!=(natural_dim4 const & o) const { return !(*this == o); }

    bool is_zero() const {
        return E.is_zero() && I.is_zero() && N.is_zero() && J.is_zero();
    }

    std::string to_string() const;
};

/// Result of dimension approximate-equality check.
enum class dim_eq_result : uint8_t {
    exact,          // 7D identical
    natural_equiv,  // identical after projection (diff in ker(P))
    mismatch        // not equivalent
};

// ── Projection matrix P (4x7) ──────────────────────────────────
//
//          L    M    T    I    Θ    N    J
//   E  [ -1    1   -1    0    1    0    0 ]
//   I  [  0    0    0    1    0    0    0 ]
//   N  [  0    0    0    0    0    1    0 ]
//   J  [  0    0    0    0    0    0    1 ]

/// Project a 7D SI dimension to 4D natural-unit space.
natural_dim4 project_natural(dim7 const & d);

/// Check if a 7D difference vector lies in ker(P).
/// ker(P) = { v in Q^7 : P*v = 0 }, 3-dimensional.
bool in_kernel(dim7 const & delta);

/// Dimension approximate-equality: compares two dims
/// accounting for natural-unit equivalence when enabled.
dim_eq_result dim_approx_eq(dim7 const & d1, dim7 const & d2,
                             bool natural_units_active);

/// Convert dim_eq_result to string for diagnostics.
char const * dim_eq_result_to_string(dim_eq_result r);

} // namespace lean
