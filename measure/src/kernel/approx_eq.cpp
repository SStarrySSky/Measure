/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/approx_eq.h"
#include <sstream>
#include <limits>
#include <stdexcept>

namespace lean {

static constexpr uint64_t UINT64_INF = std::numeric_limits<uint64_t>::max();

// --- GCD ---

uint64_t gcd_u64(uint64_t a, uint64_t b) {
    while (b != 0) {
        uint64_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}

// --- Construction ---

epsilon_val epsilon_val::zero() {
    return {0, 1};
}

epsilon_val epsilon_val::one() {
    return {1, 1};
}

epsilon_val epsilon_val::inf() {
    return {UINT64_INF, 1};
}

epsilon_val epsilon_val::make(uint64_t num, uint64_t den) {
    if (den == 0) {
        throw std::invalid_argument("epsilon_val: denominator cannot be zero");
    }
    if (num == 0) return zero();
    uint64_t g = gcd_u64(num, den);
    return {num / g, den / g};
}

// --- Predicates ---

bool epsilon_val::is_zero() const {
    return m_numerator == 0;
}

bool epsilon_val::is_inf() const {
    return m_numerator == UINT64_INF && m_denominator == 1;
}

// --- Overflow detection ---

bool epsilon_val::would_overflow_mul(uint64_t a, uint64_t b) {
    if (a == 0 || b == 0) return false;
    return a > UINT64_INF / b;
}

bool epsilon_val::cross_leq_safe(uint64_t a, uint64_t b,
                                  uint64_t c, uint64_t d) {
    // a/b <= c/d  iff  a*d <= c*b  (using __int128 to avoid overflow)
    using u128 = unsigned __int128;
    return static_cast<u128>(a) * static_cast<u128>(d)
        <= static_cast<u128>(c) * static_cast<u128>(b);
}

// --- Comparison ---

bool epsilon_val::leq(epsilon_val const & other) const {
    if (is_zero()) return true;
    if (other.is_inf()) return true;
    if (is_inf()) return other.is_inf();
    return cross_leq_safe(m_numerator, m_denominator,
                           other.m_numerator, other.m_denominator);
}

bool epsilon_val::eq(epsilon_val const & other) const {
    return leq(other) && other.leq(*this);
}

// --- Simplification ---

epsilon_val epsilon_val::simplify() const {
    if (m_numerator == 0) return zero();
    uint64_t g = gcd_u64(m_numerator, m_denominator);
    return {m_numerator / g, m_denominator / g};
}

// --- Arithmetic ---

epsilon_val epsilon_val::add(epsilon_val const & other) const {
    if (is_zero()) return other;
    if (other.is_zero()) return *this;
    if (is_inf() || other.is_inf()) return inf();

    // a/b + c/d = (a*d + c*b) / (b*d), using __int128
    using u128 = unsigned __int128;
    u128 num = static_cast<u128>(m_numerator) * other.m_denominator
             + static_cast<u128>(other.m_numerator) * m_denominator;
    u128 den = static_cast<u128>(m_denominator) * other.m_denominator;

    // Check if result fits in uint64_t
    if (num > UINT64_INF || den > UINT64_INF) {
        // Simplify with GCD before truncation check
        u128 g = den;
        u128 tmp = num;
        while (tmp != 0) { u128 t = tmp; tmp = g % tmp; g = t; }
        num /= g;
        den /= g;
        if (num > UINT64_INF || den > UINT64_INF) {
            return inf();  // overflow sentinel
        }
    }
    return make(static_cast<uint64_t>(num), static_cast<uint64_t>(den));
}

epsilon_val epsilon_val::mul(epsilon_val const & other) const {
    if (is_zero() || other.is_zero()) return zero();
    if (is_inf() || other.is_inf()) return inf();

    // Cross-simplify before multiplying to reduce overflow risk
    uint64_t g1 = gcd_u64(m_numerator, other.m_denominator);
    uint64_t g2 = gcd_u64(other.m_numerator, m_denominator);
    uint64_t num_a = m_numerator / g1;
    uint64_t den_b = other.m_denominator / g1;
    uint64_t num_b = other.m_numerator / g2;
    uint64_t den_a = m_denominator / g2;

    if (would_overflow_mul(num_a, num_b) ||
        would_overflow_mul(den_a, den_b)) {
        return inf();  // overflow sentinel
    }
    return make(num_a * num_b, den_a * den_b);
}

epsilon_val epsilon_val::max(epsilon_val const & other) const {
    return leq(other) ? other : *this;
}

// --- Serialization ---

std::string epsilon_val::to_string() const {
    if (is_zero()) return "0";
    if (is_inf()) return "inf";
    if (m_denominator == 1) {
        return std::to_string(m_numerator);
    }
    return std::to_string(m_numerator) + "/" +
           std::to_string(m_denominator);
}

} // namespace lean
