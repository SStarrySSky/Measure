/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/natural_units.h"
#include <sstream>
#include <cstdlib>

namespace lean {

// ── dim_exp helpers ─────────────────────────────────────────────

static uint64_t gcd_impl(uint64_t a, uint64_t b) {
    while (b) { uint64_t t = b; b = a % b; a = t; }
    return a;
}

dim_exp dim_exp::simplify(dim_exp e) {
    if (e.num == 0) return {0, 1};
    uint64_t abs_num = static_cast<uint64_t>(std::abs(e.num));
    uint64_t g = gcd_impl(abs_num, e.den);
    return {e.num / static_cast<int64_t>(g), e.den / g};
}

std::string dim_exp::to_string() const {
    if (num == 0) return "0";
    if (den == 1) return std::to_string(num);
    return std::to_string(num) + "/" + std::to_string(den);
}

// ── natural_dim4 ────────────────────────────────────────────────

std::string natural_dim4::to_string() const {
    std::ostringstream os;
    os << "(E=" << E.to_string()
       << ", I=" << I.to_string()
       << ", N=" << N.to_string()
       << ", J=" << J.to_string() << ")";
    return os.str();
}

// ── Projection: 7D -> 4D via matrix P ──────────────────────────
//   E = M - L - T + Theta
//   I = I
//   N = N
//   J = J

natural_dim4 project_natural(dim7 const & d) {
    natural_dim4 result;
    result.E = d.M - d.L - d.T + d.Theta;
    result.I = d.I;
    result.N = d.N;
    result.J = d.J;
    return result;
}

// ── Kernel membership: delta in ker(P) iff P*delta = 0 ─────────

bool in_kernel(dim7 const & delta) {
    auto proj = project_natural(delta);
    return proj.is_zero();
}

// ── dim_approx_eq ──────────────────────────────────────────────

dim_eq_result dim_approx_eq(dim7 const & d1, dim7 const & d2,
                             bool natural_units_active)
{
    if (d1 == d2) {
        return dim_eq_result::exact;
    }
    if (natural_units_active) {
        dim7 delta = d1 - d2;
        if (in_kernel(delta)) {
            return dim_eq_result::natural_equiv;
        }
    }
    return dim_eq_result::mismatch;
}

char const * dim_eq_result_to_string(dim_eq_result r) {
    switch (r) {
    case dim_eq_result::exact:         return "exact";
    case dim_eq_result::natural_equiv: return "natural_equiv";
    case dim_eq_result::mismatch:      return "mismatch";
    }
    return "unknown";
}

} // namespace lean
