/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include "kernel/measure_types.h"
#include "kernel/rigor_propagation.h"
#include "kernel/approx_eq.h"
#include <vector>
#include <string>
#include <optional>
#include <functional>
#include <cmath>
#include <numeric>
#include <cstdint>

namespace lean {

// ── Conservation law source ──────────────────────────────────────

enum class conservation_source : uint8_t {
    declared,    // user @[conservation] attribute
    noether,     // derived from symmetry via Noether's theorem
    inherited    // inherited from parent theory via extension
};

// ── Conservation exactness ───────────────────────────────────────

enum class conservation_exactness : uint8_t {
    exact,               // dQ/dt = 0 exactly
    approximate_bound,   // dQ/dt = O(epsilon)
    anomalously_broken   // classical symmetry broken by quantum anomaly
};

// ── Symmetry group classification ────────────────────────────────

enum class symmetry_kind : uint8_t {
    time_translation,    // -> energy conservation
    space_translation,   // -> momentum conservation
    rotation,            // -> angular momentum conservation
    gauge,               // -> charge conservation
    lorentz,             // -> relativistic invariants
    poincare,            // -> full relativistic conservation
    custom               // user-defined
};

// ── Symmetry declaration ─────────────────────────────────────────

struct symmetry_decl {
    std::string m_name;
    symmetry_kind m_kind = symmetry_kind::custom;
    std::string m_group_name;
    std::string m_transformation;
    std::string m_conserved_qty_name;
    bool m_is_exact = true;
    double m_breaking_scale = 0.0;
};

// ── Conservation law ─────────────────────────────────────────────

struct conservation_law {
    std::string m_name;
    std::string m_quantity_expr;
    conservation_source m_source = conservation_source::declared;
    conservation_exactness m_exactness = conservation_exactness::exact;
    double m_tolerance = 1e-10;
    theory_id m_theory = CORE_THEORY_ID;
    std::optional<symmetry_decl> m_symmetry;
};

// ── Static analysis verdict ──────────────────────────────────────

enum class conservation_verdict_kind : uint8_t {
    verified,           // proved: delta = 0
    verified_approx,    // proved with bounded error
    inconclusive,       // cannot determine statically
    violation           // demonstrably broken
};

struct conservation_verdict {
    conservation_verdict_kind m_kind = conservation_verdict_kind::inconclusive;
    std::string m_law_name;
    double m_delta = 0.0;
    std::string m_hint;
    std::vector<std::string> m_contributing_mutations;
};

// ── Structured expression node (AST-level, replaces regex) ──────

enum class expr_node_kind : uint8_t {
    literal,     // numeric constant
    variable,    // named state field
    binop_add,   // a + b
    binop_sub,   // a - b
    binop_mul,   // a * b
    binop_div,   // a / b
    binop_pow,   // a ^ b
    unary_neg,   // -a
    func_call    // f(args...)
};

struct expr_node {
    expr_node_kind m_kind = expr_node_kind::literal;
    double m_literal_val = 0.0;
    std::string m_name;              // variable name or function name
    std::vector<size_t> m_children;  // indices into expr_node pool
};

/// A pool-based expression tree for structured decomposition.
struct expr_pool {
    std::vector<expr_node> m_nodes;

    size_t add(expr_node const & n) {
        m_nodes.push_back(n);
        return m_nodes.size() - 1;
    }

    expr_node const & get(size_t idx) const { return m_nodes[idx]; }

    /// Collect all variable names referenced in subtree rooted at idx.
    void collect_vars(size_t idx, std::vector<std::string> & out) const;

    /// Check if subtree rooted at idx references a given variable.
    bool references_var(size_t idx, std::string const & var) const;
};

// ── Atomic mutation (Pass 1 output) ──────────────────────────────

struct atomic_mutation {
    std::string m_target;
    std::string m_old_val;
    std::string m_new_val;
    unsigned m_line = 0;
    unsigned m_col = 0;
    /// Structured RHS expression (index into expr_pool, or SIZE_MAX if unavailable)
    size_t m_rhs_expr = SIZE_MAX;
};

// ── Dimension tag for Pass 3b ───────────────────────────────────

/// Rational exponent matching Lean's QExp (num/den, den >= 1).
/// Normalized after every operation to prevent denominator overflow.
struct qexp {
    int num = 0;
    unsigned den = 1;

    constexpr qexp() = default;
    constexpr qexp(int n) : num(n), den(1) {}
    constexpr qexp(int n, unsigned d) : num(n), den(d > 0 ? d : 1) { normalize(); }

    bool is_zero() const { return num == 0; }

    bool operator==(qexp const & o) const {
        // Cross-multiply to avoid floating point: a/b == c/d iff a*d == c*b
        return static_cast<int64_t>(num) * o.den
            == static_cast<int64_t>(o.num) * den;
    }
    bool operator!=(qexp const & o) const { return !(*this == o); }

    qexp operator+(qexp const & o) const {
        int64_t n = static_cast<int64_t>(num) * o.den
                  + static_cast<int64_t>(o.num) * den;
        uint64_t d = static_cast<uint64_t>(den) * o.den;
        return make_normalized(n, d);
    }
    qexp operator-(qexp const & o) const {
        int64_t n = static_cast<int64_t>(num) * o.den
                  - static_cast<int64_t>(o.num) * den;
        uint64_t d = static_cast<uint64_t>(den) * o.den;
        return make_normalized(n, d);
    }
    qexp operator*(int n) const {
        return make_normalized(static_cast<int64_t>(num) * n, den);
    }
    qexp operator-() const { return qexp(-num, den); }

    std::string to_string() const;

private:
    /// Reduce num/den by their GCD so denominators stay small.
    constexpr void normalize() {
        if (num == 0) { den = 1; return; }
        unsigned g = gcd_unsigned(abs_val(num), den);
        num /= static_cast<int>(g);
        den /= g;
    }

    static constexpr unsigned abs_val(int x) {
        return x < 0 ? static_cast<unsigned>(-x) : static_cast<unsigned>(x);
    }

    static constexpr unsigned gcd_unsigned(unsigned a, unsigned b) {
        while (b != 0) { unsigned t = b; b = a % b; a = t; }
        return a;
    }

    /// Build a qexp from wide intermediates, normalizing back to int/unsigned.
    static qexp make_normalized(int64_t n, uint64_t d) {
        if (n == 0) return qexp(0, 1);
        uint64_t an = n < 0 ? static_cast<uint64_t>(-n) : static_cast<uint64_t>(n);
        uint64_t g = 1;
        { uint64_t a = an, b = d;
          while (b != 0) { uint64_t t = b; b = a % b; a = t; }
          g = a;
        }
        return qexp(static_cast<int>(n / static_cast<int64_t>(g)),
                     static_cast<unsigned>(d / g));
    }
};

struct dim_tag {
    qexp L, M, T, I, Theta, N, J;

    bool is_zero() const {
        return L.is_zero() && M.is_zero() && T.is_zero() && I.is_zero()
            && Theta.is_zero() && N.is_zero() && J.is_zero();
    }
    bool operator==(dim_tag const & o) const {
        return L == o.L && M == o.M && T == o.T && I == o.I
            && Theta == o.Theta && N == o.N && J == o.J;
    }
    bool operator!=(dim_tag const & o) const { return !(*this == o); }
    std::string to_string() const;
};

// ── CAS delegation interface (Pass 3d) ──────────────────────────

/// Delegate symbolic simplification to an external CAS.
/// Returns true if the CAS proves delta = 0, false if it proves
/// delta != 0, or nullopt if the CAS cannot determine.
std::optional<bool> delegate_to_cas(
    std::string const & symbolic_expr,
    conservation_law const & law);

/// Register a CAS callback from Lean side.
/// Callback signature: (symbolic_expr, law_name) -> 0=inconclusive, 1=true, 2=false
void register_cas_callback(
    std::function<uint8_t(std::string const &, std::string const &)> cb);

// ── Delta result (Pass 2 output) ─────────────────────────────────

enum class delta_kind : uint8_t {
    zero,       // delta = 0 (conservation verified)
    nonzero,    // delta = known nonzero (violation)
    symbolic    // delta is symbolic (needs Pass 3)
};

struct delta_result {
    delta_kind m_kind = delta_kind::symbolic;
    double m_numeric_value = 0.0;
    std::string m_symbolic_expr;
};

// ── Runtime check configuration ──────────────────────────────────

enum class check_frequency_kind : uint8_t {
    every_n,
    logarithmic,
    timed,
    adaptive,
    manual
};

enum class violation_action_kind : uint8_t {
    halt,
    warn,
    correct,
    halt_after_n
};

struct check_frequency {
    check_frequency_kind m_kind = check_frequency_kind::adaptive;
    unsigned m_n = 1;
    unsigned m_interval_ms = 100;
    unsigned m_initial_interval = 1;
    unsigned m_growth_factor = 2;
    unsigned m_max_interval = 10000;
    bool m_reset_on_violation = true;
};

struct violation_action {
    violation_action_kind m_kind = violation_action_kind::halt;
    unsigned m_halt_after_count = 5;
};

// ── Runtime checkpoint ───────────────────────────────────────────

struct conservation_checkpoint {
    std::vector<conservation_law> m_laws;
    std::vector<double> m_tolerances;
    violation_action m_on_violation;
    check_frequency m_frequency;
};

// ── Violation report (runtime) ───────────────────────────────────

struct violation_report {
    std::string m_law_name;
    uint64_t m_iteration = 0;
    double m_delta = 0.0;
    double m_tolerance = 0.0;
    double m_severity_ratio = 0.0;
};

// ── Noether derivation ──────────────────────────────────────────

/// Derive a conservation law from a symmetry declaration.
conservation_law derive_from_noether(symmetry_decl const & sym,
                                     theory_id theory);

// ── Static conservation checker ──────────────────────────────────

class conservation_checker {
    std::vector<conservation_law> m_laws;
    theory_id m_theory = CORE_THEORY_ID;

public:
    explicit conservation_checker(theory_id theory);

    /// Register a conservation law (from @[conservation] or Noether).
    void add_law(conservation_law const & law);

    /// Register laws derived from symmetry declarations.
    void add_symmetry_laws(std::vector<symmetry_decl> const & symmetries);

    /// Get all registered laws.
    std::vector<conservation_law> const & laws() const { return m_laws; }

    // ── Three-pass static analysis ───────────────────────────

    /// Pass 1: Decompose update function into atomic mutations.
    static std::vector<atomic_mutation> decompose(
        std::string const & fn_body);

    /// Pass 2: Compute symbolic delta for a conservation law.
    static delta_result compute_delta(
        conservation_law const & law,
        std::vector<atomic_mutation> const & mutations);

    /// Pass 3: Residual analysis for symbolic deltas.
    static conservation_verdict residual_analysis(
        delta_result const & delta,
        conservation_law const & law);

    /// Main entry: check all laws against an update function.
    std::vector<conservation_verdict> check_all(
        std::string const & fn_body) const;

    // ── Runtime checkpoint generation ────────────────────────

    /// Generate a checkpoint for laws with inconclusive verdicts.
    conservation_checkpoint generate_checkpoint(
        std::vector<conservation_verdict> const & verdicts) const;

    /// Check a runtime violation report against configured action.
    static bool should_halt(violation_report const & report,
                            violation_action const & action,
                            unsigned consecutive_count);

    /// Format a violation report for diagnostic output.
    static std::string format_violation(violation_report const & report);

    /// Format a static verdict for compiler output.
    static std::string format_verdict(conservation_verdict const & v);
};

} // namespace lean
