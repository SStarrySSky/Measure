/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

ApplicabilityDomain: defines the regime where a theory module is valid.
Each theory has dimensionless-ratio constraints that bound its domain.
See ARCHITECTURE.md Section 6.2 (domain field) and docs/theory-system.md.
*/
#pragma once
#include "kernel/approx_eq.h"
#include "kernel/natural_units.h"
#include <vector>
#include <string>
#include <optional>
#include <cmath>

namespace lean {

// ── Comparison operators for domain constraints ─────────────────

enum class domain_cmp : uint8_t {
    less_than,
    less_eq,
    greater_than,
    greater_eq,
    approx_eq
};

char const * domain_cmp_to_string(domain_cmp c);

// ── A single dimensionless-ratio constraint ─────────────────────

/// Represents a constraint of the form:
///   ratio_expr  <cmp>  bound_value
/// where ratio_expr is a dimensionless combination of physical parameters.
/// Example: v/c < 0.1  (Newtonian mechanics validity)
struct domain_constraint {
    std::string m_ratio_expr;       // e.g. "v/c", "E/E_planck"
    domain_cmp  m_cmp = domain_cmp::less_than;
    double      m_bound = 1.0;      // RHS bound value
    std::string m_description;      // human-readable explanation
    dim7        m_expected_dim;     // must be dimensionless after eval

    /// Check if a given numeric value satisfies this constraint.
    bool check(double value) const;

    std::string to_string() const;
};

// ── Domain check result ─────────────────────────────────────────

enum class domain_status : uint8_t {
    inside,         // all constraints satisfied
    boundary,       // within tolerance of a boundary
    outside,        // at least one constraint violated
    unknown         // cannot evaluate (symbolic parameters)
};

struct domain_check_result {
    domain_status m_status = domain_status::unknown;
    std::vector<std::string> m_violated;    // names of violated constraints
    std::vector<std::string> m_warnings;    // near-boundary warnings
    double m_margin = 0.0;                  // min distance to boundary

    std::string to_string() const;
};

// ── ApplicabilityDomain ─────────────────────────────────────────

/// The applicability domain of a theory module.
/// A conjunction of dimensionless-ratio constraints that define
/// the physical regime where the theory's predictions are valid.
class applicability_domain {
    std::vector<domain_constraint> m_constraints;
    std::string m_name;
    double m_boundary_tolerance = 0.05; // 5% default

public:
    applicability_domain() = default;
    explicit applicability_domain(std::string const & name);

    /// Add a constraint to the domain.
    void add_constraint(domain_constraint const & c);

    /// Get all constraints.
    std::vector<domain_constraint> const & constraints() const {
        return m_constraints;
    }

    /// Check if a set of parameter values lies within the domain.
    /// `param_values` maps ratio_expr strings to their numeric values.
    domain_check_result check(
        std::vector<std::pair<std::string, double>> const & param_values) const;

    /// Check a single parameter value against all constraints
    /// that reference it.
    domain_check_result check_param(
        std::string const & param_name, double value) const;

    /// Set the boundary tolerance (fraction, e.g. 0.05 = 5%).
    void set_boundary_tolerance(double tol) {
        m_boundary_tolerance = tol;
    }

    /// Check if this domain is a subset of another
    /// (conservative: only checks matching constraints).
    bool is_subset_of(applicability_domain const & other) const;

    /// Intersect two domains (conjunction of all constraints).
    static applicability_domain intersect(
        applicability_domain const & a,
        applicability_domain const & b);

    /// Format for diagnostics.
    std::string to_string() const;

    std::string const & name() const { return m_name; }
    size_t size() const { return m_constraints.size(); }
    bool empty() const { return m_constraints.empty(); }
};

} // namespace lean
