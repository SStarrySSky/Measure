/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/applicability_domain.h"
#include <sstream>
#include <algorithm>
#include <cmath>

namespace lean {

// ── domain_cmp helpers ──────────────────────────────────────────

char const * domain_cmp_to_string(domain_cmp c) {
    switch (c) {
    case domain_cmp::less_than:    return "<";
    case domain_cmp::less_eq:      return "<=";
    case domain_cmp::greater_than: return ">";
    case domain_cmp::greater_eq:   return ">=";
    case domain_cmp::approx_eq:    return "~=";
    }
    return "?";
}

// ── domain_constraint ───────────────────────────────────────────

bool domain_constraint::check(double value) const {
    switch (m_cmp) {
    case domain_cmp::less_than:    return value < m_bound;
    case domain_cmp::less_eq:      return value <= m_bound;
    case domain_cmp::greater_than: return value > m_bound;
    case domain_cmp::greater_eq:   return value >= m_bound;
    case domain_cmp::approx_eq:
        return std::fabs(value - m_bound) <= 0.05 * std::fabs(m_bound);
    }
    return false;
}

std::string domain_constraint::to_string() const {
    std::ostringstream os;
    os << m_ratio_expr << " " << domain_cmp_to_string(m_cmp)
       << " " << m_bound;
    if (!m_description.empty()) {
        os << "  (" << m_description << ")";
    }
    return os.str();
}

// ── domain_check_result ─────────────────────────────────────────

std::string domain_check_result::to_string() const {
    std::ostringstream os;
    switch (m_status) {
    case domain_status::inside:   os << "INSIDE"; break;
    case domain_status::boundary: os << "BOUNDARY"; break;
    case domain_status::outside:  os << "OUTSIDE"; break;
    case domain_status::unknown:  os << "UNKNOWN"; break;
    }
    if (!m_violated.empty()) {
        os << " violated: [";
        for (size_t i = 0; i < m_violated.size(); ++i) {
            if (i > 0) os << ", ";
            os << m_violated[i];
        }
        os << "]";
    }
    if (!m_warnings.empty()) {
        os << " warnings: [";
        for (size_t i = 0; i < m_warnings.size(); ++i) {
            if (i > 0) os << ", ";
            os << m_warnings[i];
        }
        os << "]";
    }
    return os.str();
}

// ── applicability_domain ────────────────────────────────────────

applicability_domain::applicability_domain(std::string const & name)
    : m_name(name) {}

void applicability_domain::add_constraint(domain_constraint const & c) {
    m_constraints.push_back(c);
}

domain_check_result applicability_domain::check(
    std::vector<std::pair<std::string, double>> const & param_values) const
{
    domain_check_result result;
    result.m_status = domain_status::inside;
    result.m_margin = std::numeric_limits<double>::max();

    for (auto const & constraint : m_constraints) {
        bool found = false;
        for (auto const & [name, value] : param_values) {
            if (name != constraint.m_ratio_expr) continue;
            found = true;

            if (!constraint.check(value)) {
                result.m_status = domain_status::outside;
                result.m_violated.push_back(constraint.to_string());
            } else {
                double dist = std::fabs(value - constraint.m_bound);
                double rel_dist = (constraint.m_bound != 0.0)
                    ? dist / std::fabs(constraint.m_bound)
                    : dist;
                result.m_margin = std::min(result.m_margin, rel_dist);

                if (rel_dist < m_boundary_tolerance) {
                    if (result.m_status == domain_status::inside)
                        result.m_status = domain_status::boundary;
                    result.m_warnings.push_back(
                        constraint.m_ratio_expr + " near boundary");
                }
            }
            break;
        }
        if (!found && result.m_status == domain_status::inside) {
            result.m_status = domain_status::unknown;
        }
    }

    if (m_constraints.empty()) {
        result.m_status = domain_status::inside;
    }
    return result;
}

domain_check_result applicability_domain::check_param(
    std::string const & param_name, double value) const
{
    return check({{param_name, value}});
}

bool applicability_domain::is_subset_of(
    applicability_domain const & other) const
{
    for (auto const & oc : other.m_constraints) {
        bool covered = false;
        for (auto const & tc : m_constraints) {
            if (tc.m_ratio_expr != oc.m_ratio_expr) continue;
            if (tc.m_cmp != oc.m_cmp) continue;
            if (tc.m_cmp == domain_cmp::less_than ||
                tc.m_cmp == domain_cmp::less_eq) {
                if (tc.m_bound <= oc.m_bound) covered = true;
            }
            if (tc.m_cmp == domain_cmp::greater_than ||
                tc.m_cmp == domain_cmp::greater_eq) {
                if (tc.m_bound >= oc.m_bound) covered = true;
            }
        }
        if (!covered) return false;
    }
    return true;
}

applicability_domain applicability_domain::intersect(
    applicability_domain const & a,
    applicability_domain const & b)
{
    applicability_domain result(a.m_name + " ^ " + b.m_name);
    for (auto const & c : a.m_constraints)
        result.add_constraint(c);
    for (auto const & c : b.m_constraints)
        result.add_constraint(c);
    return result;
}

std::string applicability_domain::to_string() const {
    std::ostringstream os;
    os << "ApplicabilityDomain(" << m_name << ") {\n";
    for (auto const & c : m_constraints)
        os << "  " << c.to_string() << "\n";
    os << "}";
    return os.str();
}

} // namespace lean
