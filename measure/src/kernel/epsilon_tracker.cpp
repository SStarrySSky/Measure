/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/epsilon_tracker.h"
#include <sstream>
#include <stdexcept>

namespace lean {

const char * eps_rule_to_string(eps_rule r) {
    switch (r) {
    case eps_rule::literal:  return "literal";
    case eps_rule::add:      return "add";
    case eps_rule::mul:      return "mul";
    case eps_rule::max_rule: return "max";
    case eps_rule::trans:    return "trans";
    case eps_rule::subst:    return "subst";
    }
    return "unknown";
}

// --- Internal helpers ---

uint64_t epsilon_tracker::alloc_node(
    eps_rule rule, epsilon_val eps,
    uint64_t left, uint64_t right,
    std::string const & hint)
{
    uint64_t id = m_next_id++;
    eps_proof_node node;
    node.m_id = id;
    node.m_rule = rule;
    node.m_epsilon = eps;
    node.m_left = left;
    node.m_right = right;
    node.m_source_hint = hint;
    node.m_overflow = check_overflow(eps);
    m_nodes.push_back(node);
    return id;
}

bool epsilon_tracker::check_overflow(epsilon_val eps) {
    if (eps.is_inf()) {
        ++m_overflow_count;
        return true;
    }
    if (!m_overflow_threshold.is_inf() &&
        !eps.leq(m_overflow_threshold)) {
        ++m_overflow_count;
        return true;
    }
    return false;
}

// --- Configuration ---

void epsilon_tracker::set_overflow_threshold(epsilon_val threshold) {
    m_overflow_threshold = threshold;
}

// --- Node constructors ---

uint64_t epsilon_tracker::mk_literal(
    epsilon_val eps, std::string const & hint)
{
    return alloc_node(eps_rule::literal, eps, 0, 0, hint);
}

uint64_t epsilon_tracker::mk_add(
    uint64_t left, uint64_t right, std::string const & hint)
{
    auto eps_l = get_epsilon(left);
    auto eps_r = get_epsilon(right);
    auto eps = eps_l.add(eps_r);
    return alloc_node(eps_rule::add, eps, left, right, hint);
}

uint64_t epsilon_tracker::mk_mul(
    uint64_t left, uint64_t right,
    epsilon_val val_a_abs, epsilon_val val_b_abs,
    std::string const & hint)
{
    auto eps_a = get_epsilon(left);
    auto eps_b = get_epsilon(right);
    // |a|*eps_b + |b|*eps_a + eps_a*eps_b
    auto term1 = val_a_abs.mul(eps_b);
    auto term2 = val_b_abs.mul(eps_a);
    auto term3 = eps_a.mul(eps_b);
    auto eps = term1.add(term2).add(term3);
    return alloc_node(eps_rule::mul, eps, left, right, hint);
}

uint64_t epsilon_tracker::mk_max(
    uint64_t left, uint64_t right, std::string const & hint)
{
    auto eps_l = get_epsilon(left);
    auto eps_r = get_epsilon(right);
    auto eps = eps_l.max(eps_r);
    return alloc_node(eps_rule::max_rule, eps, left, right, hint);
}

uint64_t epsilon_tracker::mk_trans(
    uint64_t left, uint64_t right, std::string const & hint)
{
    auto eps_l = get_epsilon(left);
    auto eps_r = get_epsilon(right);
    auto eps = eps_l.add(eps_r);
    return alloc_node(eps_rule::trans, eps, left, right, hint);
}

uint64_t epsilon_tracker::mk_subst(
    uint64_t child, epsilon_val scale, std::string const & hint)
{
    auto eps_c = get_epsilon(child);
    auto eps = eps_c.mul(scale);
    return alloc_node(eps_rule::subst, eps, child, 0, hint);
}

// --- Queries ---

eps_proof_node const * epsilon_tracker::get_node(uint64_t id) const {
    if (id == 0 || id > m_nodes.size()) return nullptr;
    return &m_nodes[id - 1];
}

epsilon_val epsilon_tracker::get_epsilon(uint64_t id) const {
    auto node = get_node(id);
    if (!node) return epsilon_val::zero();
    return node->m_epsilon;
}

bool epsilon_tracker::has_overflow() const {
    return m_overflow_count > 0;
}

uint64_t epsilon_tracker::overflow_count() const {
    return m_overflow_count;
}

size_t epsilon_tracker::size() const {
    return m_nodes.size();
}

void epsilon_tracker::reset() {
    m_nodes.clear();
    m_next_id = 1;
    m_overflow_count = 0;
}

// --- Rendering ---

std::string epsilon_tracker::render_tree(
    uint64_t id, unsigned indent) const
{
    auto node = get_node(id);
    if (!node) return "(null)";

    std::ostringstream os;
    std::string pad(indent * 2, ' ');
    os << pad << eps_rule_to_string(node->m_rule)
       << " eps=" << node->m_epsilon.to_string();
    if (node->m_overflow) os << " [OVERFLOW]";
    if (!node->m_source_hint.empty())
        os << " (" << node->m_source_hint << ")";
    os << "\n";

    if (node->m_left != 0)
        os << render_tree(node->m_left, indent + 1);
    if (node->m_right != 0)
        os << render_tree(node->m_right, indent + 1);
    return os.str();
}

std::string epsilon_tracker::render_overflow_report() const {
    if (m_overflow_count == 0)
        return "No epsilon overflow detected.\n";

    std::ostringstream os;
    os << "Epsilon overflow report: "
       << m_overflow_count << " node(s) overflowed.\n";
    for (auto const & node : m_nodes) {
        if (!node.m_overflow) continue;
        os << "  node #" << node.m_id
           << " rule=" << eps_rule_to_string(node.m_rule)
           << " eps=" << node.m_epsilon.to_string();
        if (!node.m_source_hint.empty())
            os << " (" << node.m_source_hint << ")";
        os << "\n";
    }
    return os.str();
}

} // namespace lean
