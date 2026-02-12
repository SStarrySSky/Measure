/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include "kernel/approx_eq.h"
#include <vector>
#include <string>
#include <cstdint>
#include <memory>

namespace lean {

/// The 6 epsilon accumulation rule types.
/// Each rule describes how epsilon was derived at a proof tree node.
enum class eps_rule : uint8_t {
    literal,   // base case: epsilon from a numeric literal comparison
    add,       // eps(a+b) = eps(a) + eps(b)
    mul,       // eps(a*b) = |a|*eps(b) + |b|*eps(a) + eps(a)*eps(b)
    max_rule,  // eps(f(a,b)) = max(eps(a), eps(b))
    trans,     // transitivity: eps(a~c) <= eps(a~b) + eps(b~c)
    subst      // substitution: eps(f[a/x]) from eps(a~b)
};

const char * eps_rule_to_string(eps_rule r);

/// A node in the epsilon proof tree.
/// Tracks how an epsilon bound was derived, enabling
/// diagnostic output and overflow tracing.
struct eps_proof_node {
    uint64_t    m_id = 0;
    eps_rule    m_rule = eps_rule::literal;
    epsilon_val m_epsilon;
    /// Child node IDs (0, 1, or 2 depending on rule)
    uint64_t    m_left = 0;
    uint64_t    m_right = 0;
    /// Source location hint for diagnostics
    std::string m_source_hint;
    /// Whether overflow was detected at this node
    bool        m_overflow = false;
};

/// Manages epsilon proof trees for approximate equality judgments.
/// Thread-local: one tracker per type-checking invocation.
class epsilon_tracker {
    std::vector<eps_proof_node> m_nodes;
    uint64_t m_next_id = 1;

    /// Overflow threshold: if epsilon exceeds this, flag overflow
    epsilon_val m_overflow_threshold = epsilon_val::inf();

    /// Total overflow count for diagnostics
    uint64_t m_overflow_count = 0;

public:
    epsilon_tracker() = default;

    /// Set the overflow detection threshold.
    void set_overflow_threshold(epsilon_val threshold);

    /// Create a leaf node (literal comparison).
    uint64_t mk_literal(epsilon_val eps,
                         std::string const & hint = "");

    /// Create an addition node: eps = left.eps + right.eps
    uint64_t mk_add(uint64_t left, uint64_t right,
                     std::string const & hint = "");

    /// Create a multiplication node:
    /// eps = |val_a|*eps_b + |val_b|*eps_a + eps_a*eps_b
    uint64_t mk_mul(uint64_t left, uint64_t right,
                     epsilon_val val_a_abs, epsilon_val val_b_abs,
                     std::string const & hint = "");

    /// Create a max node: eps = max(left.eps, right.eps)
    uint64_t mk_max(uint64_t left, uint64_t right,
                     std::string const & hint = "");

    /// Create a transitivity node: eps = left.eps + right.eps
    uint64_t mk_trans(uint64_t left, uint64_t right,
                      std::string const & hint = "");

    /// Create a substitution node: eps propagated through subst
    uint64_t mk_subst(uint64_t child, epsilon_val scale,
                      std::string const & hint = "");

    /// Query a node by ID. Returns nullptr if not found.
    eps_proof_node const * get_node(uint64_t id) const;

    /// Get the epsilon value at a node.
    epsilon_val get_epsilon(uint64_t id) const;

    /// Check if any node in the tree has overflowed.
    bool has_overflow() const;
    uint64_t overflow_count() const;

    /// Render the proof tree rooted at `id` as a human-readable string.
    std::string render_tree(uint64_t id, unsigned indent = 0) const;

    /// Render a diagnostic summary of overflow nodes.
    std::string render_overflow_report() const;

    /// Reset the tracker (clear all nodes).
    void reset();

    /// Total number of nodes allocated.
    size_t size() const;

private:
    uint64_t alloc_node(eps_rule rule, epsilon_val eps,
                        uint64_t left, uint64_t right,
                        std::string const & hint);
    bool check_overflow(epsilon_val eps);
};

} // namespace lean
