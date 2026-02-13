/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include "kernel/theory_module.h"
#include "kernel/approx_eq.h"
#include "kernel/rigor_propagation.h"
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <functional>
#include <optional>

namespace lean {

// ── Conflict classification ──────────────────────────────────────

enum class conflict_kind : uint8_t {
    direct,           // A asserts P, B asserts not-P
    structural,       // incompatible types for same entity
    ontological,      // disagreement on existence
    quantitative      // different predicted values
};

enum class conflict_severity : uint8_t {
    fundamental,      // axioms directly contradict
    derived,          // contradiction only in derived theorems
    regime_dependent  // conflict only in certain parameter regimes
};

/// Evidence that two theories conflict.
struct conflict_witness {
    std::string m_proposition;
    std::string m_proof_left;
    std::string m_proof_right;
    conflict_kind m_kind = conflict_kind::direct;
    conflict_severity m_severity = conflict_severity::fundamental;
    theory_id m_left = INVALID_THEORY_ID;
    theory_id m_right = INVALID_THEORY_ID;
};

// ── Approximation bridge ─────────────────────────────────────────

enum class limit_direction : uint8_t {
    to_zero,
    to_infinity,
    to_value
};

struct limit_process {
    std::string m_parameter;
    limit_direction m_direction = limit_direction::to_zero;
    unsigned m_order = 1;
    double m_target_value = 0.0;
};

enum class approx_coverage : uint8_t {
    full,
    partial,
    conditional
};

/// Formal content of an approximation relation A ⊂≈ B.
struct approx_bridge {
    theory_id m_source = INVALID_THEORY_ID;
    theory_id m_target = INVALID_THEORY_ID;
    limit_process m_limit;
    epsilon_val m_error_bound;
    approx_coverage m_coverage = approx_coverage::full;
    rigor_level m_rigor_cap = rigor_level::approximate;
};

// ── Compatibility result ─────────────────────────────────────────

enum class compat_status : uint8_t {
    compatible,
    bridgeable,
    incompatible
};

struct compat_result {
    compat_status m_status = compat_status::compatible;
    std::optional<approx_bridge> m_bridge;
    std::optional<conflict_witness> m_witness;
};

// ── Structural rule validation result ────────────────────────────

struct rule_violation {
    unsigned m_rule_number = 0;
    std::string m_description;
    theory_id m_involved_a = INVALID_THEORY_ID;
    theory_id m_involved_b = INVALID_THEORY_ID;
};

// ── Pair hash for unordered_set<pair<theory_id,theory_id>> ───────

struct theory_pair_hash {
    size_t operator()(std::pair<theory_id, theory_id> const & p) const {
        auto h1 = std::hash<theory_id>{}(p.first);
        auto h2 = std::hash<theory_id>{}(p.second);
        return h1 ^ (h2 << 16) ^ (h2 >> 16);
    }
};

using theory_pair_set = std::unordered_set<
    std::pair<theory_id, theory_id>, theory_pair_hash>;

// ── SMT delegation callback ──────────────────────────────────────

/// Register an SMT callback from Lean side.
/// Callback signature: (axioms_a, axioms_b, id_a, id_b) -> 0=compatible, 1=conflict, 2=inconclusive
void register_smt_callback(
    std::function<uint8_t(std::string const &, std::string const &,
                           theory_id, theory_id)> cb);

// ── Theory Graph ─────────────────────────────────────────────────

class theory_graph {
    /// All registered theory modules (owned by theory_registry)
    theory_registry & m_registry;

    /// Conflict pairs (normalized: first < second)
    theory_pair_set m_conflicts;

    /// Conflict witnesses indexed by normalized pair
    std::unordered_map<uint64_t, conflict_witness> m_witnesses;

    /// Approximation bridges: source -> list of bridges
    std::unordered_map<theory_id, std::vector<approx_bridge>> m_bridges;

    /// Transitive approx closure cache: directed_key(source, target) -> composed bridge
    std::unordered_map<uint64_t, approx_bridge> m_approx_closure;

    // Internal helpers
    static uint64_t pair_key(theory_id a, theory_id b);
    static uint64_t directed_key(theory_id source, theory_id target);
    static std::pair<theory_id, theory_id> normalize_pair(theory_id a, theory_id b);
    void update_approx_closure(theory_id source, theory_id target,
                               approx_bridge const & bridge);

public:
    explicit theory_graph(theory_registry & reg);

    // ── Relation registration ────────────────────────────────

    /// Register a conflict between two theories.
    /// Returns nullopt on success, or a rule_violation if structural
    /// rules are violated (e.g., self-conflict = Rule 7).
    std::optional<rule_violation> add_conflict(
        theory_id a, theory_id b, conflict_witness const & witness);

    /// Register an approximation bridge.
    /// Automatically updates transitive closure (Rule 1).
    std::optional<rule_violation> add_approx_bridge(
        approx_bridge const & bridge);

    /// Register an extension relation (child extends parent).
    /// Propagates conflicts from parent to child (Rule 5).
    std::optional<rule_violation> add_extension(
        theory_id child, theory_id parent);

    // ── Queries ──────────────────────────────────────────────

    /// Check if two theories are in conflict.
    bool are_conflicting(theory_id a, theory_id b) const;

    /// Get the conflict witness for a pair, if any.
    conflict_witness const * get_conflict_witness(
        theory_id a, theory_id b) const;

    /// Find an approximation bridge from source to target.
    approx_bridge const * find_bridge(
        theory_id source, theory_id target) const;

    /// Get all bridges originating from a theory.
    std::vector<approx_bridge> const & get_bridges(theory_id source) const;

    /// Full compatibility check (four-stage algorithm).
    compat_result check_compatibility(theory_id a, theory_id b) const;

    // ── Structural rule validation ───────────────────────────

    /// Validate all 7 structural rules for the current graph state.
    /// Returns list of violations (empty = valid).
    std::vector<rule_violation> validate_rules() const;

    // ── Traversal ────────────────────────────────────────────

    /// Find the most fundamental theory reachable via approx edges.
    theory_id most_fundamental(theory_id t) const;

    /// Get all theories that approximate a given theory.
    std::vector<std::pair<theory_id, approx_bridge>>
    approximations_of(theory_id t) const;

    // ── Statistics ───────────────────────────────────────────

    size_t conflict_count() const { return m_conflicts.size(); }
    size_t bridge_count() const;
};

} // namespace lean
