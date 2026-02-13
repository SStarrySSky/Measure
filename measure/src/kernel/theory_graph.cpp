/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/theory_graph.h"
#include <queue>
#include <algorithm>
#include <stdexcept>
#include <cstring>

namespace lean {

// ── Internal helpers ─────────────────────────────────────────────

uint64_t theory_graph::pair_key(theory_id a, theory_id b) {
    auto [lo, hi] = normalize_pair(a, b);
    return (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);
}

uint64_t theory_graph::directed_key(theory_id source, theory_id target) {
    return (static_cast<uint64_t>(source) << 32) | static_cast<uint64_t>(target);
}

std::pair<theory_id, theory_id>
theory_graph::normalize_pair(theory_id a, theory_id b) {
    return a < b ? std::make_pair(a, b) : std::make_pair(b, a);
}

static const std::vector<approx_bridge> s_empty_bridges;

theory_graph::theory_graph(theory_registry & reg)
    : m_registry(reg) {}

// ── Conflict registration (Rule 2 symmetric, Rule 7 no self) ────

std::optional<rule_violation> theory_graph::add_conflict(
    theory_id a, theory_id b, conflict_witness const & witness)
{
    if (a == b) {
        return rule_violation{7, "A theory cannot conflict with itself", a, b};
    }
    if (!m_registry.find(a) || !m_registry.find(b)) {
        return rule_violation{0, "Unknown theory_id in add_conflict", a, b};
    }

    auto norm = normalize_pair(a, b);
    auto key = pair_key(a, b);
    m_conflicts.insert(norm);
    m_witnesses[key] = witness;
    m_registry.set_relation(a, b, theory_relation::conflicting);
    return std::nullopt;
}

// ── Approximation bridge (Rule 1 transitive, Rule 6 coexist) ────

void theory_graph::update_approx_closure(
    theory_id source, theory_id target, approx_bridge const & bridge)
{
    auto key = directed_key(source, target);
    auto it = m_approx_closure.find(key);
    if (it == m_approx_closure.end()) {
        m_approx_closure[key] = bridge;
    }
}

std::optional<rule_violation> theory_graph::add_approx_bridge(
    approx_bridge const & bridge)
{
    if (!m_registry.find(bridge.m_source) ||
        !m_registry.find(bridge.m_target)) {
        return rule_violation{0, "Unknown theory_id in add_approx_bridge",
                              bridge.m_source, bridge.m_target};
    }

    m_bridges[bridge.m_source].push_back(bridge);
    update_approx_closure(bridge.m_source, bridge.m_target, bridge);

    // Rule 1: transitive closure — compose with existing bridges
    // If X ⊂≈ source already exists, then X ⊂≈ target via composition
    for (auto const & [src, bridges_vec] : m_bridges) {
        for (auto const & existing : bridges_vec) {
            if (existing.m_target == bridge.m_source) {
                approx_bridge composed;
                composed.m_source = existing.m_source;
                composed.m_target = bridge.m_target;
                composed.m_limit = bridge.m_limit;
                composed.m_error_bound =
                    existing.m_error_bound.add(bridge.m_error_bound);
                composed.m_coverage = approx_coverage::partial;
                composed.m_rigor_cap = static_cast<rigor_level>(
                    std::max(static_cast<uint8_t>(existing.m_rigor_cap),
                             static_cast<uint8_t>(bridge.m_rigor_cap)));
                update_approx_closure(
                    composed.m_source, composed.m_target, composed);
            }
        }
    }
    // Also: if target ⊂≈ Y exists, then source ⊂≈ Y
    auto it = m_bridges.find(bridge.m_target);
    if (it != m_bridges.end()) {
        for (auto const & downstream : it->second) {
            approx_bridge composed;
            composed.m_source = bridge.m_source;
            composed.m_target = downstream.m_target;
            composed.m_limit = downstream.m_limit;
            composed.m_error_bound =
                bridge.m_error_bound.add(downstream.m_error_bound);
            composed.m_coverage = approx_coverage::partial;
            composed.m_rigor_cap = static_cast<rigor_level>(
                std::max(static_cast<uint8_t>(bridge.m_rigor_cap),
                         static_cast<uint8_t>(downstream.m_rigor_cap)));
            update_approx_closure(
                composed.m_source, composed.m_target, composed);
        }
    }

    return std::nullopt;
}

// ── Extension (Rule 4 transitive, Rule 5 conflict propagation) ──

std::optional<rule_violation> theory_graph::add_extension(
    theory_id child, theory_id parent)
{
    if (!m_registry.find(child) || !m_registry.find(parent)) {
        return rule_violation{0, "Unknown theory_id in add_extension",
                              child, parent};
    }

    // Check Rule 7 variant: extension + conflict = illegal
    if (are_conflicting(child, parent)) {
        return rule_violation{7,
            "Cannot extend a conflicting theory (extension + conflict is illegal)",
            child, parent};
    }

    m_registry.set_relation(child, parent, theory_relation::extends);

    // Rule 5: propagate conflicts from parent to child
    // If parent ⊥ X, then child ⊥ X
    for (auto const & norm_pair : m_conflicts) {
        theory_id conflict_other = INVALID_THEORY_ID;
        if (norm_pair.first == parent) {
            conflict_other = norm_pair.second;
        } else if (norm_pair.second == parent) {
            conflict_other = norm_pair.first;
        }
        if (conflict_other != INVALID_THEORY_ID &&
            conflict_other != child) {
            auto parent_key = pair_key(parent, conflict_other);
            auto wit_it = m_witnesses.find(parent_key);
            if (wit_it != m_witnesses.end()) {
                conflict_witness propagated = wit_it->second;
                propagated.m_left = child;
                propagated.m_right = conflict_other;
                propagated.m_severity = conflict_severity::derived;
                add_conflict(child, conflict_other, propagated);
            }
        }
    }

    return std::nullopt;
}

// ── Queries ──────────────────────────────────────────────────────

bool theory_graph::are_conflicting(theory_id a, theory_id b) const {
    return m_conflicts.count(normalize_pair(a, b)) > 0;
}

conflict_witness const * theory_graph::get_conflict_witness(
    theory_id a, theory_id b) const
{
    auto it = m_witnesses.find(pair_key(a, b));
    return it != m_witnesses.end() ? &it->second : nullptr;
}

approx_bridge const * theory_graph::find_bridge(
    theory_id source, theory_id target) const
{
    // Check direct bridges first
    auto it = m_bridges.find(source);
    if (it != m_bridges.end()) {
        for (auto const & b : it->second) {
            if (b.m_target == target) return &b;
        }
    }
    // Check transitive closure (directional: source -> target)
    auto cit = m_approx_closure.find(directed_key(source, target));
    return cit != m_approx_closure.end() ? &cit->second : nullptr;
}

std::vector<approx_bridge> const &
theory_graph::get_bridges(theory_id source) const {
    auto it = m_bridges.find(source);
    return it != m_bridges.end() ? it->second : s_empty_bridges;
}

// ── Stage 2 helpers: structured axiom conflict patterns ─────────

/// Normalize an axiom string: trim whitespace, lowercase.
static std::string normalize_axiom(std::string const & ax) {
    std::string s = ax;
    // trim leading/trailing whitespace
    size_t start = s.find_first_not_of(" \t\n\r");
    size_t end = s.find_last_not_of(" \t\n\r");
    if (start == std::string::npos) return "";
    s = s.substr(start, end - start + 1);
    // collapse internal whitespace
    std::string out;
    bool prev_space = false;
    for (char c : s) {
        if (c == ' ' || c == '\t') {
            if (!prev_space) { out += ' '; prev_space = true; }
        } else {
            out += c;
            prev_space = false;
        }
    }
    return out;
}

/// Check forall/exists conflict pattern:
///   "forall x, P(x)" vs "exists x, not P(x)"
static bool check_forall_exists_conflict(
    std::string const & a, std::string const & b)
{
    auto na = normalize_axiom(a);
    auto nb = normalize_axiom(b);

    // Pattern: "forall <var>, <body>" vs "exists <var>, not <body>"
    auto extract_forall = [](std::string const & s)
        -> std::pair<std::string, std::string> {
        // "forall ", "All ", or Unicode "∀ " (UTF-8: \xE2\x88\x80)
        if (s.substr(0, 7) == "forall " || s.substr(0, 4) == "All " ||
            s.compare(0, 4, "\xE2\x88\x80 ") == 0) {
            auto comma = s.find(',');
            if (comma != std::string::npos && comma + 2 < s.size()) {
                return {s.substr(0, comma), s.substr(comma + 2)};
            }
        }
        return {"", ""};
    };

    auto extract_exists_not = [](std::string const & s)
        -> std::pair<std::string, std::string> {
        // "exists ", "Ex ", or Unicode "∃ " (UTF-8: \xE2\x88\x83)
        if (s.substr(0, 7) == "exists " || s.substr(0, 3) == "Ex " ||
            s.compare(0, 4, "\xE2\x88\x83 ") == 0) {
            auto comma = s.find(',');
            if (comma != std::string::npos && comma + 2 < s.size()) {
                std::string body = s.substr(comma + 2);
                // "not ", "! ", or Unicode "¬" (UTF-8: \xC2\xAC)
                if (body.substr(0, 4) == "not " || body.substr(0, 2) == "! " ||
                    body.compare(0, 2, "\xC2\xAC") == 0) {
                    size_t skip = (body[0] == 'n') ? 4 :
                                  (body[0] == '!') ? 2 : 2; // ¬ is 2 bytes
                    return {s.substr(0, comma), body.substr(skip)};
                }
            }
        }
        return {"", ""};
    };

    auto [fa_q, fa_body] = extract_forall(na);
    auto [eb_q, eb_body] = extract_exists_not(nb);
    if (!fa_body.empty() && !eb_body.empty() && fa_body == eb_body)
        return true;

    // Try reversed
    auto [fb_q, fb_body] = extract_forall(nb);
    auto [ea_q, ea_body] = extract_exists_not(na);
    if (!fb_body.empty() && !ea_body.empty() && fb_body == ea_body)
        return true;

    return false;
}

/// Check equality vs inequality conflict:
///   "a = b" vs "a != b" or "a /= b" or "a ≠ b"
static bool check_eq_neq_conflict(
    std::string const & a, std::string const & b)
{
    auto na = normalize_axiom(a);
    auto nb = normalize_axiom(b);

    auto extract_eq = [](std::string const & s)
        -> std::pair<std::string, std::string> {
        // Look for " = " (not " == " or " != ")
        auto pos = s.find(" = ");
        if (pos != std::string::npos) {
            if (pos > 0 && s[pos - 1] == '!') return {"", ""};
            if (pos + 3 < s.size() && s[pos + 3] == '=') return {"", ""};
            return {s.substr(0, pos), s.substr(pos + 3)};
        }
        return {"", ""};
    };

    auto extract_neq = [](std::string const & s)
        -> std::pair<std::string, std::string> {
        // Check ASCII separators
        for (auto sep : {" != ", " /= "}) {
            auto pos = s.find(sep);
            if (pos != std::string::npos) {
                size_t len = std::strlen(sep);
                return {s.substr(0, pos), s.substr(pos + len)};
            }
        }
        // Check Unicode ≠ (UTF-8: \xE2\x89\xA0)
        {
            std::string usep = " \xE2\x89\xA0 ";
            auto pos = s.find(usep);
            if (pos != std::string::npos) {
                return {s.substr(0, pos), s.substr(pos + usep.size())};
            }
        }
        return {"", ""};
    };

    auto [eq_l, eq_r] = extract_eq(na);
    auto [neq_l, neq_r] = extract_neq(nb);
    if (!eq_l.empty() && !neq_l.empty()
        && eq_l == neq_l && eq_r == neq_r)
        return true;

    // Try reversed
    auto [eq_l2, eq_r2] = extract_eq(nb);
    auto [neq_l2, neq_r2] = extract_neq(na);
    if (!eq_l2.empty() && !neq_l2.empty()
        && eq_l2 == neq_l2 && eq_r2 == neq_r2)
        return true;

    return false;
}

// ── Stage 3: Semantic normalization helpers ─────────────────────

/// Strip universe annotations like `.{u}`, `.{u, v}` from a string.
/// Matches the Lean `stripUniverses` function.
static std::string strip_universes(std::string const & s) {
    std::string out;
    out.reserve(s.size());
    int depth = 0;
    for (size_t i = 0; i < s.size(); ++i) {
        if (i + 1 < s.size() && s[i] == '.' && s[i + 1] == '{') {
            depth++;
            i++; // skip the '{' as well
            continue;
        }
        if (s[i] == '{' && depth > 0) {
            depth++;
            continue;
        }
        if (s[i] == '}' && depth > 0) {
            depth--;
            continue;
        }
        if (depth > 0) continue;
        out += s[i];
    }
    return out;
}

/// Expand common type aliases to canonical names.
/// Matches the Lean `expandAlias` function.
static std::string expand_alias(std::string const & word) {
    // UTF-8 encoded Unicode symbols
    if (word == "\xe2\x84\x9d") return "Real";       // ℝ
    if (word == "\xe2\x84\x82") return "Complex";     // ℂ
    if (word == "\xe2\x84\x95") return "Nat";         // ℕ
    if (word == "\xe2\x84\xa4") return "Int";         // ℤ
    if (word == "\xe2\x84\x9a") return "Rat";         // ℚ
    if (word == "\xe2\x84\x8f") return "hbar";        // ℏ
    if (word == "\xce\xb1")     return "fine_structure_constant"; // α
    return word;
}

/// Full semantic normalization pipeline for an axiom type string:
///   1. Trim/collapse whitespace
///   2. Strip universe annotations
///   3. Expand type aliases word by word
///   4. Re-normalize whitespace
/// Returns a canonical string for comparison.
/// Matches the Lean `semanticNormalize` function.
static std::string semantic_normalize(std::string const & s) {
    std::string r = normalize_axiom(s);
    r = strip_universes(r);
    // Expand aliases word by word
    std::string result;
    std::string word;
    for (size_t i = 0; i <= r.size(); ++i) {
        if (i < r.size() && r[i] != ' ') {
            word += r[i];
        } else {
            if (!word.empty()) {
                if (!result.empty()) result += ' ';
                result += expand_alias(word);
                word.clear();
            }
        }
    }
    return normalize_axiom(result);
}

/// Check if two axiom type strings are semantically contradictory
/// after full normalization. Re-runs the Stage 2 syntactic patterns
/// (negation, forall/exists, eq/neq) on normalized forms.
/// Matches the Lean `areSemanticConflict` function.
static bool are_semantic_conflict(std::string const & type_a,
                                  std::string const & type_b) {
    std::string na = semantic_normalize(type_a);
    std::string nb = semantic_normalize(type_b);
    // Direct negation after normalization
    // "not P", "not_P", or Unicode "¬P" (UTF-8: \xC2\xAC)
    bool negation =
        (na == "not " + nb) || (nb == "not " + na) ||
        (na == "not_" + nb) || (nb == "not_" + na) ||
        (na == "\xC2\xAC" + nb) || (nb == "\xC2\xAC" + na);
    if (negation) return true;
    // Eq vs Neq after normalization
    if (check_eq_neq_conflict(na, nb)) return true;
    // Forall/Exists after normalization
    if (check_forall_exists_conflict(na, nb)) return true;
    return false;
}

/// Check if two axiom type strings define the same constant with
/// different values after normalization.
/// Detects "X = v1" vs "X = v2" where v1 != v2.
/// Matches the Lean `areQuantitativeConflict` function.
static std::optional<conflict_witness> are_quantitative_conflict(
    std::string const & type_a, std::string const & type_b,
    theory_id id_a, theory_id id_b)
{
    std::string na = semantic_normalize(type_a);
    std::string nb = semantic_normalize(type_b);

    // Extract "lhs = rhs" (but not "!=" or "==")
    auto safe_extract_eq = [](std::string const & s)
        -> std::pair<std::string, std::string> {
        auto pos = s.find(" = ");
        if (pos == std::string::npos) return {"", ""};
        if (pos > 0 && s[pos - 1] == '!') return {"", ""};
        if (pos > 0 && s[pos - 1] == '/') return {"", ""};
        if (pos + 3 < s.size() && s[pos + 3] == '=') return {"", ""};
        return {s.substr(0, pos), s.substr(pos + 3)};
    };

    auto [lhs_a, rhs_a] = safe_extract_eq(na);
    auto [lhs_b, rhs_b] = safe_extract_eq(nb);

    if (!lhs_a.empty() && !lhs_b.empty() &&
        lhs_a == lhs_b && rhs_a != rhs_b) {
        conflict_witness wit;
        wit.m_proposition = lhs_a + " has conflicting values";
        wit.m_proof_left = type_a;
        wit.m_proof_right = type_b;
        wit.m_kind = conflict_kind::quantitative;
        wit.m_severity = conflict_severity::fundamental;
        wit.m_left = id_a;
        wit.m_right = id_b;
        return wit;
    }
    return std::nullopt;
}

/// Check for structural conflict: same entity with incompatible types
/// after normalization. Detects "X : T1" vs "X : T2" patterns.
/// Matches the Lean `areStructuralConflict` function.
static std::optional<conflict_witness> are_structural_conflict(
    std::string const & type_a, std::string const & type_b,
    theory_id id_a, theory_id id_b)
{
    std::string na = semantic_normalize(type_a);
    std::string nb = semantic_normalize(type_b);

    auto colon_a = na.find(" : ");
    auto colon_b = nb.find(" : ");
    if (colon_a != std::string::npos && colon_b != std::string::npos) {
        std::string name_a = na.substr(0, colon_a);
        std::string name_b = nb.substr(0, colon_b);
        std::string ty_a = na.substr(colon_a + 3);
        std::string ty_b = nb.substr(colon_b + 3);
        if (name_a == name_b && ty_a != ty_b) {
            conflict_witness wit;
            wit.m_proposition = name_a + " has incompatible types";
            wit.m_proof_left = type_a;
            wit.m_proof_right = type_b;
            wit.m_kind = conflict_kind::structural;
            wit.m_severity = conflict_severity::fundamental;
            wit.m_left = id_a;
            wit.m_right = id_b;
            return wit;
        }
    }
    return std::nullopt;
}

/// Stage 3: Semantic conflict check.
/// Normalizes axiom strings (strip universes, expand aliases, collapse
/// whitespace) then re-runs contradiction checks on canonical forms.
/// Catches conflicts that Stage 2 misses due to surface-level differences.
/// Matches the Lean `semanticScreen` function.
static std::optional<conflict_witness> semantic_conflict_check(
    theory_module const & mod_a, theory_module const & mod_b,
    theory_id id_a, theory_id id_b)
{
    // Check all axiom pairs for semantic contradictions, quantitative
    // conflicts, and structural conflicts (on axiom strings).
    for (size_t i = 0; i < mod_a.m_axioms.size(); ++i) {
        for (size_t j = 0; j < mod_b.m_axioms.size(); ++j) {
            auto const & ax_a = mod_a.m_axioms[i];
            auto const & ax_b = mod_b.m_axioms[j];

            // Semantic contradiction (negation, eq/neq, forall/exists
            // after normalization)
            if (are_semantic_conflict(ax_a, ax_b)) {
                conflict_witness wit;
                wit.m_proposition = ax_a;
                wit.m_proof_left = ax_a;
                wit.m_proof_right = ax_b;
                wit.m_kind = conflict_kind::direct;
                wit.m_severity = conflict_severity::fundamental;
                wit.m_left = id_a;
                wit.m_right = id_b;
                return wit;
            }

            // Quantitative conflict (same LHS, different RHS in equalities)
            auto quant = are_quantitative_conflict(ax_a, ax_b, id_a, id_b);
            if (quant.has_value()) return quant;

            // Structural conflict on axiom type annotations
            auto struc = are_structural_conflict(ax_a, ax_b, id_a, id_b);
            if (struc.has_value()) return struc;
        }
    }

    // Also check definitions for structural conflicts
    for (auto const & def_a : mod_a.m_definitions) {
        for (auto const & def_b : mod_b.m_definitions) {
            auto struc = are_structural_conflict(def_a, def_b, id_a, id_b);
            if (struc.has_value()) return struc;
        }
    }

    return std::nullopt;
}

// ── Stage 4: SMT delegation via Lean FFI callback ───────────────

/// Global callback registered from Lean side.
/// Signature: (axioms_a_joined, axioms_b_joined, id_a, id_b) -> 0=compatible, 1=conflict, 2=inconclusive
static std::function<uint8_t(std::string const &, std::string const &,
                              theory_id, theory_id)>
    g_smt_callback = nullptr;

void register_smt_callback(
    std::function<uint8_t(std::string const &, std::string const &,
                           theory_id, theory_id)> cb)
{
    g_smt_callback = std::move(cb);
}

/// Delegate axiom compatibility checking to an external SMT solver
/// via Lean's External engine infrastructure.
/// Returns a conflict_witness if the solver finds UNSAT (contradiction),
/// or nullopt if SAT (compatible) or if the solver is unavailable.
static std::optional<conflict_witness> delegate_to_smt(
    std::vector<std::string> const & axioms_a,
    std::vector<std::string> const & axioms_b,
    theory_id id_a,
    theory_id id_b)
{
    if (!g_smt_callback) {
        return std::nullopt;
    }
    // Join axioms into newline-separated strings for transport
    std::string joined_a, joined_b;
    for (auto const & ax : axioms_a) {
        if (!joined_a.empty()) joined_a += "\n";
        joined_a += ax;
    }
    for (auto const & ax : axioms_b) {
        if (!joined_b.empty()) joined_b += "\n";
        joined_b += ax;
    }
    uint8_t result = g_smt_callback(joined_a, joined_b, id_a, id_b);
    switch (result) {
    case 1: {
        // Conflict detected
        conflict_witness w;
        w.m_proposition = "SMT solver found axiom sets unsatisfiable";
        w.m_kind = conflict_kind::direct;
        w.m_severity = conflict_severity::fundamental;
        w.m_left = id_a;
        w.m_right = id_b;
        return w;
    }
    default:
        return std::nullopt;  // compatible or inconclusive
    }
}

// ── Four-stage compatibility check ──────────────────────────────

compat_result theory_graph::check_compatibility(
    theory_id a, theory_id b) const
{
    // Stage 1: Cache lookup — O(1)
    if (are_conflicting(a, b)) {
        auto * bridge = find_bridge(a, b);
        if (!bridge) bridge = find_bridge(b, a);
        if (bridge) {
            return {compat_status::bridgeable, *bridge, std::nullopt};
        }
        auto * wit = get_conflict_witness(a, b);
        if (wit) {
            return {compat_status::incompatible, std::nullopt, *wit};
        }
    }

    // Stage 2: Syntactic screening — structured axiom comparison
    auto const * mod_a = m_registry.find(a);
    auto const * mod_b = m_registry.find(b);
    if (!mod_a || !mod_b) {
        return {compat_status::compatible, std::nullopt, std::nullopt};
    }

    for (auto const & ax_a : mod_a->m_axioms) {
        for (auto const & ax_b : mod_b->m_axioms) {
            // Pattern 1: direct negation "P" vs "not P" / "not_P" / "¬P"
            bool negation_match =
                (ax_a == "not " + ax_b) || (ax_b == "not " + ax_a) ||
                (ax_a == "not_" + ax_b) || (ax_b == "not_" + ax_a) ||
                (ax_a == "\xC2\xAC" + ax_b) || (ax_b == "\xC2\xAC" + ax_a);
            // Pattern 2: forall/exists conflict
            //   "forall x, P(x)" vs "exists x, not P(x)"
            if (!negation_match) {
                negation_match = check_forall_exists_conflict(ax_a, ax_b);
            }
            // Pattern 3: equality vs inequality
            //   "a = b" vs "a != b" or "a ≠ b"
            if (!negation_match) {
                negation_match = check_eq_neq_conflict(ax_a, ax_b);
            }

            if (negation_match) {
                conflict_witness wit;
                wit.m_proposition = ax_a;
                wit.m_proof_left = ax_a;
                wit.m_proof_right = ax_b;
                wit.m_kind = conflict_kind::direct;
                wit.m_severity = conflict_severity::fundamental;
                wit.m_left = a;
                wit.m_right = b;

                auto * bridge = find_bridge(a, b);
                if (!bridge) bridge = find_bridge(b, a);
                if (bridge) {
                    return {compat_status::bridgeable, *bridge, wit};
                }
                return {compat_status::incompatible, std::nullopt, wit};
            }
        }
    }

    // Stage 3: Semantic normalization — strip universes, expand aliases,
    // collapse whitespace, then re-check for contradictions + quantitative/structural conflicts.
    {
        auto semantic_wit = semantic_conflict_check(*mod_a, *mod_b, a, b);
        if (semantic_wit.has_value()) {
            auto * bridge = find_bridge(a, b);
            if (!bridge) bridge = find_bridge(b, a);
            if (bridge) {
                return {compat_status::bridgeable, *bridge, semantic_wit.value()};
            }
            return {compat_status::incompatible, std::nullopt, semantic_wit.value()};
        }
    }

    // Stage 4: SMT delegation
    {
        auto smt_wit = delegate_to_smt(
            mod_a->m_axioms, mod_b->m_axioms, a, b);
        if (smt_wit.has_value()) {
            auto * bridge = find_bridge(a, b);
            if (!bridge) bridge = find_bridge(b, a);
            if (bridge) {
                return {compat_status::bridgeable, *bridge, smt_wit.value()};
            }
            return {compat_status::incompatible, std::nullopt, smt_wit.value()};
        }
    }

    return {compat_status::compatible, std::nullopt, std::nullopt};
}

// ── Structural rule validation ──────────────────────────────────

std::vector<rule_violation> theory_graph::validate_rules() const {
    std::vector<rule_violation> violations;

    // Rule 7: no self-conflict
    for (auto const & p : m_conflicts) {
        if (p.first == p.second) {
            violations.push_back({7, "Self-conflict detected",
                                  p.first, p.second});
        }
    }

    // Rule 2: conflict symmetry (enforced by add_conflict, verify)
    for (auto const & p : m_conflicts) {
        auto rev = normalize_pair(p.second, p.first);
        if (m_conflicts.count(rev) == 0) {
            violations.push_back({2, "Conflict not symmetric",
                                  p.first, p.second});
        }
    }

    // Rule 5 + Rule 7 variant: extension + conflict = illegal
    for (auto const & p : m_conflicts) {
        auto rel_ab = m_registry.get_relation(p.first, p.second);
        auto rel_ba = m_registry.get_relation(p.second, p.first);
        if (rel_ab == theory_relation::extends ||
            rel_ba == theory_relation::extends) {
            violations.push_back({7,
                "Extension and conflict coexist (illegal)",
                p.first, p.second});
        }
    }

    return violations;
}

// ── Traversal ───────────────────────────────────────────────────

theory_id theory_graph::most_fundamental(theory_id t) const {
    theory_id current = t;
    std::unordered_set<theory_id> visited;
    visited.insert(current);

    bool found = true;
    while (found) {
        found = false;
        auto it = m_bridges.find(current);
        if (it != m_bridges.end() && !it->second.empty()) {
            theory_id next = it->second.front().m_target;
            if (visited.count(next) == 0) {
                visited.insert(next);
                current = next;
                found = true;
            }
        }
    }
    return current;
}

std::vector<std::pair<theory_id, approx_bridge>>
theory_graph::approximations_of(theory_id t) const {
    std::vector<std::pair<theory_id, approx_bridge>> result;
    for (auto const & [src, bridges_vec] : m_bridges) {
        for (auto const & b : bridges_vec) {
            if (b.m_target == t) {
                result.push_back({src, b});
            }
        }
    }
    return result;
}

size_t theory_graph::bridge_count() const {
    size_t count = 0;
    for (auto const & [_, vec] : m_bridges) {
        count += vec.size();
    }
    return count;
}

} // namespace lean
