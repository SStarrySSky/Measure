/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/theory_module.h"
#include <queue>
#include <stdexcept>

namespace lean {

// --- Constructor: auto-register Core (id=0) ---

theory_registry::theory_registry() {
    theory_module core;
    core.m_id = CORE_THEORY_ID;
    core.m_name = "Core";
    core.m_rigor = rigor_level::strict;
    core.m_max_epsilon = epsilon_val::zero();
    m_modules[CORE_THEORY_ID] = core;
    m_name_to_id["Core"] = CORE_THEORY_ID;
}

// --- Registration ---

theory_id theory_registry::register_theory(
    std::string const & name,
    std::vector<theory_id> const & parents,
    rigor_level rigor,
    epsilon_val max_eps)
{
    if (m_name_to_id.count(name)) {
        throw std::runtime_error(
            "Theory already registered: " + name);
    }
    theory_id id = m_next_id++;
    theory_module mod;
    mod.m_id = id;
    mod.m_name = name;
    mod.m_parents = parents;
    mod.m_rigor = rigor;
    mod.m_max_epsilon = max_eps;

    // Auto-set extends relation for parents
    for (auto pid : parents) {
        mod.m_relations[pid] = theory_relation::extends;
    }

    m_modules[id] = mod;
    m_name_to_id[name] = id;
    return id;
}

// --- Query ---

theory_module const & theory_registry::get(theory_id id) const {
    auto it = m_modules.find(id);
    if (it == m_modules.end()) {
        throw std::runtime_error(
            "Unknown theory_id: " + std::to_string(id));
    }
    return it->second;
}

theory_module const * theory_registry::find(theory_id id) const {
    auto it = m_modules.find(id);
    return it != m_modules.end() ? &it->second : nullptr;
}

theory_id theory_registry::find_by_name(
    std::string const & n) const
{
    auto it = m_name_to_id.find(n);
    return it != m_name_to_id.end()
        ? it->second : INVALID_THEORY_ID;
}

// --- Relations ---

void theory_registry::set_relation(theory_id a, theory_id b,
                                    theory_relation rel)
{
    auto it_a = m_modules.find(a);
    auto it_b = m_modules.find(b);
    if (it_a == m_modules.end() || it_b == m_modules.end()) {
        throw std::runtime_error("Unknown theory_id in set_relation");
    }
    it_a->second.m_relations[b] = rel;
    // extends is directional (child -> parent), not symmetric
    // compatible and conflicting are symmetric
    if (rel != theory_relation::extends) {
        it_b->second.m_relations[a] = rel;
    }
}

theory_relation theory_registry::get_relation(
    theory_id a, theory_id b) const
{
    auto it = m_modules.find(a);
    if (it == m_modules.end()) return theory_relation::independent;
    auto rit = it->second.m_relations.find(b);
    if (rit == it->second.m_relations.end()) {
        return theory_relation::independent;
    }
    return rit->second;
}

// --- BFS Reachability ---

bool theory_registry::is_accessible(theory_id from,
                                     theory_id target) const
{
    if (from == target) return true;
    // Core is always accessible from any theory
    if (target == CORE_THEORY_ID) return true;

    std::queue<theory_id> queue;
    std::unordered_set<theory_id> visited;
    queue.push(from);
    visited.insert(from);

    while (!queue.empty()) {
        theory_id cur = queue.front();
        queue.pop();

        auto it = m_modules.find(cur);
        if (it == m_modules.end()) continue;

        for (auto const & [tid, rel] : it->second.m_relations) {
            if (visited.count(tid)) continue;
            // Only traverse extends and compatible edges
            if (rel == theory_relation::extends ||
                rel == theory_relation::compatible) {
                if (tid == target) return true;
                visited.insert(tid);
                queue.push(tid);
            }
        }
    }
    return false;
}

} // namespace lean
