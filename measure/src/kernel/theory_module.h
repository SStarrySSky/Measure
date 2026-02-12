/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include "kernel/measure_types.h"
#include "kernel/approx_eq.h"
#include "kernel/rigor_propagation.h"
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <cstdint>

namespace lean {

enum class theory_relation : uint8_t {
    independent,
    extends,
    compatible,
    conflicting
};

struct theory_module {
    theory_id   m_id = CORE_THEORY_ID;
    std::string m_name;
    std::vector<std::string> m_axioms;
    std::vector<std::string> m_definitions;
    std::vector<theory_id> m_parents;
    std::unordered_map<theory_id, theory_relation> m_relations;
    epsilon_val m_max_epsilon = epsilon_val::zero();
    rigor_level m_rigor = rigor_level::strict;
};

/// Registry managing all registered theory modules.
class theory_registry {
    std::unordered_map<theory_id, theory_module> m_modules;
    std::unordered_map<std::string, theory_id> m_name_to_id;
    theory_id m_next_id = 1;  // 0 reserved for Core

public:
    theory_registry();

    theory_id register_theory(
        std::string const & name,
        std::vector<theory_id> const & parents,
        rigor_level rigor,
        epsilon_val max_eps);

    theory_module const & get(theory_id id) const;
    theory_module const * find(theory_id id) const;
    theory_id find_by_name(std::string const & n) const;

    void set_relation(theory_id a, theory_id b,
                      theory_relation rel);
    theory_relation get_relation(theory_id a,
                                  theory_id b) const;

    /// BFS reachability via extends/compatible edges.
    bool is_accessible(theory_id from, theory_id target) const;
};

} // namespace lean
