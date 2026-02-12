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
#include <cstdint>
#include <iosfwd>
#include <unordered_map>

namespace lean {

struct measure_metadata {
    theory_id    m_theory = 0;
    rigor_level  m_rigor = rigor_level::strict;
    epsilon_val  m_epsilon_bound = epsilon_val::zero();
    std::vector<theory_id> m_theory_deps;
    std::vector<std::string> m_axiom_deps;
    uint64_t m_epsilon_proof_root = 0;

    static measure_metadata default_meta();
    bool is_default() const;
};

// .measure sidecar file magic and version
constexpr uint32_t MEASURE_MAGIC = 0x4D535231; // "MSR1"
constexpr uint16_t MEASURE_VERSION = 1;

// Serialization
void serialize_measure_meta(
    std::ostream & out,
    std::unordered_map<std::string, measure_metadata> const & meta);

std::unordered_map<std::string, measure_metadata>
deserialize_measure_meta(std::istream & in);

// Path derivation: foo.olean -> foo.measure
std::string measure_path_from_olean(std::string const & olean_path);

// Merge multiple side tables (union, error on conflict)
std::unordered_map<std::string, measure_metadata>
merge_measure_meta(
    std::vector<std::unordered_map<std::string, measure_metadata>> const & sources);

} // namespace lean
