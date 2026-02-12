/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <cstdint>
#include <algorithm>

namespace lean {

/// Rigor spectrum: 4 levels, lower value = more rigorous.
/// See ARCHITECTURE.md S6.7 and theory-system.md S2.4.
enum class rigor_level : uint8_t {
    strict      = 0,  // full formal proof, eps = 0
    approximate = 1,  // controlled approximation
    empirical   = 2,  // empirical verification
    numerical   = 3   // numerical verification
};

/// Propagation: take max (weakest link).
inline rigor_level propagate_rigor(rigor_level a, rigor_level b) {
    return static_cast<rigor_level>(
        std::max(static_cast<uint8_t>(a),
                 static_cast<uint8_t>(b)));
}

/// Compatibility: actual rigor must not exceed declared.
inline bool is_rigor_compatible(rigor_level declared,
                                 rigor_level actual) {
    return static_cast<uint8_t>(actual)
        <= static_cast<uint8_t>(declared);
}

const char* rigor_to_string(rigor_level r);

} // namespace lean
