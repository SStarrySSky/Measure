/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/rigor_propagation.h"

namespace lean {

const char* rigor_to_string(rigor_level r) {
    switch (r) {
    case rigor_level::strict:      return "strict";
    case rigor_level::approximate: return "approximate";
    case rigor_level::empirical:   return "empirical";
    case rigor_level::numerical:   return "numerical";
    }
    return "unknown";
}

} // namespace lean
