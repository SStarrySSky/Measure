/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <cstdint>

namespace lean {

using theory_id = uint32_t;
constexpr theory_id CORE_THEORY_ID = 0;
constexpr theory_id INVALID_THEORY_ID = UINT32_MAX;

} // namespace lean
