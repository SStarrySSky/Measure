/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Theory.Module

/-! # Theory Graph — Type Definitions

Type definitions for the theory relation graph. The actual conflict detection
pipeline (4 stages: cache, syntactic, semantic, SMT) runs through the C++ FFI
kernel — see `Measure.Kernel.FFI`.

These types are retained for potential future Lean-side tooling.
-/

namespace Measure.Theory

end Measure.Theory
