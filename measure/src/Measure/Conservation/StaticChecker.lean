/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Conservation.Law

/-! # Conservation Static Checker

Type definitions for three-pass static analysis.
The actual checking runs through the C++ FFI kernel.
-/

namespace Measure.Conservation

/-- Result of static conservation analysis. -/
inductive ConservationVerdict where
  | verified (proof : String)
  | verifiedApprox (bound : String)
  | inconclusive (reason : String)
  | violation (delta : String) (hint : String)
  deriving Inhabited, Repr

/-- An atomic state mutation from Pass 1. -/
structure AtomicMutation where
  target : String
  oldVal : String
  newVal : String
  line : Nat := 0
  deriving Inhabited, Repr

/-- Delta classification from Pass 2. -/
inductive DeltaResult where
  | zero
  | nonzero (value : Float)
  | symbolic (expr : String)
  deriving Inhabited, Repr

end Measure.Conservation
