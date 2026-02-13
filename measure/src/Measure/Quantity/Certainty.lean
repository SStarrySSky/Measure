/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Certainty discrimination: exact vs uncertain.
See docs/type-system.md Section 2.1.
-/
import Measure.Dim.Basic

namespace Measure.Quantity

/-- Certainty level: whether a quantity carries uncertainty. -/
inductive Certainty where
  | exact
  | uncertain (model : Type)
  deriving Inhabited

/-- Error data depends on Certainty. -/
@[reducible] def ErrorData : Certainty → Type
  | .exact => Unit
  | .uncertain α => α

/-- ErrorData for exact is trivially inhabited. -/
instance : Inhabited (ErrorData .exact) := ⟨()⟩

end Measure.Quantity
