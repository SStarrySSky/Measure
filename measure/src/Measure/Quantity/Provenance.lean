/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Provenance tracking for Quantity values.
See docs/type-system.md Section 2.3.
-/

namespace Measure.Quantity

/-- Data source provenance for audit and debugging. -/
inductive Provenance where
  | measurement (lab : String) (instrument : String)
  | database (source : String) (version : String)
  | calculation (op : String) (inputs : List Provenance)
  | userDefined (label : String)
  | combined (op : String) (children : List Provenance)
  | none
  deriving Repr, Inhabited

namespace Provenance

/-- Combine two provenances via a binary operation. -/
def combine (op : String) (a b : Provenance) : Provenance :=
  .combined op [a, b]

/-- Combine a list of provenances via an n-ary operation. -/
def combineMany (op : String) (ps : List Provenance) : Provenance :=
  .combined op ps

/-- Apply a unary operation to provenance. -/
def applyOp (op : String) (p : Provenance) : Provenance :=
  .calculation op [p]

/-- Check if provenance is trivial (none). -/
def isNone : Provenance → Bool
  | .none => true
  | _ => false

end Provenance

end Measure.Quantity
