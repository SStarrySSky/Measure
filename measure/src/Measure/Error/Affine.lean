/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Affine Arithmetic: noise-symbol tracking for correlated uncertainties.
See docs/type-system.md Section 4.3.
-/
import Std
import Measure.Error.UncertaintyModel

namespace Measure.Error

/-- Noise symbol ID (unique within a computation graph). -/
structure NoiseId where
  id : Nat
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable, Ord

/-- Affine form: x_hat = x0 + sum(xi * ei), each ei in [-1, 1].
    Carries a `nextId` counter so fresh noise symbols are allocated purely. -/
structure Affine where
  center : Float
  terms  : Std.HashMap NoiseId Float
  nextId : Nat := 0
  deriving Repr, Inhabited

namespace Affine

/-- Total uncertainty half-width: sum of |xi|. -/
def radius (a : Affine) : Float :=
  a.terms.fold (init := 0.0) fun acc _ coeff => acc + Float.abs coeff

/-- Convert to interval [center - radius, center + radius]. -/
def toInterval (a : Affine) : Float × Float :=
  let r := a.radius
  (a.center - r, a.center + r)

/-- Allocate a fresh noise symbol, returning the ID and the updated form. -/
def freshId (a : Affine) : NoiseId × Affine :=
  (⟨a.nextId⟩, { a with nextId := a.nextId + 1 })

/-- Merge the `nextId` counters of two forms so subsequent allocations are unique. -/
def mergeNextId (a b : Affine) : Nat :=
  Nat.max a.nextId b.nextId

/-- Create from uncertain measurement (new noise symbol). -/
def fromUncertain (val halfWidth : Float) : Affine :=
  let eid : NoiseId := ⟨0⟩
  { center := val
  , terms := (∅ : Std.HashMap NoiseId Float) |>.insert eid halfWidth
  , nextId := 1 }

/-- Create from exact value (no noise terms). -/
def exact (val : Float) : Affine :=
  { center := val, terms := ∅, nextId := 0 }

end Affine

end Measure.Error
