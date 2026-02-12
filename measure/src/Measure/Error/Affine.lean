/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Affine Arithmetic: noise-symbol tracking for correlated uncertainties.
See docs/type-system.md Section 4.3.
-/
import Std
import Measure.Error.UncertaintyModel

namespace Measure.Error

/-- Noise symbol ID (globally unique). -/
structure NoiseId where
  id : Nat
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable, Ord

namespace NoiseId

private unsafe def counterRef : IO.Ref Nat :=
  let f : BaseIO (IO.Ref Nat) := IO.mkRef (0 : Nat)
  let g : Unit → IO.Ref Nat := unsafeCast f
  g ()

unsafe def freshUnsafe : NoiseId :=
  let r := counterRef
  let act : BaseIO Nat := r.modifyGet fun n => (n, n + 1)
  let g : Unit → Nat := unsafeCast act
  { id := g () }

@[implemented_by freshUnsafe]
opaque fresh : NoiseId

end NoiseId

/-- Affine form: x_hat = x0 + sum(xi * ei), each ei in [-1, 1]. -/
structure Affine where
  center : Float
  terms  : Std.HashMap NoiseId Float
  deriving Repr, Inhabited

namespace Affine

/-- Total uncertainty half-width: sum of |xi|. -/
def radius (a : Affine) : Float :=
  a.terms.fold (init := 0.0) fun acc _ coeff => acc + Float.abs coeff

/-- Convert to interval [center - radius, center + radius]. -/
def toInterval (a : Affine) : Float × Float :=
  let r := a.radius
  (a.center - r, a.center + r)

/-- Create from uncertain measurement (new noise symbol). -/
def fromUncertain (val halfWidth : Float) : Affine :=
  let eid := NoiseId.fresh
  { center := val
  , terms := (∅ : Std.HashMap NoiseId Float) |>.insert eid halfWidth }

/-- Create from exact value (no noise terms). -/
def exact (val : Float) : Affine :=
  { center := val, terms := ∅ }

end Affine

end Measure.Error
