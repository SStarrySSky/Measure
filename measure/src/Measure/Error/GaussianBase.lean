/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Gaussian Propagation: derivative-tag tracking for correlated uncertainties.
Inspired by Julia's Measurements.jl.
See docs/type-system.md Section 4.2.
-/
import Std
import Measure.Error.UncertaintyModel

namespace Measure.Error

/-- Unique tag identifying an independent measurement source. -/
structure Tag where
  id : Nat
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace Tag

/-- Global counter for fresh tag allocation. -/
private unsafe def counterRef : IO.Ref Nat :=
  let f : BaseIO (IO.Ref Nat) := IO.mkRef (0 : Nat)
  let g : Unit → IO.Ref Nat := unsafeCast f
  g ()

/-- Allocate a fresh unique tag. Thread-safe via atomic increment. -/
unsafe def freshUnsafe : Tag :=
  let r := counterRef
  let act : BaseIO Nat := r.modifyGet fun n => (n, n + 1)
  let g : Unit → Nat := unsafeCast act
  { id := g () }

@[implemented_by freshUnsafe]
opaque fresh : Tag

end Tag

/-- Derivative map: partial derivatives w.r.t. each independent source. -/
abbrev Derivatives := Std.HashMap Tag Float

end Measure.Error
