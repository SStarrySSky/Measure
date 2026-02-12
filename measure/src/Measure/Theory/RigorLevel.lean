/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Theory Module Basic Definitions

Core data structures for the theory module system:
- `RigorLevel`: epistemic quality spectrum
- `TheoryRelation`: three relation types between theories
- `TheoryModule`: the fundamental unit of axiom isolation
-/

namespace Measure.Theory

/-- Epistemic quality spectrum. Ordered: strict > approximate > empirical > numerical.
    Forms a bounded meet-semilattice with `min` as meet. -/
inductive RigorLevel where
  | strict
  | approximate
  | empirical
  | numerical
  deriving Inhabited, BEq, Repr

namespace RigorLevel

def toNat : RigorLevel -> Nat
  | strict      => 3
  | approximate => 2
  | empirical   => 1
  | numerical   => 0

instance : LE RigorLevel where
  le a b := a.toNat ≤ b.toNat

instance : Ord RigorLevel where
  compare a b := compare a.toNat b.toNat

/-- Lattice meet: rigor of combined derivation is minimum of parts. -/
def meet (a b : RigorLevel) : RigorLevel :=
  if a.toNat ≤ b.toNat then a else b

instance : Min RigorLevel where
  min := meet

def toString : RigorLevel -> String
  | strict      => "strict"
  | approximate => "approximate"
  | empirical   => "empirical"
  | numerical   => "numerical"

instance : ToString RigorLevel where
  toString := RigorLevel.toString

end RigorLevel
