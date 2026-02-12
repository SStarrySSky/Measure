/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dimension unification and inference for the Measure type system.
See docs/type-system.md Section 1.5 for the algorithm specification.
-/
import Lean

namespace Measure.Dim

/-- Rational exponent for dimension components. -/
structure QExp where
  num : Int
  den : Nat
  den_pos : den ≥ 1 := by omega
  deriving DecidableEq, Repr, BEq

instance : Inhabited QExp where
  default := ⟨0, 1, by omega⟩

namespace QExp

def zero : QExp := ⟨0, 1, by omega⟩
def one : QExp := ⟨1, 1, by omega⟩

def mk' (n : Int) (d : Nat) (_h : d ≥ 1 := by omega) : QExp :=
  let g := Int.natAbs n |>.gcd d
  if g == 0 then ⟨0, 1, by omega⟩
  else
    let d' := d / g
    if h' : d' ≥ 1 then ⟨n / g, d', h'⟩
    else ⟨n / g, 1, by omega⟩

def isZero (q : QExp) : Bool := q.num == 0

def neg (q : QExp) : QExp := { q with num := -q.num }

private theorem mul_den_pos (a b : Nat) (ha : a ≥ 1) (hb : b ≥ 1) : a * b ≥ 1 :=
  Nat.le_trans (Nat.le_refl 1) (Nat.le_trans ha (Nat.le_mul_of_pos_right a (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)))

def add (a b : QExp) : QExp :=
  mk' (a.num * b.den + b.num * a.den) (a.den * b.den)
    (mul_den_pos a.den b.den a.den_pos b.den_pos)

def sub (a b : QExp) : QExp := add a (neg b)

def mul (a b : QExp) : QExp :=
  mk' (a.num * b.num) (a.den * b.den)
    (mul_den_pos a.den b.den a.den_pos b.den_pos)

instance : Add QExp := ⟨add⟩
instance : Sub QExp := ⟨sub⟩
instance : Mul QExp := ⟨mul⟩
instance : Neg QExp := ⟨neg⟩

def toFloat (q : QExp) : Float :=
  Float.ofInt q.num / Float.ofNat q.den

end QExp

/-- 7-dimensional SI dimension vector. -/
structure Dim where
  L : QExp := QExp.zero  -- Length
  M : QExp := QExp.zero  -- Mass
  T : QExp := QExp.zero  -- Time
  I : QExp := QExp.zero  -- Current
  Θ : QExp := QExp.zero  -- Temperature
  N : QExp := QExp.zero  -- Amount
  J : QExp := QExp.zero  -- Luminosity
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Dim

def dimensionless : Dim := {}

def isDimensionless (d : Dim) : Bool :=
  d == dimensionless

def mul (a b : Dim) : Dim :=
  { L := a.L + b.L, M := a.M + b.M, T := a.T + b.T
  , I := a.I + b.I, Θ := a.Θ + b.Θ, N := a.N + b.N
  , J := a.J + b.J }

def div (a b : Dim) : Dim :=
  { L := a.L - b.L, M := a.M - b.M, T := a.T - b.T
  , I := a.I - b.I, Θ := a.Θ - b.Θ, N := a.N - b.N
  , J := a.J - b.J }

def pow (a : Dim) (n : QExp) : Dim :=
  { L := a.L * n, M := a.M * n, T := a.T * n
  , I := a.I * n, Θ := a.Θ * n, N := a.N * n
  , J := a.J * n }

def inv (a : Dim) : Dim :=
  { L := -a.L, M := -a.M, T := -a.T
  , I := -a.I, Θ := -a.Θ, N := -a.N
  , J := -a.J }

def sqrt (a : Dim) : Dim :=
  pow a (QExp.mk' 1 2)

instance : HMul Dim Dim Dim := ⟨mul⟩
instance : HDiv Dim Dim Dim := ⟨div⟩

end Dim

-- Common derived dimensions
def Velocity     : Dim := { L := QExp.one, T := -QExp.one }
def Acceleration : Dim := { L := QExp.one, T := QExp.mk' (-2) 1 }
def Force        : Dim := { L := QExp.one, M := QExp.one, T := QExp.mk' (-2) 1 }
def Energy       : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1 }
def Power        : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-3) 1 }
def Pressure     : Dim := { L := QExp.mk' (-1) 1, M := QExp.one, T := QExp.mk' (-2) 1 }
def Charge       : Dim := { T := QExp.one, I := QExp.one }

-- Electromagnetic derived dimensions
def Voltage          : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-3) 1, I := QExp.mk' (-1) 1 }
def Resistance       : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-3) 1, I := QExp.mk' (-2) 1 }
def Capacitance      : Dim := { L := QExp.mk' (-2) 1, M := QExp.mk' (-1) 1, T := QExp.mk' 4 1, I := QExp.mk' 2 1 }
def Inductance       : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-2) 1 }
def MagneticFlux     : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-1) 1 }
def MagneticFluxDens : Dim := { M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-1) 1 }

end Measure.Dim
