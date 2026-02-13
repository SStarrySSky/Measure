/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dimension unification and inference for the Measure type system.
See docs/type-system.md Section 1.5 for the algorithm specification.
-/
import Lean

/-! # Dimension Algebra

This module defines the core dimension types for the Measure language.

`QExp` represents rational exponents (e.g., L^(1/2) for √length), and `Dim` is a
7-component SI dimension vector indexed by `QExp`. Together they form a free abelian
group under multiplication/division, which the type-checker uses to enforce dimensional
consistency at compile time.

Common derived dimensions (Velocity, Force, Energy, etc.) are provided as top-level
abbreviations at the end of the file.
-/

namespace Measure.Dim

/-- Rational exponent for dimension components.
    Stores a fraction `num/den` with `den ≥ 1`. Used as the exponent in each
    slot of a `Dim` vector, enabling fractional dimensions such as L^(1/2). -/
structure QExp where
  num : Int
  den : Nat
  den_pos : den ≥ 1 := by omega
  deriving DecidableEq, Repr, BEq

instance : Inhabited QExp where
  default := ⟨0, 1, by omega⟩

namespace QExp

/-- The zero exponent (0/1), representing a dimension not present. -/
def zero : QExp := ⟨0, 1, by omega⟩

/-- The unit exponent (1/1), representing a dimension raised to the first power. -/
def one : QExp := ⟨1, 1, by omega⟩

/-- Smart constructor that normalises the fraction by dividing out the GCD. -/
def mk' (n : Int) (d : Nat) (_h : d ≥ 1 := by omega) : QExp :=
  let g := Int.natAbs n |>.gcd d
  if g == 0 then ⟨0, 1, by omega⟩
  else
    let d' := d / g
    if h' : d' ≥ 1 then ⟨n / g, d', h'⟩
    else ⟨n / g, 1, by omega⟩

/-- Return `true` when the exponent is zero (dimension absent). -/
def isZero (q : QExp) : Bool := q.num == 0

/-- Negate the exponent, used when inverting a dimension. -/
def neg (q : QExp) : QExp := { q with num := -q.num }

private theorem mul_den_pos (a b : Nat) (ha : a ≥ 1) (hb : b ≥ 1) : a * b ≥ 1 :=
  Nat.le_trans (Nat.le_refl 1) (Nat.le_trans ha (Nat.le_mul_of_pos_right a (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)))

/-- Add two rational exponents (common-denominator addition). -/
def add (a b : QExp) : QExp :=
  mk' (a.num * b.den + b.num * a.den) (a.den * b.den)
    (mul_den_pos a.den b.den a.den_pos b.den_pos)

/-- Subtract two rational exponents: `a - b = a + (-b)`. -/
def sub (a b : QExp) : QExp := add a (neg b)

/-- Multiply two rational exponents (used by `Dim.pow`). -/
def mul (a b : QExp) : QExp :=
  mk' (a.num * b.num) (a.den * b.den)
    (mul_den_pos a.den b.den a.den_pos b.den_pos)

instance : Add QExp := ⟨add⟩
instance : Sub QExp := ⟨sub⟩
instance : Mul QExp := ⟨mul⟩
instance : Neg QExp := ⟨neg⟩

/-- Convert the rational exponent to a `Float` approximation. -/
def toFloat (q : QExp) : Float :=
  Float.ofInt q.num / Float.ofNat q.den

end QExp

/-- 7-dimensional SI dimension vector.
    Each field is a `QExp` representing the exponent of one of the seven SI base
    dimensions: Length (L), Mass (M), Time (T), Electric current (I),
    Temperature (Θ), Amount of substance (N), and Luminous intensity (J).
    A dimensionless quantity has all exponents equal to zero. -/
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

/-- The dimensionless dimension (all exponents zero). -/
def dimensionless : Dim := {}

/-- Return `true` when all exponents are zero. -/
def isDimensionless (d : Dim) : Bool :=
  d == dimensionless

/-- Multiply two dimensions by adding their exponents component-wise. -/
def mul (a b : Dim) : Dim :=
  { L := a.L + b.L, M := a.M + b.M, T := a.T + b.T
  , I := a.I + b.I, Θ := a.Θ + b.Θ, N := a.N + b.N
  , J := a.J + b.J }

/-- Divide two dimensions by subtracting their exponents component-wise. -/
def div (a b : Dim) : Dim :=
  { L := a.L - b.L, M := a.M - b.M, T := a.T - b.T
  , I := a.I - b.I, Θ := a.Θ - b.Θ, N := a.N - b.N
  , J := a.J - b.J }

/-- Raise a dimension to a rational power by multiplying each exponent by `n`. -/
def pow (a : Dim) (n : QExp) : Dim :=
  { L := a.L * n, M := a.M * n, T := a.T * n
  , I := a.I * n, Θ := a.Θ * n, N := a.N * n
  , J := a.J * n }

/-- Invert a dimension by negating all exponents. -/
def inv (a : Dim) : Dim :=
  { L := -a.L, M := -a.M, T := -a.T
  , I := -a.I, Θ := -a.Θ, N := -a.N
  , J := -a.J }

/-- Square root of a dimension: halve every exponent. -/
def sqrt (a : Dim) : Dim :=
  pow a (QExp.mk' 1 2)

instance : HMul Dim Dim Dim := ⟨mul⟩
instance : HDiv Dim Dim Dim := ⟨div⟩

end Dim

-- Common derived dimensions

/-- Velocity: L T⁻¹ (m/s). -/
def Velocity     : Dim := { L := QExp.one, T := -QExp.one }
/-- Acceleration: L T⁻² (m/s²). -/
def Acceleration : Dim := { L := QExp.one, T := QExp.mk' (-2) 1 }
/-- Force: M L T⁻² (kg·m/s² = N). -/
def Force        : Dim := { L := QExp.one, M := QExp.one, T := QExp.mk' (-2) 1 }
/-- Energy: M L² T⁻² (kg·m²/s² = J). -/
def Energy       : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1 }
/-- Power: M L² T⁻³ (W). -/
def Power        : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-3) 1 }
/-- Pressure: M L⁻¹ T⁻² (Pa). -/
def Pressure     : Dim := { L := QExp.mk' (-1) 1, M := QExp.one, T := QExp.mk' (-2) 1 }
/-- Electric charge: T I (A·s = C). -/
def Charge       : Dim := { T := QExp.one, I := QExp.one }

-- Electromagnetic derived dimensions

/-- Electric potential (voltage): M L² T⁻³ I⁻¹ (V). -/
def Voltage          : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-3) 1, I := QExp.mk' (-1) 1 }
/-- Electrical resistance: M L² T⁻³ I⁻² (Ω). -/
def Resistance       : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-3) 1, I := QExp.mk' (-2) 1 }
/-- Capacitance: M⁻¹ L⁻² T⁴ I² (F). -/
def Capacitance      : Dim := { L := QExp.mk' (-2) 1, M := QExp.mk' (-1) 1, T := QExp.mk' 4 1, I := QExp.mk' 2 1 }
/-- Inductance: M L² T⁻² I⁻² (H). -/
def Inductance       : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-2) 1 }
/-- Magnetic flux: M L² T⁻² I⁻¹ (Wb). -/
def MagneticFlux     : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-1) 1 }
/-- Magnetic flux density: M T⁻² I⁻¹ (T). -/
def MagneticFluxDens : Dim := { M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-1) 1 }

end Measure.Dim
