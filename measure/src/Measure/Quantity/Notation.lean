/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Physics notation syntax sugar for Quantity operations.
Adds missing operator instances and unit-literal helpers so physicists
can write natural mathematical expressions.
-/
import Measure.Quantity.Ops
import Measure.Quantity.MixedOps
import Measure.Unit.SI

/-! # Physics Notation Sugar

This module fills gaps in the operator coverage for `ExactQ` and `UncertainQ`:

- Right scalar multiplication: `q * s` where `s : Float`
- Scalar division: `q / s`
- Natural-number power: `q ^ n` (dimension raised to the n-th power)
- Unit literals: `5.0 #kg`, `9.8 #m`, etc. producing correctly-typed `ExactQ` values

All dimension arithmetic happens at the type level via `Dim.mul`, `Dim.div`, `Dim.pow`.
-/

namespace Measure.Quantity

open Measure.Dim
open Measure.Error
open Measure.Unit
open Measure.Unit.SI

-- ============================================================
-- Missing exact operators
-- ============================================================

/-- Right scalar multiplication: ExactQ * Float. -/
instance {d : Dim} : HMul (ExactQ d) Float (ExactQ d) where
  hMul q s := {
    value := q.value * s
    error := ()
    provenance := .applyOp "scale" q.provenance
  }

/-- Scalar division: ExactQ / Float (divide by dimensionless scalar). -/
instance {d : Dim} : HDiv (ExactQ d) Float (ExactQ d) where
  hDiv q s := {
    value := q.value / s
    error := ()
    provenance := .applyOp "scale" q.provenance
  }

/-- Scalar division: Float / ExactQ (dimensionless / quantity = inverse dimension). -/
instance {d : Dim} : HDiv Float (ExactQ d) (ExactQ (Dim.inv d)) where
  hDiv s q := {
    value := s / q.value
    error := ()
    provenance := .applyOp "inv_scale" q.provenance
  }

-- ============================================================
-- Natural-number power for ExactQ
-- ============================================================

/-- Helper: compute `Dim.pow d (QExp.mk' n 1)` for a natural number exponent. -/
abbrev dimNatPow (d : Dim) (n : Nat) : Dim :=
  Dim.pow d (QExp.mk' (Int.ofNat n) 1)

/-- Raise an exact quantity to a natural-number power.
    The result dimension is `Dim.pow d n`. -/
def ExactQ.pow {d : Dim} (q : ExactQ d) (n : Nat) : ExactQ (dimNatPow d n) :=
  { value := Float.pow q.value (Float.ofNat n)
    error := ()
    provenance := .applyOp s!"pow_{n}" q.provenance }

-- Note: HPow (ExactQ d) Nat (ExactQ (dimNatPow d n)) cannot be defined as a
-- typeclass instance because the output type depends on the exponent value `n`,
-- which is not available as a type parameter in HPow. Use `ExactQ.pow q n` instead.

-- ============================================================
-- Missing uncertain operators
-- ============================================================

/-- Right scalar multiplication: UncertainQ * Float. -/
instance {α : Type} [UncertaintyModel α] {d : Dim} :
    HMul (UncertainQ d α) Float (UncertainQ d α) where
  hMul q s :=
    { value := q.value * s
      error := UncertaintyModel.scale s q.error
      provenance := .applyOp "scale" q.provenance }

/-- Right scalar multiplication: Quantity uncertain * Float. -/
instance {d : Dim} {model : Type} [UncertaintyModel model] :
    HMul (Quantity d (.uncertain model)) Float (Quantity d (.uncertain model)) where
  hMul q s :=
    let eq : model := q.error
    { value := q.value * s
      error := UncertaintyModel.scale s eq
      provenance := .applyOp "scale" q.provenance }

-- ============================================================
-- Natural-number power for UncertainQ
-- ============================================================

/-- Raise an uncertain quantity to a natural-number power.
    Uses UncertaintyModel.pow for error propagation. -/
def UncertainQ.pow {d : Dim} {α : Type} [UncertaintyModel α]
    (q : UncertainQ d α) (n : Nat) : UncertainQ (dimNatPow d n) α :=
  { value := Float.pow q.value (Float.ofNat n)
    error := UncertaintyModel.pow q.error q.value (Float.ofNat n)
    provenance := .applyOp s!"pow_{n}" q.provenance }

/-- Square an uncertain quantity. -/
def UncertainQ.sq {d : Dim} {α : Type} [UncertaintyModel α]
    (q : UncertainQ d α) : UncertainQ (Dim.mul d d) α :=
  q * q

/-- Cube an uncertain quantity. -/
def UncertainQ.cube {d : Dim} {α : Type} [UncertaintyModel α]
    (q : UncertainQ d α) : UncertainQ (Dim.mul (Dim.mul d d) d) α :=
  q * q * q

-- ============================================================
-- Quantity-level sqrt (Gap 2)
-- ============================================================

/-- Square root of an exact quantity. Dimension is halved. -/
def ExactQ.sqrt {d : Dim} (q : ExactQ d) : ExactQ (Dim.sqrt d) :=
  { value := Float.sqrt q.value
    error := ()
    provenance := .applyOp "sqrt" q.provenance }

/-- Square root of an uncertain quantity. Dimension is halved.
    Uses chain rule: d(sqrt x)/dx = 1/(2 sqrt x). -/
def UncertainQ.sqrt {d : Dim} {α : Type} [UncertaintyModel α]
    (q : UncertainQ d α) : UncertainQ (Dim.sqrt d) α :=
  { value := Float.sqrt q.value
    error := UncertaintyModel.applyFunc q.error q.value Float.sqrt (fun x => 0.5 / Float.sqrt x)
    provenance := .applyOp "sqrt" q.provenance }

-- ============================================================
-- UncertainQ / Float (Gap 4)
-- ============================================================

/-- Scalar division: UncertainQ / Float. -/
instance {d : Dim} {α : Type} [UncertaintyModel α] :
    HDiv (UncertainQ d α) Float (UncertainQ d α) where
  hDiv q s :=
    { value := q.value / s
      error := UncertaintyModel.scale (1.0 / s) q.error
      provenance := .applyOp "scale" q.provenance }

/-- Scalar division: Quantity uncertain / Float. -/
instance {d : Dim} {model : Type} [UncertaintyModel model] :
    HDiv (Quantity d (.uncertain model)) Float (Quantity d (.uncertain model)) where
  hDiv q s :=
    let eq : model := q.error
    { value := q.value / s
      error := UncertaintyModel.scale (1.0 / s) eq
      provenance := .applyOp "scale" q.provenance }

-- ============================================================
-- Unit-literal notation
-- ============================================================

/-- Base dimensions as abbreviations for use in Dim position. -/
abbrev dimLength      : Dim := { L := QExp.one }
abbrev dimMass        : Dim := { M := QExp.one }
abbrev dimTime        : Dim := { T := QExp.one }
abbrev dimCurrent     : Dim := { I := QExp.one }
abbrev dimTemperature : Dim := { Θ := QExp.one }
abbrev dimAmount      : Dim := { N := QExp.one }
abbrev dimLuminosity  : Dim := { J := QExp.one }

/-- Create an ExactQ from a Float value and a Unit.
    The unit's conversion factor scales the value to SI base units. -/
def ExactQ.ofUnit {d : Dim} (v : Float) (_u : Measure.Unit.Unit d) : ExactQ d :=
  { value := v * _u.toSI + _u.offset
    error := ()
    provenance := .userDefined s!"{v} {_u.symbol}" }

-- SI base unit quantities: `5.0 #kg` etc.
-- These produce ExactQ values in SI base units (conversion factor = 1).

scoped notation:max v " #m"      => ExactQ.mk dimLength v
scoped notation:max v " #kg"     => ExactQ.mk dimMass v
scoped notation:max v " #s"      => ExactQ.mk dimTime v
scoped notation:max v " #A"      => ExactQ.mk dimCurrent v
scoped notation:max v " #K"      => ExactQ.mk dimTemperature v
scoped notation:max v " #mol"    => ExactQ.mk dimAmount v
scoped notation:max v " #cd"     => ExactQ.mk dimLuminosity v

-- Derived unit quantities
scoped notation:max v " #N"      => ExactQ.mk Force v
scoped notation:max v " #J"      => ExactQ.mk Energy v
scoped notation:max v " #W"      => ExactQ.mk Power v
scoped notation:max v " #Pa"     => ExactQ.mk Pressure v
scoped notation:max v " #C"      => ExactQ.mk Charge v
scoped notation:max v " #V"      => ExactQ.mk Voltage v
scoped notation:max v " #Ω"      => ExactQ.mk Resistance v

-- Electromagnetic derived unit quantities (Gap 7)
scoped notation:max v " #Hz"     => ExactQ.mk Frequency v
scoped notation:max v " #T"      => ExactQ.mk MagneticFluxDens v
scoped notation:max v " #Wb"     => ExactQ.mk MagneticFlux v
scoped notation:max v " #H"      => ExactQ.mk Inductance v
scoped notation:max v " #F"      => ExactQ.mk Capacitance v

-- Dimensionless
scoped notation:max v " #1"      => ExactQ.mk Dim.dimensionless v

-- ============================================================
-- Convenience: square and cube
-- ============================================================

/-- Square an exact quantity. -/
def ExactQ.sq {d : Dim} (q : ExactQ d) : ExactQ (Dim.mul d d) :=
  q * q

/-- Cube an exact quantity. -/
def ExactQ.cube {d : Dim} (q : ExactQ d) : ExactQ (Dim.mul (Dim.mul d d) d) :=
  q * q * q

/-- Reciprocal of an exact quantity. -/
def ExactQ.inv {d : Dim} (q : ExactQ d) : ExactQ (Dim.inv d) :=
  { value := 1.0 / q.value
    error := ()
    provenance := .applyOp "inv" q.provenance }

-- ============================================================
-- Display (Gap 5: ToString with dimension info)
-- ============================================================

/-- ToString for ExactQ showing value and dimension. -/
instance {d : Dim} : ToString (ExactQ d) where
  toString q := s!"{q.value} {d}"

/-- ToString for UncertainQ showing value, uncertainty, and dimension. -/
instance {d : Dim} {α : Type} [UncertaintyModel α] : ToString (UncertainQ d α) where
  toString q :=
    let u := UncertaintyModel.uncertainty q.error
    s!"{q.value} ± {u} {d}"

-- ============================================================
-- High-level conversion API (Gap 6)
-- ============================================================

/-- Convert an exact quantity to a different unit of the same dimension.
    Returns the numeric value in the target unit. -/
def ExactQ.convertTo {d : Dim} (q : ExactQ d) (u : Measure.Unit.Unit d) : ExactQ d :=
  { value := (q.value - u.offset) / u.toSI
    error := ()
    provenance := .applyOp s!"to_{u.symbol}" q.provenance }

/-- Convert an uncertain quantity to a different unit of the same dimension.
    Returns the numeric value in the target unit. -/
def UncertainQ.convertTo {d : Dim} {α : Type} [UncertaintyModel α]
    (q : UncertainQ d α) (u : Measure.Unit.Unit d) : UncertainQ d α :=
  { value := (q.value - u.offset) / u.toSI
    error := UncertaintyModel.scale (1.0 / u.toSI) q.error
    provenance := .applyOp s!"to_{u.symbol}" q.provenance }

end Measure.Quantity
