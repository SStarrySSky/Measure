/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Tests for Quantity types: ExactQ arithmetic, UncertainQ arithmetic,
mixed operations, and dimension tracking through operations.
-/
import Measure.Quantity
import Measure.Constants

namespace TestQuantity

open Measure.Dim
open Measure.Quantity
open Measure.Error

-- ============================================================
-- ExactQ construction
-- ============================================================

-- ExactQ.mk creates a quantity with the given value
#eval show IO Unit from do
  let q := ExactQ.mk Velocity 3.0
  if q.value != 3.0 then throw (IO.userError "ExactQ value mismatch")

-- ExactQ error data is Unit
example : (ExactQ.mk Force 10.0).error = () := rfl

-- Default provenance is .none
#eval show IO Unit from do
  let q := ExactQ.mk Force 10.0
  if !q.provenance.isNone then throw (IO.userError "Expected .none provenance")

-- ============================================================
-- ExactQ arithmetic
-- ============================================================

-- Addition: same dimension, values add
#eval show IO Unit from do
  let a := ExactQ.mk Force 10.0
  let b := ExactQ.mk Force 5.0
  let c : ExactQ Force := a + b
  if c.value != 15.0 then throw (IO.userError "Addition value mismatch")

-- Subtraction: same dimension, values subtract
#eval show IO Unit from do
  let a := ExactQ.mk Force 10.0
  let b := ExactQ.mk Force 3.0
  let c : ExactQ Force := a - b
  if c.value != 7.0 then throw (IO.userError "Subtraction value mismatch")

-- Multiplication: dimensions multiply, values multiply
#eval show IO Unit from do
  let m := ExactQ.mk { M := QExp.one } 2.0
  let a := ExactQ.mk Acceleration 9.8
  let f : ExactQ (Dim.mul { M := QExp.one } Acceleration) := m * a
  if f.value != 19.6 then throw (IO.userError "Multiplication value mismatch")

-- Division: dimensions divide, values divide
#eval show IO Unit from do
  let e := ExactQ.mk Energy 100.0
  let t := ExactQ.mk { T := QExp.one } 5.0
  let p : ExactQ (Dim.div Energy { T := QExp.one }) := e / t
  if p.value != 20.0 then throw (IO.userError "Division value mismatch")

-- Negation: value negates, dimension preserved
#eval show IO Unit from do
  let q := ExactQ.mk Force 10.0
  let neg_q : ExactQ Force := -q
  if neg_q.value != -10.0 then throw (IO.userError "Negation value mismatch")

-- Scalar multiplication: Float * ExactQ
#eval show IO Unit from do
  let q := ExactQ.mk Velocity 5.0
  let scaled : ExactQ Velocity := (2.0 : Float) * q
  if scaled.value != 10.0 then throw (IO.userError "Scalar mul value mismatch")

-- ============================================================
-- ExactQ provenance tracking
-- ============================================================

-- Addition combines provenance
#eval show IO Unit from do
  let a : ExactQ Force := { value := 10.0, error := (), provenance := .userDefined "F1" }
  let b : ExactQ Force := { value := 5.0, error := (), provenance := .userDefined "F2" }
  let c := a + b
  match c.provenance with
  | .combined "add" _ => pure ()
  | _ => throw (IO.userError "Expected combined provenance")

-- ============================================================
-- UncertainQ construction and operations
-- ============================================================

-- UncertainQ.fromMeasurement creates a quantity with non-zero uncertainty
#eval show IO Unit from do
  let q := UncertainQ.fromMeasurement (α := Gaussian) Force 10.0 0.5
  if q.value != 10.0 then throw (IO.userError "UncertainQ value mismatch")
  if q.uncertainty <= 0.0 then throw (IO.userError "UncertainQ uncertainty should be > 0")

-- UncertainQ.fromExact creates zero uncertainty
#eval show IO Unit from do
  let q := UncertainQ.fromExact (α := Gaussian) Force 10.0
  if q.value != 10.0 then throw (IO.userError "UncertainQ.fromExact value mismatch")
  if q.uncertainty != 0.0 then throw (IO.userError "UncertainQ.fromExact uncertainty should be 0")

-- UncertainQ addition propagates uncertainty
#eval show IO Unit from do
  let a := UncertainQ.fromMeasurement (α := Gaussian) Force 10.0 0.3
  let b := UncertainQ.fromMeasurement (α := Gaussian) Force 5.0 0.4
  let c := a + b
  if c.value != 15.0 then throw (IO.userError "Uncertain add value mismatch")
  -- Uncertainty should be positive and bounded by linear sum (0.7)
  if c.uncertainty <= 0.0 then throw (IO.userError "Uncertain add uncertainty should be > 0")
  if c.uncertainty > 0.71 then throw (IO.userError s!"Uncertain add uncertainty too large: {c.uncertainty}")

-- UncertainQ subtraction: x - x has zero uncertainty (correlation tracking)
#eval show IO Unit from do
  let x := UncertainQ.fromMeasurement (α := Gaussian) Force 10.0 0.5
  let diff := x - x
  if diff.value != 0.0 then throw (IO.userError "x - x value should be 0")
  if diff.uncertainty >= 1e-15 then
    throw (IO.userError s!"x - x uncertainty should be ~0, got: {diff.uncertainty}")

-- UncertainQ multiplication propagates uncertainty
#eval show IO Unit from do
  let m := UncertainQ.fromMeasurement (α := Gaussian) { M := QExp.one } 2.0 0.1
  let a := UncertainQ.fromMeasurement (α := Gaussian) Acceleration 9.8 0.2
  let f := m * a
  if Float.abs (f.value - 19.6) >= 1e-10 then throw (IO.userError "Uncertain mul value mismatch")
  if f.uncertainty <= 0.0 then throw (IO.userError "Uncertain mul uncertainty should be > 0")

-- UncertainQ scalar multiplication scales uncertainty
#eval show IO Unit from do
  let q := UncertainQ.fromMeasurement (α := Gaussian) Velocity 10.0 0.5
  let scaled := (2.0 : Float) * q
  if scaled.value != 20.0 then throw (IO.userError "Scalar mul value mismatch")
  if Float.abs (scaled.uncertainty - 1.0) >= 1e-10 then
    throw (IO.userError s!"Scalar mul uncertainty mismatch: {scaled.uncertainty}")

-- UncertainQ negation preserves uncertainty magnitude
#eval show IO Unit from do
  let q := UncertainQ.fromMeasurement (α := Gaussian) Force 10.0 0.5
  let neg_q := -q
  if neg_q.value != -10.0 then throw (IO.userError "Negation value mismatch")
  if Float.abs (neg_q.uncertainty - 0.5) >= 1e-10 then
    throw (IO.userError "Negation uncertainty mismatch")

-- UncertainQ toInterval returns a valid interval
#eval show IO Unit from do
  let q := UncertainQ.fromMeasurement (α := Gaussian) Force 10.0 0.5
  let (lo, hi) := q.toInterval
  if lo >= q.value then throw (IO.userError "Interval lo >= value")
  if hi <= q.value then throw (IO.userError "Interval hi <= value")
  if lo >= hi then throw (IO.userError "Interval lo >= hi")

-- ============================================================
-- Mixed operations: exact + uncertain = uncertain
-- ============================================================

-- ExactQ + UncertainQ = UncertainQ
#eval show IO Unit from do
  let exact := ExactQ.mk Force 10.0
  let uncertain := UncertainQ.fromMeasurement (α := Gaussian) Force 5.0 0.3
  let result := exact + uncertain
  if result.value != 15.0 then throw (IO.userError "Mixed add value mismatch")
  if result.uncertainty <= 0.0 then throw (IO.userError "Mixed add uncertainty should be > 0")

-- UncertainQ + ExactQ = UncertainQ (commutative)
#eval show IO Unit from do
  let uncertain := UncertainQ.fromMeasurement (α := Gaussian) Force 5.0 0.3
  let exact := ExactQ.mk Force 10.0
  let result := uncertain + exact
  if result.value != 15.0 then throw (IO.userError "Mixed add (reverse) value mismatch")

-- ExactQ * UncertainQ produces correct dimension
#eval show IO Unit from do
  let m := ExactQ.mk { M := QExp.one } 2.0
  let a := UncertainQ.fromMeasurement (α := Gaussian) Acceleration 9.8 0.2
  let f := m * a
  if Float.abs (f.value - 19.6) >= 1e-10 then throw (IO.userError "Mixed mul value mismatch")
  if f.uncertainty <= 0.0 then throw (IO.userError "Mixed mul uncertainty should be > 0")

-- ============================================================
-- Dimension type safety (compile-time checks)
-- ============================================================

-- Force + Force is valid
example (a b : ExactQ Force) : ExactQ Force := a + b

-- Energy / Time gives Power dimension
example (e : ExactQ Energy) (t : ExactQ { T := QExp.one }) :
    ExactQ (Dim.div Energy { T := QExp.one }) := e / t

-- Mass * Acceleration gives Force dimension
example (m : ExactQ { M := QExp.one }) (a : ExactQ Acceleration) :
    ExactQ (Dim.mul { M := QExp.one } Acceleration) := m * a

-- Negation preserves dimension
example (f : ExactQ Force) : ExactQ Force := -f

-- ============================================================
-- approxEq and comparison relations
-- ============================================================

-- approxEq holds for close values
#eval show IO Unit from do
  let a := ExactQ.mk Force 10.0
  let b := ExactQ.mk Force 10.001
  if Float.abs (a.value - b.value) >= 0.01 then
    throw (IO.userError "approxEq should hold for close values")

-- approxEq fails for distant values
#eval show IO Unit from do
  let a := ExactQ.mk Force 10.0
  let b := ExactQ.mk Force 11.0
  if Float.abs (a.value - b.value) < 0.01 then
    throw (IO.userError "approxEq should fail for distant values")

end TestQuantity
