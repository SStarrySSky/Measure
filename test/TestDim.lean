/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Tests for the dimension system: QExp arithmetic, Dim operations,
derived dimension identities, and the unification algorithm.
-/
import Measure.Dim

namespace TestDim

open Measure.Dim

-- ============================================================
-- QExp arithmetic
-- ============================================================

-- QExp.zero has num = 0
example : QExp.zero.num = 0 := by native_decide

-- QExp.one has num = 1, den = 1
example : QExp.one.num = 1 := by native_decide
example : QExp.one.den = 1 := by native_decide

-- Addition: 1 + 1 = 2
example : (QExp.one + QExp.one) == QExp.mk' 2 1 := by native_decide

-- Subtraction: 1 - 1 = 0
example : (QExp.one - QExp.one) == QExp.zero := by native_decide

-- Negation: -(1) has num = -1
example : (-QExp.one).num = -1 := by native_decide

-- Multiplication: 2 * 3 = 6
example : (QExp.mk' 2 1 * QExp.mk' 3 1) == QExp.mk' 6 1 := by native_decide

-- Fractional exponent: 1/2 has den = 2
example : (QExp.mk' 1 2).den = 2 := by native_decide

-- isZero on zero returns true
example : QExp.zero.isZero = true := by native_decide

-- isZero on one returns false
example : QExp.one.isZero = false := by native_decide

-- ============================================================
-- Dim construction and equality
-- ============================================================

-- Dimensionless is the default Dim
example : Dim.dimensionless == (default : Dim) := by native_decide

-- isDimensionless on dimensionless returns true
example : Dim.dimensionless.isDimensionless = true := by native_decide

-- Velocity is not dimensionless
example : Velocity.isDimensionless = false := by native_decide

-- ============================================================
-- Dim mul / div / pow / inv
-- ============================================================

-- Length * Time⁻¹ = Velocity
example : Dim.mul { L := QExp.one } { T := -QExp.one } == Velocity := by native_decide

-- Force = M * L * T⁻²
example : Force == { L := QExp.one, M := QExp.one, T := QExp.mk' (-2) 1 } := by native_decide

-- Energy = Force * Length
example : Dim.mul Force { L := QExp.one } == Energy := by native_decide

-- Power = Energy / Time
example : Dim.div Energy { T := QExp.one } == Power := by native_decide

-- Velocity / Velocity = dimensionless
example : (Dim.div Velocity Velocity).isDimensionless = true := by native_decide

-- inv(Velocity) = T * L⁻¹
example : Dim.inv Velocity == { L := -QExp.one, T := QExp.one } := by native_decide

-- Acceleration = Velocity / Time
example : Dim.div Velocity { T := QExp.one } == Acceleration := by native_decide

-- Pressure = Force / Area (L²)
example : Dim.div Force { L := QExp.mk' 2 1 } == Pressure := by native_decide

-- Charge = Current * Time
example : Dim.mul { I := QExp.one } { T := QExp.one } == Charge := by native_decide

-- ============================================================
-- Electromagnetic derived dimensions
-- ============================================================

-- Voltage dimension check
example : Voltage == { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-3) 1, I := QExp.mk' (-1) 1 } := by
  native_decide

-- Resistance = Voltage / Current
example : Dim.div Voltage { I := QExp.one } == Resistance := by native_decide

-- ============================================================
-- Unification algorithm
-- ============================================================

-- Unifying two identical concrete dims succeeds
#eval show IO Unit from do
  match unify (.concrete Force) (.concrete Force) with
  | .success _ => pure ()
  | .failure _ _ msg => throw (IO.userError s!"Expected success, got: {msg}")

-- Unifying different concrete dims fails
#eval show IO Unit from do
  match unify (.concrete Force) (.concrete Energy) with
  | .failure _ _ _ => pure ()
  | .success _ => throw (IO.userError "Expected failure for Force vs Energy")

-- Unifying mul terms structurally
#eval show IO Unit from do
  match unify
      (.mul (.concrete { M := QExp.one }) (.concrete Acceleration))
      (.concrete Force) with
  | .success _ => pure ()
  | .failure _ _ msg => throw (IO.userError s!"Expected success, got: {msg}")

-- Variable binding: unify ?X with Force succeeds and binds
#eval show IO Unit from do
  match unify (.var ⟨0⟩) (.concrete Force) with
  | .success σ =>
    match σ.get? ⟨0⟩ with
    | some d =>
      if d == Force then pure ()
      else throw (IO.userError "Variable not bound to Force")
    | none => throw (IO.userError "Variable not in substitution")
  | .failure _ _ msg => throw (IO.userError s!"Expected success, got: {msg}")

-- DimTerm.eval on concrete returns the dim
#eval show IO Unit from do
  match DimTerm.eval (.concrete Velocity) ∅ with
  | some d =>
    if d == Velocity then pure ()
    else throw (IO.userError "Expected Velocity")
  | none => throw (IO.userError "Expected Some")

-- DimTerm.containsVar detects variable presence
example : DimTerm.containsVar (.mul (.var ⟨0⟩) (.concrete Force)) ⟨0⟩ = true := by native_decide

-- DimTerm.containsVar returns false for absent variable
example : DimTerm.containsVar (.concrete Force) ⟨0⟩ = false := by native_decide

-- ============================================================
-- Dimension inference
-- ============================================================

-- Literal is dimensionless
#eval show IO Unit from do
  match infer (.lit 3.14) with
  | .ok d _ =>
    if d.isDimensionless then pure ()
    else throw (IO.userError "Expected dimensionless")
  | .error msg => throw (IO.userError s!"Expected ok, got: {msg}")

-- Variable lookup succeeds when in env
#eval show IO Unit from do
  let env : DimEnv := (∅ : DimEnv).insert `v Velocity
  match infer (.var `v) env with
  | .ok d _ =>
    if d == Velocity then pure ()
    else throw (IO.userError "Expected Velocity")
  | .error msg => throw (IO.userError s!"Expected ok, got: {msg}")

-- Variable lookup fails when not in env
#eval show IO Unit from do
  match infer (.var `unknown) with
  | .error _ => pure ()
  | .ok _ _ => throw (IO.userError "Expected error for unknown variable")

-- mul infers product dimension
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `m { M := QExp.one }).insert `a Acceleration
  match infer (.mul (.var `m) (.var `a)) env with
  | .ok d _ =>
    if d == Force then pure ()
    else throw (IO.userError "Expected Force dimension")
  | .error msg => throw (IO.userError s!"Expected ok, got: {msg}")

-- add requires same dimension — succeeds when matched
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `f1 Force).insert `f2 Force
  match infer (.add (.var `f1) (.var `f2)) env with
  | .ok d _ =>
    if d == Force then pure ()
    else throw (IO.userError "Expected Force dimension")
  | .error msg => throw (IO.userError s!"Expected ok, got: {msg}")

-- add rejects mismatched dimensions
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `f Force).insert `e Energy
  match infer (.add (.var `f) (.var `e)) env with
  | .error _ => pure ()
  | .ok _ _ => throw (IO.userError "Expected dimension mismatch error")

-- div infers quotient dimension
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `e Energy).insert `t { T := QExp.one }
  match infer (.div (.var `e) (.var `t)) env with
  | .ok d _ =>
    if d == Power then pure ()
    else throw (IO.userError "Expected Power dimension")
  | .error msg => throw (IO.userError s!"Expected ok, got: {msg}")

-- pow infers exponentiated dimension
#eval show IO Unit from do
  let env : DimEnv := (∅ : DimEnv).insert `l { L := QExp.one }
  match infer (.pow (.var `l) (QExp.mk' 2 1)) env with
  | .ok d _ =>
    let expected : Dim := { L := QExp.mk' 2 1 }
    if d == expected then pure ()
    else throw (IO.userError "Expected L² dimension")
  | .error msg => throw (IO.userError s!"Expected ok, got: {msg}")

-- Annotation check passes when dimension matches
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `m { M := QExp.one }).insert `a Acceleration
  match infer (.ann (.mul (.var `m) (.var `a)) Force) env with
  | .ok d _ =>
    if d == Force then pure ()
    else throw (IO.userError "Expected Force dimension")
  | .error msg => throw (IO.userError s!"Expected ok, got: {msg}")

-- Annotation check fails when dimension mismatches
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `m { M := QExp.one }).insert `a Acceleration
  match infer (.ann (.mul (.var `m) (.var `a)) Energy) env with
  | .error _ => pure ()
  | .ok _ _ => throw (IO.userError "Expected annotation mismatch error")

-- Let binding propagates dimension
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `m { M := QExp.one }).insert `a Acceleration
  match infer (.letBind `f (.mul (.var `m) (.var `a)) (.var `f)) env with
  | .ok d _ =>
    if d == Force then pure ()
    else throw (IO.userError "Expected Force dimension")
  | .error msg => throw (IO.userError s!"Expected ok, got: {msg}")

end TestDim
