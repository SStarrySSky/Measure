/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Tests for the Float/Real bridge: IEEE 754 decoding, Float.toRat,
and RealQuantity conversions.
-/
import Measure.Quantity.Bridge

namespace TestBridge

open Measure.Dim
open Measure.Quantity

-- ============================================================
-- IEEE 754 field extraction (runtime tests)
-- ============================================================

-- Sign bit of +1.0 is 0
#eval show IO Unit from do
  let s := Float.ieeeSign 1.0
  if s != 0 then throw (IO.userError s!"sign(1.0) = {s}, expected 0")

-- Sign bit of +0.0 is 0
#eval show IO Unit from do
  let s := Float.ieeeSign 0.0
  if s != 0 then throw (IO.userError s!"sign(0.0) = {s}, expected 0")

-- ============================================================
-- Float.toRat correctness (basic cases)
-- ============================================================

-- toRat(0.0) = 0
#eval show IO Unit from do
  let r := Float.toRat 0.0
  if r != (0 : ℚ) then throw (IO.userError s!"toRat(0.0) = {r}, expected 0")

-- toRat of Inf maps to 0
#eval show IO Unit from do
  let r := Float.toRat (1.0 / 0.0)
  if r != (0 : ℚ) then throw (IO.userError s!"toRat(Inf) = {r}, expected 0")

-- toRat of NaN maps to 0
#eval show IO Unit from do
  let r := Float.toRat (0.0 / 0.0)
  if r != (0 : ℚ) then throw (IO.userError s!"toRat(NaN) = {r}, expected 0")

-- toRat of -Inf maps to 0
#eval show IO Unit from do
  let r := Float.toRat (-1.0 / 0.0)
  if r != (0 : ℚ) then throw (IO.userError s!"toRat(-Inf) = {r}, expected 0")

-- ============================================================
-- RealQuantity structure
-- ============================================================

-- RealQuantity.val extracts the value field
example : ∀ (d : Dim) (c : Certainty) (q : RealQuantity d c), q.val = q.value :=
  fun _ _ _ => rfl

-- RealQuantity.dimensionless wraps a real as dimensionless (noncomputable)
noncomputable example : ExactRQ Dim.dimensionless :=
  RealQuantity.dimensionless 42

-- ============================================================
-- Type-level checks: RealQuantity arithmetic compiles
-- ============================================================

-- ExactRQ addition type-checks for same dimension
noncomputable example (a b : ExactRQ Force) : ExactRQ Force := a + b

-- ExactRQ subtraction type-checks for same dimension
noncomputable example (a b : ExactRQ Force) : ExactRQ Force := a - b

-- ExactRQ multiplication produces correct dimension
noncomputable example (a : ExactRQ { M := QExp.one }) (b : ExactRQ Acceleration) :
    ExactRQ (Dim.mul { M := QExp.one } Acceleration) := a * b

-- ExactRQ division produces correct dimension
noncomputable example (a : ExactRQ Energy) (b : ExactRQ { T := QExp.one }) :
    ExactRQ (Dim.div Energy { T := QExp.one }) := a / b

-- ExactRQ negation preserves dimension
noncomputable example (a : ExactRQ Force) : ExactRQ Force := -a

-- Scalar multiplication: Real * ExactRQ
noncomputable example (s : ℝ) (q : ExactRQ Velocity) : ExactRQ Velocity := s * q

-- ============================================================
-- IEEE 754 structure: compile-time type checks
-- ============================================================

-- Float.ieeeSign returns Nat
example : Float → Nat := Float.ieeeSign

-- Float.ieeeExponent returns Nat
example : Float → Nat := Float.ieeeExponent

-- Float.ieeeMantissa returns Nat
example : Float → Nat := Float.ieeeMantissa

-- Float.toRat returns ℚ
example : Float → ℚ := Float.toRat

-- Float.toReal is noncomputable and returns ℝ
noncomputable example : Float → ℝ := Float.toReal

end TestBridge
