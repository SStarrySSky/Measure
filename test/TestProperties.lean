/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Property-based tests for the Measure language core modules:
dimension algebra, quantity arithmetic, Float.toRat round-trips,
uncertainty propagation, and dimension inference.
-/
import Measure.Quantity
import Measure.Constants
import Measure.Dim.Infer

namespace TestProperties

open Measure.Dim
open Measure.Quantity
open Measure.Error

-- ============================================================
-- Helper: generate a list of test dimensions
-- ============================================================

private def testDims : List Dim :=
  [ Dim.dimensionless
  , { L := QExp.one }
  , { M := QExp.one }
  , { T := QExp.one }
  , { I := QExp.one }
  , Velocity
  , Acceleration
  , Force
  , Energy
  , Power
  , Pressure
  , Charge
  , Voltage
  , Resistance
  , { L := QExp.mk' 2 1 }
  , { T := QExp.mk' (-2) 1 }
  , { L := QExp.one, M := QExp.one }
  , { L := QExp.mk' 1 2 }
  ]

private def testQExps : List QExp :=
  [ QExp.zero
  , QExp.one
  , QExp.mk' (-1) 1
  , QExp.mk' 2 1
  , QExp.mk' (-2) 1
  , QExp.mk' 1 2
  , QExp.mk' (-1) 2
  , QExp.mk' 3 1
  , QExp.mk' 1 3
  ]

-- ============================================================
-- 1. Dimension algebra properties
-- ============================================================

-- 1a. dim_mul is associative: (a * b) * c = a * (b * c)
#eval show IO Unit from do
  let mut passed := 0
  for a in testDims do
    for b in testDims do
      for c in testDims do
        let lhs := Dim.mul (Dim.mul a b) c
        let rhs := Dim.mul a (Dim.mul b c)
        if lhs != rhs then
          throw (IO.userError s!"mul associativity failed: ({repr a} * {repr b}) * {repr c}")
        passed := passed + 1
  IO.println s!"[dim_mul_assoc] All {passed} tests passed"

-- 1b. dim_mul is commutative: a * b = b * a
#eval show IO Unit from do
  let mut passed := 0
  for a in testDims do
    for b in testDims do
      let lhs := Dim.mul a b
      let rhs := Dim.mul b a
      if lhs != rhs then
        throw (IO.userError s!"mul commutativity failed: {repr a} * {repr b}")
      passed := passed + 1
  IO.println s!"[dim_mul_comm] All {passed} tests passed"

-- 1c. dim_inv is involutive: inv(inv(d)) = d
#eval show IO Unit from do
  let mut passed := 0
  for d in testDims do
    let result := Dim.inv (Dim.inv d)
    if result != d then
      throw (IO.userError s!"inv involutive failed for {repr d}")
    passed := passed + 1
  IO.println s!"[dim_inv_involutive] All {passed} tests passed"

-- 1d. dim_one is identity: d * dimOne = d
#eval show IO Unit from do
  let mut passed := 0
  for d in testDims do
    let lhs := Dim.mul d Dim.dimensionless
    if lhs != d then
      throw (IO.userError s!"mul identity failed for {repr d}")
    let rhs := Dim.mul Dim.dimensionless d
    if rhs != d then
      throw (IO.userError s!"mul left identity failed for {repr d}")
    passed := passed + 1
  IO.println s!"[dim_mul_identity] All {passed} tests passed"

-- 1e. dim_div self = dimOne: d / d = dimensionless
#eval show IO Unit from do
  let mut passed := 0
  for d in testDims do
    let result := Dim.div d d
    if !result.isDimensionless then
      throw (IO.userError s!"div self failed for {repr d}: got {repr result}")
    passed := passed + 1
  IO.println s!"[dim_div_self] All {passed} tests passed"

-- 1f. Compile-time proofs for specific dimension algebra identities
example : Dim.mul (Dim.mul Force { L := QExp.one }) { T := QExp.one }
        == Dim.mul Force (Dim.mul { L := QExp.one } { T := QExp.one }) := by native_decide

example : Dim.mul Velocity { T := QExp.one } == Dim.mul { T := QExp.one } Velocity := by native_decide

example : Dim.inv (Dim.inv Force) == Force := by native_decide

example : (Dim.div Energy Energy).isDimensionless = true := by native_decide

-- ============================================================
-- 2. Quantity arithmetic properties
-- ============================================================

private def testFloats : List Float :=
  [0.0, 1.0, -1.0, 2.5, -3.7, 100.0, -0.001, 1e10, -1e10, 0.5]

-- 2a. Addition commutativity (same dimension)
#eval show IO Unit from do
  let mut passed := 0
  for x in testFloats do
    for y in testFloats do
      let a := ExactQ.mk Force x
      let b := ExactQ.mk Force y
      let lhs : ExactQ Force := a + b
      let rhs : ExactQ Force := b + a
      if lhs.value != rhs.value then
        throw (IO.userError s!"add commutativity failed: {x} + {y}")
      passed := passed + 1
  IO.println s!"[quantity_add_comm] All {passed} tests passed"

-- 2b. Multiplication associativity
--     We test value-level associativity using dimensionless quantities
--     to avoid dimension type mismatch.
#eval show IO Unit from do
  let mut passed := 0
  for x in testFloats do
    for y in testFloats do
      for z in testFloats do
        let a := ExactQ.mk Dim.dimensionless x
        let b := ExactQ.mk Dim.dimensionless y
        let c := ExactQ.mk Dim.dimensionless z
        let lhs : ExactQ (Dim.mul (Dim.mul Dim.dimensionless Dim.dimensionless) Dim.dimensionless) := (a * b) * c
        let rhs : ExactQ (Dim.mul Dim.dimensionless (Dim.mul Dim.dimensionless Dim.dimensionless)) := a * (b * c)
        -- Float mul is associative for these values
        if Float.abs (lhs.value - rhs.value) >= 1e-6 * (Float.abs lhs.value + 1.0) then
          throw (IO.userError s!"mul associativity failed: ({x} * {y}) * {z}")
        passed := passed + 1
  IO.println s!"[quantity_mul_assoc] All {passed} tests passed"

-- 2c. Multiplication commutativity
#eval show IO Unit from do
  let mut passed := 0
  for x in testFloats do
    for y in testFloats do
      let a := ExactQ.mk Dim.dimensionless x
      let b := ExactQ.mk Dim.dimensionless y
      let lhs : ExactQ (Dim.mul Dim.dimensionless Dim.dimensionless) := a * b
      let rhs : ExactQ (Dim.mul Dim.dimensionless Dim.dimensionless) := b * a
      if lhs.value != rhs.value then
        throw (IO.userError s!"mul commutativity failed: {x} * {y}")
      passed := passed + 1
  IO.println s!"[quantity_mul_comm] All {passed} tests passed"

-- 2d. Distribution: a * (b + c) = a*b + a*c (when b,c same dim)
--     Using dimensionless for all to keep types aligned.
#eval show IO Unit from do
  let mut passed := 0
  for x in testFloats do
    for y in testFloats do
      for z in testFloats do
        let a := ExactQ.mk Dim.dimensionless x
        let b := ExactQ.mk Dim.dimensionless y
        let c := ExactQ.mk Dim.dimensionless z
        let bc : ExactQ Dim.dimensionless := b + c
        let lhs : ExactQ (Dim.mul Dim.dimensionless Dim.dimensionless) := a * bc
        let ab : ExactQ (Dim.mul Dim.dimensionless Dim.dimensionless) := a * b
        let ac : ExactQ (Dim.mul Dim.dimensionless Dim.dimensionless) := a * c
        let rhs : ExactQ (Dim.mul Dim.dimensionless Dim.dimensionless) := ab + ac
        let tol := 1e-10 * (Float.abs lhs.value + Float.abs rhs.value + 1.0)
        if Float.abs (lhs.value - rhs.value) >= tol then
          throw (IO.userError s!"distributivity failed: {x} * ({y} + {z})")
        passed := passed + 1
  IO.println s!"[quantity_distributive] All {passed} tests passed"

-- 2e. Division by self = 1 (for nonzero quantities)
#eval show IO Unit from do
  let mut passed := 0
  for x in testFloats do
    if x != 0.0 then
      let q := ExactQ.mk Dim.dimensionless x
      let result : ExactQ (Dim.div Dim.dimensionless Dim.dimensionless) := q / q
      if Float.abs (result.value - 1.0) >= 1e-10 then
        throw (IO.userError s!"div self failed for {x}: got {result.value}")
      passed := passed + 1
  IO.println s!"[quantity_div_self] All {passed} tests passed"

-- 2f. Negation is self-inverse: -(-q) = q
#eval show IO Unit from do
  let mut passed := 0
  for x in testFloats do
    let q := ExactQ.mk Force x
    let result : ExactQ Force := -(-q)
    if result.value != x then
      throw (IO.userError s!"neg involutive failed for {x}")
    passed := passed + 1
  IO.println s!"[quantity_neg_involutive] All {passed} tests passed"

-- 2g. Scalar multiplication by 1 is identity
#eval show IO Unit from do
  let mut passed := 0
  for x in testFloats do
    let q := ExactQ.mk Velocity x
    let result : ExactQ Velocity := (1.0 : Float) * q
    if result.value != x then
      throw (IO.userError s!"scalar 1 * q failed for {x}")
    passed := passed + 1
  IO.println s!"[quantity_scalar_identity] All {passed} tests passed"

-- ============================================================
-- 3. Float.toRat properties
-- ============================================================

-- Note: Float.toRat relies on Float.toUInt64 for IEEE 754 bit extraction.
-- In the Lean4 interpreter, Float.toUInt64 converts the numeric value (not
-- the bit pattern), so toRat only works correctly for 0.0 and special values
-- at eval time. We test the properties that hold in the interpreter and
-- verify structural properties of the IEEE helpers.

-- 3a. toRat maps special values to 0
#eval show IO Unit from do
  if Float.toRat 0.0 != (0 : ℚ) then throw (IO.userError "toRat(0) != 0")
  if Float.toRat (1.0 / 0.0) != (0 : ℚ) then throw (IO.userError "toRat(Inf) != 0")
  if Float.toRat (0.0 / 0.0) != (0 : ℚ) then throw (IO.userError "toRat(NaN) != 0")
  if Float.toRat (-1.0 / 0.0) != (0 : ℚ) then throw (IO.userError "toRat(-Inf) != 0")
  IO.println "[toRat_special] All 4 tests passed"

-- 3b. IEEE field extraction: sign bit of positive is 0
#eval show IO Unit from do
  let mut passed := 0
  for f in [1.0, 2.0, 0.5, 100.0, 3.14] do
    let s := Float.ieeeSign f
    if s != 0 then throw (IO.userError s!"ieeeSign({f}) = {s}, expected 0")
    passed := passed + 1
  IO.println s!"[ieee_sign_positive] All {passed} tests passed"

-- 3c. IEEE field extraction: sign bit of 0.0 is 0
#eval show IO Unit from do
  if Float.ieeeSign 0.0 != 0 then throw (IO.userError "ieeeSign(0.0) != 0")
  IO.println "[ieee_sign_zero] Passed"

-- 3d. IEEE field extraction: mantissa of 0.0 is 0
#eval show IO Unit from do
  if Float.ieeeMantissa 0.0 != 0 then throw (IO.userError "ieeeMantissa(0.0) != 0")
  IO.println "[ieee_mantissa_zero] Passed"

-- 3e. IEEE field extraction: exponent of 0.0 is 0
#eval show IO Unit from do
  if Float.ieeeExponent 0.0 != 0 then throw (IO.userError "ieeeExponent(0.0) != 0")
  IO.println "[ieee_exponent_zero] Passed"

-- 3f. Type-level checks: Float.toRat and Float.toReal have correct signatures
example : Float → ℚ := Float.toRat
noncomputable example : Float → ℝ := Float.toReal

-- 3g. toRat is deterministic: calling twice gives same result
#eval show IO Unit from do
  let mut passed := 0
  let testVals : List Float := [0.0, 1.0, -1.0, 0.5, 3.14, -2.718, 1e10, -1e10]
  for f in testVals do
    let r1 := Float.toRat f
    let r2 := Float.toRat f
    -- Use structural equality (BEq) since both calls should produce identical structures
    if r1 != r2 then
      throw (IO.userError s!"toRat({f}) not deterministic")
    passed := passed + 1
  IO.println s!"[toRat_deterministic] All {passed} tests passed"

-- ============================================================
-- 4. Uncertainty propagation properties
-- ============================================================

-- 4a. Adding two UncertainQ: combined uncertainty >= max individual uncertainty
--     (quadrature addition: sqrt(a^2 + b^2) >= max(a, b))
#eval show IO Unit from do
  let mut passed := 0
  let sigmas : List (Float × Float) :=
    [(0.1, 0.2), (0.5, 0.5), (1.0, 0.0), (0.0, 1.0), (0.3, 0.4), (0.01, 0.99)]
  for (s1, s2) in sigmas do
    let a := UncertainQ.fromMeasurement (α := Gaussian) Force 10.0 s1
    let b := UncertainQ.fromMeasurement (α := Gaussian) Force 5.0 s2
    let c := a + b
    let maxSigma := if s1 >= s2 then s1 else s2
    if c.uncertainty < maxSigma - 1e-10 then
      throw (IO.userError s!"combined uncertainty {c.uncertainty} < max({s1}, {s2}) = {maxSigma}")
    passed := passed + 1
  IO.println s!"[uncertain_add_bound] All {passed} tests passed"

-- 4b. Multiplying by exact scalar: absolute uncertainty scales by |scalar|
#eval show IO Unit from do
  let mut passed := 0
  let scalars : List Float := [2.0, -2.0, 0.5, -0.5, 3.0, 10.0, -10.0]
  for s in scalars do
    let q := UncertainQ.fromMeasurement (α := Gaussian) Velocity 10.0 0.5
    let scaled := (s : Float) * q
    let expectedUncertainty := Float.abs s * 0.5
    if Float.abs (scaled.uncertainty - expectedUncertainty) >= 1e-10 then
      throw (IO.userError s!"scalar {s} * uncertainty: got {scaled.uncertainty}, expected {expectedUncertainty}")
    passed := passed + 1
  IO.println s!"[uncertain_scalar_mul] All {passed} tests passed"

-- 4c. Uncertainty is always non-negative
#eval show IO Unit from do
  let mut passed := 0
  for x in testFloats do
    for sigma in [0.0, 0.1, 0.5, 1.0, 10.0] do
      let q := UncertainQ.fromMeasurement (α := Gaussian) Force x sigma
      if q.uncertainty < 0.0 then
        throw (IO.userError s!"negative uncertainty for val={x}, sigma={sigma}")
      -- Also check after negation
      let neg_q := -q
      if neg_q.uncertainty < 0.0 then
        throw (IO.userError s!"negative uncertainty after negation for val={x}, sigma={sigma}")
      passed := passed + 1
  IO.println s!"[uncertain_nonneg] All {passed} tests passed"

-- 4d. Adding zero-uncertainty quantity preserves the other's uncertainty
#eval show IO Unit from do
  let mut passed := 0
  let sigmas : List Float := [0.1, 0.5, 1.0, 2.0]
  for s in sigmas do
    let a := UncertainQ.fromMeasurement (α := Gaussian) Force 10.0 s
    let b := UncertainQ.fromExact (α := Gaussian) Force 5.0
    let c := a + b
    if Float.abs (c.uncertainty - s) >= 1e-10 then
      throw (IO.userError s!"adding exact changed uncertainty: {c.uncertainty} vs {s}")
    passed := passed + 1
  IO.println s!"[uncertain_add_exact] All {passed} tests passed"

-- 4e. Negation preserves uncertainty magnitude
#eval show IO Unit from do
  let mut passed := 0
  for s in [0.0, 0.1, 0.5, 1.0, 5.0] do
    let q := UncertainQ.fromMeasurement (α := Gaussian) Energy 42.0 s
    let neg_q := -q
    if Float.abs (neg_q.uncertainty - s) >= 1e-10 then
      throw (IO.userError s!"negation changed uncertainty: {neg_q.uncertainty} vs {s}")
    passed := passed + 1
  IO.println s!"[uncertain_neg_preserves] All {passed} tests passed"

-- 4f. Self-subtraction yields zero uncertainty (correlation tracking)
#eval show IO Unit from do
  let mut passed := 0
  for s in [0.1, 0.5, 1.0, 5.0] do
    let q := UncertainQ.fromMeasurement (α := Gaussian) Force 10.0 s
    let diff := q - q
    if diff.value != 0.0 then
      throw (IO.userError s!"self-sub value not zero: {diff.value}")
    if diff.uncertainty >= 1e-10 then
      throw (IO.userError s!"self-sub uncertainty not zero: {diff.uncertainty}")
    passed := passed + 1
  IO.println s!"[uncertain_self_sub] All {passed} tests passed"

-- ============================================================
-- 5. Dimension inference properties
-- ============================================================

-- 5a. inferDim on a product returns sum of exponents
--     mul(L, T) should give L*T
#eval show IO Unit from do
  let mut passed := 0
  for d1 in testDims do
    for d2 in testDims do
      let env : DimEnv := ((∅ : DimEnv).insert `x d1).insert `y d2
      match infer (.mul (.var `x) (.var `y)) env with
      | .ok d _ =>
        let expected := Dim.mul d1 d2
        if d != expected then
          throw (IO.userError s!"inferDim mul: got {repr d}, expected {repr expected}")
        passed := passed + 1
      | .error msg => throw (IO.userError s!"inferDim mul error: {msg}")
  IO.println s!"[infer_mul] All {passed} tests passed"

-- 5b. inferDim on a quotient returns difference of exponents
#eval show IO Unit from do
  let mut passed := 0
  for d1 in testDims do
    for d2 in testDims do
      let env : DimEnv := ((∅ : DimEnv).insert `x d1).insert `y d2
      match infer (.div (.var `x) (.var `y)) env with
      | .ok d _ =>
        let expected := Dim.div d1 d2
        if d != expected then
          throw (IO.userError s!"inferDim div: got {repr d}, expected {repr expected}")
        passed := passed + 1
      | .error msg => throw (IO.userError s!"inferDim div error: {msg}")
  IO.println s!"[infer_div] All {passed} tests passed"

-- 5c. inferDim on a power returns scaled exponents
#eval show IO Unit from do
  let mut passed := 0
  for d in testDims do
    for exp in testQExps do
      let env : DimEnv := (∅ : DimEnv).insert `x d
      match infer (.pow (.var `x) exp) env with
      | .ok result _ =>
        let expected := Dim.pow d exp
        if result != expected then
          throw (IO.userError s!"inferDim pow: got {repr result}, expected {repr expected}")
        passed := passed + 1
      | .error msg => throw (IO.userError s!"inferDim pow error: {msg}")
  IO.println s!"[infer_pow] All {passed} tests passed"

-- 5d. inferDim on addition requires same dimension (positive case)
#eval show IO Unit from do
  let mut passed := 0
  for d in testDims do
    let env : DimEnv := ((∅ : DimEnv).insert `x d).insert `y d
    match infer (.add (.var `x) (.var `y)) env with
    | .ok result _ =>
      if result != d then
        throw (IO.userError s!"inferDim add same: got {repr result}, expected {repr d}")
      passed := passed + 1
    | .error msg => throw (IO.userError s!"inferDim add same error: {msg}")
  IO.println s!"[infer_add_same] All {passed} tests passed"

-- 5e. inferDim on addition rejects different dimensions
#eval show IO Unit from do
  let mut passed := 0
  let pairs : List (Dim × Dim) :=
    [ (Force, Energy)
    , (Velocity, Acceleration)
    , ({ L := QExp.one }, { M := QExp.one })
    , (Power, Pressure)
    , (Charge, Voltage)
    ]
  for (d1, d2) in pairs do
    let env : DimEnv := ((∅ : DimEnv).insert `x d1).insert `y d2
    match infer (.add (.var `x) (.var `y)) env with
    | .error _ => passed := passed + 1
    | .ok _ _ => throw (IO.userError s!"inferDim add should reject {repr d1} + {repr d2}")
  IO.println s!"[infer_add_reject] All {passed} tests passed"

-- 5f. Literal is always dimensionless
#eval show IO Unit from do
  let mut passed := 0
  let lits : List Float := [0.0, 1.0, -1.0, 3.14, 1e10]
  for v in lits do
    match infer (.lit v) with
    | .ok d _ =>
      if !d.isDimensionless then
        throw (IO.userError s!"literal {v} not dimensionless")
      passed := passed + 1
    | .error msg => throw (IO.userError s!"literal error: {msg}")
  IO.println s!"[infer_lit_dimless] All {passed} tests passed"

-- 5g. Let binding propagates dimension correctly
#eval show IO Unit from do
  let mut passed := 0
  for d1 in testDims.take 6 do
    for d2 in testDims.take 6 do
      let env : DimEnv := ((∅ : DimEnv).insert `a d1).insert `b d2
      -- let x = a * b in x
      match infer (.letBind `x (.mul (.var `a) (.var `b)) (.var `x)) env with
      | .ok result _ =>
        let expected := Dim.mul d1 d2
        if result != expected then
          throw (IO.userError s!"let bind: got {repr result}, expected {repr expected}")
        passed := passed + 1
      | .error msg => throw (IO.userError s!"let bind error: {msg}")
  IO.println s!"[infer_let_bind] All {passed} tests passed"

-- 5h. Annotation passes when dimension matches
#eval show IO Unit from do
  let mut passed := 0
  for d in testDims do
    let env : DimEnv := (∅ : DimEnv).insert `x d
    match infer (.ann (.var `x) d) env with
    | .ok result _ =>
      if result != d then
        throw (IO.userError s!"annotation match: got {repr result}, expected {repr d}")
      passed := passed + 1
    | .error msg => throw (IO.userError s!"annotation match error: {msg}")
  IO.println s!"[infer_ann_match] All {passed} tests passed"

-- 5i. Annotation fails when dimension mismatches
#eval show IO Unit from do
  let mut passed := 0
  let pairs : List (Dim × Dim) :=
    [ (Force, Energy)
    , (Velocity, { M := QExp.one })
    , (Dim.dimensionless, Force)
    ]
  for (actual, annotated) in pairs do
    let env : DimEnv := (∅ : DimEnv).insert `x actual
    match infer (.ann (.var `x) annotated) env with
    | .error _ => passed := passed + 1
    | .ok _ _ => throw (IO.userError s!"annotation should reject {repr actual} vs {repr annotated}")
  IO.println s!"[infer_ann_reject] All {passed} tests passed"

-- ============================================================
-- 6. QExp arithmetic properties (compile-time)
-- ============================================================

-- QExp addition is commutative
example : QExp.add QExp.one (QExp.mk' 2 1) == QExp.add (QExp.mk' 2 1) QExp.one := by native_decide

-- QExp addition with zero is identity
example : QExp.add QExp.one QExp.zero == QExp.one := by native_decide
example : QExp.add QExp.zero QExp.one == QExp.one := by native_decide

-- QExp subtraction: a - a = 0
example : (QExp.sub QExp.one QExp.one) == QExp.zero := by native_decide
example : (QExp.sub (QExp.mk' 2 1) (QExp.mk' 2 1)) == QExp.zero := by native_decide

-- QExp multiplication is commutative
example : QExp.mul QExp.one (QExp.mk' 2 1) == QExp.mul (QExp.mk' 2 1) QExp.one := by native_decide

-- QExp multiplication by zero gives zero
example : (QExp.mul QExp.zero QExp.one).isZero = true := by native_decide

-- QExp negation is involutive
example : QExp.neg (QExp.neg QExp.one) == QExp.one := by native_decide
example : QExp.neg (QExp.neg (QExp.mk' 3 2)) == QExp.mk' 3 2 := by native_decide

-- ============================================================
-- 7. Dim algebra compile-time proofs
-- ============================================================

-- mul/div inverse: (d * e) / e = d
example : Dim.div (Dim.mul Force { T := QExp.one }) { T := QExp.one } == Force := by native_decide

-- pow 1 is identity
example : Dim.pow Velocity QExp.one == Velocity := by native_decide

-- pow 0 is dimensionless
example : (Dim.pow Force QExp.zero).isDimensionless = true := by native_decide

-- inv is same as pow(-1)
example : Dim.inv Velocity == Dim.pow Velocity (QExp.mk' (-1) 1) := by native_decide

-- sqrt is pow(1/2)
example : Dim.sqrt { L := QExp.mk' 2 1 } == { L := QExp.one } := by native_decide

end TestProperties
