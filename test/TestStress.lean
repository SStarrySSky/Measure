/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Stress tests for the dimension system: deep nesting, fractional exponents,
boundary values, commutativity/associativity, and round-trip properties.
-/
import Measure.Quantity

namespace TestStress

open Measure.Dim
open Measure.Quantity

-- ============================================================
-- 1. Deep nesting tests
-- ============================================================

-- 1a. Chain of 12 multiplications: L^1 * L^1 * ... * L^1 = L^12
#eval show IO Unit from do
  let l : Dim := { L := QExp.one }
  let mut acc := l
  for _ in List.range 11 do
    acc := Dim.mul acc l
  let expected : Dim := { L := QExp.mk' 12 1 }
  if acc != expected then
    throw (IO.userError s!"12x mul chain: got {repr acc}, expected {repr expected}")
  IO.println "[stress_deep_mul_chain] Passed"

-- 1b. Chain of 12 divisions: start at L^12, divide by L 12 times = dimensionless
#eval show IO Unit from do
  let l : Dim := { L := QExp.one }
  let mut acc : Dim := { L := QExp.mk' 12 1 }
  for _ in List.range 12 do
    acc := Dim.div acc l
  if !acc.isDimensionless then
    throw (IO.userError s!"12x div chain: got {repr acc}, expected dimensionless")
  IO.println "[stress_deep_div_chain] Passed"

-- 1c. Mixed operations: (L * M / T * I / Theta * N / J * L / M * T / I * Theta)
--     Track each step manually to verify accumulation
#eval show IO Unit from do
  let dimL : Dim := { L := QExp.one }
  let dimM : Dim := { M := QExp.one }
  let dimT : Dim := { T := QExp.one }
  let dimI : Dim := { I := QExp.one }
  let dimTh : Dim := { Θ := QExp.one }
  let dimN : Dim := { N := QExp.one }
  let dimJ : Dim := { J := QExp.one }
  -- Build: L * M / T * I / Theta * N / J * L / M * T / I * Theta
  let mut acc := dimL
  acc := Dim.mul acc dimM      -- L*M
  acc := Dim.div acc dimT      -- L*M*T^-1
  acc := Dim.mul acc dimI      -- L*M*T^-1*I
  acc := Dim.div acc dimTh     -- L*M*T^-1*I*Theta^-1
  acc := Dim.mul acc dimN      -- L*M*T^-1*I*Theta^-1*N
  acc := Dim.div acc dimJ      -- L*M*T^-1*I*Theta^-1*N*J^-1
  acc := Dim.mul acc dimL      -- L^2*M*T^-1*I*Theta^-1*N*J^-1
  acc := Dim.div acc dimM      -- L^2*T^-1*I*Theta^-1*N*J^-1
  acc := Dim.mul acc dimT      -- L^2*I*Theta^-1*N*J^-1
  acc := Dim.div acc dimI      -- L^2*Theta^-1*N*J^-1
  acc := Dim.mul acc dimTh     -- L^2*N*J^-1
  let expected : Dim := { L := QExp.mk' 2 1, N := QExp.one, J := QExp.mk' (-1) 1 }
  if acc != expected then
    throw (IO.userError s!"mixed ops chain: got {repr acc}, expected {repr expected}")
  IO.println "[stress_mixed_ops_chain] Passed"

-- 1d. Deep nesting with all 7 SI base dimensions simultaneously
#eval show IO Unit from do
  let full : Dim :=
    { L := QExp.one, M := QExp.one, T := QExp.one
    , I := QExp.one, Θ := QExp.one, N := QExp.one, J := QExp.one }
  let mut acc := full
  for _ in List.range 9 do
    acc := Dim.mul acc full
  -- After 10 multiplications: each exponent should be 10
  let ten := QExp.mk' 10 1
  let expected : Dim := { L := ten, M := ten, T := ten, I := ten, Θ := ten, N := ten, J := ten }
  if acc != expected then
    throw (IO.userError s!"deep 7-dim mul: got {repr acc}")
  IO.println "[stress_deep_7dim_mul] Passed"

-- ============================================================
-- 2. Fractional exponent tests
-- ============================================================

-- 2a. QExp with large denominators: 1/7, 3/11
example : (QExp.mk' 1 7).den = 7 := by native_decide
example : (QExp.mk' 1 7).num = 1 := by native_decide
example : (QExp.mk' 3 11).den = 11 := by native_decide
example : (QExp.mk' 3 11).num = 3 := by native_decide

-- 2b. QExp arithmetic with different denominators: 1/7 + 3/11 = 32/77
example : (QExp.mk' 1 7 + QExp.mk' 3 11) == QExp.mk' 32 77 := by native_decide

-- 2c. QExp subtraction with different denominators: 3/11 - 1/7 = 10/77
example : (QExp.mk' 3 11 - QExp.mk' 1 7) == QExp.mk' 10 77 := by native_decide

-- 2d. QExp multiplication with different denominators: (1/7) * (3/11) = 3/77
example : (QExp.mk' 1 7 * QExp.mk' 3 11) == QExp.mk' 3 77 := by native_decide

-- 2e. QExp normalization: 2/4 should equal 1/2
example : QExp.mk' 2 4 == QExp.mk' 1 2 := by native_decide

-- 2f. QExp normalization: 6/9 should equal 2/3
example : QExp.mk' 6 9 == QExp.mk' 2 3 := by native_decide

-- 2g. QExp normalization: 15/25 should equal 3/5
example : QExp.mk' 15 25 == QExp.mk' 3 5 := by native_decide

-- 2h. QExp normalization: -4/6 should equal -2/3
example : QExp.mk' (-4) 6 == QExp.mk' (-2) 3 := by native_decide

-- 2i. QExp normalization: 0/5 should equal zero
example : (QExp.mk' 0 5).isZero = true := by native_decide

-- 2j. Dim.pow with fractional exponent: L^(1/3) then cubed = L
example : Dim.pow (Dim.pow { L := QExp.one : Dim } (QExp.mk' 1 3)) (QExp.mk' 3 1)
        == ({ L := QExp.one } : Dim) := by native_decide

-- 2k. Dim.pow with 1/7 exponent: L^(1/7) raised to 7 = L
example : Dim.pow (Dim.pow { L := QExp.one : Dim } (QExp.mk' 1 7)) (QExp.mk' 7 1)
        == ({ L := QExp.one } : Dim) := by native_decide

-- 2l. Fractional exponent arithmetic across dimensions
#eval show IO Unit from do
  -- (L^(1/3) * M^(2/5))^15 should give L^5 * M^6
  let d : Dim := { L := QExp.mk' 1 3, M := QExp.mk' 2 5 }
  let result := Dim.pow d (QExp.mk' 15 1)
  let expected : Dim := { L := QExp.mk' 5 1, M := QExp.mk' 6 1 }
  if result != expected then
    throw (IO.userError s!"fractional pow: got {repr result}, expected {repr expected}")
  IO.println "[stress_fractional_pow] Passed"

-- 2m. Large denominator stress: 1/97 + 1/101
#eval show IO Unit from do
  let a := QExp.mk' 1 97
  let b := QExp.mk' 1 101
  let sum := a + b
  -- 1/97 + 1/101 = (101 + 97) / (97*101) = 198/9797 = 198/9797
  -- gcd(198, 9797) = 1, so 198/9797
  let expected := QExp.mk' 198 9797
  if sum != expected then
    throw (IO.userError s!"large denom add: got num={sum.num} den={sum.den}, expected num=198 den=9797")
  IO.println "[stress_large_denom_add] Passed"

-- ============================================================
-- 3. Boundary value tests
-- ============================================================

-- 3a. Zero dimension (dimensionless) operations
example : Dim.mul Dim.dimensionless Dim.dimensionless == Dim.dimensionless := by native_decide
example : Dim.div Dim.dimensionless Dim.dimensionless == Dim.dimensionless := by native_decide
example : Dim.inv Dim.dimensionless == Dim.dimensionless := by native_decide
example : Dim.pow Dim.dimensionless (QExp.mk' 42 1) == Dim.dimensionless := by native_decide
example : Dim.sqrt Dim.dimensionless == Dim.dimensionless := by native_decide

-- 3b. Very large exponents
#eval show IO Unit from do
  let bigExp := QExp.mk' 1000 1
  let d : Dim := { L := QExp.one }
  let result := Dim.pow d bigExp
  let expected : Dim := { L := QExp.mk' 1000 1 }
  if result != expected then
    throw (IO.userError s!"large exponent: got {repr result}")
  IO.println "[stress_large_exponent] Passed"

-- 3c. Very large negative exponents
#eval show IO Unit from do
  let bigNegExp := QExp.mk' (-1000) 1
  let d : Dim := { T := QExp.one }
  let result := Dim.pow d bigNegExp
  let expected : Dim := { T := QExp.mk' (-1000) 1 }
  if result != expected then
    throw (IO.userError s!"large neg exponent: got {repr result}")
  IO.println "[stress_large_neg_exponent] Passed"

-- 3d. Negative exponents: T^(-2) is standard for acceleration
example : Acceleration.T == QExp.mk' (-2) 1 := by native_decide

-- 3e. Pow by zero always gives dimensionless
#eval show IO Unit from do
  let dims : List Dim :=
    [ Force, Energy, Power, Velocity, Acceleration, Pressure, Charge, Voltage, Resistance ]
  let mut passed := 0
  for d in dims do
    let result := Dim.pow d QExp.zero
    if !result.isDimensionless then
      throw (IO.userError s!"pow 0 not dimensionless for {repr d}")
    passed := passed + 1
  IO.println s!"[stress_pow_zero] All {passed} tests passed"

-- 3f. Pow by one is identity
#eval show IO Unit from do
  let dims : List Dim :=
    [ Force, Energy, Power, Velocity, Acceleration, Pressure, Charge, Voltage, Resistance ]
  let mut passed := 0
  for d in dims do
    let result := Dim.pow d QExp.one
    if result != d then
      throw (IO.userError s!"pow 1 not identity for {repr d}")
    passed := passed + 1
  IO.println s!"[stress_pow_one] All {passed} tests passed"

-- 3g. QExp with num=0 is always zero regardless of denominator
example : (QExp.mk' 0 1).isZero = true := by native_decide
example : (QExp.mk' 0 100).isZero = true := by native_decide
example : (QExp.mk' 0 9999).isZero = true := by native_decide

-- ============================================================
-- 4. Commutativity / associativity verification
-- ============================================================

-- 4a. dim_mul commutativity for all 7 SI base dimensions (pairwise)
#eval show IO Unit from do
  let bases : List Dim :=
    [ { L := QExp.one }
    , { M := QExp.one }
    , { T := QExp.one }
    , { I := QExp.one }
    , { Θ := QExp.one }
    , { N := QExp.one }
    , { J := QExp.one }
    ]
  let mut passed := 0
  for a in bases do
    for b in bases do
      let lhs := Dim.mul a b
      let rhs := Dim.mul b a
      if lhs != rhs then
        throw (IO.userError s!"SI commutativity failed: {repr a} * {repr b}")
      passed := passed + 1
  IO.println s!"[stress_si_commutativity] All {passed} (7x7=49) tests passed"

-- 4b. dim_mul commutativity compile-time proofs for each SI pair with L
example : Dim.mul { L := QExp.one } { M := QExp.one }
        == Dim.mul { M := QExp.one } { L := QExp.one } := by native_decide
example : Dim.mul { L := QExp.one } { T := QExp.one }
        == Dim.mul { T := QExp.one } { L := QExp.one } := by native_decide
example : Dim.mul { L := QExp.one } { I := QExp.one }
        == Dim.mul { I := QExp.one } { L := QExp.one } := by native_decide
example : Dim.mul { L := QExp.one } { Θ := QExp.one }
        == Dim.mul { Θ := QExp.one } { L := QExp.one } := by native_decide
example : Dim.mul { L := QExp.one } { N := QExp.one }
        == Dim.mul { N := QExp.one } { L := QExp.one } := by native_decide
example : Dim.mul { L := QExp.one } { J := QExp.one }
        == Dim.mul { J := QExp.one } { L := QExp.one } := by native_decide

-- 4c. dim_mul associativity with derived dimensions
example : Dim.mul (Dim.mul Force { L := QExp.one }) { T := QExp.mk' (-1) 1 }
        == Dim.mul Force (Dim.mul { L := QExp.one } { T := QExp.mk' (-1) 1 }) := by native_decide

example : Dim.mul (Dim.mul Velocity { M := QExp.one }) { T := QExp.mk' (-1) 1 }
        == Dim.mul Velocity (Dim.mul { M := QExp.one } { T := QExp.mk' (-1) 1 }) := by native_decide

-- 4d. dim_mul associativity exhaustive over SI bases (7^3 = 343 triples)
#eval show IO Unit from do
  let bases : List Dim :=
    [ { L := QExp.one }
    , { M := QExp.one }
    , { T := QExp.one }
    , { I := QExp.one }
    , { Θ := QExp.one }
    , { N := QExp.one }
    , { J := QExp.one }
    ]
  let mut passed := 0
  for a in bases do
    for b in bases do
      for c in bases do
        let lhs := Dim.mul (Dim.mul a b) c
        let rhs := Dim.mul a (Dim.mul b c)
        if lhs != rhs then
          throw (IO.userError s!"SI associativity failed")
        passed := passed + 1
  IO.println s!"[stress_si_associativity] All {passed} (7^3=343) tests passed"

-- 4e. dim_div inverse property: (a * b) / b = a
#eval show IO Unit from do
  let dims : List Dim :=
    [ { L := QExp.one }
    , { M := QExp.one }
    , { T := QExp.one }
    , Force
    , Energy
    , Velocity
    , Acceleration
    , Power
    , Pressure
    ]
  let mut passed := 0
  for a in dims do
    for b in dims do
      let product := Dim.mul a b
      let result := Dim.div product b
      if result != a then
        throw (IO.userError s!"div inverse failed: ({repr a} * {repr b}) / {repr b} != {repr a}")
      passed := passed + 1
  IO.println s!"[stress_div_inverse] All {passed} tests passed"

-- 4f. dim_div inverse property: a / b * b = a
#eval show IO Unit from do
  let dims : List Dim :=
    [ { L := QExp.one }
    , { M := QExp.one }
    , Force
    , Energy
    , Velocity
    ]
  let mut passed := 0
  for a in dims do
    for b in dims do
      let quotient := Dim.div a b
      let result := Dim.mul quotient b
      if result != a then
        throw (IO.userError s!"mul inverse failed: ({repr a} / {repr b}) * {repr b} != {repr a}")
      passed := passed + 1
  IO.println s!"[stress_mul_inverse] All {passed} tests passed"

-- ============================================================
-- 5. Round-trip tests
-- ============================================================

-- 5a. Create a dimension, multiply by its inverse, verify dimensionless
#eval show IO Unit from do
  let dims : List Dim :=
    [ { L := QExp.one }
    , { M := QExp.mk' 2 1 }
    , Force
    , Energy
    , Power
    , Velocity
    , Acceleration
    , Pressure
    , Charge
    , Voltage
    , Resistance
    , Capacitance
    , Inductance
    , MagneticFlux
    , MagneticFluxDens
    , { L := QExp.mk' 1 3, M := QExp.mk' (-2) 5, T := QExp.mk' 7 11 }
    ]
  let mut passed := 0
  for d in dims do
    let inv := Dim.inv d
    let result := Dim.mul d inv
    if !result.isDimensionless then
      throw (IO.userError s!"d * inv(d) not dimensionless for {repr d}: got {repr result}")
    passed := passed + 1
  IO.println s!"[stress_mul_inv_roundtrip] All {passed} tests passed"

-- 5b. Compile-time: Force * inv(Force) = dimensionless
example : (Dim.mul Force (Dim.inv Force)).isDimensionless = true := by native_decide
example : (Dim.mul Energy (Dim.inv Energy)).isDimensionless = true := by native_decide
example : (Dim.mul Velocity (Dim.inv Velocity)).isDimensionless = true := by native_decide

-- 5c. inv(inv(d)) = d for derived dimensions
example : Dim.inv (Dim.inv Force) == Force := by native_decide
example : Dim.inv (Dim.inv Energy) == Energy := by native_decide
example : Dim.inv (Dim.inv Voltage) == Voltage := by native_decide

-- 5d. Quantity round-trip: create ExactQ, extract value, verify unchanged
#eval show IO Unit from do
  let testVals : List Float := [0.0, 1.0, -1.0, 3.14, -2.718, 1e10, -1e10, 1e-15, -1e-15]
  let mut passed := 0
  for v in testVals do
    let q := ExactQ.mk Force v
    if q.value != v then
      throw (IO.userError s!"ExactQ round-trip failed for {v}")
    passed := passed + 1
  IO.println s!"[stress_exactq_roundtrip] All {passed} tests passed"

-- 5e. Quantity mul/div round-trip: (q * r) / r has same value as q (for nonzero r)
#eval show IO Unit from do
  let mut passed := 0
  let vals : List Float := [1.0, -1.0, 2.5, -3.7, 100.0, 0.001]
  for x in vals do
    for y in vals do
      let qx := ExactQ.mk { L := QExp.one } x
      let qy := ExactQ.mk { T := QExp.one } y
      let product : ExactQ (Dim.mul { L := QExp.one } { T := QExp.one }) := qx * qy
      let result : ExactQ (Dim.div (Dim.mul { L := QExp.one } { T := QExp.one }) { T := QExp.one }) := product / qy
      let tol := 1e-10 * (Float.abs x + 1.0)
      if Float.abs (result.value - x) >= tol then
        throw (IO.userError s!"quantity mul/div roundtrip failed: ({x} * {y}) / {y} = {result.value}")
      passed := passed + 1
  IO.println s!"[stress_quantity_mul_div_roundtrip] All {passed} tests passed"

-- 5f. Dimension pow/root round-trip: pow(d, n) then pow(result, 1/n) = d
#eval show IO Unit from do
  let dims : List Dim :=
    [ { L := QExp.one }
    , { M := QExp.one }
    , Force
    , Energy
    ]
  -- Use pre-built (pow_exp, root_exp) pairs to avoid omega issues with Int.toNat
  let expPairs : List (QExp × QExp) :=
    [ (QExp.mk' 2 1, QExp.mk' 1 2)
    , (QExp.mk' 3 1, QExp.mk' 1 3)
    , (QExp.mk' 4 1, QExp.mk' 1 4)
    , (QExp.mk' 5 1, QExp.mk' 1 5)
    ]
  let mut passed := 0
  for d in dims do
    for (powExp, rootExp) in expPairs do
      let powered := Dim.pow d powExp
      let rooted := Dim.pow powered rootExp
      if rooted != d then
        throw (IO.userError s!"pow/root roundtrip failed for {repr d}")
      passed := passed + 1
  IO.println s!"[stress_pow_root_roundtrip] All {passed} tests passed"

-- 5g. QExp add/sub round-trip: (a + b) - b = a
#eval show IO Unit from do
  let qexps : List QExp :=
    [ QExp.zero, QExp.one, QExp.mk' (-1) 1, QExp.mk' 2 1
    , QExp.mk' 1 2, QExp.mk' 3 7, QExp.mk' (-5) 3, QExp.mk' 11 13 ]
  let mut passed := 0
  for a in qexps do
    for b in qexps do
      let sum := a + b
      let result := sum - b
      if result != a then
        throw (IO.userError s!"QExp add/sub roundtrip: ({a.num}/{a.den} + {b.num}/{b.den}) - {b.num}/{b.den} != {a.num}/{a.den}")
      passed := passed + 1
  IO.println s!"[stress_qexp_add_sub_roundtrip] All {passed} tests passed"

-- ============================================================
-- 6. Additional edge cases
-- ============================================================

-- 6a. Repeated squaring: L -> L^2 -> L^4 -> L^8 -> L^16
#eval show IO Unit from do
  let mut d : Dim := { L := QExp.one }
  let two := QExp.mk' 2 1
  for _ in List.range 4 do
    d := Dim.pow d two
  let expected : Dim := { L := QExp.mk' 16 1 }
  if d != expected then
    throw (IO.userError s!"repeated squaring: got {repr d}")
  IO.println "[stress_repeated_squaring] Passed"

-- 6b. Alternating mul/inv should cancel: d * inv(d) * d * inv(d) * ... = dimensionless
#eval show IO Unit from do
  let d := Force
  let mut acc := Dim.dimensionless
  for _ in List.range 50 do
    acc := Dim.mul acc d
    acc := Dim.mul acc (Dim.inv d)
  if !acc.isDimensionless then
    throw (IO.userError s!"alternating mul/inv not dimensionless: {repr acc}")
  IO.println "[stress_alternating_mul_inv] Passed"

-- 6c. Dimension with all negative exponents
#eval show IO Unit from do
  let neg : Dim :=
    { L := QExp.mk' (-1) 1, M := QExp.mk' (-1) 1, T := QExp.mk' (-1) 1
    , I := QExp.mk' (-1) 1, Θ := QExp.mk' (-1) 1, N := QExp.mk' (-1) 1
    , J := QExp.mk' (-1) 1 }
  let pos : Dim :=
    { L := QExp.one, M := QExp.one, T := QExp.one
    , I := QExp.one, Θ := QExp.one, N := QExp.one, J := QExp.one }
  let result := Dim.mul neg pos
  if !result.isDimensionless then
    throw (IO.userError s!"all-neg * all-pos not dimensionless: {repr result}")
  -- Also verify inv gives the positive version
  let invNeg := Dim.inv neg
  if invNeg != pos then
    throw (IO.userError s!"inv(all-neg) != all-pos")
  IO.println "[stress_all_negative_exponents] Passed"

-- 6d. QExp with equal num and den normalizes to 1
example : QExp.mk' 7 7 == QExp.one := by native_decide
example : QExp.mk' 13 13 == QExp.one := by native_decide
example : QExp.mk' 100 100 == QExp.one := by native_decide

-- 6e. Dim.sqrt round-trip: sqrt(d^2) = d (for non-negative exponents)
example : Dim.sqrt (Dim.pow { L := QExp.one : Dim } (QExp.mk' 2 1))
        == ({ L := QExp.one } : Dim) := by native_decide

example : Dim.sqrt (Dim.pow { L := QExp.mk' 2 1, T := QExp.mk' (-4) 1 : Dim } (QExp.mk' 2 1))
        == ({ L := QExp.mk' 2 1, T := QExp.mk' (-4) 1 } : Dim) := by native_decide

end TestStress
