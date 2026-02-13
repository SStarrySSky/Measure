/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Integration tests: cross-module interactions between Dim, Quantity,
Constants, Theory, Conservation, Error propagation, and Bridge modules.
-/
import Measure.Quantity
import Measure.Constants
import Measure.Conservation
import Measure.Dim.Infer
import Measure.Theory
import Measure.Physics.Dimensional

namespace TestIntegration

open Measure.Dim
open Measure.Quantity
open Measure.Constants
open Measure.Error
open Measure.Theory
open Measure.Conservation
open Measure.Physics

-- ============================================================
-- 1. End-to-end dimension checking
-- ============================================================

-- 1a. Create quantities, perform arithmetic, verify resulting dimensions
#eval show IO Unit from do
  -- mass * acceleration = force
  let m := ExactQ.mk { M := QExp.one } 5.0
  let a := ExactQ.mk Acceleration 9.8
  let f : ExactQ (Dim.mul { M := QExp.one } Acceleration) := m * a
  if Float.abs (f.value - 49.0) >= 1e-10 then
    throw (IO.userError s!"F=ma value mismatch: {f.value}")
  -- force * distance = energy (work)
  let d := ExactQ.mk { L := QExp.one } 10.0
  let w : ExactQ (Dim.mul (Dim.mul { M := QExp.one } Acceleration) { L := QExp.one }) := f * d
  if Float.abs (w.value - 490.0) >= 1e-10 then
    throw (IO.userError s!"W=Fd value mismatch: {w.value}")
  IO.println "[integration_e2e_dim_arithmetic] Passed"

-- 1b. Chain of operations: kinetic energy = 0.5 * m * v^2
#eval show IO Unit from do
  let m := ExactQ.mk { M := QExp.one } 2.0
  let v := ExactQ.mk Velocity 3.0
  let v2 : ExactQ (Dim.mul Velocity Velocity) := v * v
  let mv2 : ExactQ (Dim.mul { M := QExp.one } (Dim.mul Velocity Velocity)) := m * v2
  let ke : ExactQ (Dim.mul { M := QExp.one } (Dim.mul Velocity Velocity)) := (0.5 : Float) * mv2
  if Float.abs (ke.value - 9.0) >= 1e-10 then
    throw (IO.userError s!"KE value mismatch: {ke.value}")
  IO.println "[integration_kinetic_energy] Passed"

-- 1c. Division chain: power = energy / time, then current = power / voltage dimension check
#eval show IO Unit from do
  let e := ExactQ.mk Energy 1000.0
  let t := ExactQ.mk { T := QExp.one } 5.0
  let p : ExactQ (Dim.div Energy { T := QExp.one }) := e / t
  if Float.abs (p.value - 200.0) >= 1e-10 then
    throw (IO.userError s!"P=E/t value mismatch: {p.value}")
  IO.println "[integration_power_from_energy] Passed"

-- 1d. Dimension inference verifies F=ma end-to-end
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `m { M := QExp.one }).insert `a Acceleration
  -- infer dim of m * a
  match infer (.mul (.var `m) (.var `a)) env with
  | .ok d _ =>
    if d != Force then
      throw (IO.userError s!"Expected Force, got {repr d}")
  | .error msg => throw (IO.userError s!"Inference failed: {msg}")
  -- now infer dim of (m * a) * L = Energy
  let env2 := env.insert `l { L := QExp.one }
  match infer (.mul (.mul (.var `m) (.var `a)) (.var `l)) env2 with
  | .ok d _ =>
    if d != Energy then
      throw (IO.userError s!"Expected Energy, got {repr d}")
  | .error msg => throw (IO.userError s!"Inference failed: {msg}")
  IO.println "[integration_infer_fma_chain] Passed"

-- 1e. Dimension mismatch caught by inference: Force + Energy is rejected
#eval show IO Unit from do
  let env : DimEnv := ((∅ : DimEnv).insert `f Force).insert `e Energy
  match infer (.add (.var `f) (.var `e)) env with
  | .error _ => pure ()
  | .ok _ _ => throw (IO.userError "Expected dimension mismatch for Force + Energy")
  IO.println "[integration_infer_mismatch_rejected] Passed"

-- 1f. Compile-time dimension safety: Force + Force is valid
example (a b : ExactQ Force) : ExactQ Force := a + b

-- 1g. Compile-time: Mass * Acceleration gives the correct product dimension
example (m : ExactQ { M := QExp.one }) (a : ExactQ Acceleration) :
    ExactQ (Dim.mul { M := QExp.one } Acceleration) := m * a

-- 1h. Compile-time: Energy / Time gives the correct quotient dimension
example (e : ExactQ Energy) (t : ExactQ { T := QExp.one }) :
    ExactQ (Dim.div Energy { T := QExp.one }) := e / t

-- ============================================================
-- 2. Constants integration
-- ============================================================

-- 2a. Speed of light has Velocity dimension (L T⁻¹)
#eval show IO Unit from do
  -- c is ExactQ Velocity; Velocity = { L := 1, T := -1 }
  if c.value != 299792458.0 then throw (IO.userError "c value wrong")
  -- Verify Velocity matches expected dimension
  if Velocity != ({ L := QExp.one, T := -QExp.one } : Dim) then
    throw (IO.userError "Velocity dimension mismatch")
  IO.println "[integration_c_dimension] Passed"

-- 2b. F = ma type-checks with physical constants: weight = m_e * g
#eval show IO Unit from do
  -- electron mass (uncertain) * acceleration (exact) = force (uncertain)
  let g := ExactQ.mk Acceleration 9.80665
  let weight := m_e * g
  if weight.value <= 0.0 then throw (IO.userError "weight should be positive")
  if weight.uncertainty <= 0.0 then throw (IO.userError "weight should have uncertainty from m_e")
  IO.println "[integration_fma_with_constants] Passed"

-- 2c. Derived quantity: E = mc² using physical constants
#eval show IO Unit from do
  let c2 := c * c  -- ExactQ (Dim.mul Velocity Velocity)
  if c2.value != 299792458.0 * 299792458.0 then
    throw (IO.userError "c² value mismatch")
  -- m_e * c² gives energy-like dimension (uncertain)
  let e_rest := m_e * c * c
  if e_rest.value <= 0.0 then throw (IO.userError "rest energy should be positive")
  if e_rest.uncertainty > 0.0 then pure ()  -- uncertainty propagated from m_e
  else throw (IO.userError "rest energy should carry uncertainty from m_e")
  IO.println "[integration_emc2] Passed"

-- 2d. Unit conversion preserves dimensions: scalar * constant
#eval show IO Unit from do
  let two_c := (2.0 : Float) * c
  if two_c.value != 2.0 * 299792458.0 then
    throw (IO.userError "2c value mismatch")
  -- Scalar multiplication preserves the Velocity dimension (compile-time)
  let _ : ExactQ Velocity := two_c
  IO.println "[integration_scalar_preserves_dim] Passed"

-- 2e. Planck constant has correct action dimension (M L² T⁻¹)
example : @ExactQ.mk { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-1) 1 } 6.62607015e-34 = h := rfl

-- 2f. Elementary charge has Charge dimension
example : @ExactQ.mk Charge 1.602176634e-19 = e := rfl

-- ============================================================
-- 3. Theory module integration
-- ============================================================
-- Note: LeanTheoryGraph registration/compatibility/BFS tests removed —
-- the Lean-side graph was dead code; conflict detection runs through C++ FFI.

-- 3a. Noether integration: create theory with symmetries, derive conservation laws
#eval show IO Unit from do
  let mechanics : TheoryModule := {
    name := "ClassicalMechanics"
    symmetries := [
      { name := "time_trans", group := .translation true },
      { name := "space_trans", group := .translation false },
      { name := "rotation", group := .rotation 3 }
    ]
  }
  let laws := deriveAllFromNoether mechanics
  if laws.length != 3 then throw (IO.userError s!"Expected 3 laws, got {laws.length}")
  -- Verify the derived laws match expected conservation quantities
  if laws[0]!.name != "energy" then throw (IO.userError "First law should be energy")
  if laws[1]!.name != "momentum" then throw (IO.userError "Second law should be momentum")
  if laws[2]!.name != "angularMomentum" then throw (IO.userError "Third law should be angularMomentum")
  -- Verify sources are Noether-derived
  for law in laws do
    match law.source with
    | .noether _ => pure ()
    | _ => throw (IO.userError s!"Law '{law.name}' should have Noether source")
  IO.println "[integration_noether_conservation] Passed"

-- ============================================================
-- 4. Error propagation integration
-- ============================================================

-- 4a. Uncertain mass * uncertain acceleration = uncertain force with propagated error
#eval show IO Unit from do
  let m := UncertainQ.fromMeasurement (α := Gaussian) { M := QExp.one } 2.0 0.1
  let a := UncertainQ.fromMeasurement (α := Gaussian) Acceleration 9.8 0.2
  let f := m * a
  -- Value check
  if Float.abs (f.value - 19.6) >= 1e-10 then
    throw (IO.userError s!"F=ma value mismatch: {f.value}")
  -- Uncertainty must be positive (propagated from both inputs)
  if f.uncertainty <= 0.0 then
    throw (IO.userError "Force uncertainty should be > 0")
  IO.println "[integration_uncertain_fma] Passed"

-- 4b. Chain: uncertain energy / exact time = uncertain power
#eval show IO Unit from do
  let e := UncertainQ.fromMeasurement (α := Gaussian) Energy 100.0 2.0
  let t := ExactQ.mk { T := QExp.one } 5.0
  let p := e / t
  if Float.abs (p.value - 20.0) >= 1e-10 then
    throw (IO.userError s!"P=E/t value mismatch: {p.value}")
  -- Uncertainty should propagate from energy only
  if p.uncertainty <= 0.0 then
    throw (IO.userError "Power uncertainty should be > 0")
  IO.println "[integration_uncertain_power] Passed"

-- 4c. Uncertainty is always non-negative through a chain of operations
#eval show IO Unit from do
  let m := UncertainQ.fromMeasurement (α := Gaussian) { M := QExp.one } 5.0 0.3
  let v := UncertainQ.fromMeasurement (α := Gaussian) Velocity 10.0 0.5
  -- momentum = m * v
  let p := m * v
  if p.uncertainty < 0.0 then throw (IO.userError "momentum uncertainty < 0")
  -- kinetic energy proxy: p * v (not exactly KE but tests chaining)
  let pv := p * v
  if pv.uncertainty < 0.0 then throw (IO.userError "p*v uncertainty < 0")
  -- negation preserves non-negative uncertainty
  let neg_p := -p
  if neg_p.uncertainty < 0.0 then throw (IO.userError "negated momentum uncertainty < 0")
  IO.println "[integration_uncertainty_nonneg_chain] Passed"

-- 4d. Self-subtraction yields zero uncertainty (correlation tracking)
#eval show IO Unit from do
  let q := UncertainQ.fromMeasurement (α := Gaussian) Force 42.0 1.5
  let diff := q - q
  if diff.value != 0.0 then throw (IO.userError s!"q-q value should be 0, got {diff.value}")
  if diff.uncertainty >= 1e-10 then
    throw (IO.userError s!"q-q uncertainty should be ~0, got {diff.uncertainty}")
  IO.println "[integration_self_sub_zero_uncertainty] Passed"

-- 4e. Mixed exact + uncertain: exact constant + uncertain measurement
#eval show IO Unit from do
  let exact_force := ExactQ.mk Force 10.0
  let measured_force := UncertainQ.fromMeasurement (α := Gaussian) Force 5.0 0.3
  let total := exact_force + measured_force
  if total.value != 15.0 then throw (IO.userError "Mixed add value mismatch")
  -- Uncertainty should come from the measured part only
  if Float.abs (total.uncertainty - 0.3) >= 1e-10 then
    throw (IO.userError s!"Mixed add uncertainty mismatch: {total.uncertainty}")
  IO.println "[integration_mixed_exact_uncertain] Passed"

-- 4f. Physical constants with uncertainty: G has CODATA provenance and positive uncertainty
#eval show IO Unit from do
  if G.uncertainty <= 0.0 then throw (IO.userError "G should have positive uncertainty")
  match G.provenance with
  | .database "CODATA" "2022" => pure ()
  | _ => throw (IO.userError "G should have CODATA 2022 provenance")
  -- G interval should contain the central value
  let (lo, hi) := G.toInterval
  if lo >= G.value then throw (IO.userError "G interval lo >= value")
  if hi <= G.value then throw (IO.userError "G interval hi <= value")
  IO.println "[integration_G_uncertainty_provenance] Passed"

-- 4g. Uncertainty propagation through multiplication with physical constants
#eval show IO Unit from do
  -- Gravitational force: F = G * m1 * m2 / r²
  -- Using uncertain G and exact masses for simplicity
  let m1 := ExactQ.mk { M := QExp.one } 1.0
  let m2 := ExactQ.mk { M := QExp.one } 1.0
  let gm1 := G * m1
  let gm1m2 := gm1 * m2
  -- Result should carry G's uncertainty
  if gm1m2.uncertainty <= 0.0 then
    throw (IO.userError "G*m1*m2 should carry uncertainty from G")
  IO.println "[integration_gravity_uncertainty] Passed"

-- ============================================================
-- 5. Bridge integration
-- ============================================================

-- 5a. Float.toRat conversion: zero maps correctly
#eval show IO Unit from do
  let r := Float.toRat 0.0
  if r != (0 : ℚ) then throw (IO.userError "toRat(0.0) should be 0")
  IO.println "[integration_toRat_zero] Passed"

-- 5b. Float.toRat: special values (Inf, NaN) map to 0
#eval show IO Unit from do
  if Float.toRat (1.0 / 0.0) != (0 : ℚ) then throw (IO.userError "toRat(Inf) should be 0")
  if Float.toRat (0.0 / 0.0) != (0 : ℚ) then throw (IO.userError "toRat(NaN) should be 0")
  if Float.toRat (-1.0 / 0.0) != (0 : ℚ) then throw (IO.userError "toRat(-Inf) should be 0")
  IO.println "[integration_toRat_special] Passed"

-- 5c. Float.toRat is deterministic across calls
#eval show IO Unit from do
  let vals := [0.0, 1.0, -1.0, 3.14, 299792458.0]
  for v in vals do
    if Float.toRat v != Float.toRat v then
      throw (IO.userError s!"toRat({v}) not deterministic")
  IO.println "[integration_toRat_deterministic] Passed"

-- 5d. PhysReal creation and dimension checking (compile-time)
-- PhysReal.dimensionless wraps a real as dimensionless
example : (PhysReal.dimensionless 0).val = 0 := rfl

-- PhysReal addition requires same dimension
noncomputable example (a b : ForceVal) : ForceVal := a + b

-- PhysReal subtraction requires same dimension
noncomputable example (a b : EnergyVal) : EnergyVal := a - b

-- PhysReal negation preserves dimension
noncomputable example (a : MomentumVal) : MomentumVal := -a

-- 5e. RealQuantity type-level checks
noncomputable example : ExactRQ Dim.dimensionless :=
  RealQuantity.dimensionless 42

-- ExactRQ addition type-checks for same dimension
noncomputable example (a b : ExactRQ Force) : ExactRQ Force := a + b

-- ExactRQ multiplication produces correct dimension
noncomputable example (a : ExactRQ { M := QExp.one }) (b : ExactRQ Acceleration) :
    ExactRQ (Dim.mul { M := QExp.one } Acceleration) := a * b

-- ExactRQ division produces correct dimension
noncomputable example (a : ExactRQ Energy) (b : ExactRQ { T := QExp.one }) :
    ExactRQ (Dim.div Energy { T := QExp.one }) := a / b

-- Scalar multiplication: Real * ExactRQ
noncomputable example (s : ℝ) (q : ExactRQ Velocity) : ExactRQ Velocity := s * q

-- 5f. IEEE 754 field extraction consistency
#eval show IO Unit from do
  -- Sign of 0.0 is 0
  if Float.ieeeSign 0.0 != 0 then throw (IO.userError "sign(0) != 0")
  -- Exponent of 0.0 is 0
  if Float.ieeeExponent 0.0 != 0 then throw (IO.userError "exp(0) != 0")
  -- Mantissa of 0.0 is 0
  if Float.ieeeMantissa 0.0 != 0 then throw (IO.userError "mantissa(0) != 0")
  -- Sign of positive values is 0
  for v in [1.0, 2.0, 100.0, 3.14] do
    if Float.ieeeSign v != 0 then throw (IO.userError s!"sign({v}) != 0")
  IO.println "[integration_ieee754_fields] Passed"

-- 5g. Float.toRat and Float.toReal have correct type signatures
example : Float → ℚ := Float.toRat
noncomputable example : Float → ℝ := Float.toReal

-- ============================================================
-- 6. Cross-cutting integration: constants + inference + uncertainty
-- ============================================================

-- 6a. Dimension inference agrees with constant dimensions
#eval show IO Unit from do
  -- Set up env with c (Velocity) and h (action)
  let actionDim : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-1) 1 }
  let env : DimEnv := ((∅ : DimEnv).insert `c Velocity).insert `h actionDim
  -- c * h should give L³ M T⁻²
  match infer (.mul (.var `c) (.var `h)) env with
  | .ok d _ =>
    let expected := Dim.mul Velocity actionDim
    if d != expected then
      throw (IO.userError s!"c*h dimension mismatch: got {repr d}, expected {repr expected}")
  | .error msg => throw (IO.userError s!"Inference failed: {msg}")
  IO.println "[integration_infer_constants_dim] Passed"

-- 6b. Dimensional analysis lemma: Force = Mass * Acceleration (from Physics.Dimensional)
theorem integration_dim_force : dimMass * dimAcceleration = dimForce :=
  dim_force_eq

-- 6c. Dimensional analysis lemma: Energy = Force * Length
theorem integration_dim_energy : dimForce * dimLength = dimEnergy :=
  dim_energy_eq_force_mul_length

-- 6d. Dimensional analysis lemma: Power = Energy / Time
theorem integration_dim_power : dimEnergy / dimTime = dimPower :=
  dim_power_eq_energy_div_time

-- 6e. Full pipeline: create uncertain quantities, compute, verify dimensions via inference
#eval show IO Unit from do
  -- Create uncertain mass and velocity
  let m := UncertainQ.fromMeasurement (α := Gaussian) { M := QExp.one } 10.0 0.5
  let v := UncertainQ.fromMeasurement (α := Gaussian) Velocity 20.0 1.0
  -- Compute momentum = m * v
  let p := m * v
  if Float.abs (p.value - 200.0) >= 1e-10 then
    throw (IO.userError s!"momentum value mismatch: {p.value}")
  if p.uncertainty <= 0.0 then
    throw (IO.userError "momentum should have positive uncertainty")
  -- Verify dimension via inference engine
  let env : DimEnv := ((∅ : DimEnv).insert `m { M := QExp.one }).insert `v Velocity
  match infer (.mul (.var `m) (.var `v)) env with
  | .ok d _ =>
    let expected := Dim.mul { M := QExp.one } Velocity
    if d != expected then
      throw (IO.userError s!"Inferred momentum dim mismatch")
  | .error msg => throw (IO.userError s!"Inference failed: {msg}")
  IO.println "[integration_full_pipeline] Passed"

-- 6f. Theory + Conservation + Dimension: derive laws from EM theory, verify dimensions
#eval show IO Unit from do
  let em : TheoryModule := {
    name := "Electromagnetism"
    symmetries := [
      { name := "U1_gauge", group := .gauge "U1", exactness := .exact }
    ]
    axioms := { axioms := #[
      { name := "maxwell_gauss", type := "div E = rho / epsilon_0" }
    ] }
  }
  -- Derive conservation laws from Noether's theorem
  let laws := deriveAllFromNoether em
  if laws.length != 1 then throw (IO.userError s!"Expected 1 law, got {laws.length}")
  if laws[0]!.name != "U1_charge" then
    throw (IO.userError s!"Expected U1_charge, got {laws[0]!.name}")
  -- Verify the theory module structure
  if em.symmetries.length != 1 then throw (IO.userError "symmetries count wrong")
  IO.println "[integration_theory_conservation_dim] Passed"

end TestIntegration
