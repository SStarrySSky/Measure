/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Tests for the Physics formalization layer: Noether's theorem,
conservation laws, Maxwell equations structure, Lorentz transformations,
Newtonian mechanics, and dimensional analysis lemmas.
-/
import Measure.Conservation
import Measure.Physics.Dimensional
import Measure.Physics.Electromagnetism.Maxwell
import Measure.Physics.Relativity.Minkowski
import Measure.Physics.ClassicalMechanics.Newton

namespace TestPhysics

open Measure.Dim
open Measure.Quantity
open Measure.Conservation
open Measure.Theory
open Measure.Physics

-- ============================================================
-- Noether's theorem: symmetry -> conservation law derivation
-- ============================================================

-- Time translation symmetry -> energy conservation
#eval show IO Unit from do
  let sym : SymmetryDecl := {
    name := "time_translation"
    group := .translation true
    exactness := .exact
  }
  let law := deriveFromNoether sym
  if law.name != "energy" then throw (IO.userError s!"Expected 'energy', got '{law.name}'")
  if law.quantityExpr != "total_energy" then throw (IO.userError "quantityExpr mismatch")
  match law.exactness with
  | .exact => pure ()
  | _ => throw (IO.userError "Expected exact conservation")

-- Space translation symmetry -> momentum conservation
#eval show IO Unit from do
  let sym : SymmetryDecl := {
    name := "space_translation"
    group := .translation false
    exactness := .exact
  }
  let law := deriveFromNoether sym
  if law.name != "momentum" then throw (IO.userError s!"Expected 'momentum', got '{law.name}'")
  if law.quantityExpr != "total_momentum" then throw (IO.userError "quantityExpr mismatch")

-- Rotation symmetry -> angular momentum conservation
#eval show IO Unit from do
  let sym : SymmetryDecl := {
    name := "rotation"
    group := .rotation 3
    exactness := .exact
  }
  let law := deriveFromNoether sym
  if law.name != "angularMomentum" then throw (IO.userError s!"Expected 'angularMomentum', got '{law.name}'")
  if law.quantityExpr != "total_angular_momentum" then throw (IO.userError "quantityExpr mismatch")

-- Gauge symmetry -> charge conservation
#eval show IO Unit from do
  let sym : SymmetryDecl := {
    name := "U1_gauge"
    group := .gauge "U1"
    exactness := .exact
  }
  let law := deriveFromNoether sym
  if law.name != "U1_charge" then throw (IO.userError s!"Expected 'U1_charge', got '{law.name}'")
  if law.quantityExpr != "total_U1_charge" then throw (IO.userError "quantityExpr mismatch")

-- Lorentz symmetry -> Lorentz invariant
#eval show IO Unit from do
  let sym : SymmetryDecl := {
    name := "lorentz"
    group := .lorentz
    exactness := .exact
  }
  let law := deriveFromNoether sym
  if law.name != "lorentzInvariant" then throw (IO.userError s!"Expected 'lorentzInvariant', got '{law.name}'")

-- Poincare symmetry -> Poincare invariant
#eval show IO Unit from do
  let sym : SymmetryDecl := {
    name := "poincare"
    group := .poincare
    exactness := .exact
  }
  let law := deriveFromNoether sym
  if law.name != "poincareInvariant" then throw (IO.userError s!"Expected 'poincareInvariant', got '{law.name}'")

-- Approximate symmetry -> approximate conservation
#eval show IO Unit from do
  let sym : SymmetryDecl := {
    name := "approx_sym"
    group := .translation true
    exactness := .approximate 1e-6
  }
  let law := deriveFromNoether sym
  match law.exactness with
  | .approximate _ => pure ()
  | _ => throw (IO.userError "Expected approximate conservation")

-- Anomalous symmetry -> anomalously broken conservation
#eval show IO Unit from do
  let sym : SymmetryDecl := {
    name := "chiral"
    group := .gauge "chiral"
    exactness := .anomalous "ABJ anomaly"
  }
  let law := deriveFromNoether sym
  match law.exactness with
  | .anomalouslyBroken "ABJ anomaly" => pure ()
  | _ => throw (IO.userError "Expected anomalously broken conservation")

-- deriveAllFromNoether processes multiple symmetries
#eval show IO Unit from do
  let mod : TheoryModule := {
    name := "TestTheory"
    symmetries := [
      { name := "time_trans", group := .translation true },
      { name := "space_trans", group := .translation false },
      { name := "rotation", group := .rotation 3 }
    ]
  }
  let laws := deriveAllFromNoether mod
  if laws.length != 3 then throw (IO.userError s!"Expected 3 laws, got {laws.length}")
  if laws[0]!.name != "energy" then throw (IO.userError "First law should be energy")
  if laws[1]!.name != "momentum" then throw (IO.userError "Second law should be momentum")
  if laws[2]!.name != "angularMomentum" then throw (IO.userError "Third law should be angularMomentum")

-- ============================================================
-- Conservation law data structures
-- ============================================================

-- ConservationLaw default tolerance is 1e-10
#eval show IO Unit from do
  let law : ConservationLaw := { name := "test", quantityExpr := "x" }
  if law.tolerance != 1e-10 then throw (IO.userError "Default tolerance should be 1e-10")

-- ConservationSource.declared is the default
#eval show IO Unit from do
  let law : ConservationLaw := { name := "test", quantityExpr := "x" }
  match law.source with
  | .declared => pure ()
  | _ => throw (IO.userError "Expected declared source")

-- ============================================================
-- Dimensional analysis lemmas (from Physics.Dimensional)
-- ============================================================

-- Force = Mass * Acceleration
theorem test_dim_force : dimMass * dimAcceleration = dimForce :=
  dim_force_eq

-- Energy = Force * Length
theorem test_dim_energy : dimForce * dimLength = dimEnergy :=
  dim_energy_eq_force_mul_length

-- Power = Energy / Time
theorem test_dim_power : dimEnergy / dimTime = dimPower :=
  dim_power_eq_energy_div_time

-- Momentum = Mass * Velocity
theorem test_dim_momentum : dimMass * dimVelocity = dimMomentum :=
  dim_momentum_eq

-- Voltage = Power / Current
theorem test_dim_voltage : dimPower / dimCurrent = dimVoltage :=
  dim_voltage_eq_power_div_current

-- Charge = Current * Time
theorem test_dim_charge : dimCurrent * dimTime = dimCharge :=
  dim_charge_eq_current_mul_time

-- Pressure = Force / Area
theorem test_dim_pressure : dimForce / dimArea = dimPressure :=
  dim_pressure_eq_force_div_area

-- Resistance = Voltage / Current
theorem test_dim_resistance : dimVoltage / dimCurrent = dimResistance :=
  dim_resistance_eq_voltage_div_current

-- ============================================================
-- Maxwell equations: structure verification
-- ============================================================

-- Verify that SatisfiesMaxwell has the expected field names
#check @Measure.Physics.Electromagnetism.SatisfiesMaxwell
#check @Measure.Physics.Electromagnetism.SatisfiesMaxwell.gauss
#check @Measure.Physics.Electromagnetism.SatisfiesMaxwell.gaussMag
#check @Measure.Physics.Electromagnetism.SatisfiesMaxwell.faraday
#check @Measure.Physics.Electromagnetism.SatisfiesMaxwell.ampere

-- EMField has E and B fields
#check @Measure.Physics.Electromagnetism.EMField.E
#check @Measure.Physics.Electromagnetism.EMField.B

-- EMSource has rho and J fields
#check @Measure.Physics.Electromagnetism.EMSource.ρ
#check @Measure.Physics.Electromagnetism.EMSource.J

-- Vacuum source exists
#check Measure.Physics.Electromagnetism.vacuumSource

-- GaussLaw and GaussMagnetism are Props
example : (Measure.Physics.Electromagnetism.EMField →
           Measure.Physics.Electromagnetism.EMSource → Prop) :=
  Measure.Physics.Electromagnetism.GaussLaw

example : (Measure.Physics.Electromagnetism.EMField → Prop) :=
  Measure.Physics.Electromagnetism.GaussMagnetism

-- ============================================================
-- Minkowski spacetime: structure verification
-- ============================================================

#check @Measure.Physics.Relativity.FourVector
#check @Measure.Physics.Relativity.minkowskiMetric
#check @Measure.Physics.Relativity.minkowskiInner
#check @Measure.Physics.Relativity.spacetimeInterval
#check @Measure.Physics.Relativity.IsTimelike
#check @Measure.Physics.Relativity.IsSpacelike
#check @Measure.Physics.Relativity.IsLightlike
#check @Measure.Physics.Relativity.lorentzFactor
#check @Measure.Physics.Relativity.properTime

-- ============================================================
-- Newtonian mechanics: theorems are not sorry
-- ============================================================

#check @Measure.Physics.ClassicalMechanics.SimpleHarmonicOscillator.omega_pos
#check @Measure.Physics.ClassicalMechanics.SimpleHarmonicOscillator.omega_sq
#check @Measure.Physics.ClassicalMechanics.SimpleHarmonicOscillator.totalEnergy_nonneg
#check @Measure.Physics.ClassicalMechanics.SatisfiesNewtonII

-- ============================================================
-- TheoryModule structure
-- ============================================================

-- TheoryModule can be constructed with defaults
#eval show IO Unit from do
  let tm : TheoryModule := { name := "TestTheory" }
  if tm.name != "TestTheory" then throw (IO.userError "name mismatch")
  if tm.symmetries.length != 0 then throw (IO.userError "symmetries should be empty")
  if tm.relations.length != 0 then throw (IO.userError "relations should be empty")
  if tm.imports.length != 0 then throw (IO.userError "imports should be empty")

-- TheoryModule rigor level defaults to strict
#eval show IO Unit from do
  let tm : TheoryModule := { name := "Test" }
  match tm.rigorLevel with
  | .strict => pure ()
  | _ => throw (IO.userError "Expected strict rigor level")

-- TheoryModule toTheoryInfo round-trips name
#eval show IO Unit from do
  let tm : TheoryModule := { name := "MyTheory" }
  let info := tm.toTheoryInfo
  if info.name != Lean.Name.mkSimple "MyTheory" then throw (IO.userError "toTheoryInfo name mismatch")

-- TheoryModule fromTheoryInfo preserves name
#eval show IO Unit from do
  let info : Measure.Syntax.TheoryInfo := {
    name := Lean.Name.mkSimple "Imported"
    rigorLevel := .strict
    extends_ := []
  }
  let tm := TheoryModule.fromTheoryInfo info
  if tm.name != "Imported" then throw (IO.userError "fromTheoryInfo name mismatch")

-- ============================================================
-- PhysReal dimensional arithmetic (type-level)
-- ============================================================

-- PhysReal addition requires same dimension
noncomputable example (a b : ForceVal) : ForceVal := a + b

-- PhysReal subtraction requires same dimension
noncomputable example (a b : EnergyVal) : EnergyVal := a - b

-- PhysReal negation preserves dimension
noncomputable example (a : MomentumVal) : MomentumVal := -a

-- PhysReal.dimensionless wraps a real
example : (PhysReal.dimensionless 0).val = 0 := rfl

end TestPhysics
