/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Bridge between the Physics module and the Dim (dimensional analysis) system.
Provides dimensionally-annotated physical quantity types and dimensional
consistency lemmas for common physical relations.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Measure.Dim.Basic
import Measure.Quantity.Basic
import Measure.Quantity.Bridge

namespace Measure.Physics

open Measure.Dim
open Measure.Quantity

/-! ## Dimensionally-annotated physical quantity type -/

/-- A real-valued physical quantity tagged with its SI dimension `d`.
    The dimension is a compile-time phantom; the runtime payload is `ℝ`. -/
structure PhysReal (d : Dim) where
  val : ℝ

instance (d : Dim) : Inhabited (PhysReal d) where
  default := ⟨0⟩

/-- Lift a raw real into a dimensionless `PhysReal`. -/
def PhysReal.dimensionless (v : ℝ) : PhysReal Dim.dimensionless :=
  ⟨v⟩

/-! ## Arithmetic that tracks dimensions -/

/-- Addition: only values of the *same* dimension may be added. -/
noncomputable def PhysReal.add {d : Dim} (a b : PhysReal d) : PhysReal d :=
  ⟨a.val + b.val⟩

/-- Subtraction: same-dimension constraint. -/
noncomputable def PhysReal.sub {d : Dim} (a b : PhysReal d) : PhysReal d :=
  ⟨a.val - b.val⟩

/-- Multiplication: dimensions are multiplied (exponents added). -/
noncomputable def PhysReal.mul {d₁ d₂ : Dim} (a : PhysReal d₁) (b : PhysReal d₂) :
    PhysReal (d₁ * d₂) :=
  ⟨a.val * b.val⟩

/-- Division: dimensions are divided (exponents subtracted). -/
noncomputable def PhysReal.div {d₁ d₂ : Dim} (a : PhysReal d₁) (b : PhysReal d₂) :
    PhysReal (d₁ / d₂) :=
  ⟨a.val / b.val⟩

/-- Scalar multiplication (dimensionless scalar on the left). -/
noncomputable def PhysReal.smul {d : Dim} (c : ℝ) (a : PhysReal d) : PhysReal d :=
  ⟨c * a.val⟩

/-- Negation preserves dimension. -/
noncomputable def PhysReal.neg {d : Dim} (a : PhysReal d) : PhysReal d :=
  ⟨-a.val⟩

noncomputable instance (d : Dim) : Add (PhysReal d) := ⟨PhysReal.add⟩
noncomputable instance (d : Dim) : Sub (PhysReal d) := ⟨PhysReal.sub⟩
noncomputable instance (d : Dim) : Neg (PhysReal d) := ⟨PhysReal.neg⟩

/-! ## SI base dimension aliases (single-component) -/

/-- Length: m -/
def dimLength : Dim := { L := QExp.one }

/-- Mass: kg -/
def dimMass : Dim := { M := QExp.one }

/-- Time: s -/
def dimTime : Dim := { T := QExp.one }

/-- Electric current: A -/
def dimCurrent : Dim := { I := QExp.one }

/-- Temperature: K -/
def dimTemperature : Dim := { Θ := QExp.one }

/-- Amount of substance: mol -/
def dimAmount : Dim := { N := QExp.one }

/-- Luminous intensity: cd -/
def dimLuminosity : Dim := { J := QExp.one }

/-! ## Derived dimension aliases (matching Dim.Basic definitions) -/

/-- Velocity: m⋅s⁻¹ -/
def dimVelocity : Dim := Velocity

/-- Acceleration: m⋅s⁻² -/
def dimAcceleration : Dim := Acceleration

/-- Force: kg⋅m⋅s⁻² (newton) -/
def dimForce : Dim := Force

/-- Energy / Work: kg⋅m²⋅s⁻² (joule) -/
def dimEnergy : Dim := Energy

/-- Power: kg⋅m²⋅s⁻³ (watt) -/
def dimPower : Dim := Power

/-- Pressure: kg⋅m⁻¹⋅s⁻² (pascal) -/
def dimPressure : Dim := Pressure

/-- Electric charge: A⋅s (coulomb) -/
def dimCharge : Dim := Charge

/-- Electric potential: kg⋅m²⋅s⁻³⋅A⁻¹ (volt) -/
def dimVoltage : Dim := Voltage

/-- Electrical resistance: kg⋅m²⋅s⁻³⋅A⁻² (ohm) -/
def dimResistance : Dim := Resistance

/-- Capacitance: kg⁻¹⋅m⁻²⋅s⁴⋅A² (farad) -/
def dimCapacitance : Dim := Capacitance

/-- Inductance: kg⋅m²⋅s⁻²⋅A⁻² (henry) -/
def dimInductance : Dim := Inductance

/-- Magnetic flux: kg⋅m²⋅s⁻²⋅A⁻¹ (weber) -/
def dimMagneticFlux : Dim := MagneticFlux

/-- Magnetic flux density: kg⋅s⁻²⋅A⁻¹ (tesla) -/
def dimMagneticFluxDensity : Dim := MagneticFluxDens

/-- Momentum: kg⋅m⋅s⁻¹ -/
def dimMomentum : Dim := { L := QExp.one, M := QExp.one, T := -QExp.one }

/-- Angular momentum: kg⋅m²⋅s⁻¹ -/
def dimAngularMomentum : Dim :=
  { L := QExp.mk' 2 1, M := QExp.one, T := -QExp.one }

/-- Frequency: s⁻¹ (hertz) -/
def dimFrequency : Dim := { T := -QExp.one }

/-- Area: m² -/
def dimArea : Dim := { L := QExp.mk' 2 1 }

/-- Volume: m³ -/
def dimVolume : Dim := { L := QExp.mk' 3 1 }

/-- Density: kg⋅m⁻³ -/
def dimDensity : Dim := { L := QExp.mk' (-3) 1, M := QExp.one }

/-! ## Convenience type aliases for common physical quantities -/

abbrev ForceVal        := PhysReal dimForce
abbrev EnergyVal       := PhysReal dimEnergy
abbrev PowerVal        := PhysReal dimPower
abbrev VelocityVal     := PhysReal dimVelocity
abbrev AccelerationVal := PhysReal dimAcceleration
abbrev MomentumVal     := PhysReal dimMomentum
abbrev ChargeVal       := PhysReal dimCharge
abbrev VoltageVal      := PhysReal dimVoltage
abbrev ResistanceVal   := PhysReal dimResistance
abbrev PressureVal     := PhysReal dimPressure
abbrev FrequencyVal    := PhysReal dimFrequency
abbrev LengthVal       := PhysReal dimLength
abbrev MassVal         := PhysReal dimMass
abbrev TimeVal         := PhysReal dimTime
abbrev CurrentVal      := PhysReal dimCurrent

/-! ## Dimensional analysis lemmas

These state that combining base dimensions via `Dim.mul` / `Dim.div`
yields the expected derived dimension.  All proofs use `native_decide`
since `Dim` and `QExp` have `DecidableEq` instances. -/

/-- Force = Mass * Acceleration  (kg⋅m⋅s⁻² = kg * m⋅s⁻²). -/
theorem dim_force_eq : dimMass * dimAcceleration = dimForce := by
  native_decide

/-- Energy = Force * Length  (kg⋅m²⋅s⁻² = kg⋅m⋅s⁻² * m). -/
theorem dim_energy_eq_force_mul_length :
    dimForce * dimLength = dimEnergy := by
  native_decide

/-- Power = Energy / Time  (kg⋅m²⋅s⁻³ = kg⋅m²⋅s⁻² / s). -/
theorem dim_power_eq_energy_div_time :
    dimEnergy / dimTime = dimPower := by
  native_decide

/-- Momentum = Mass * Velocity  (kg⋅m⋅s⁻¹ = kg * m⋅s⁻¹). -/
theorem dim_momentum_eq :
    dimMass * dimVelocity = dimMomentum := by
  native_decide

/-- Voltage = Power / Current  (kg⋅m²⋅s⁻³⋅A⁻¹ = kg⋅m²⋅s⁻³ / A). -/
theorem dim_voltage_eq_power_div_current :
    dimPower / dimCurrent = dimVoltage := by
  native_decide

/-- Charge = Current * Time  (A⋅s = A * s). -/
theorem dim_charge_eq_current_mul_time :
    dimCurrent * dimTime = dimCharge := by
  native_decide

/-- Pressure = Force / Area  (kg⋅m⁻¹⋅s⁻² = kg⋅m⋅s⁻² / m²). -/
theorem dim_pressure_eq_force_div_area :
    dimForce / dimArea = dimPressure := by
  native_decide

/-- Resistance = Voltage / Current  (Ω = V / A). -/
theorem dim_resistance_eq_voltage_div_current :
    dimVoltage / dimCurrent = dimResistance := by
  native_decide

/-! ## Conversion helpers -/

/-- Promote a `Quantity` (Float-based) to a `PhysReal` (ℝ-based) for proofs.
    This is necessarily noncomputable since Float → ℝ is not constructive. -/
noncomputable def PhysReal.ofQuantity {d : Dim} {c : Certainty}
    (q : Quantity d c) : PhysReal d :=
  ⟨Float.toReal q.value⟩

end Measure.Physics
