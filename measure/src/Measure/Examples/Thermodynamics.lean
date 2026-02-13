/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Example: Classical thermodynamics — ideal gas law and Carnot cycle.

Demonstrates:
  - Defining thermodynamic dimensions (pressure, volume, temperature, entropy, etc.)
  - Ideal gas law: PV = nRT with full dimensional consistency
  - Carnot efficiency: eta = 1 - T_cold / T_hot (dimensionless)
  - Uncertainty propagation through thermodynamic calculations
  - Using constants from Measure.Constants (k_B, N_A)
  - All dimensional checks via native_decide

The `theory` block triggers the 6-phase self-consistency pipeline.
If this file compiles, the theory is self-consistent.
-/
import Measure.Syntax.Theory
import Measure.Syntax.Tactics
import Measure.Dim.Basic
import Measure.Quantity.Basic
import Measure.Quantity.Ops
import Measure.Quantity.MixedOps
import Measure.Error.GaussianInstance
import Measure.Constants
import Measure.Physics.Dimensional

open Measure.Dim
open Measure.Quantity
open Measure.Error
open Measure.Constants
open Measure.Physics

-- ============================================================
-- Domain-specific dimension shorthands for thermodynamics
-- (Base/derived dims reuse canonical definitions from Measure.Physics.Dimensional)
-- ============================================================

/-- Entropy dimension: M L^2 T^{-2} Theta^{-1} (J/K)
    From [S] = [Energy] / [Temperature]. -/
def tdDimEntropy : Dim :=
  { M := QExp.one, L := QExp.mk' 2 1, T := QExp.mk' (-2) 1, Θ := QExp.mk' (-1) 1 }

/-- Molar gas constant dimension: M L^2 T^{-2} Theta^{-1} N^{-1} (J/(mol K))
    [R] = [Energy] / ([Amount] * [Temperature]). -/
def tdDimGasConst : Dim :=
  { M := QExp.one, L := QExp.mk' 2 1, T := QExp.mk' (-2) 1,
    Θ := QExp.mk' (-1) 1, N := QExp.mk' (-1) 1 }

/-- Boltzmann constant dimension: M L^2 T^{-2} Theta^{-1} (J/K)
    Same as entropy dimension. -/
def tdDimBoltzmann : Dim :=
  { M := QExp.one, L := QExp.mk' 2 1, T := QExp.mk' (-2) 1, Θ := QExp.mk' (-1) 1 }

/-- Avogadro constant dimension: N^{-1} (mol^{-1}) -/
def tdDimAvogadro : Dim := { N := QExp.mk' (-1) 1 }

/-- Heat capacity dimension: M L^2 T^{-2} Theta^{-1} (J/K)
    Same as entropy. -/
def tdDimHeatCapacity : Dim :=
  { M := QExp.one, L := QExp.mk' 2 1, T := QExp.mk' (-2) 1, Θ := QExp.mk' (-1) 1 }

/-- Dimensionless: for efficiency, ratios, etc. -/
def tdDimless : Dim := {}

-- ============================================================
-- The theory: Classical Thermodynamics
-- ============================================================

theory ClassicalThermodynamics where

  /-- Universal gas constant: R = N_A * k_B.
      SI value: 8.314 462 618 153 24 J/(mol K) (exact).
      Dimension: M L^2 T^{-2} Theta^{-1} N^{-1}. -/
  axiom gasConstant : ExactQ tdDimGasConst

  /-- Boltzmann constant: k_B = 1.380 649 x 10^{-23} J/K (exact).
      Dimension: M L^2 T^{-2} Theta^{-1}. -/
  axiom boltzmannConst : ExactQ tdDimBoltzmann

  /-- Avogadro constant: N_A = 6.022 140 76 x 10^{23} mol^{-1} (exact).
      Dimension: N^{-1}. -/
  axiom avogadroConst : ExactQ tdDimAvogadro

  /-- Ideal gas law: PV = nRT.
      [P * V] = (M L^{-1} T^{-2})(L^3) = M L^2 T^{-2} = [Energy].
      [n * R * T] = N * (M L^2 T^{-2} Theta^{-1} N^{-1}) * Theta = M L^2 T^{-2} = [Energy].
      Both sides have energy dimension. -/
  axiom idealGasLaw
    (P : ExactQ dimPressure)
    (V : ExactQ dimVolume)
    (n : ExactQ dimAmount)
    (R : ExactQ tdDimGasConst)
    (T : ExactQ dimTemperature)
    : ExactQ dimEnergy

  /-- Isothermal work: W = nRT ln(V2/V1).
      The logarithm argument V2/V1 is dimensionless.
      [nRT] = M L^2 T^{-2} = [Energy].
      Result has energy dimension. -/
  axiom isothermalWork
    (n : ExactQ dimAmount)
    (R : ExactQ tdDimGasConst)
    (T : ExactQ dimTemperature)
    : ExactQ dimEnergy

  /-- Carnot efficiency: eta = 1 - T_cold / T_hot.
      [T_cold / T_hot] = Theta / Theta = dimensionless.
      Result is dimensionless (a pure ratio). -/
  axiom carnotEfficiency
    (Tcold Thot : ExactQ dimTemperature)
    : ExactQ tdDimless

  /-- Heat transfer: Q = n C Delta T.
      [n * C * Delta T] = N * (M L^2 T^{-2} Theta^{-1} N^{-1}) * Theta
                         = M L^2 T^{-2} = [Energy].
      C here is the molar heat capacity with dimension [R] = M L^2 T^{-2} Theta^{-1} N^{-1}.
      Result has energy dimension. -/
  axiom heatTransfer
    (n : ExactQ dimAmount)
    (C : ExactQ tdDimGasConst)
    (dT : ExactQ dimTemperature)
    : ExactQ dimEnergy

  /-- Entropy change for reversible process: Delta S = Q / T.
      [Q / T] = (M L^2 T^{-2}) / Theta = M L^2 T^{-2} Theta^{-1} = [Entropy].
      Result has entropy dimension. -/
  axiom entropyChange
    (Q : ExactQ dimEnergy)
    (T : ExactQ dimTemperature)
    : ExactQ tdDimEntropy

  /-- Adiabatic relation: P V^gamma = const.
      For dimensionless gamma, [P * V^gamma] depends on gamma.
      When gamma = 1, this reduces to PV = const (isothermal).
      The axiom states that the product is conserved (energy-like). -/
  axiom adiabaticInvariant
    (P : ExactQ dimPressure)
    (V : ExactQ dimVolume)
    : ExactQ dimEnergy

  /-- First law of thermodynamics: dU = delta Q - delta W.
      Given heat added Q and work done W, returns the internal energy change.
      All terms have energy dimension M L^2 T^{-2}. -/
  axiom firstLaw (Q W : ExactQ dimEnergy) : ExactQ dimEnergy

  /-- Second law: total entropy of an isolated system never decreases.
      Delta S >= 0 for any spontaneous process.
      Returns the non-negative entropy change. -/
  axiom secondLaw (S_final S_initial : ExactQ tdDimEntropy) : ExactQ tdDimEntropy

  /-- Noether symmetry: time-translation invariance implies energy conservation. -/
  symmetry time_translation

-- ============================================================
-- If we reach here, the theory compiled successfully.
-- Phase 6 verified:
--   All axioms are dimensionally consistent
--   No conservation law violations detected
--   Conservation laws derived from declared symmetries:
--     time_translation -> energy conservation
--   Theory 'ClassicalThermodynamics' is self-consistent
-- ============================================================

-- ============================================================
-- Dimensional consistency proofs
-- ============================================================

/-- Ideal gas law LHS: P * V has energy dimension.
    [P * V] = (M L^{-1} T^{-2})(L^3) = M L^2 T^{-2} = [Energy]. -/
theorem pressure_times_volume_is_energy :
    Dim.mul dimPressure dimVolume = dimEnergy := by
  native_decide

/-- Ideal gas law RHS: n * R * T has energy dimension.
    [n * R] = N * (M L^2 T^{-2} Theta^{-1} N^{-1}) = M L^2 T^{-2} Theta^{-1}.
    [n * R * T] = (M L^2 T^{-2} Theta^{-1}) * Theta = M L^2 T^{-2} = [Energy]. -/
theorem nRT_is_energy :
    Dim.mul (Dim.mul dimAmount tdDimGasConst) dimTemperature = dimEnergy := by
  native_decide

/-- Both sides of PV = nRT have the same dimension (energy).
    This is the core dimensional consistency check for the ideal gas law. -/
theorem ideal_gas_law_dim_consistent :
    Dim.mul dimPressure dimVolume =
    Dim.mul (Dim.mul dimAmount tdDimGasConst) dimTemperature := by
  native_decide

/-- Carnot efficiency: T_cold / T_hot is dimensionless.
    [T / T] = Theta / Theta = 1. -/
theorem temperature_ratio_is_dimensionless :
    Dim.div dimTemperature dimTemperature = tdDimless := by
  native_decide

/-- Entropy change: Q / T has entropy dimension.
    [Q / T] = (M L^2 T^{-2}) / Theta = M L^2 T^{-2} Theta^{-1} = [Entropy]. -/
theorem heat_over_temperature_is_entropy :
    Dim.div dimEnergy dimTemperature = tdDimEntropy := by
  native_decide

/-- R = k_B * N_A dimensionally: [k_B] * [N_A] = [R].
    (M L^2 T^{-2} Theta^{-1}) * (N^{-1}) = M L^2 T^{-2} Theta^{-1} N^{-1} = [R]. -/
theorem gas_constant_from_kB_NA :
    Dim.mul tdDimBoltzmann tdDimAvogadro = tdDimGasConst := by
  native_decide

/-- Pressure is force per area: [F / L^2] = [P].
    (M L T^{-2}) / L^2 = M L^{-1} T^{-2} = [Pressure]. -/
theorem pressure_is_force_per_area :
    Dim.div { M := QExp.one, L := QExp.one, T := QExp.mk' (-2) 1 }
            { L := QExp.mk' 2 1 } = dimPressure := by
  native_decide

/-- Heat capacity times temperature has energy dimension.
    [C * T] = (M L^2 T^{-2} Theta^{-1}) * Theta = M L^2 T^{-2} = [Energy]. -/
theorem heat_capacity_times_temp_is_energy :
    Dim.mul tdDimHeatCapacity dimTemperature = dimEnergy := by
  native_decide

/-- Power is energy per time: [E / T_time] = [Power].
    (M L^2 T^{-2}) / T = M L^2 T^{-3} = [Power]. -/
theorem energy_per_time_is_power :
    Dim.div dimEnergy dimTime = dimPower := by
  native_decide

-- ============================================================
-- Uncertainty propagation example: Carnot efficiency with
-- measured temperatures carrying Gaussian uncertainty.
-- ============================================================

/-- Example: Carnot efficiency with uncertain temperature measurements.
    T_hot = (500.0 +/- 2.0) K, T_cold = (300.0 +/- 1.5) K.
    eta = 1 - T_cold / T_hot, with uncertainty propagated via Gaussian model. -/
def exampleCarnotUncertain : UncertainQ tdDimless Gaussian :=
  let Thot  : UncertainQ dimTemperature Gaussian :=
    UncertainQ.fromMeasurement dimTemperature 500.0 2.0
      (.database "lab" "2026")
  let Tcold : UncertainQ dimTemperature Gaussian :=
    UncertainQ.fromMeasurement dimTemperature 300.0 1.5
      (.database "lab" "2026")
  let ratio : UncertainQ tdDimless Gaussian := Tcold / Thot
  let one   : UncertainQ tdDimless Gaussian :=
    UncertainQ.fromExact tdDimless 1.0
  one - ratio

/-- Example: Ideal gas pressure from measured n, T, V with uncertainty.
    n = (1.00 +/- 0.01) mol, T = (298.15 +/- 0.5) K, V = (0.02445 +/- 0.0001) m^3.
    P = nRT / V, with R exact.
    The result type carries the computed dimension from arithmetic operations. -/
def exampleIdealGasPressure :
    UncertainQ (Dim.div (Dim.mul (Dim.mul dimAmount tdDimGasConst) dimTemperature)
                         dimVolume) Gaussian :=
  let n : UncertainQ dimAmount Gaussian :=
    UncertainQ.fromMeasurement dimAmount 1.00 0.01
      (.database "lab" "2026")
  let T : UncertainQ dimTemperature Gaussian :=
    UncertainQ.fromMeasurement dimTemperature 298.15 0.5
      (.database "lab" "2026")
  let V : UncertainQ dimVolume Gaussian :=
    UncertainQ.fromMeasurement dimVolume 0.02445 0.0001
      (.database "lab" "2026")
  let R : UncertainQ tdDimGasConst Gaussian :=
    UncertainQ.fromExact tdDimGasConst 8.31446261815324
  -- P = nRT / V: [n * R * T / V] = Energy / L^3 = M L^{-1} T^{-2} = [Pressure]
  ((n * R) * T) / V

/-- The computed dimension of nRT/V equals pressure dimension. -/
theorem ideal_gas_pressure_dim :
    Dim.div (Dim.mul (Dim.mul dimAmount tdDimGasConst) dimTemperature)
            dimVolume = dimPressure := by
  native_decide
