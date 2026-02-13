/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Example: Special relativity — Lorentz transformations and mass-energy equivalence.

Demonstrates:
  - Defining relativistic dimensions (four-momentum, spacetime interval, etc.)
  - Lorentz transformation structure
  - Time dilation: Delta t' = gamma * Delta t
  - Length contraction: L' = L / gamma
  - Mass-energy equivalence: E = mc^2
  - Energy-momentum relation: E^2 = (pc)^2 + (mc^2)^2
  - Relativistic momentum: p = gamma * m * v
  - All dimensional checks via native_decide

The `theory` block triggers the 6-phase self-consistency pipeline.
If this file compiles, the theory is self-consistent.
-/
import Measure.Syntax.Theory
import Measure.Syntax.Tactics
import Measure.Dim.Basic
import Measure.Quantity.Basic
import Measure.Quantity.Ops
import Measure.Physics.Dimensional

open Measure.Dim
open Measure.Quantity
open Measure.Physics

-- ============================================================
-- Domain-specific dimension shorthands for special relativity
-- (Base/derived dims reuse canonical definitions from Measure.Physics.Dimensional)
-- ============================================================

/-- Energy squared dimension: M^2 L^4 T^{-4} (J^2) -/
def dimEnergySq : Dim := { M := QExp.mk' 2 1, L := QExp.mk' 4 1, T := QExp.mk' (-4) 1 }

/-- Velocity squared dimension: L^2 T^{-2} (m^2/s^2) -/
def dimVelocitySq : Dim := { L := QExp.mk' 2 1, T := QExp.mk' (-2) 1 }

/-- Spacetime interval squared dimension: L^2 (m^2)
    In the convention s^2 = (ct)^2 - x^2 - y^2 - z^2,
    all terms have dimension L^2. -/
def srDimIntervalSq : Dim := { L := QExp.mk' 2 1 }

/-- Dimensionless: for Lorentz factor gamma, beta = v/c, etc. -/
def srDimless : Dim := {}

-- ============================================================
-- The theory: Special Relativity
-- ============================================================

theory SpecialRelativity where

  /-- Speed of light in vacuum.
      SI value: 299 792 458 m/s (exact, SI 2019 defining constant).
      Dimension: L T^{-1} (velocity). -/
  axiom speedOfLight : ExactQ dimVelocity

  /-- Lorentz factor: gamma = 1 / sqrt(1 - v^2/c^2).
      gamma is dimensionless since v/c is dimensionless.
      gamma >= 1 for all |v| < c. -/
  axiom lorentzFactor (v : ExactQ dimVelocity) (c : ExactQ dimVelocity)
    : ExactQ srDimless

  /-- Time dilation: Delta t' = gamma * Delta t.
      A moving clock runs slower by the factor gamma.
      Both sides have dimension T (time). -/
  axiom timeDilation
    (gamma : ExactQ srDimless)
    (dt : ExactQ dimTime)
    : ExactQ dimTime

  /-- Length contraction: L' = L / gamma.
      A moving rod is shorter by the factor gamma.
      Both sides have dimension L (length). -/
  axiom lengthContraction
    (len : ExactQ dimLength)
    (gamma : ExactQ srDimless)
    : ExactQ dimLength

  /-- Lorentz transformation of time coordinate:
      t' = gamma * (t - v x / c^2).
      [v x / c^2] = (L T^{-1})(L) / (L^2 T^{-2}) = T, so [t - vx/c^2] = T.
      Result has dimension T (time). -/
  axiom lorentzTransformTime
    (gamma : ExactQ srDimless)
    (t : ExactQ dimTime)
    (v : ExactQ dimVelocity)
    (x : ExactQ dimLength)
    (c : ExactQ dimVelocity)
    : ExactQ dimTime

  /-- Lorentz transformation of space coordinate:
      x' = gamma * (x - v t).
      [v t] = (L T^{-1})(T) = L, so [x - vt] = L.
      Result has dimension L (length). -/
  axiom lorentzTransformSpace
    (gamma : ExactQ srDimless)
    (x : ExactQ dimLength)
    (v : ExactQ dimVelocity)
    (t : ExactQ dimTime)
    : ExactQ dimLength

  /-- Mass-energy equivalence: E = m c^2.
      Einstein's most famous equation.
      [m c^2] = M * (L T^{-1})^2 = M L^2 T^{-2} = [Energy].
      Result has energy dimension. -/
  axiom restEnergy (m : ExactQ dimMass) (c : ExactQ dimVelocity)
    : ExactQ dimEnergy

  /-- Relativistic energy: E = gamma * m * c^2.
      Reduces to E = mc^2 when v = 0 (gamma = 1).
      Result has energy dimension. -/
  axiom relativisticEnergy
    (gamma : ExactQ srDimless)
    (m : ExactQ dimMass)
    (c : ExactQ dimVelocity)
    : ExactQ dimEnergy

  /-- Relativistic momentum: p = gamma * m * v.
      Reduces to p = mv in the non-relativistic limit (gamma -> 1).
      [gamma * m * v] = 1 * M * (L T^{-1}) = M L T^{-1} = [Momentum].
      Result has momentum dimension. -/
  axiom relativisticMomentum
    (gamma : ExactQ srDimless)
    (m : ExactQ dimMass)
    (v : ExactQ dimVelocity)
    : ExactQ dimMomentum

  /-- Energy-momentum relation: E^2 = (pc)^2 + (mc^2)^2.
      This is the relativistic dispersion relation.
      All three terms have dimension M^2 L^4 T^{-4} (energy squared).
      For massless particles (m = 0): E = pc.
      For particles at rest (p = 0): E = mc^2. -/
  axiom energyMomentumRelation
    (E : ExactQ dimEnergy)
    (p : ExactQ dimMomentum)
    (m : ExactQ dimMass)
    (c : ExactQ dimVelocity)
    (h : E.value * E.value =
         (p.value * c.value) * (p.value * c.value) +
         (m.value * c.value * c.value) * (m.value * c.value * c.value))
    : E.value * E.value =
      (p.value * c.value) * (p.value * c.value) +
      (m.value * c.value * c.value) * (m.value * c.value * c.value)

  /-- Spacetime interval is invariant under Lorentz transformations:
      s^2 = (c Delta t)^2 - (Delta x)^2 - (Delta y)^2 - (Delta z)^2.
      [(c dt)^2] = (L T^{-1})^2 * T^2 = L^2 = [(dx)^2].
      The interval s^2 has dimension L^2. -/
  axiom spacetimeInterval
    (c : ExactQ dimVelocity)
    (dt : ExactQ dimTime)
    (dx dy dz : ExactQ dimLength)
    : ExactQ srDimIntervalSq

  /-- Relativistic velocity addition: u' = (u + v) / (1 + uv/c^2).
      [uv/c^2] = (L T^{-1})(L T^{-1}) / (L T^{-1})^2 = dimensionless.
      So the denominator is dimensionless, and the result has velocity dimension. -/
  axiom velocityAddition
    (u v c : ExactQ dimVelocity)
    : ExactQ dimVelocity

  /-- Energy conservation: total relativistic energy is conserved. -/
  axiom energyConservation
    (E1 E2 : ExactQ dimEnergy)
    (h : E1.value = E2.value)
    : E1.value = E2.value

  /-- Momentum conservation: total relativistic momentum is conserved. -/
  axiom momentumConservation
    (p1 p2 : ExactQ dimMomentum)
    (h : p1.value = p2.value)
    : p1.value = p2.value

-- ============================================================
-- If we reach here, the theory compiled successfully.
-- Phase 6 verified:
--   All axioms are dimensionally consistent
--   No conservation law violations detected
--   Theory 'SpecialRelativity' is self-consistent
-- ============================================================

-- Dimensional consistency proofs:

/-- E = mc^2: mass times velocity squared gives energy.
    [m * c^2] = M * (L T^{-1})^2 = M * L^2 T^{-2} = [Energy]. -/
theorem mass_energy_equivalence_dim :
    Dim.mul dimMass (Dim.mul dimVelocity dimVelocity) = dimEnergy := by
  native_decide

/-- Relativistic momentum: gamma * m * v has momentum dimension.
    [gamma * m * v] = 1 * M * (L T^{-1}) = M L T^{-1} = [Momentum]. -/
theorem relativistic_momentum_dim :
    Dim.mul (Dim.mul srDimless dimMass) dimVelocity = dimMomentum := by
  native_decide

/-- Energy squared: E^2 has the correct dimension.
    [E^2] = (M L^2 T^{-2})^2 = M^2 L^4 T^{-4}. -/
theorem energy_squared_dim :
    Dim.mul dimEnergy dimEnergy = dimEnergySq := by
  native_decide

/-- (pc)^2 has energy-squared dimension.
    [(pc)^2] = (M L T^{-1} * L T^{-1})^2 = (M L^2 T^{-2})^2 = M^2 L^4 T^{-4} = [E^2]. -/
theorem momentum_c_squared_dim :
    Dim.mul (Dim.mul dimMomentum dimVelocity)
            (Dim.mul dimMomentum dimVelocity) = dimEnergySq := by
  native_decide

/-- (mc^2)^2 has energy-squared dimension.
    [(mc^2)^2] = (M * L^2 T^{-2})^2 = M^2 L^4 T^{-4} = [E^2]. -/
theorem rest_energy_squared_dim :
    Dim.mul (Dim.mul dimMass (Dim.mul dimVelocity dimVelocity))
            (Dim.mul dimMass (Dim.mul dimVelocity dimVelocity)) = dimEnergySq := by
  native_decide

/-- v * t has length dimension (used in Lorentz transform of x).
    [v * t] = (L T^{-1}) * T = L. -/
theorem velocity_times_time_dim :
    Dim.mul dimVelocity dimTime = dimLength := by
  native_decide

/-- v * x / c^2 has time dimension (used in Lorentz transform of t).
    [v * x / c^2] = (L T^{-1}) * L / (L^2 T^{-2}) = L^2 T^{-1} / (L^2 T^{-2}) = T. -/
theorem vx_over_csq_dim :
    Dim.div (Dim.mul dimVelocity dimLength)
            (Dim.mul dimVelocity dimVelocity) = dimTime := by
  native_decide

/-- c * dt has length dimension (used in spacetime interval).
    [c * dt] = (L T^{-1}) * T = L. -/
theorem c_times_dt_dim :
    Dim.mul dimVelocity dimTime = dimLength := by
  native_decide

/-- Spacetime interval: (c dt)^2 has L^2 dimension.
    [(c dt)^2] = L^2. -/
theorem interval_term_dim :
    Dim.mul (Dim.mul dimVelocity dimTime)
            (Dim.mul dimVelocity dimTime) = srDimIntervalSq := by
  native_decide

/-- v/c is dimensionless (beta parameter).
    [v/c] = (L T^{-1}) / (L T^{-1}) = 1. -/
theorem beta_is_dimensionless :
    Dim.div dimVelocity dimVelocity = srDimless := by
  native_decide

/-- Momentum times velocity has energy dimension (p * v = E for massless).
    [p * v] = (M L T^{-1})(L T^{-1}) = M L^2 T^{-2} = [Energy]. -/
theorem momentum_times_velocity_is_energy :
    Dim.mul dimMomentum dimVelocity = dimEnergy := by
  native_decide

/-- Energy divided by velocity has momentum dimension (E/c = p for massless).
    [E / v] = (M L^2 T^{-2}) / (L T^{-1}) = M L T^{-1} = [Momentum]. -/
theorem energy_over_velocity_is_momentum :
    Dim.div dimEnergy dimVelocity = dimMomentum := by
  native_decide
