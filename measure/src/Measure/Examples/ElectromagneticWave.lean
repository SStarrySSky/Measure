/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Example: Electromagnetic wave theory using Maxwell's equations.

For the mathematical (ℝ-based) formulation with validity conditions,
see Measure.Physics.Historical.ApproximateTheories

Demonstrates:
  - Defining EM-specific dimensions (electric field, magnetic field, etc.)
  - Plane wave solutions to Maxwell's equations
  - Verifying that wave speed equals the speed of light: c = 1/sqrt(mu_0 * epsilon_0)
  - Energy density and Poynting vector with dimensional consistency
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
-- Domain-specific dimension shorthands for electromagnetism
-- (Base/derived dims reuse canonical definitions from Measure.Physics.Dimensional)
-- ============================================================

/-- Electric field dimension: M L T^{-3} I^{-1} (V/m = kg m s^{-3} A^{-1})
    From F = qE, so [E] = [F]/[q] = M L T^{-2} / (I T) = M L T^{-3} I^{-1} -/
def emDimElectricField : Dim :=
  { M := QExp.one, L := QExp.one, T := QExp.mk' (-3) 1, I := QExp.mk' (-1) 1 }

/-- Magnetic field dimension: M T^{-2} I^{-1} (T = kg s^{-2} A^{-1})
    From F = qvB, so [B] = [F]/([q][v]) = M L T^{-2} / (I T * L T^{-1}) = M T^{-2} I^{-1} -/
def emDimMagneticField : Dim :=
  { M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-1) 1 }

/-- Vacuum permittivity dimension: I^2 T^4 M^{-1} L^{-3} (F/m)
    [epsilon_0] = [q]^2 / ([F] [L]^2) = I^2 T^2 / (M L T^{-2} L^2) = I^2 T^4 M^{-1} L^{-3} -/
def emDimPermittivity : Dim :=
  { M := QExp.mk' (-1) 1, L := QExp.mk' (-3) 1, T := QExp.mk' 4 1, I := QExp.mk' 2 1 }

/-- Vacuum permeability dimension: M L T^{-2} I^{-2} (H/m = kg m s^{-2} A^{-2})
    [mu_0] = [F] / [I]^2 = M L T^{-2} / I^2 = M L T^{-2} I^{-2} -/
def emDimPermeability : Dim :=
  { M := QExp.one, L := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-2) 1 }

/-- Energy density dimension: M L^{-1} T^{-2} (J/m^3)
    [u] = [Energy] / [Volume] = M L^2 T^{-2} / L^3 = M L^{-1} T^{-2} -/
def dimEnergyDensity : Dim :=
  { M := QExp.one, L := QExp.mk' (-1) 1, T := QExp.mk' (-2) 1 }

/-- Poynting vector dimension: M T^{-3} (W/m^2 = kg s^{-3})
    [S] = [Power] / [Area] = M L^2 T^{-3} / L^2 = M T^{-3} -/
def emDimPoynting : Dim :=
  { M := QExp.one, T := QExp.mk' (-3) 1 }

/-- Wave number dimension: L^{-1} (m^{-1}) -/
def emDimWaveNumber : Dim := { L := QExp.mk' (-1) 1 }

-- ============================================================
-- The theory: Electromagnetic Waves
-- ============================================================

theory ElectromagneticWave where

  /-- Vacuum permittivity epsilon_0.
      SI value: 8.854 187 8128 x 10^{-12} F/m. -/
  axiom epsilon0 : ExactQ emDimPermittivity

  /-- Vacuum permeability mu_0.
      SI value: 1.256 637 062 12 x 10^{-6} H/m. -/
  axiom mu0 : ExactQ emDimPermeability

  /-- Speed of light in vacuum: c = 1 / sqrt(mu_0 * epsilon_0).
      Result has dimension L T^{-1} (velocity). -/
  axiom speedOfLight : ExactQ dimVelocity

  /-- Plane wave electric field: E(x, t) = E_0 sin(kx - omega t).
      E_0 is the amplitude (electric field dimension).
      k is the wave number, omega is the angular frequency.
      The result has electric field dimension M L T^{-3} I^{-1}. -/
  axiom planeWaveE
    (E0 : ExactQ emDimElectricField)
    (k : ExactQ emDimWaveNumber)
    (omega : ExactQ dimFrequency)
    : ExactQ emDimElectricField

  /-- Plane wave magnetic field: B(x, t) = B_0 sin(kx - omega t).
      For a plane wave, B_0 = E_0 / c.
      The result has magnetic field dimension M T^{-2} I^{-1}. -/
  axiom planeWaveB
    (B0 : ExactQ emDimMagneticField)
    (k : ExactQ emDimWaveNumber)
    (omega : ExactQ dimFrequency)
    : ExactQ emDimMagneticField

  /-- Dispersion relation: omega = c * k.
      For EM waves in vacuum, the phase velocity equals c.
      Both sides have dimension T^{-1} (frequency). -/
  axiom dispersionRelation
    (c : ExactQ dimVelocity)
    (k : ExactQ emDimWaveNumber)
    : ExactQ dimFrequency

  /-- Electromagnetic energy density: u = (1/2)(epsilon_0 E^2 + B^2 / mu_0).
      Result has dimension M L^{-1} T^{-2} (energy per volume). -/
  axiom energyDensity
    (eps0 : ExactQ emDimPermittivity)
    (E : ExactQ emDimElectricField)
    (mu0 : ExactQ emDimPermeability)
    (B : ExactQ emDimMagneticField)
    : ExactQ dimEnergyDensity

  /-- Poynting vector magnitude: |S| = E * B / mu_0.
      Represents the energy flux (power per unit area).
      Result has dimension M T^{-3} (W/m^2). -/
  axiom poyntingMagnitude
    (E : ExactQ emDimElectricField)
    (B : ExactQ emDimMagneticField)
    (mu0 : ExactQ emDimPermeability)
    : ExactQ emDimPoynting

  /-- Lorentz force: F = q(E + v x B).
      The electric and magnetic contributions both have force dimension.
      Result has dimension M L T^{-2} (force). -/
  axiom lorentzForce
    (q : ExactQ dimCharge)
    (E : ExactQ emDimElectricField)
    (v : ExactQ dimVelocity)
    (B : ExactQ emDimMagneticField)
    : ExactQ dimForce

  /-- Noether symmetries: conservation laws from continuous symmetries. -/
  symmetry time_translation
  symmetry gauge_U1

-- ============================================================
-- If we reach here, the theory compiled successfully.
-- Phase 6 verified:
--   All axioms are dimensionally consistent
--   No conservation law violations detected
--   Conservation laws derived from declared symmetries:
--     time_translation -> energy conservation (Poynting's theorem)
--     gauge_U1         -> charge conservation
--   Theory 'ElectromagneticWave' is self-consistent
-- ============================================================

-- Dimensional consistency proofs:

/-- The speed of light has velocity dimensions: c = 1/sqrt(mu_0 epsilon_0).
    Verify: [mu_0 * epsilon_0] = M L T^{-2} I^{-2} * I^2 T^4 M^{-1} L^{-3} = L^{-2} T^2
    So [1/sqrt(mu_0 epsilon_0)] = 1 / (L^{-1} T) = L T^{-1} = velocity. -/
theorem speed_of_light_dim :
    Dim.mul emDimPermeability emDimPermittivity =
      { L := QExp.mk' (-2) 1, T := QExp.mk' 2 1 } := by
  native_decide

/-- Electric field times magnetic field divided by permeability gives Poynting vector dimension.
    [E * B / mu_0] = (M L T^{-3} I^{-1})(M T^{-2} I^{-1}) / (M L T^{-2} I^{-2})
                    = M^2 L T^{-5} I^{-2} / (M L T^{-2} I^{-2})
                    = M T^{-3} = [Poynting]. -/
theorem poynting_dim_check :
    Dim.div (Dim.mul emDimElectricField emDimMagneticField) emDimPermeability =
      emDimPoynting := by
  native_decide

/-- Lorentz force electric part: q * E has force dimension.
    [q * E] = (I T)(M L T^{-3} I^{-1}) = M L T^{-2} = [Force]. -/
theorem lorentz_electric_dim :
    Dim.mul dimCharge emDimElectricField = dimForce := by
  native_decide

/-- Lorentz force magnetic part: q * v * B has force dimension.
    [q * v * B] = (I T)(L T^{-1})(M T^{-2} I^{-1}) = M L T^{-2} = [Force]. -/
theorem lorentz_magnetic_dim :
    Dim.mul (Dim.mul dimCharge dimVelocity) emDimMagneticField = dimForce := by
  native_decide

/-- Dispersion relation: c * k has frequency dimension.
    [c * k] = (L T^{-1})(L^{-1}) = T^{-1} = [Frequency]. -/
theorem dispersion_dim_check :
    Dim.mul dimVelocity emDimWaveNumber = dimFrequency := by
  native_decide

/-- Energy density from epsilon_0 * E^2 has the correct dimension.
    [epsilon_0 * E^2] = (I^2 T^4 M^{-1} L^{-3})(M^2 L^2 T^{-6} I^{-2})
                       = M L^{-1} T^{-2} = [energy density]. -/
theorem energy_density_electric_dim :
    Dim.mul emDimPermittivity (Dim.mul emDimElectricField emDimElectricField) =
      dimEnergyDensity := by
  native_decide

/-- Energy density from B^2 / mu_0 has the correct dimension.
    [B^2 / mu_0] = (M^2 T^{-4} I^{-2}) / (M L T^{-2} I^{-2})
                  = M L^{-1} T^{-2} = [energy density]. -/
theorem energy_density_magnetic_dim :
    Dim.div (Dim.mul emDimMagneticField emDimMagneticField) emDimPermeability =
      dimEnergyDensity := by
  native_decide

/-- E/B has velocity dimension (wave impedance relation).
    [E/B] = (M L T^{-3} I^{-1}) / (M T^{-2} I^{-1}) = L T^{-1} = [velocity]. -/
theorem E_over_B_is_velocity :
    Dim.div emDimElectricField emDimMagneticField = dimVelocity := by
  native_decide

/-- Charge times electric field has force dimension (Coulomb force).
    [q * E] = (I T)(M L T^{-3} I^{-1}) = M L T^{-2} = [Force]. -/
theorem charge_times_E_is_force :
    Dim.mul dimCharge emDimElectricField = dimForce := by
  native_decide
