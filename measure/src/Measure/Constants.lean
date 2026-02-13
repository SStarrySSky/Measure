/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Fundamental physical constants (CODATA 2022 recommended values).
Constants marked "exact" have zero uncertainty by definition in the 2019 SI redefinition.
Measured constants carry Gaussian uncertainty (1-sigma standard uncertainty).
See docs/type-system.md Section 5.
-/
import Measure.Quantity.Basic
import Measure.Quantity.MixedOps
import Measure.Error.GaussianInstance
import Measure.Dim.Basic

/-! # Physical Constants (CODATA 2022)

This module defines the fundamental physical constants used throughout the Measure
language. Each constant is a dimension-typed `Quantity` whose certainty tag reflects
whether the value is exact or carries measurement uncertainty.

**Exact constants** (`ExactQ`) are those fixed by the 2019 SI redefinition: the speed
of light `c`, Planck constant `h`, Boltzmann constant `k_B`, Avogadro constant `N_A`,
and elementary charge `e`. The reduced Planck constant `ℏ` and Stefan-Boltzmann
constant `σ` are derived from these and are therefore also exact.

**Measured constants** (`UncertainQ ... Gaussian`) carry a 1-sigma standard uncertainty
from the CODATA 2022 adjustment: the gravitational constant `G`, electron mass `m_e`,
proton mass `m_p`, fine-structure constant `α`, vacuum permeability `μ₀`, and vacuum
permittivity `ε₀`.
-/

namespace Measure.Constants

open Measure.Dim
open Measure.Quantity
open Measure.Error

-- ============================================================
-- Exact constants (defined values in 2019 SI redefinition)
-- ============================================================

/-- Speed of light in vacuum: 299 792 458 m/s (exact). -/
def c : ExactQ Velocity :=
  ExactQ.mk Velocity 299792458.0

/-- Planck constant: 6.626 070 15 × 10⁻³⁴ J·s (exact).
    Dimension: M L² T⁻¹ (energy × time = action). -/
def h : ExactQ { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-1) 1 } :=
  ExactQ.mk _ 6.62607015e-34

/-- Boltzmann constant: 1.380 649 × 10⁻²³ J/K (exact).
    Dimension: M L² T⁻² Θ⁻¹. -/
def k_B : ExactQ { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1, Θ := QExp.mk' (-1) 1 } :=
  ExactQ.mk _ 1.380649e-23

/-- Avogadro constant: 6.022 140 76 × 10²³ mol⁻¹ (exact).
    Dimension: N⁻¹. -/
def N_A : ExactQ { N := QExp.mk' (-1) 1 } :=
  ExactQ.mk _ 6.02214076e23

/-- Elementary charge: 1.602 176 634 × 10⁻¹⁹ C (exact).
    Dimension: T I (charge). -/
def e : ExactQ Charge :=
  ExactQ.mk Charge 1.602176634e-19

-- ============================================================
-- Derived exact constants
-- ============================================================

/-- Reduced Planck constant: ℏ = h / (2π) (exact, derived from exact h).
    Dimension: M L² T⁻¹ (action). -/
def ℏ : ExactQ { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-1) 1 } :=
  ExactQ.mk _ (6.62607015e-34 / (2.0 * 3.14159265358979323846))

-- ============================================================
-- Measured constants (CODATA 2022, non-zero uncertainty)
-- Uses Gaussian error model with 1-sigma standard uncertainty.
-- ============================================================

/-- Dimension alias for gravitational constant: L³ M⁻¹ T⁻². -/
private def dimG : Dim :=
  { L := QExp.mk' 3 1, M := QExp.mk' (-1) 1, T := QExp.mk' (-2) 1 }

/-- Newtonian gravitational constant: (6.674 30 ± 0.000 15) × 10⁻¹¹ m³ kg⁻¹ s⁻².
    CODATA 2022. Relative standard uncertainty: 2.2 × 10⁻⁵. -/
def G : UncertainQ dimG Gaussian :=
  UncertainQ.fromMeasurement dimG 6.67430e-11 0.00015e-11
    (.database "CODATA" "2022")

/-- Dimension alias for mass: M. -/
private def dimMass : Dim := { M := QExp.one }

/-- Electron mass: (9.109 383 7015 ± 0.000 000 0028) × 10⁻³¹ kg.
    CODATA 2022. Relative standard uncertainty: 3.0 × 10⁻¹⁰. -/
def m_e : UncertainQ dimMass Gaussian :=
  UncertainQ.fromMeasurement dimMass 9.1093837015e-31 0.0000000028e-31
    (.database "CODATA" "2022")

/-- Proton mass: (1.672 621 923 69 ± 0.000 000 000 51) × 10⁻²⁷ kg.
    CODATA 2022. Relative standard uncertainty: 3.1 × 10⁻¹⁰. -/
def m_p : UncertainQ dimMass Gaussian :=
  UncertainQ.fromMeasurement dimMass 1.67262192369e-27 0.00000000051e-27
    (.database "CODATA" "2022")

/-- Fine-structure constant: (7.297 352 5693 ± 0.000 000 0011) × 10⁻³.
    CODATA 2022. Dimensionless. Relative standard uncertainty: 1.5 × 10⁻¹⁰. -/
def α : UncertainQ Dim.dimensionless Gaussian :=
  UncertainQ.fromMeasurement Dim.dimensionless 7.2973525693e-3 0.0000000011e-3
    (.database "CODATA" "2022")

/-- Dimension alias for permeability: M L T⁻² I⁻² (kg·m·s⁻²·A⁻²). -/
private def dimPermeability : Dim :=
  { L := QExp.one, M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-2) 1 }

/-- Vacuum magnetic permeability: (1.256 637 062 12 ± 0.000 000 000 19) × 10⁻⁶ N/A².
    CODATA 2022. No longer exact after 2019 SI redefinition.
    Dimension: M L T⁻² I⁻². -/
def μ₀ : UncertainQ dimPermeability Gaussian :=
  UncertainQ.fromMeasurement dimPermeability 1.25663706212e-6 0.00000000019e-6
    (.database "CODATA" "2022")

/-- Dimension alias for permittivity: M⁻¹ L⁻³ T⁴ I² (F/m). -/
private def dimPermittivity : Dim :=
  { L := QExp.mk' (-3) 1, M := QExp.mk' (-1) 1, T := QExp.mk' 4 1, I := QExp.mk' 2 1 }

/-- Vacuum electric permittivity: (8.854 187 8128 ± 0.000 000 0013) × 10⁻¹² F/m.
    CODATA 2022. Derived from μ₀ and c; no longer exact.
    Dimension: M⁻¹ L⁻³ T⁴ I². -/
def ε₀ : UncertainQ dimPermittivity Gaussian :=
  UncertainQ.fromMeasurement dimPermittivity 8.8541878128e-12 0.0000000013e-12
    (.database "CODATA" "2022")

/-- Dimension alias for Stefan-Boltzmann constant: M T⁻³ Θ⁻⁴ (W·m⁻²·K⁻⁴). -/
private def dimStefanBoltzmann : Dim :=
  { M := QExp.one, T := QExp.mk' (-3) 1, Θ := QExp.mk' (-4) 1 }

/-- Stefan-Boltzmann constant: 5.670 374 419 × 10⁻⁸ W·m⁻²·K⁻⁴ (exact).
    Derived from exact constants (k_B, h, c): σ = 2π⁵k_B⁴/(15h³c²).
    Dimension: M T⁻³ Θ⁻⁴. -/
def σ : ExactQ dimStefanBoltzmann :=
  ExactQ.mk dimStefanBoltzmann 5.670374419e-8

end Measure.Constants
