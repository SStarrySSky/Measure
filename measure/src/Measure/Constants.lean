/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Fundamental physical constants (CODATA 2022 recommended values).
Constants marked "exact" have zero uncertainty by definition in the 2019 SI redefinition.
See docs/type-system.md Section 5.
-/
import Measure.Quantity.Basic
import Measure.Dim.Basic

namespace Measure.Constants

open Measure.Dim
open Measure.Quantity

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
-- Measured constants (CODATA 2022, non-zero uncertainty)
-- ============================================================

/-- Newtonian gravitational constant: 6.674 30 × 10⁻¹¹ m³ kg⁻¹ s⁻² (±0.000 15 × 10⁻¹¹).
    Dimension: L³ M⁻¹ T⁻². -/
def G : ExactQ { L := QExp.mk' 3 1, M := QExp.mk' (-1) 1, T := QExp.mk' (-2) 1 } :=
  ExactQ.mk _ 6.67430e-11

/-- Electron mass: 9.109 383 7015 × 10⁻³¹ kg.
    Dimension: M. -/
def m_e : ExactQ { M := QExp.one } :=
  ExactQ.mk _ 9.1093837015e-31

/-- Proton mass: 1.672 621 923 69 × 10⁻²⁷ kg.
    Dimension: M. -/
def m_p : ExactQ { M := QExp.one } :=
  ExactQ.mk _ 1.67262192369e-27

/-- Fine-structure constant: 7.297 352 5693 × 10⁻³ (dimensionless). -/
def α : ExactQ Dim.dimensionless :=
  ExactQ.mk Dim.dimensionless 7.2973525693e-3

end Measure.Constants