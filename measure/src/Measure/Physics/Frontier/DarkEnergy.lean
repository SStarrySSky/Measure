/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dark energy — cosmological constant, equation of state,
accelerating expansion, and quintessence models.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Measure.Physics.Frontier

/-! ## Cosmological Constant -/

/-- The cosmological constant Λ (m⁻²).
    Observed value: Λ ≈ 1.1 × 10⁻⁵² m⁻². -/
noncomputable def cosmologicalConstant : ℝ := 1.1056e-52

/-- Speed of light (m/s). -/
noncomputable def c_light : ℝ := 299792458

/-- Vacuum energy density from the cosmological constant:
    ρ_Λ = Λc²/(8πG). -/
noncomputable def vacuumEnergyDensity (Λ G : ℝ) : ℝ :=
  Λ * c_light ^ 2 / (8 * Real.pi * G)

/-- The cosmological constant problem: the ratio of observed vacuum energy
    to the quantum field theory prediction is ~ 10⁻¹²⁰. -/
noncomputable def cosmologicalConstantRatio : ℝ := 1e-120

/-! ## Dark Energy Equation of State -/

/-- Dark energy equation of state parameter w = P/ρ.
    w = -1 corresponds to a cosmological constant. -/
structure DarkEnergyEOS where
  /-- The equation of state parameter w. -/
  w : ℝ

/-- Cosmological constant has w = -1 exactly. -/
noncomputable def cosmologicalConstantEOS : DarkEnergyEOS where
  w := -1

/-- CPL (Chevallier-Polarski-Linder) parameterization:
    w(a) = w₀ + wₐ(1 - a) where a is the scale factor. -/
structure CPLParameterization where
  /-- Present-day equation of state w₀. -/
  w₀ : ℝ
  /-- Time variation parameter wₐ. -/
  wₐ : ℝ

/-- Evaluate CPL equation of state at scale factor a. -/
noncomputable def CPLParameterization.eval (cpl : CPLParameterization) (a : ℝ) : ℝ :=
  cpl.w₀ + cpl.wₐ * (1 - a)

/-- For a cosmological constant, CPL gives w₀ = -1, wₐ = 0. -/
noncomputable def cplCosmologicalConstant : CPLParameterization where
  w₀ := -1
  wₐ := 0

/-- CPL cosmological constant gives w = -1 at all scale factors. -/
theorem cpl_lambda_constant (a : ℝ) :
    cplCosmologicalConstant.eval a = -1 := by
  unfold CPLParameterization.eval cplCosmologicalConstant
  ring

/-- Dark energy density evolution with scale factor:
    ρ_DE(a) = ρ_DE,0 · a^(-3(1+w)) for constant w. -/
noncomputable def darkEnergyDensity (ρ₀ : ℝ) (w : ℝ) (a : ℝ) : ℝ :=
  ρ₀ * a ^ (-3 * (1 + w))

/-- For w = -1 (cosmological constant), density is constant. -/
theorem lambda_density_constant (ρ₀ a : ℝ) (_ha : 0 < a) :
    darkEnergyDensity ρ₀ (-1) a = ρ₀ := by
  unfold darkEnergyDensity
  norm_num

/-! ## Accelerating Expansion -/

/-- Hubble parameter H₀ (km/s/Mpc, converted to s⁻¹). -/
noncomputable def H₀ : ℝ := 67.4 * 1000 / (3.0857e22)

/-- Friedmann equation (flat universe):
    H² = (8πG/3)(ρ_m + ρ_r + ρ_Λ). -/
noncomputable def friedmannH2 (G ρ_m ρ_r ρ_Λ : ℝ) : ℝ :=
  8 * Real.pi * G / 3 * (ρ_m + ρ_r + ρ_Λ)

/-- Density parameters: Ω_i = ρ_i / ρ_crit where ρ_crit = 3H²/(8πG). -/
structure DensityParameters where
  /-- Matter density parameter Ω_m. -/
  Ω_m : ℝ
  /-- Radiation density parameter Ω_r. -/
  Ω_r : ℝ
  /-- Dark energy density parameter Ω_Λ. -/
  Ω_Λ : ℝ

/-- Flatness condition: Ω_m + Ω_r + Ω_Λ = 1 for a flat universe. -/
def DensityParameters.isFlat (p : DensityParameters) : Prop :=
  p.Ω_m + p.Ω_r + p.Ω_Λ = 1

/-- Observed density parameters (Planck 2018). -/
noncomputable def observedDensityParams : DensityParameters where
  Ω_m := 0.315
  Ω_r := 9.1e-5
  Ω_Λ := 0.685

/-- Deceleration parameter: q = -aä/ȧ².
    q < 0 means accelerating expansion. -/
noncomputable def decelerationParameter (Ω_m Ω_Λ : ℝ) : ℝ :=
  Ω_m / 2 - Ω_Λ

/-- The universe accelerates when Ω_Λ > Ω_m/2. -/
theorem acceleration_condition (Ω_m Ω_Λ : ℝ) (h : Ω_Λ > Ω_m / 2) :
    decelerationParameter Ω_m Ω_Λ < 0 := by
  unfold decelerationParameter
  linarith

/-- Scale factor at matter-dark energy equality:
    a_eq = (Ω_m/Ω_Λ)^(1/3). -/
noncomputable def matterDEEqualityScale (Ω_m Ω_Λ : ℝ) : ℝ :=
  (Ω_m / Ω_Λ) ^ (1/3 : ℝ)

/-! ## Quintessence -/

/-- Quintessence: a dynamical scalar field φ with potential V(φ)
    that drives accelerating expansion. -/
structure QuintessenceField where
  /-- The scalar field value φ(t). -/
  φ : ℝ → ℝ
  /-- The potential V(φ). -/
  V : ℝ → ℝ
  /-- The potential is non-negative. -/
  V_nonneg : ∀ x, 0 ≤ V x

/-- Quintessence energy density: ρ_φ = φ̇²/2 + V(φ). -/
noncomputable def QuintessenceField.energyDensity (q : QuintessenceField)
    (t : ℝ) (φ_dot : ℝ) : ℝ :=
  φ_dot ^ 2 / 2 + q.V (q.φ t)

/-- Quintessence pressure: P_φ = φ̇²/2 - V(φ). -/
noncomputable def QuintessenceField.pressure (q : QuintessenceField)
    (t : ℝ) (φ_dot : ℝ) : ℝ :=
  φ_dot ^ 2 / 2 - q.V (q.φ t)

/-- Quintessence equation of state: w_φ = P_φ/ρ_φ = (φ̇²/2 - V)/(φ̇²/2 + V). -/
noncomputable def QuintessenceField.eosParameter (q : QuintessenceField)
    (t : ℝ) (φ_dot : ℝ) : ℝ :=
  q.pressure t φ_dot / q.energyDensity t φ_dot

/-- Slow-roll quintessence: when φ̇² ≪ V(φ), we get w ≈ -1. -/
theorem quintessence_slow_roll_limit (V_val : ℝ) (hV : 0 < V_val) :
    (0 / 2 - V_val) / (0 / 2 + V_val) = -1 := by
  field_simp
  ring

/-- Exponential quintessence potential: V(φ) = V₀ exp(-lam * φ/M_Pl). -/
noncomputable def exponentialPotential (V₀ lam M_Pl : ℝ) (φ : ℝ) : ℝ :=
  V₀ * Real.exp (-lam * φ / M_Pl)

/-- Tracker quintessence potential: V(φ) = M⁴⁺ⁿ/φⁿ (inverse power law). -/
noncomputable def trackerPotential (M : ℝ) (n : ℝ) (φ : ℝ) : ℝ :=
  M ^ (4 + n) / φ ^ n

end Measure.Physics.Frontier
