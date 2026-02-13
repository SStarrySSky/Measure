/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Cosmology — Friedmann equation, Hubble parameter, cosmological redshift,
critical density, density parameter, and deceleration parameter.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Measure.Physics.Astrophysics

/-! ## Physical Constants (Cosmology) -/

/-- Gravitational constant G for cosmological equations (m³ kg⁻¹ s⁻²). -/
noncomputable def G_cosmo : ℝ := 6.67430e-11

/-! ## Scale Factor and Hubble Parameter -/

/-- A cosmological model described by a scale factor a(t). -/
structure CosmologicalModel where
  /-- Scale factor a(t), dimensionless. -/
  a : ℝ → ℝ
  /-- Scale factor is positive at all times. -/
  a_pos : ∀ t, 0 < a t

/-- Hubble parameter: H(t) = ȧ(t) / a(t).
    Measures the rate of expansion of the universe. -/
noncomputable def CosmologicalModel.hubbleParameter (model : CosmologicalModel) (t : ℝ) : ℝ :=
  deriv model.a t / model.a t

/-- Present-day Hubble constant H₀ (s⁻¹).
    H₀ ≈ 67.4 km/s/Mpc converted to SI. -/
noncomputable def H₀ : ℝ := 67.4 * 1000 / 3.0857e22

/-! ## Friedmann Equation -/

/-- Spatial curvature parameter k ∈ {-1, 0, +1}. -/
inductive SpatialCurvature where
  /-- Open universe (hyperbolic geometry). -/
  | open_
  /-- Flat universe (Euclidean geometry). -/
  | flat
  /-- Closed universe (spherical geometry). -/
  | closed

/-- Numerical value of the curvature parameter. -/
def SpatialCurvature.toReal : SpatialCurvature → ℝ
  | .open_ => -1
  | .flat => 0
  | .closed => 1

/-- Friedmann equation: H² = 8πG/3 · ρ - k/a².
    Relates the expansion rate to the energy density and curvature. -/
noncomputable def friedmannEquation (model : CosmologicalModel)
    (ρ : ℝ → ℝ) (k : SpatialCurvature) (t : ℝ) : Prop :=
  model.hubbleParameter t ^ 2 =
    8 * Real.pi * G_cosmo / 3 * ρ t - k.toReal / model.a t ^ 2

/-- A cosmological model satisfies the Friedmann equation at all times. -/
def SatisfiesFriedmann (model : CosmologicalModel)
    (ρ : ℝ → ℝ) (k : SpatialCurvature) : Prop :=
  ∀ t : ℝ, friedmannEquation model ρ k t

/-- For a flat universe (k = 0), the Friedmann equation simplifies to
    H² = 8πG/3 · ρ. -/
theorem friedmann_flat (model : CosmologicalModel) (ρ : ℝ → ℝ) (t : ℝ)
    (h : friedmannEquation model ρ .flat t) :
    model.hubbleParameter t ^ 2 = 8 * Real.pi * G_cosmo / 3 * ρ t := by
  unfold friedmannEquation at h
  simp [SpatialCurvature.toReal] at h
  linarith

/-! ## Cosmological Redshift -/

/-- Cosmological redshift: 1 + z = a₀ / a(t_emit).
    Light emitted at scale factor a is redshifted by the expansion. -/
noncomputable def cosmologicalRedshift (a₀ a_emit : ℝ) : ℝ :=
  a₀ / a_emit - 1

/-- The redshift relation: 1 + z = a₀ / a. -/
noncomputable def onePlusRedshift (a₀ a_emit : ℝ) : ℝ :=
  a₀ / a_emit

/-- Redshift is zero when a = a₀ (present epoch). -/
theorem redshift_at_present (a₀ : ℝ) (ha : a₀ ≠ 0) :
    cosmologicalRedshift a₀ a₀ = 0 := by
  unfold cosmologicalRedshift
  rw [div_self ha]
  ring

/-- Redshift is positive for a_emit < a₀ (past emission). -/
theorem redshift_positive (a₀ a_emit : ℝ) (ha₀ : 0 < a₀)
    (ha_emit : 0 < a_emit) (h : a_emit < a₀) :
    0 < cosmologicalRedshift a₀ a_emit := by
  unfold cosmologicalRedshift
  have h1 : 0 < a₀ / a_emit := div_pos ha₀ ha_emit
  have h2 : 1 < a₀ / a_emit := by
    rw [one_lt_div ha_emit]
    exact h
  linarith

/-! ## Critical Density -/

/-- Critical density: ρ_c = 3H² / (8πG).
    The density at which the universe is spatially flat. -/
noncomputable def criticalDensity (H : ℝ) : ℝ :=
  3 * H ^ 2 / (8 * Real.pi * G_cosmo)

/-- Critical density is non-negative. -/
theorem criticalDensity_nonneg (H : ℝ) :
    0 ≤ criticalDensity H := by
  unfold criticalDensity
  apply div_nonneg
  · apply mul_nonneg
    · linarith
    · exact sq_nonneg H
  · apply mul_nonneg
    · apply mul_nonneg
      · linarith
      · exact Real.pi_nonneg
    · unfold G_cosmo
      positivity

/-- For a flat universe, ρ = ρ_c (the density equals the critical density). -/
theorem flat_universe_density (model : CosmologicalModel) (ρ : ℝ → ℝ) (t : ℝ)
    (h : friedmannEquation model ρ .flat t) :
    ρ t = criticalDensity (model.hubbleParameter t) := by
  unfold friedmannEquation at h
  unfold criticalDensity
  simp [SpatialCurvature.toReal] at h
  -- h : model.hubbleParameter t ^ 2 = 8 * Real.pi * G_cosmo / 3 * ρ t
  have hG : (0 : ℝ) < G_cosmo := by unfold G_cosmo; positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h8piG : (0 : ℝ) < 8 * Real.pi * G_cosmo := by positivity
  rw [h]
  field_simp

/-! ## Density Parameter -/

/-- Density parameter: Ω = ρ / ρ_c.
    Ω = 1 for a flat universe, Ω < 1 for open, Ω > 1 for closed. -/
noncomputable def densityParameter (ρ H : ℝ) : ℝ :=
  ρ / criticalDensity H

/-- Density parameters for the multi-component universe. -/
structure DensityParameters where
  /-- Matter density parameter Ω_m. -/
  Ω_m : ℝ
  /-- Radiation density parameter Ω_r. -/
  Ω_r : ℝ
  /-- Dark energy density parameter Ω_Λ. -/
  Ω_Λ : ℝ
  /-- Curvature density parameter Ω_k. -/
  Ω_k : ℝ

/-- Closure relation: Ω_m + Ω_r + Ω_Λ + Ω_k = 1. -/
def DensityParameters.satisfiesClosure (p : DensityParameters) : Prop :=
  p.Ω_m + p.Ω_r + p.Ω_Λ + p.Ω_k = 1

/-- A flat universe has Ω_k = 0, so Ω_m + Ω_r + Ω_Λ = 1. -/
def DensityParameters.isFlat (p : DensityParameters) : Prop :=
  p.Ω_k = 0

/-- Flatness implies the sum of matter, radiation, and dark energy is unity. -/
theorem flat_closure (p : DensityParameters)
    (hclosure : p.satisfiesClosure) (hflat : p.isFlat) :
    p.Ω_m + p.Ω_r + p.Ω_Λ = 1 := by
  unfold DensityParameters.satisfiesClosure at hclosure
  unfold DensityParameters.isFlat at hflat
  linarith

/-- Observed density parameters (Planck 2018). -/
noncomputable def planck2018Params : DensityParameters where
  Ω_m := 0.315
  Ω_r := 9.1e-5
  Ω_Λ := 0.685
  Ω_k := 0

/-- For Ω = 1, the density equals the critical density. -/
theorem omega_one_is_critical (ρ H : ℝ) (hH : H ≠ 0)
    (h : densityParameter ρ H = 1) :
    ρ = criticalDensity H := by
  unfold densityParameter at h
  have hcd : criticalDensity H ≠ 0 := by
    unfold criticalDensity
    apply ne_of_gt
    apply div_pos
    · apply mul_pos
      · linarith
      · positivity
    · apply mul_pos
      · apply mul_pos
        · linarith
        · exact Real.pi_pos
      · unfold G_cosmo; positivity
  exact (div_eq_one_iff_eq hcd).mp h

/-! ## Deceleration Parameter -/

/-- Deceleration parameter: q = -a ä / ȧ².
    q > 0 means decelerating expansion, q < 0 means accelerating. -/
noncomputable def decelerationParameter (model : CosmologicalModel) (t : ℝ) : ℝ :=
  -(model.a t * deriv (deriv model.a) t) / (deriv model.a t) ^ 2

/-- In terms of density parameters (matter-dominated + dark energy):
    q = Ω_m/2 - Ω_Λ. -/
noncomputable def decelerationFromDensity (Ω_m Ω_Λ : ℝ) : ℝ :=
  Ω_m / 2 - Ω_Λ

/-- The universe accelerates when Ω_Λ > Ω_m / 2. -/
theorem acceleration_condition (Ω_m Ω_Λ : ℝ) (h : Ω_Λ > Ω_m / 2) :
    decelerationFromDensity Ω_m Ω_Λ < 0 := by
  unfold decelerationFromDensity
  linarith

/-- The universe decelerates when Ω_Λ < Ω_m / 2. -/
theorem deceleration_condition (Ω_m Ω_Λ : ℝ) (h : Ω_Λ < Ω_m / 2) :
    0 < decelerationFromDensity Ω_m Ω_Λ := by
  unfold decelerationFromDensity
  linarith

end Measure.Physics.Astrophysics
