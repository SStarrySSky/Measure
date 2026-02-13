/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Atmospheric physics — barometric formula, adiabatic lapse rate,
Coriolis force, and geostrophic wind equations.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Measure.Physics.Geophysics.Atmosphere

/-! ## Atmospheric Constants -/

/-- Physical constants for atmospheric calculations. -/
structure AtmosphericConstants where
  /-- Gravitational acceleration g (m/s²). -/
  g : ℝ
  /-- Molar mass of dry air M (kg/mol). -/
  M : ℝ
  /-- Universal gas constant R (J/(mol·K)). -/
  R : ℝ
  /-- Boltzmann constant k_B (J/K). -/
  kB : ℝ
  /-- All constants are positive. -/
  g_pos : 0 < g
  M_pos : 0 < M
  R_pos : 0 < R
  kB_pos : 0 < kB

/-- Standard atmospheric constants. -/
noncomputable def stdAtmConstants : AtmosphericConstants where
  g := 9.80665
  M := 0.0289644
  R := 8.31446
  kB := 1.380649e-23
  g_pos := by norm_num
  M_pos := by norm_num
  R_pos := by norm_num
  kB_pos := by norm_num

/-! ## Barometric Formula -/

/-- The barometric formula for an isothermal atmosphere:
    P(h) = P₀ exp(-Mgh / RT).
    Describes how atmospheric pressure decreases with altitude. -/
noncomputable def barometricPressure (ac : AtmosphericConstants)
    (P₀ T h : ℝ) : ℝ :=
  P₀ * Real.exp (-ac.M * ac.g * h / (ac.R * T))

/-- At ground level (h = 0), the pressure equals the reference pressure. -/
theorem barometric_at_ground (ac : AtmosphericConstants) (P₀ T : ℝ) :
    barometricPressure ac P₀ T 0 = P₀ := by
  simp [barometricPressure]

/-- Pressure decreases with altitude in an isothermal atmosphere. -/
theorem barometric_decreasing (ac : AtmosphericConstants) (P₀ T h₁ h₂ : ℝ)
    (hP : 0 < P₀) (hT : 0 < T) (hh : h₁ < h₂) :
    barometricPressure ac P₀ T h₂ < barometricPressure ac P₀ T h₁ := by
  unfold barometricPressure
  apply mul_lt_mul_of_pos_left _ hP
  apply Real.exp_lt_exp.mpr
  have hRT : 0 < ac.R * T := mul_pos ac.R_pos hT
  have hMg : 0 < ac.M * ac.g := mul_pos ac.M_pos ac.g_pos
  -- Need: -ac.M * ac.g * h₂ / (ac.R * T) < -ac.M * ac.g * h₁ / (ac.R * T)
  apply div_lt_div_of_pos_right _ hRT
  nlinarith

/-- The pressure scale height H = RT/(Mg).
    The altitude at which pressure drops by a factor of e. -/
noncomputable def scaleHeight (ac : AtmosphericConstants) (T : ℝ) : ℝ :=
  ac.R * T / (ac.M * ac.g)

/-- The scale height is positive. -/
theorem scaleHeight_pos (ac : AtmosphericConstants) (T : ℝ) (hT : 0 < T) :
    0 < scaleHeight ac T :=
  div_pos (mul_pos ac.R_pos hT) (mul_pos ac.M_pos ac.g_pos)

/-- At one scale height, pressure drops to P₀/e. -/
theorem barometric_at_scaleHeight (ac : AtmosphericConstants) (P₀ T : ℝ)
    (_hT : 0 < T) :
    barometricPressure ac P₀ T (scaleHeight ac T) =
      P₀ * Real.exp (-1) := by
  unfold barometricPressure scaleHeight
  congr 1
  have hM : ac.M ≠ 0 := ne_of_gt ac.M_pos
  have hg : ac.g ≠ 0 := ne_of_gt ac.g_pos
  have hR : ac.R ≠ 0 := ne_of_gt ac.R_pos
  have hT' : T ≠ 0 := ne_of_gt _hT
  field_simp

/-- The hypsometric equation: the thickness of a layer between two
    pressure levels. Δz = (RT/Mg) ln(P₁/P₂). -/
noncomputable def hypsometricThickness (ac : AtmosphericConstants)
    (T P₁ P₂ : ℝ) : ℝ :=
  (ac.R * T / (ac.M * ac.g)) * Real.log (P₁ / P₂)

/-! ## Adiabatic Lapse Rate -/

/-- The dry adiabatic lapse rate: Γ_d = g / c_p.
    Rate of temperature decrease with altitude for a dry air parcel
    rising adiabatically. -/
noncomputable def dryAdiabaticLapseRate (g c_p : ℝ) : ℝ :=
  g / c_p

/-- Standard dry adiabatic lapse rate ≈ 9.8 K/km.
    Using g = 9.80665 m/s² and c_p = 1004 J/(kg·K). -/
noncomputable def stdDryLapseRate : ℝ :=
  dryAdiabaticLapseRate 9.80665 1004

/-- The moist adiabatic lapse rate (saturated): Γ_m = Γ_d · (1 + L_v r_s / (R_d T)) /
    (1 + L_v² r_s / (c_p R_v T²)).
    Always less than the dry lapse rate due to latent heat release. -/
noncomputable def moistAdiabaticLapseRate (Γ_d L_v r_s R_d R_v c_p T : ℝ) : ℝ :=
  Γ_d * (1 + L_v * r_s / (R_d * T)) /
    (1 + L_v ^ 2 * r_s / (c_p * R_v * T ^ 2))

/-- Temperature as a function of altitude under dry adiabatic conditions:
    T(h) = T₀ - Γ_d · h. -/
noncomputable def adiabaticTemperature (T₀ Γ h : ℝ) : ℝ :=
  T₀ - Γ * h

/-- The potential temperature θ = T (P₀/P)^(R/c_p).
    Conserved for adiabatic processes. -/
noncomputable def potentialTemperature (T P P₀ R c_p : ℝ) : ℝ :=
  T * Real.exp (R / c_p * Real.log (P₀ / P))

/-- Atmospheric stability: the atmosphere is stable if the environmental
    lapse rate is less than the adiabatic lapse rate. -/
def IsStableAtmosphere (envLapseRate adiabaticLapseRate : ℝ) : Prop :=
  envLapseRate < adiabaticLapseRate

/-- An unstable atmosphere has environmental lapse rate exceeding the
    adiabatic lapse rate (promotes convection). -/
def IsUnstableAtmosphere (envLapseRate adiabaticLapseRate : ℝ) : Prop :=
  adiabaticLapseRate < envLapseRate

/-! ## Coriolis Force -/

/-- The Coriolis parameter f = 2Ω sin(φ) where Ω is Earth's angular
    velocity and φ is latitude. -/
noncomputable def coriolisParameter (Ω φ : ℝ) : ℝ :=
  2 * Ω * Real.sin φ

/-- Earth's angular velocity Ω ≈ 7.2921 × 10⁻⁵ rad/s. -/
noncomputable def earthAngularVelocity : ℝ := 7.2921e-5

/-- The Coriolis parameter is zero at the equator (φ = 0). -/
theorem coriolis_zero_at_equator (Ω : ℝ) :
    coriolisParameter Ω 0 = 0 := by
  simp [coriolisParameter, Real.sin_zero]

/-- The Coriolis acceleration for horizontal motion:
    a_C = -f × v = (-f·v_y, f·v_x) in the horizontal plane. -/
noncomputable def coriolisAcceleration (f : ℝ) (vx vy : ℝ) : ℝ × ℝ :=
  (f * vy, -f * vx)

/-- The beta parameter β = df/dy = (2Ω/R_E) cos(φ).
    Measures the variation of the Coriolis parameter with latitude. -/
noncomputable def betaParameter (Ω R_E φ : ℝ) : ℝ :=
  2 * Ω * Real.cos φ / R_E

/-- The beta-plane approximation: f ≈ f₀ + βy. -/
noncomputable def betaPlaneApprox (f₀ beta y : ℝ) : ℝ :=
  f₀ + beta * y

/-! ## Geostrophic Wind -/

/-- The geostrophic wind equations: the balance between Coriolis force
    and pressure gradient force.
    u_g = -(1/ρf) ∂P/∂y,  v_g = (1/ρf) ∂P/∂x. -/
structure GeostrophicWind where
  /-- Zonal (east-west) component u_g. -/
  u : ℝ
  /-- Meridional (north-south) component v_g. -/
  v : ℝ

/-- Compute geostrophic wind from pressure gradients.
    u_g = -(1/ρf) ∂P/∂y,  v_g = (1/ρf) ∂P/∂x. -/
noncomputable def geostrophicWindFromPressure (ρ f dPdx dPdy : ℝ) :
    GeostrophicWind where
  u := -(1 / (ρ * f)) * dPdy
  v := (1 / (ρ * f)) * dPdx

/-- The geostrophic wind balance: Coriolis force equals pressure gradient.
    fρu_g = -∂P/∂y and fρv_g = ∂P/∂x. -/
theorem geostrophic_balance (ρ f dPdx dPdy : ℝ)
    (hρ : ρ ≠ 0) (hf : f ≠ 0) :
    let w := geostrophicWindFromPressure ρ f dPdx dPdy
    f * ρ * w.u = -dPdy ∧ f * ρ * w.v = dPdx := by
  simp [geostrophicWindFromPressure]
  constructor <;> field_simp

/-- The thermal wind equation relates vertical wind shear to horizontal
    temperature gradients: ∂u_g/∂z = -(g/fT) ∂T/∂y. -/
noncomputable def thermalWindShear (g f T dTdy : ℝ) : ℝ :=
  -(g / (f * T)) * dTdy

/-- The Rossby number Ro = U/(fL) measures the importance of Coriolis
    effects. Ro << 1 means geostrophic balance is a good approximation. -/
noncomputable def rossbyNumber (U f L : ℝ) : ℝ :=
  U / (f * L)

/-- Geostrophic balance is valid when the Rossby number is small. -/
def IsGeostrophic (Ro : ℝ) : Prop :=
  Ro < 0.1

end Measure.Physics.Geophysics.Atmosphere
