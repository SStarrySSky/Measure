/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Stellar structure — hydrostatic equilibrium, mass continuity,
luminosity equation, mass-luminosity relation, and Eddington limit.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Measure.Physics.Astrophysics

/-! ## Physical Constants -/

/-- Gravitational constant G (m³ kg⁻¹ s⁻²). -/
noncomputable def G : ℝ := 6.67430e-11

/-- Speed of light c (m/s). -/
noncomputable def c_light : ℝ := 299792458

/-- Stefan-Boltzmann constant σ (W m⁻² K⁻⁴). -/
noncomputable def σ_SB : ℝ := 5.670374419e-8

/-- Thomson scattering cross section σ_T (m²). -/
noncomputable def σ_T : ℝ := 6.6524587321e-29

/-- Proton mass m_p (kg). -/
noncomputable def m_p : ℝ := 1.67262192369e-27

/-- Solar luminosity L☉ (W). -/
noncomputable def L_sun : ℝ := 3.828e26

/-- Solar mass M☉ (kg). -/
noncomputable def M_sun : ℝ := 1.989e30

/-! ## Stellar Model Parameters -/

/-- A spherically symmetric stellar model parameterized by radius. -/
structure StellarModel where
  /-- Pressure P(r) (Pa). -/
  P : ℝ → ℝ
  /-- Density ρ(r) (kg/m³). -/
  ρ : ℝ → ℝ
  /-- Enclosed mass m(r) (kg). -/
  m : ℝ → ℝ
  /-- Luminosity L(r) (W). -/
  L : ℝ → ℝ
  /-- Temperature T(r) (K). -/
  T : ℝ → ℝ
  /-- Energy generation rate per unit mass ε(r) (W/kg). -/
  ε : ℝ → ℝ
  /-- Density is non-negative. -/
  ρ_nonneg : ∀ r, 0 ≤ ρ r

/-! ## Hydrostatic Equilibrium -/

/-- Hydrostatic equilibrium equation: dP/dr = -G ρ(r) m(r) / r².
    The pressure gradient balances gravitational attraction. -/
noncomputable def hydrostaticEquilibrium (star : StellarModel) (r : ℝ) : Prop :=
  deriv star.P r = -G * star.ρ r * star.m r / r ^ 2

/-- A stellar model satisfies hydrostatic equilibrium at all radii. -/
def SatisfiesHydrostaticEquilibrium (star : StellarModel) : Prop :=
  ∀ r : ℝ, 0 < r → hydrostaticEquilibrium star r

/-! ## Mass Continuity -/

/-- Mass continuity equation: dm/dr = 4π r² ρ(r).
    The enclosed mass increases with the density at each shell. -/
noncomputable def massContinuity (star : StellarModel) (r : ℝ) : Prop :=
  deriv star.m r = 4 * Real.pi * r ^ 2 * star.ρ r

/-- A stellar model satisfies mass continuity at all radii. -/
def SatisfiesMassContinuity (star : StellarModel) : Prop :=
  ∀ r : ℝ, 0 < r → massContinuity star r

/-! ## Luminosity Equation -/

/-- Luminosity equation: dL/dr = 4π r² ρ(r) ε(r).
    Energy generation in each shell contributes to the total luminosity. -/
noncomputable def luminosityEquation (star : StellarModel) (r : ℝ) : Prop :=
  deriv star.L r = 4 * Real.pi * r ^ 2 * star.ρ r * star.ε r

/-- A stellar model satisfies the luminosity equation at all radii. -/
def SatisfiesLuminosityEquation (star : StellarModel) : Prop :=
  ∀ r : ℝ, 0 < r → luminosityEquation star r

/-! ## Complete Stellar Structure -/

/-- A stellar model satisfies all three structure equations. -/
def SatisfiesStellarStructure (star : StellarModel) : Prop :=
  SatisfiesHydrostaticEquilibrium star ∧
  SatisfiesMassContinuity star ∧
  SatisfiesLuminosityEquation star

/-! ## Main-Sequence Mass-Luminosity Relation -/

/-- Main-sequence mass-luminosity relation: L/L☉ ≈ (M/M☉)^3.5.
    Empirical relation for main-sequence stars. -/
noncomputable def massLuminosityRelation (M : ℝ) : ℝ :=
  L_sun * (M / M_sun) ^ (3.5 : ℝ)

/-- The mass-luminosity relation gives L☉ for a solar-mass star. -/
theorem massLuminosity_solar :
    massLuminosityRelation M_sun = L_sun := by
  unfold massLuminosityRelation
  have hM : M_sun / M_sun = 1 := div_self (by unfold M_sun; positivity)
  rw [hM, Real.one_rpow]
  ring

/-- More massive stars are more luminous (for positive masses on the main sequence). -/
theorem massLuminosity_monotone (M₁ M₂ : ℝ)
    (hM₁ : 0 < M₁) (_hM₂ : 0 < M₂) (h : M₁ < M₂) :
    massLuminosityRelation M₁ < massLuminosityRelation M₂ := by
  unfold massLuminosityRelation
  have hL : (0 : ℝ) < L_sun := by unfold L_sun; positivity
  have hMs : (0 : ℝ) < M_sun := by unfold M_sun; positivity
  apply mul_lt_mul_of_pos_left _ hL
  apply Real.rpow_lt_rpow (div_nonneg (le_of_lt hM₁) (le_of_lt hMs))
  · exact div_lt_div_of_pos_right h hMs
  · norm_num

/-! ## Eddington Luminosity -/

/-- Eddington luminosity: L_Edd = 4π G M c / κ_es
    where κ_es = σ_T / m_p is the electron scattering opacity.
    This is the maximum luminosity at which radiation pressure
    balances gravity for a fully ionized hydrogen envelope. -/
noncomputable def eddingtonLuminosity (M : ℝ) : ℝ :=
  4 * Real.pi * G * M * c_light * m_p / σ_T

/-- The Eddington luminosity is proportional to mass. -/
theorem eddington_proportional (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    eddingtonLuminosity M₁ / eddingtonLuminosity M₂ = M₁ / M₂ := by
  unfold eddingtonLuminosity
  have hσ : (0 : ℝ) < σ_T := by unfold σ_T; positivity
  have hmp : (0 : ℝ) < m_p := by unfold m_p; positivity
  have hG : (0 : ℝ) < G := by unfold G; positivity
  have hc : (0 : ℝ) < c_light := by unfold c_light; positivity
  field_simp

/-- The Eddington luminosity is positive for positive mass. -/
theorem eddington_pos (M : ℝ) (hM : 0 < M) :
    0 < eddingtonLuminosity M := by
  unfold eddingtonLuminosity
  apply div_pos
  · apply mul_pos
    · apply mul_pos
      · apply mul_pos
        · apply mul_pos
          · apply mul_pos
            · linarith
            · exact Real.pi_pos
          · unfold G; positivity
        · exact hM
      · unfold c_light; positivity
    · unfold m_p; positivity
  · unfold σ_T; positivity

/-- A star is super-Eddington if its luminosity exceeds the Eddington limit. -/
def IsSuperEddington (L M : ℝ) : Prop :=
  eddingtonLuminosity M < L

/-- Eddington ratio: Γ = L / L_Edd. -/
noncomputable def eddingtonRatio (L M : ℝ) : ℝ :=
  L / eddingtonLuminosity M

/-! ## Effective Temperature -/

/-- Stefan-Boltzmann law for stellar luminosity:
    L = 4π R² σ T_eff⁴. -/
noncomputable def stefanBoltzmannLuminosity (R T_eff : ℝ) : ℝ :=
  4 * Real.pi * R ^ 2 * σ_SB * T_eff ^ 4

/-- Effective temperature from luminosity and radius:
    T_eff = (L / (4π R² σ))^(1/4). -/
noncomputable def effectiveTemperature (L R : ℝ) : ℝ :=
  (L / (4 * Real.pi * R ^ 2 * σ_SB)) ^ ((1 : ℝ) / 4)

end Measure.Physics.Astrophysics
