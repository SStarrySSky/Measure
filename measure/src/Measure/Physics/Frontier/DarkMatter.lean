/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dark matter — candidate particles, halo models, rotation curves,
and direct detection principles.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Measure.Physics.Frontier

/-! ## Dark Matter Candidate Particles -/

/-- Classification of dark matter candidate particles. -/
inductive DarkMatterCandidate where
  /-- Weakly Interacting Massive Particle. -/
  | wimp
  /-- Axion: light pseudoscalar from Peccei-Quinn symmetry breaking. -/
  | axion
  /-- Sterile neutrino: right-handed neutrino with keV-scale mass. -/
  | sterileNeutrino
  /-- Primordial black hole. -/
  | primordialBlackHole
  /-- Gravitino: supersymmetric partner of the graviton. -/
  | gravitino
  /-- Fuzzy dark matter: ultralight scalar (m ~ 10⁻²² eV). -/
  | fuzzy

/-- Properties of a dark matter candidate. -/
structure DMCandidateProps where
  /-- The candidate type. -/
  candidate : DarkMatterCandidate
  /-- Mass in eV/c². -/
  mass : ℝ
  /-- Mass is positive. -/
  mass_pos : 0 < mass
  /-- Interaction cross section in cm² (with nucleons). -/
  crossSection : ℝ
  /-- Cross section is non-negative. -/
  crossSection_nonneg : 0 ≤ crossSection

/-- WIMP miracle: the thermal relic cross section ⟨σv⟩ ≈ 3 × 10⁻²⁶ cm³/s
    naturally gives the observed dark matter density. -/
noncomputable def wimpMiracleCrossSection : ℝ := 3e-26

/-! ## NFW Dark Matter Halo Profile -/

/-- Navarro-Frenk-White (NFW) profile parameters.
    ρ(r) = ρ_s / ((r/r_s)(1 + r/r_s)²). -/
structure NFWProfile where
  /-- Scale density ρ_s (kg/m³). -/
  rho_s : ℝ
  /-- Scale radius r_s (m). -/
  r_s : ℝ
  /-- Scale density is positive. -/
  rho_s_pos : 0 < rho_s
  /-- Scale radius is positive. -/
  r_s_pos : 0 < r_s

/-- NFW density at radius r: ρ(r) = ρ_s / ((r/r_s)(1 + r/r_s)²). -/
noncomputable def NFWProfile.density (p : NFWProfile) (r : ℝ) : ℝ :=
  p.rho_s / ((r / p.r_s) * (1 + r / p.r_s) ^ 2)

/-- The concentration parameter c = r_vir / r_s. -/
noncomputable def NFWProfile.concentration (p : NFWProfile) (r_vir : ℝ) : ℝ :=
  r_vir / p.r_s

/-- NFW enclosed mass M(r) = 4π ρ_s r_s³ [ln(1 + r/r_s) - (r/r_s)/(1 + r/r_s)]. -/
noncomputable def NFWProfile.enclosedMass (p : NFWProfile) (r : ℝ) : ℝ :=
  4 * Real.pi * p.rho_s * p.r_s ^ 3 *
    (Real.log (1 + r / p.r_s) - (r / p.r_s) / (1 + r / p.r_s))

/-! ## Rotation Curves -/

/-- Gravitational constant G (m³ kg⁻¹ s⁻²). -/
noncomputable def G_grav : ℝ := 6.67430e-11

/-- Keplerian rotation velocity: v(r) = √(GM/r).
    Expected for a point mass or outside a spherical mass distribution. -/
noncomputable def keplerianVelocity (M r : ℝ) : ℝ :=
  Real.sqrt (G_grav * M / r)

/-- Observed flat rotation curve velocity at large radii.
    v(r) ≈ const, inconsistent with Keplerian falloff. -/
structure RotationCurve where
  /-- Observed velocity as a function of radius. -/
  v_obs : ℝ → ℝ
  /-- Baryonic (visible) mass enclosed as a function of radius. -/
  M_baryon : ℝ → ℝ

/-- The rotation curve anomaly: the ratio of observed to Keplerian velocity.
    Values > 1 indicate missing mass (dark matter). -/
noncomputable def RotationCurve.anomalyRatio (rc : RotationCurve) (r : ℝ) : ℝ :=
  rc.v_obs r / keplerianVelocity (rc.M_baryon r) r

/-- NFW halo rotation velocity: v(r) = √(G M(r) / r). -/
noncomputable def NFWProfile.rotationVelocity (p : NFWProfile) (r : ℝ) : ℝ :=
  Real.sqrt (G_grav * p.enclosedMass r / r)

/-- The total rotation velocity combining baryonic and dark matter contributions:
    v_total² = v_baryon² + v_DM². -/
noncomputable def totalRotationVelocity (v_baryon v_DM : ℝ) : ℝ :=
  Real.sqrt (v_baryon ^ 2 + v_DM ^ 2)

/-! ## Direct Detection -/

/-- Dark matter direct detection: a WIMP scatters off a nucleus,
    depositing recoil energy E_R. -/
structure DirectDetectionEvent where
  /-- Nuclear recoil energy (keV). -/
  recoilEnergy : ℝ
  /-- Target nucleus mass number A. -/
  targetMassNumber : ℕ
  /-- WIMP mass (GeV/c²). -/
  wimpMass : ℝ
  /-- Recoil energy is positive. -/
  recoil_pos : 0 < recoilEnergy

/-- Maximum recoil energy for elastic WIMP-nucleus scattering:
    E_R^max = 2μ²v²/m_N where μ is the reduced mass. -/
noncomputable def maxRecoilEnergy (m_wimp m_nucleus v : ℝ) : ℝ :=
  let μ := m_wimp * m_nucleus / (m_wimp + m_nucleus)
  2 * μ ^ 2 * v ^ 2 / m_nucleus

/-- Spin-independent WIMP-nucleon cross section scales as A²
    (coherent enhancement). -/
noncomputable def coherentEnhancement (σ_n : ℝ) (A : ℕ) : ℝ :=
  σ_n * (A : ℝ) ^ 2

/-- Annual modulation: the detection rate varies sinusoidally due to
    Earth's orbital motion through the dark matter halo.
    R(t) = R₀ + R_m cos(2π(t - t₀)/T) where T = 1 year. -/
noncomputable def annualModulationRate (R₀ R_m t t₀ : ℝ) : ℝ :=
  R₀ + R_m * Real.cos (2 * Real.pi * (t - t₀) / 365.25)

end Measure.Physics.Frontier
