/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Approximate theories: well-established theories that are known to be
limiting cases of more fundamental theories. Each is annotated with
its validity conditions, the exact theory it approximates, and the
order of magnitude of the approximation error.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Measure.Physics.Historical

/-! ## Newtonian Gravity

Newton's law of universal gravitation (1687).
Exact theory: General relativity (Einstein, 1915).
Valid when: v ≪ c, Φ/c² ≪ 1 (weak field), no strong curvature.
Error: O(v²/c²) or O(GM/(rc²)). -/

/-- Newtonian gravitational constant. -/
noncomputable def G : ℝ := 6.67430e-11

/-- Speed of light. -/
noncomputable def c_light : ℝ := 299792458

-- For the formal theory-block version with dimensional type safety,
-- see Measure.Examples.NewtonianGravity

/-- Newtonian gravity as an approximate theory.
    Exact theory: general relativity (Einstein, 1915).
    Valid when v ≪ c and Φ/c² ≪ 1.
    Error magnitude: O(v²/c² + GM/(rc²)). -/
structure NewtonianGravity where
  /-- Gravitational potential Φ(r) at distance r from mass M. -/
  potential : ℝ → ℝ
  /-- Source mass (kg). -/
  mass : ℝ
  mass_pos : 0 < mass

/-- Newtonian gravitational potential: Φ(r) = -GM/r. -/
noncomputable def newtonianPotential (M r : ℝ) : ℝ :=
  -G * M / r

/-- Newtonian gravitational force: F = -GMm/r². -/
noncomputable def newtonianForce (M m r : ℝ) : ℝ :=
  -G * M * m / r ^ 2

/-- Validity parameter for Newtonian gravity: Φ/c² ≪ 1.
    For Earth's surface: Φ/c² ≈ 7 × 10⁻¹⁰.
    For Sun's surface: Φ/c² ≈ 2 × 10⁻⁶.
    For neutron star: Φ/c² ≈ 0.2 (Newtonian gravity breaks down). -/
noncomputable def gravitationalWeakFieldParam (M r : ℝ) : ℝ :=
  G * M / (r * c_light ^ 2)

/-- First post-Newtonian correction to the gravitational potential.
    Φ_PN = Φ_N · (1 + O(v²/c²)). The leading GR correction is of order Φ/c². -/
noncomputable def postNewtonianCorrection (M r v : ℝ) : ℝ :=
  newtonianPotential M r * (1 + v ^ 2 / c_light ^ 2 +
    G * M / (r * c_light ^ 2))

/-! ## Classical Electrodynamics

Maxwell's equations (1865) with the Lorentz force law.
Exact theory: Quantum electrodynamics (QED, Feynman-Schwinger-Tomonaga, 1948).
Valid when: photon energies ≪ mₑc² (511 keV), field strengths ≪ Schwinger limit.
Error: O(α) ≈ O(1/137) for quantum corrections. -/

/-- Fine structure constant α ≈ 1/137. -/
noncomputable def fineStructureConstant : ℝ := 1 / 137.035999084

-- For the formal theory-block version with dimensional type safety,
-- see Measure.Examples.ElectromagneticWave

/-- Classical electrodynamics as an approximate theory.
    Exact theory: quantum electrodynamics (QED).
    Valid when photon energy ≪ 511 keV and E ≪ E_Schwinger.
    Error magnitude: O(α) ≈ O(1/137) per loop correction. -/
structure ClassicalElectrodynamics where
  /-- Electric field magnitude (V/m). -/
  fieldStrength : ℝ
  /-- Characteristic photon energy (J). -/
  photonEnergy : ℝ
  fieldStrength_nonneg : 0 ≤ fieldStrength
  photonEnergy_nonneg : 0 ≤ photonEnergy

/-- Schwinger critical field: E_S = m²c³/(eℏ) ≈ 1.32 × 10¹⁸ V/m.
    Above this field strength, vacuum pair production becomes significant
    and classical electrodynamics breaks down. -/
noncomputable def schwingerField : ℝ := 1.3232e18

/-- Electron rest energy: mₑc² ≈ 8.187 × 10⁻¹⁴ J ≈ 511 keV.
    Classical ED breaks down when photon energies approach this scale. -/
noncomputable def electronRestEnergy : ℝ := 8.1871057769e-14

/-- Validity check: classical ED is valid when both conditions hold. -/
noncomputable def ClassicalElectrodynamics.isValid (ced : ClassicalElectrodynamics) : Prop :=
  ced.photonEnergy < electronRestEnergy ∧ ced.fieldStrength < schwingerField

/-- Leading QED correction to the electron magnetic moment:
    g = 2(1 + α/(2π) + ...). The anomalous magnetic moment a = (g-2)/2. -/
noncomputable def anomalousMagneticMoment : ℝ :=
  fineStructureConstant / (2 * Real.pi)

/-! ## Non-Relativistic Quantum Mechanics

Schrödinger equation (1926) and non-relativistic quantum theory.
Exact theory: Quantum field theory (QFT).
Valid when: particle energies ≪ rest mass energy, no particle creation/annihilation.
Error: O(v²/c²) for kinematic corrections, O(α) for radiative corrections. -/

/-- Non-relativistic quantum mechanics as an approximate theory.
    Exact theory: relativistic quantum field theory.
    Valid when kinetic energy ≪ mc² and no pair production.
    Error magnitude: O(v²/c²) for relativistic corrections. -/
structure NonRelQM where
  /-- Particle mass (kg). -/
  particleMass : ℝ
  /-- Characteristic kinetic energy (J). -/
  kineticEnergy : ℝ
  particleMass_pos : 0 < particleMass
  kineticEnergy_nonneg : 0 ≤ kineticEnergy

/-- Validity parameter: E_kin / (mc²). Must be ≪ 1 for NRQM to hold. -/
noncomputable def NonRelQM.validityParam (nrqm : NonRelQM) : ℝ :=
  nrqm.kineticEnergy / (nrqm.particleMass * c_light ^ 2)

/-- Leading relativistic correction to kinetic energy:
    E = p²/(2m) - p⁴/(8m³c²) + ...
    The second term is the leading error of NRQM. -/
noncomputable def relativisticKineticCorrection (p m : ℝ) : ℝ :=
  -p ^ 4 / (8 * m ^ 3 * c_light ^ 2)

/-! ## Geometrical Optics

Ray optics: light travels in straight lines, reflects and refracts.
Exact theory: Wave optics (physical optics, Maxwell's equations).
Valid when: feature sizes ≫ wavelength λ, i.e., λ/a → 0.
Error: O(λ/a) where a is the characteristic length scale. -/

/-- Geometrical optics as an approximate theory.
    Exact theory: wave optics (Maxwell's equations).
    Valid when λ ≪ a (characteristic feature size).
    Error magnitude: O(λ/a). Diffraction effects are O(λ/a). -/
structure GeometricalOptics where
  /-- Wavelength of light (m). -/
  wavelength : ℝ
  /-- Characteristic feature size (m). -/
  featureSize : ℝ
  wavelength_pos : 0 < wavelength
  featureSize_pos : 0 < featureSize

/-- Validity parameter: λ/a. Must be ≪ 1 for geometrical optics. -/
noncomputable def GeometricalOptics.validityParam (go : GeometricalOptics) : ℝ :=
  go.wavelength / go.featureSize

/-- Snell's law: n₁ sin θ₁ = n₂ sin θ₂.
    Valid in both geometrical and wave optics. -/
noncomputable def snellsLaw (n₁ n₂ θ₁ : ℝ) : ℝ :=
  Real.arcsin (n₁ * Real.sin θ₁ / n₂)

/-- Fresnel number: N_F = a²/(λL). When N_F ≫ 1, geometrical optics applies.
    When N_F ~ 1, Fresnel diffraction is important.
    When N_F ≪ 1, Fraunhofer diffraction dominates. -/
noncomputable def fresnelNumber (a wl L : ℝ) : ℝ :=
  a ^ 2 / (wl * L)

/-! ## Rigid Body Mechanics

Treats extended bodies as having fixed shape and size.
Exact theory: Continuum mechanics (elasticity theory).
Valid when: applied stresses ≪ elastic modulus, deformations ≪ body size.
Error: O(σ/E) where σ is stress and E is Young's modulus. -/

/-- Rigid body mechanics as an approximate theory.
    Exact theory: continuum mechanics (elasticity, plasticity).
    Valid when deformations are negligible: σ ≪ E (Young's modulus).
    Error magnitude: O(σ/E) = O(strain). -/
structure RigidBodyApprox where
  /-- Mass of the body (kg). -/
  mass : ℝ
  /-- Moment of inertia tensor (kg·m²), represented as 3×3 matrix. -/
  inertia : Matrix (Fin 3) (Fin 3) ℝ
  /-- Young's modulus of the material (Pa). -/
  youngsModulus : ℝ
  /-- Applied stress (Pa). -/
  appliedStress : ℝ
  mass_pos : 0 < mass
  youngsModulus_pos : 0 < youngsModulus
  appliedStress_nonneg : 0 ≤ appliedStress

/-- Validity parameter: σ/E (strain). Must be ≪ 1 for rigid body approx. -/
noncomputable def RigidBodyApprox.validityParam (rb : RigidBodyApprox) : ℝ :=
  rb.appliedStress / rb.youngsModulus

/-- Euler's rotation equation for a rigid body: I·α + ω × (I·ω) = τ.
    This is the rotational analog of F = ma, valid only for rigid bodies. -/
noncomputable def eulerRotationTorque
    (I : Matrix (Fin 3) (Fin 3) ℝ) (ω α : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let Iω := I.mulVec ω
  let Iα := I.mulVec α
  let cross : Fin 3 → ℝ := fun i =>
    match i with
    | ⟨0, _⟩ => ω ⟨1, by omega⟩ * Iω ⟨2, by omega⟩ - ω ⟨2, by omega⟩ * Iω ⟨1, by omega⟩
    | ⟨1, _⟩ => ω ⟨2, by omega⟩ * Iω ⟨0, by omega⟩ - ω ⟨0, by omega⟩ * Iω ⟨2, by omega⟩
    | ⟨2, _⟩ => ω ⟨0, by omega⟩ * Iω ⟨1, by omega⟩ - ω ⟨1, by omega⟩ * Iω ⟨0, by omega⟩
    | ⟨n+3, h⟩ => absurd h (by omega)
  fun i => Iα i + cross i

end Measure.Physics.Historical
