/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Historical quantum models superseded by modern quantum mechanics and QED.
Includes the Bohr model, old quantum theory, classical electron models,
and the BKS theory.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Measure.Physics.Historical

/-! ## Bohr Model (1913)

Niels Bohr's model of the hydrogen atom with quantized circular orbits.
Superseded by the Schrödinger equation (1926) and full quantum mechanics.
Still gives exact energy levels for hydrogen-like atoms (single electron). -/

/-- Physical constants for atomic models. -/
noncomputable def electronMass : ℝ := 9.1093837015e-31
noncomputable def electronCharge : ℝ := 1.602176634e-19
noncomputable def planckConstant : ℝ := 6.62607015e-34
noncomputable def reducedPlanck : ℝ := planckConstant / (2 * Real.pi)
noncomputable def coulombConstant : ℝ := 8.9875517923e9
noncomputable def bohrRadius : ℝ :=
  reducedPlanck ^ 2 / (electronMass * coulombConstant * electronCharge ^ 2)

/-- The Bohr model of hydrogen-like atoms.
    Proposed by Bohr (1913). Superseded by quantum mechanics (1926).
    Exact for hydrogen energy levels; fails for multi-electron atoms,
    fine structure, and angular momentum (predicts L = nℏ, actual L = √(l(l+1))ℏ). -/
structure BohrModel where
  /-- Atomic number Z (number of protons). -/
  Z : ℕ
  /-- Principal quantum number n ≥ 1. -/
  n : ℕ
  n_pos : 0 < n

/-- Bohr orbit radius: rₙ = a₀ n² / Z. -/
noncomputable def BohrModel.orbitRadius (b : BohrModel) : ℝ :=
  bohrRadius * (b.n : ℝ) ^ 2 / (b.Z : ℝ)

/-- Bohr energy levels: Eₙ = -13.6 eV · Z² / n².
    This formula is exact for hydrogen (Z=1) and agrees with
    the Schrödinger equation solution. -/
noncomputable def BohrModel.energy (b : BohrModel) : ℝ :=
  let eV := 1.602176634e-19
  (-13.6) * eV * (b.Z : ℝ) ^ 2 / (b.n : ℝ) ^ 2

/-- Bohr orbital velocity: vₙ = αc · Z / n, where α is the fine structure constant. -/
noncomputable def BohrModel.orbitalVelocity (b : BohrModel) : ℝ :=
  let α := 1 / 137.036
  let c := 299792458
  α * c * (b.Z : ℝ) / (b.n : ℝ)

/-- Bohr angular momentum quantization: L = nℏ.
    This is wrong — actual QM gives L = √(l(l+1))ℏ.
    The ground state (l=0) has zero angular momentum, not ℏ. -/
noncomputable def BohrModel.angularMomentum (b : BohrModel) : ℝ :=
  (b.n : ℝ) * reducedPlanck

/-- Rydberg formula for spectral lines: 1/λ = R_∞ Z² (1/n₁² - 1/n₂²). -/
noncomputable def rydbergFormula (Z n₁ n₂ : ℕ) : ℝ :=
  let R_inf := 1.0973731568160e7  -- Rydberg constant (m⁻¹)
  R_inf * (Z : ℝ) ^ 2 * (1 / (n₁ : ℝ) ^ 2 - 1 / (n₂ : ℝ) ^ 2)

/-! ## Old Quantum Theory — Sommerfeld Quantization (1916)

Extended Bohr's model with elliptical orbits and the quantization condition
∮ pᵢ dqᵢ = nᵢ h. Partially explained fine structure via relativistic corrections.
Superseded by matrix mechanics (Heisenberg, 1925) and wave mechanics
(Schrödinger, 1926). -/

/-- Sommerfeld quantization condition: ∮ p dq = nh for each degree of freedom.
    Proposed by Sommerfeld (1916). Superseded by full quantum mechanics.
    Valid in the semiclassical (WKB) limit for large quantum numbers. -/
structure SommerfeldQuantization where
  /-- Number of degrees of freedom. -/
  dof : ℕ
  /-- Quantum numbers for each degree of freedom. -/
  quantumNumbers : Fin dof → ℕ
  /-- All quantum numbers are positive. -/
  all_pos : ∀ i, 0 < quantumNumbers i

/-- Sommerfeld's relativistic correction to hydrogen energy levels.
    Eₙₖ = E_Bohr · [1 + (αZ)²/n · (1/k - 3/(4n))], where k is the
    azimuthal quantum number. Partially explains fine structure. -/
noncomputable def sommerfeldFineStructure (Z n k : ℕ) : ℝ :=
  let α := 1 / 137.036
  let eV := 1.602176634e-19
  let E_bohr := (-13.6) * eV * (Z : ℝ) ^ 2 / (n : ℝ) ^ 2
  E_bohr * (1 + (α * (Z : ℝ)) ^ 2 / (n : ℝ) * (1 / (k : ℝ) - 3 / (4 * (n : ℝ))))

/-! ## Classical Electron Models

Thomson's plum pudding model (1904) and Rutherford's nuclear model (1911).
Both superseded by quantum mechanics. -/

/-- Thomson's plum pudding model: electrons embedded in a uniform positive charge.
    Proposed by J.J. Thomson (1904). Refuted by Rutherford's gold foil
    experiment (1911). No valid approximation regime. -/
structure ThomsonModel where
  /-- Number of electrons. -/
  numElectrons : ℕ
  /-- Radius of the positive charge sphere (m). -/
  sphereRadius : ℝ
  /-- Total positive charge equals total negative charge. -/
  sphereRadius_pos : 0 < sphereRadius

/-- Thomson model predicted oscillation frequency for electrons in the sphere.
    ω² = Ze²/(4πε₀ m_e R³). -/
noncomputable def ThomsonModel.oscillationFreq (t : ThomsonModel) : ℝ :=
  let ε₀ := 8.854187817e-12
  Real.sqrt ((t.numElectrons : ℝ) * electronCharge ^ 2 /
    (4 * Real.pi * ε₀ * electronMass * t.sphereRadius ^ 3))

/-- Rutherford's nuclear model: electrons orbit a tiny, dense nucleus.
    Proposed by Rutherford (1911). Classically unstable (accelerating charges
    radiate). Superseded by Bohr model (1913) and quantum mechanics (1926). -/
structure RutherfordModel where
  /-- Atomic number (nuclear charge). -/
  Z : ℕ
  /-- Nuclear radius (m). -/
  nuclearRadius : ℝ
  nuclearRadius_pos : 0 < nuclearRadius

/-- Rutherford scattering cross-section: dσ/dΩ = (Zze²/4E)² · 1/sin⁴(θ/2).
    This formula remains valid in classical scattering theory. -/
noncomputable def rutherfordCrossSection (Z₁ Z₂ : ℕ) (E θ : ℝ) : ℝ :=
  let k := coulombConstant
  (k * (Z₁ : ℝ) * (Z₂ : ℝ) * electronCharge ^ 2 / (4 * E)) ^ 2 /
    Real.sin (θ / 2) ^ 4

/-! ## BKS Theory (1924)

Bohr-Kramers-Slater theory attempted to preserve classical electromagnetic
theory by abandoning strict energy-momentum conservation in individual
quantum processes. Refuted by Bothe-Geiger and Compton-Simon experiments (1925).
Superseded by quantum electrodynamics. -/

/-- The BKS (Bohr-Kramers-Slater) theory.
    Proposed in 1924. Abandoned strict energy conservation for individual
    atomic processes, replacing it with statistical conservation.
    Refuted experimentally in 1925. No valid approximation regime. -/
structure BKSTheory where
  /-- Transition probability per unit time (statistical). -/
  transitionRate : ℝ
  /-- Virtual radiation field oscillator frequency. -/
  virtualFrequency : ℝ
  transitionRate_nonneg : 0 ≤ transitionRate
  virtualFrequency_pos : 0 < virtualFrequency

/-- BKS virtual oscillator: each atom has virtual oscillators at all
    transition frequencies. The virtual field guides transitions
    statistically but does not carry definite energy. -/
noncomputable def BKSTheory.virtualOscillatorEnergy (b : BKSTheory) : ℝ :=
  planckConstant * b.virtualFrequency

end Measure.Physics.Historical
