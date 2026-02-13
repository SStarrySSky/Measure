/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Hydrogen atom — energy levels, Bohr model, fine structure constant,
selection rules, and spectral series.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Measure.Physics.AtomicPhysics

/-! ## Fundamental constants -/

/-- Electron mass mₑ (kg). -/
noncomputable def electronMass : ℝ := 9.1093837015e-31

/-- Elementary charge e (C). -/
noncomputable def elementaryCharge : ℝ := 1.602176634e-19

/-- Reduced Planck constant ℏ (J·s). -/
noncomputable def hbar : ℝ := 1.054571817e-34

/-- Planck constant h (J·s). -/
noncomputable def planckConstant : ℝ := 6.62607015e-34

/-- Vacuum permittivity ε₀ (F/m). -/
noncomputable def ε₀ : ℝ := 8.854187817e-12

/-- Speed of light c (m/s). -/
noncomputable def c_light : ℝ := 2.99792458e8

/-- Boltzmann constant kB (J/K). -/
noncomputable def kB : ℝ := 1.380649e-23

/-! ## Fine structure constant -/

/-- Fine structure constant: α = e²/(4πε₀ℏc) ≈ 1/137. -/
noncomputable def fineStructureConstant : ℝ :=
  elementaryCharge ^ 2 / (4 * Real.pi * ε₀ * hbar * c_light)

/-- α is positive. -/
theorem fineStructureConstant_pos : 0 < fineStructureConstant := by
  unfold fineStructureConstant elementaryCharge ε₀ hbar c_light
  positivity

/-! ## Bohr model -/

/-- Bohr radius: a₀ = ℏ/(mₑcα) = 4πε₀ℏ²/(mₑe²). -/
noncomputable def bohrRadius : ℝ :=
  4 * Real.pi * ε₀ * hbar ^ 2 / (electronMass * elementaryCharge ^ 2)

/-- Bohr radius is positive. -/
theorem bohrRadius_pos : 0 < bohrRadius := by
  unfold bohrRadius electronMass elementaryCharge ε₀ hbar
  positivity

/-- Hydrogen energy levels: Eₙ = -13.6 eV / n².
    Here we use eV as the unit. -/
noncomputable def hydrogenEnergy (n : ℕ) (_hn : 0 < n) : ℝ :=
  -13.6 / (↑n : ℝ) ^ 2

/-- Ground state energy E₁ = -13.6 eV. -/
noncomputable def groundStateEnergy : ℝ := hydrogenEnergy 1 (by omega)

/-- Ground state energy equals -13.6 eV. -/
theorem groundState_eq : groundStateEnergy = -13.6 := by
  unfold groundStateEnergy hydrogenEnergy
  norm_num

/-- Energy levels are negative (bound states). -/
theorem hydrogenEnergy_neg (n : ℕ) (hn : 0 < n) :
    hydrogenEnergy n hn < 0 := by
  unfold hydrogenEnergy
  apply div_neg_of_neg_of_pos
  · linarith
  · positivity

/-- Energy increases (becomes less negative) with n. -/
theorem hydrogenEnergy_increasing (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hnm : n < m) :
    hydrogenEnergy n hn < hydrogenEnergy m hm := by
  unfold hydrogenEnergy
  simp only [neg_div]
  apply neg_lt_neg
  apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 13.6)
  · positivity
  · have : (↑n : ℝ) < (↑m : ℝ) := Nat.cast_lt.mpr hnm
    have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
    nlinarith [sq_nonneg ((↑m : ℝ) - ↑n), sq_nonneg (↑n : ℝ), sq_nonneg (↑m : ℝ)]

/-- Orbital radius in Bohr model: rₙ = n² a₀. -/
noncomputable def bohrOrbitRadius (n : ℕ) : ℝ :=
  (↑n : ℝ) ^ 2 * bohrRadius

/-- Orbital velocity in Bohr model: vₙ = αc/n. -/
noncomputable def bohrOrbitVelocity (n : ℕ) (_hn : 0 < n) : ℝ :=
  fineStructureConstant * c_light / (↑n : ℝ)

/-! ## Spectral transitions -/

/-- Photon energy for a transition from level nᵢ to nf:
    ΔE = 13.6 eV × (1/nf² - 1/nᵢ²). -/
noncomputable def transitionEnergy (n_i n_f : ℕ) (_hi : 0 < n_i) (_hf : 0 < n_f) : ℝ :=
  13.6 * (1 / (↑n_f : ℝ) ^ 2 - 1 / (↑n_i : ℝ) ^ 2)

/-- Rydberg constant R∞ (m⁻¹). -/
noncomputable def rydbergConstant : ℝ := 1.0973731568e7

/-- Rydberg formula: 1/λ = R∞(1/nf² - 1/nᵢ²). -/
noncomputable def rydbergFormula (n_i n_f : ℕ) (_hi : 0 < n_i) (_hf : 0 < n_f) : ℝ :=
  rydbergConstant * (1 / (↑n_f : ℝ) ^ 2 - 1 / (↑n_i : ℝ) ^ 2)

/-! ## Spectral series -/

/-- Lyman series: transitions to n = 1 (ultraviolet). -/
noncomputable def lymanSeries (n : ℕ) (hn : 1 < n) : ℝ :=
  rydbergFormula n 1 (by omega) (by omega)

/-- Balmer series: transitions to n = 2 (visible). -/
noncomputable def balmerSeries (n : ℕ) (hn : 2 < n) : ℝ :=
  rydbergFormula n 2 (by omega) (by omega)

/-- Paschen series: transitions to n = 3 (infrared). -/
noncomputable def paschenSeries (n : ℕ) (hn : 3 < n) : ℝ :=
  rydbergFormula n 3 (by omega) (by omega)

/-- Brackett series: transitions to n = 4. -/
noncomputable def brackettSeries (n : ℕ) (hn : 4 < n) : ℝ :=
  rydbergFormula n 4 (by omega) (by omega)

/-- Pfund series: transitions to n = 5. -/
noncomputable def pfundSeries (n : ℕ) (hn : 5 < n) : ℝ :=
  rydbergFormula n 5 (by omega) (by omega)

/-! ## Selection rules -/

/-- Quantum numbers for a hydrogen-like state. -/
structure HydrogenState where
  /-- Principal quantum number n ≥ 1. -/
  n : ℕ
  /-- Orbital angular momentum quantum number l. -/
  l : ℕ
  /-- Magnetic quantum number mₗ. -/
  ml : ℤ
  /-- n ≥ 1. -/
  n_pos : 0 < n
  /-- l < n. -/
  l_bound : l < n
  /-- |mₗ| ≤ l. -/
  ml_bound : ml.natAbs ≤ l

/-- Electric dipole selection rule: Δl = ±1. -/
def selectionRuleDeltaL (s₁ s₂ : HydrogenState) : Prop :=
  (s₂.l = s₁.l + 1) ∨ (s₁.l = s₂.l + 1)

/-- Selection rule for magnetic quantum number: Δmₗ = 0, ±1. -/
def selectionRuleDeltaML (s₁ s₂ : HydrogenState) : Prop :=
  s₂.ml = s₁.ml ∨ s₂.ml = s₁.ml + 1 ∨ s₂.ml = s₁.ml - 1

/-- An allowed electric dipole transition satisfies both selection rules. -/
def AllowedTransition (s₁ s₂ : HydrogenState) : Prop :=
  selectionRuleDeltaL s₁ s₂ ∧ selectionRuleDeltaML s₁ s₂

/-! ## Degeneracy -/

/-- Degeneracy of energy level n (without spin): gₙ = n². -/
def degeneracyNoSpin (n : ℕ) : ℕ := n ^ 2

/-- Degeneracy of energy level n (with spin): gₙ = 2n². -/
def degeneracyWithSpin (n : ℕ) : ℕ := 2 * n ^ 2

end Measure.Physics.AtomicPhysics
