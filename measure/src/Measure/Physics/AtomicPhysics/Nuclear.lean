/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Nuclear physics — binding energy, radioactive decay, mass-energy equivalence,
and nuclear reaction Q-values.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Measure.Physics.AtomicPhysics.Hydrogen

namespace Measure.Physics.AtomicPhysics

/-! ## Mass-energy equivalence -/

/-- Mass-energy equivalence: E = mc². -/
noncomputable def massEnergy (m : ℝ) : ℝ :=
  m * c_light ^ 2

/-- Mass-energy is non-negative for non-negative mass. -/
theorem massEnergy_nonneg (m : ℝ) (hm : 0 ≤ m) : 0 ≤ massEnergy m := by
  unfold massEnergy
  apply mul_nonneg hm
  positivity

/-- Mass-energy is zero iff mass is zero. -/
theorem massEnergy_eq_zero_iff (m : ℝ) : massEnergy m = 0 ↔ m = 0 := by
  unfold massEnergy
  constructor
  · intro h
    have hc : c_light ^ 2 ≠ 0 := by unfold c_light; positivity
    exact (mul_eq_zero.mp h).resolve_right hc
  · intro h; simp [h]

/-! ## Atomic mass unit -/

/-- Atomic mass unit u (kg). -/
noncomputable def atomicMassUnit : ℝ := 1.66053906660e-27

/-- Proton mass (kg). -/
noncomputable def protonMass : ℝ := 1.67262192369e-27

/-- Neutron mass (kg). -/
noncomputable def neutronMass : ℝ := 1.67492749804e-27

/-! ## Nuclear binding energy -/

/-- A nucleus characterized by proton number Z and neutron number N. -/
structure Nucleus where
  /-- Proton number (atomic number). -/
  Z : ℕ
  /-- Neutron number. -/
  N : ℕ
  /-- At least one nucleon. -/
  nucleon_pos : 0 < Z + N

/-- Mass number A = Z + N. -/
def Nucleus.massNumber (nuc : Nucleus) : ℕ := nuc.Z + nuc.N

/-- Mass defect: Δm = Z·mₚ + N·mₙ - M_nucleus. -/
noncomputable def massDefect (nuc : Nucleus) (M_nucleus : ℝ) : ℝ :=
  ↑nuc.Z * protonMass + ↑nuc.N * neutronMass - M_nucleus

/-- Nuclear binding energy: B = Δm · c². -/
noncomputable def bindingEnergy (nuc : Nucleus) (M_nucleus : ℝ) : ℝ :=
  massEnergy (massDefect nuc M_nucleus)

/-- Binding energy per nucleon: B/A. -/
noncomputable def bindingEnergyPerNucleon (nuc : Nucleus) (M_nucleus : ℝ) : ℝ :=
  bindingEnergy nuc M_nucleus / ↑nuc.massNumber

/-- Semi-empirical mass formula (Bethe-Weizsäcker):
    B(Z,A) = aᵥA - aₛA^{2/3} - a_c Z(Z-1)/A^{1/3} - a_a(A-2Z)²/A + δ(A,Z). -/
structure SEMFCoefficients where
  /-- Volume term coefficient (MeV). -/
  a_v : ℝ
  /-- Surface term coefficient (MeV). -/
  a_s : ℝ
  /-- Coulomb term coefficient (MeV). -/
  a_c : ℝ
  /-- Asymmetry term coefficient (MeV). -/
  a_a : ℝ
  /-- Pairing term coefficient (MeV). -/
  a_p : ℝ

/-- Standard SEMF coefficients (MeV). -/
noncomputable def standardSEMF : SEMFCoefficients where
  a_v := 15.75
  a_s := 17.8
  a_c := 0.711
  a_a := 23.7
  a_p := 11.18

/-! ## Radioactive decay -/

/-- Decay constant λ (s⁻¹). -/
abbrev DecayConstant := ℝ

/-- Number of undecayed nuclei at time t: N(t) = N₀ exp(-λt). -/
noncomputable def decayLaw (N₀ : ℝ) (dc : DecayConstant) (t : ℝ) : ℝ :=
  N₀ * Real.exp (-dc * t)

/-- At t = 0, N(0) = N₀. -/
theorem decayLaw_initial (N₀ : ℝ) (dc : DecayConstant) :
    decayLaw N₀ dc 0 = N₀ := by
  unfold decayLaw
  simp

/-- Decay law is monotonically decreasing for λ > 0 and N₀ > 0. -/
theorem decayLaw_decreasing (N₀ : ℝ) (dc : DecayConstant) (t₁ t₂ : ℝ)
    (hN : 0 < N₀) (_hdc : 0 < dc) (ht : t₁ < t₂) :
    decayLaw N₀ dc t₂ < decayLaw N₀ dc t₁ := by
  unfold decayLaw
  apply mul_lt_mul_of_pos_left _ hN
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- Decay law is always non-negative for N₀ ≥ 0. -/
theorem decayLaw_nonneg (N₀ : ℝ) (dc : DecayConstant) (t : ℝ) (hN : 0 ≤ N₀) :
    0 ≤ decayLaw N₀ dc t := by
  unfold decayLaw
  apply mul_nonneg hN
  exact le_of_lt (Real.exp_pos _)

/-- Half-life: t₁/₂ = ln 2 / λ. -/
noncomputable def halfLife (dc : DecayConstant) : ℝ :=
  Real.log 2 / dc

/-- At t = t₁/₂, N = N₀/2. -/
theorem decayLaw_halfLife (N₀ : ℝ) (dc : DecayConstant) (_hdc : dc ≠ 0) :
    decayLaw N₀ dc (halfLife dc) = N₀ / 2 := by
  unfold decayLaw halfLife
  rw [neg_mul, mul_div_cancel₀ _ _hdc, Real.exp_neg, Real.exp_log (by norm_num : (2:ℝ) > 0)]
  ring

/-- Mean lifetime: τ = 1/λ. -/
noncomputable def meanLifetime (dc : DecayConstant) : ℝ :=
  1 / dc

/-- Activity (decay rate): A(t) = λN(t) = λN₀ exp(-λt). -/
noncomputable def activity (N₀ : ℝ) (dc : DecayConstant) (t : ℝ) : ℝ :=
  dc * decayLaw N₀ dc t

/-! ## Nuclear reactions -/

/-- Q-value of a nuclear reaction: Q = (Σm_reactants - Σm_products)c². -/
noncomputable def reactionQ (m_reactants m_products : ℝ) : ℝ :=
  massEnergy (m_reactants - m_products)

/-- Exothermic reaction: Q > 0. -/
def isExothermic (m_reactants m_products : ℝ) : Prop :=
  reactionQ m_reactants m_products > 0

/-- Endothermic reaction: Q < 0. -/
def isEndothermic (m_reactants m_products : ℝ) : Prop :=
  reactionQ m_reactants m_products < 0

/-- Threshold energy for endothermic reaction:
    E_th = -Q(1 + m_projectile/m_target) (non-relativistic). -/
noncomputable def thresholdEnergy (Q m_proj m_target : ℝ) : ℝ :=
  -Q * (1 + m_proj / m_target)

/-- Conservation of baryon number in nuclear reactions. -/
def baryonNumberConserved (A_reactants A_products : ℕ) : Prop :=
  A_reactants = A_products

/-- Conservation of charge in nuclear reactions. -/
def chargeConserved (Z_reactants Z_products : ℕ) : Prop :=
  Z_reactants = Z_products

end Measure.Physics.AtomicPhysics
