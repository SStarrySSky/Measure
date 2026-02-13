/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The four laws of thermodynamics.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Measure.Physics.Thermodynamics

/-- A thermodynamic state characterized by macroscopic variables. -/
structure ThermodynamicState where
  /-- Temperature (Kelvin). -/
  T : ℝ
  /-- Pressure (Pascal). -/
  P : ℝ
  /-- Volume (m³). -/
  V : ℝ
  /-- Internal energy (Joule). -/
  U : ℝ
  /-- Entropy (J/K). -/
  S : ℝ
  /-- Temperature is positive. -/
  T_pos : 0 < T
  /-- Pressure is non-negative. -/
  P_nonneg : 0 ≤ P
  /-- Volume is positive. -/
  V_pos : 0 < V

/-- Thermal equilibrium is an equivalence relation (Zeroth Law). -/
def InThermalEquilibrium (s₁ s₂ : ThermodynamicState) : Prop :=
  s₁.T = s₂.T

theorem zeroth_law_trans {s₁ s₂ s₃ : ThermodynamicState}
    (h₁₂ : InThermalEquilibrium s₁ s₂) (h₂₃ : InThermalEquilibrium s₂ s₃) :
    InThermalEquilibrium s₁ s₃ :=
  h₁₂.trans h₂₃

theorem zeroth_law_symm {s₁ s₂ : ThermodynamicState}
    (h : InThermalEquilibrium s₁ s₂) : InThermalEquilibrium s₂ s₁ :=
  h.symm

theorem zeroth_law_refl (s : ThermodynamicState) : InThermalEquilibrium s s :=
  rfl

/-- A thermodynamic process: a path through state space. -/
abbrev ThermodynamicProcess := ℝ → ThermodynamicState

/-- First Law: change in internal energy equals heat added minus work done.
    dU = δQ - δW. For a quasi-static process, δW = P dV. -/
structure FirstLaw (proc : ThermodynamicProcess) (Q W : ℝ → ℝ) : Prop where
  /-- Energy conservation: ΔU = Q - W. -/
  energy_conservation : ∀ (t : ℝ),
    deriv (fun s => (proc s).U) t = deriv Q t - deriv W t

/-- Second Law (Clausius): entropy of an isolated system never decreases. -/
def SecondLaw (proc : ThermodynamicProcess) : Prop :=
  ∀ (t : ℝ), 0 ≤ deriv (fun s => (proc s).S) t

/-- Third Law: entropy approaches zero as temperature approaches absolute zero. -/
def ThirdLaw : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∃ (δ : ℝ), 0 < δ ∧
    ∀ (s : ThermodynamicState), s.T < δ → s.S < ε

/-- Ideal gas: PV = nRT. -/
structure IdealGas where
  /-- Number of moles. -/
  n : ℝ
  /-- n is positive. -/
  n_pos : 0 < n

/-- Boltzmann constant kB (J/K). Exact in 2019 SI. -/
noncomputable def kB : ℝ := 1.380649e-23

/-- Avogadro's number (mol⁻¹). Exact in 2019 SI. -/
noncomputable def NA : ℝ := 6.02214076e23

/-- Universal gas constant R = NA * kB (J/(mol·K)).
    Value 8.31446261815324 is the exact product of the SI-defining constants. -/
noncomputable def R : ℝ := 8.31446261815324

/-- Ideal gas law: PV = nRT. -/
def IdealGasLaw (gas : IdealGas) (s : ThermodynamicState) : Prop :=
  s.P * s.V = gas.n * R * s.T

/-- R equals the product NA * kB by definition of the 2019 SI constants. -/
theorem R_eq_NA_kB : R = NA * kB := by
  unfold R NA kB
  norm_num

/-! ## Carnot efficiency -/

/-- Carnot efficiency: η = 1 - T_cold/T_hot. -/
noncomputable def carnotEfficiency (T_cold T_hot : ℝ) : ℝ :=
  1 - T_cold / T_hot

/-- Carnot efficiency is non-negative when T_cold ≤ T_hot and T_hot > 0. -/
theorem carnot_efficiency_nonneg (T_cold T_hot : ℝ)
    (hle : T_cold ≤ T_hot) (hpos : 0 < T_hot) :
    0 ≤ carnotEfficiency T_cold T_hot := by
  unfold carnotEfficiency
  have : T_cold / T_hot ≤ 1 := by rwa [div_le_one hpos]
  linarith

/-- Carnot efficiency is at most 1 when T_cold ≥ 0 and T_hot > 0. -/
theorem carnot_efficiency_le_one (T_cold T_hot : ℝ)
    (hnn : 0 ≤ T_cold) (hpos : 0 < T_hot) :
    carnotEfficiency T_cold T_hot ≤ 1 := by
  unfold carnotEfficiency
  have : 0 ≤ T_cold / T_hot := div_nonneg hnn (le_of_lt hpos)
  linarith

/-- Carnot efficiency is bounded: 0 ≤ η ≤ 1 for valid temperatures. -/
theorem carnot_efficiency_bounded (T_cold T_hot : ℝ)
    (hnn : 0 ≤ T_cold) (hle : T_cold ≤ T_hot) (hpos : 0 < T_hot) :
    0 ≤ carnotEfficiency T_cold T_hot ∧ carnotEfficiency T_cold T_hot ≤ 1 :=
  ⟨carnot_efficiency_nonneg T_cold T_hot hle hpos,
   carnot_efficiency_le_one T_cold T_hot hnn hpos⟩

/-- Carnot efficiency is zero when T_cold = T_hot (no temperature difference). -/
theorem carnot_efficiency_zero (T : ℝ) (hpos : 0 < T) :
    carnotEfficiency T T = 0 := by
  unfold carnotEfficiency
  rw [div_self (ne_of_gt hpos)]
  ring

/-- Carnot efficiency increases when T_cold decreases (with T_hot fixed). -/
theorem carnot_efficiency_mono_cold (T₁ T₂ T_hot : ℝ)
    (h : T₁ ≤ T₂) (hpos : 0 < T_hot) :
    carnotEfficiency T₂ T_hot ≤ carnotEfficiency T₁ T_hot := by
  unfold carnotEfficiency
  have : T₁ / T_hot ≤ T₂ / T_hot := div_le_div_of_nonneg_right h (le_of_lt hpos)
  linarith

/-! ## Clausius inequality -/

/-- The Clausius inequality states that for a cyclic process,
    the cyclic integral of δQ/T ≤ 0. We model this as a property of
    a discrete approximation: Σ Qᵢ/Tᵢ ≤ 0. -/
def ClausiusInequality {n : ℕ} (Q T : Fin n → ℝ) : Prop :=
  ∑ i, Q i / T i ≤ 0

/-- A reversible cyclic process has equality in the Clausius inequality:
    Σ Qᵢ/Tᵢ = 0. -/
def ClausiusEquality {n : ℕ} (Q T : Fin n → ℝ) : Prop :=
  ∑ i, Q i / T i = 0

/-- Clausius equality implies the Clausius inequality. -/
theorem clausius_equality_implies_inequality {n : ℕ} (Q T : Fin n → ℝ)
    (h : ClausiusEquality Q T) : ClausiusInequality Q T := by
  unfold ClausiusInequality
  unfold ClausiusEquality at h
  linarith

/-! ## Ideal gas properties -/

/-- For an ideal gas, temperature is determined by PV/(nR). -/
theorem idealGas_temperature (gas : IdealGas) (s : ThermodynamicState)
    (h : IdealGasLaw gas s) : s.T = s.P * s.V / (gas.n * R) := by
  unfold IdealGasLaw at h
  have hn : gas.n ≠ 0 := ne_of_gt gas.n_pos
  have hR : R ≠ 0 := by unfold R; norm_num
  have hnR : gas.n * R ≠ 0 := mul_ne_zero hn hR
  field_simp at h ⊢
  linarith

/-- Thermal equilibrium is an equivalence relation. -/
theorem thermalEquilibrium_equiv :
    Equivalence InThermalEquilibrium :=
  ⟨zeroth_law_refl, fun h => zeroth_law_symm h, fun h₁ h₂ => zeroth_law_trans h₁ h₂⟩

end Measure.Physics.Thermodynamics
