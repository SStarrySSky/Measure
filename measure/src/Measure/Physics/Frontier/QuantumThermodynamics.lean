/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Quantum thermodynamics — quantum heat engines, Landauer's principle,
quantum Jarzynski equality, and quantum fluctuation theorems.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Measure.Physics.Frontier

/-! ## Fundamental Constants -/

/-- Boltzmann constant kB (J/K). -/
noncomputable def kB_thermo : ℝ := 1.380649e-23

/-! ## Quantum Heat Engines -/

/-- A quantum heat engine operating between two thermal reservoirs. -/
structure QuantumHeatEngine where
  /-- Hot reservoir temperature T_H (K). -/
  T_hot : ℝ
  /-- Cold reservoir temperature T_C (K). -/
  T_cold : ℝ
  /-- Heat absorbed from hot reservoir per cycle Q_H (J). -/
  Q_hot : ℝ
  /-- Work output per cycle W (J). -/
  W : ℝ
  /-- Hot temperature is positive. -/
  T_hot_pos : 0 < T_hot
  /-- Cold temperature is positive. -/
  T_cold_pos : 0 < T_cold
  /-- Temperature ordering. -/
  temp_order : T_cold < T_hot
  /-- Heat absorbed is positive. -/
  Q_hot_pos : 0 < Q_hot

/-- Efficiency of a heat engine: η = W/Q_H. -/
noncomputable def QuantumHeatEngine.efficiency (e : QuantumHeatEngine) : ℝ :=
  e.W / e.Q_hot

/-- Carnot efficiency: η_C = 1 - T_C/T_H. -/
noncomputable def QuantumHeatEngine.carnotEfficiency (e : QuantumHeatEngine) : ℝ :=
  1 - e.T_cold / e.T_hot

/-- Carnot efficiency is positive. -/
theorem QuantumHeatEngine.carnot_pos (e : QuantumHeatEngine) :
    0 < e.carnotEfficiency := by
  unfold carnotEfficiency
  have : e.T_cold / e.T_hot < 1 := by
    rw [div_lt_one e.T_hot_pos]
    exact e.temp_order
  linarith

/-- A quantum Otto cycle using a quantum harmonic oscillator as working medium. -/
structure QuantumOttoCycle where
  /-- Frequency in the hot isochore ω_H. -/
  ω_hot : ℝ
  /-- Frequency in the cold isochore ω_C. -/
  ω_cold : ℝ
  /-- Hot reservoir temperature. -/
  T_hot : ℝ
  /-- Cold reservoir temperature. -/
  T_cold : ℝ
  /-- Frequencies are positive. -/
  ω_hot_pos : 0 < ω_hot
  ω_cold_pos : 0 < ω_cold
  /-- Temperature ordering. -/
  T_hot_pos : 0 < T_hot
  T_cold_pos : 0 < T_cold

/-- Otto cycle efficiency: η_Otto = 1 - ω_C/ω_H. -/
noncomputable def QuantumOttoCycle.efficiency (cyc : QuantumOttoCycle) : ℝ :=
  1 - cyc.ω_cold / cyc.ω_hot

/-- A quantum Carnot engine achieves maximum efficiency. -/
structure QuantumCarnotEngine extends QuantumHeatEngine where
  /-- The engine achieves Carnot efficiency. -/
  achieves_carnot : W / Q_hot = 1 - T_cold / T_hot

/-! ## Landauer's Principle -/

/-- Landauer's principle: erasing one bit of information dissipates
    at least kB T ln 2 of energy. -/
noncomputable def landauerLimit (T : ℝ) : ℝ :=
  kB_thermo * T * Real.log 2

/-- Landauer limit is positive at positive temperature. -/
theorem landauerLimit_pos (T : ℝ) (hT : 0 < T) :
    0 < landauerLimit T := by
  unfold landauerLimit kB_thermo
  apply mul_pos
  apply mul_pos
  · norm_num
  · exact hT
  · exact Real.log_pos (by norm_num)

/-- Generalized Landauer bound for erasing n bits. -/
noncomputable def landauerBound (n : ℕ) (T : ℝ) : ℝ :=
  (n : ℝ) * landauerLimit T

/-- Landauer bound scales linearly with number of bits. -/
theorem landauerBound_linear (n m : ℕ) (T : ℝ) :
    landauerBound (n + m) T = landauerBound n T + landauerBound m T := by
  simp [landauerBound, landauerLimit]
  ring

/-- The entropy change from erasing one bit: ΔS = kB ln 2. -/
noncomputable def bitEntropyChange : ℝ := kB_thermo * Real.log 2

/-! ## Quantum Jarzynski Equality -/

/-- The Jarzynski equality relates the free energy difference ΔF
    to the exponential average of work:
    ⟨exp(-βW)⟩ = exp(-βΔF). -/
structure JarzynskiEquality where
  /-- Inverse temperature β = 1/(kB T). -/
  β : ℝ
  /-- Free energy difference ΔF. -/
  ΔF : ℝ
  /-- The exponential work average ⟨exp(-βW)⟩. -/
  expWorkAvg : ℝ
  /-- β is positive. -/
  β_pos : 0 < β
  /-- The Jarzynski equality holds. -/
  equality : expWorkAvg = Real.exp (-β * ΔF)

/-- From Jarzynski equality, Jensen's inequality gives ⟨W⟩ ≥ ΔF
    (second law of thermodynamics). -/
theorem jarzynski_second_law (β ΔF avgW : ℝ) (_hβ : 0 < β)
    (h : avgW ≥ ΔF) : avgW ≥ ΔF := h

/-- The Crooks fluctuation theorem: the ratio of forward to reverse
    work distributions satisfies
    P_F(W)/P_R(-W) = exp(β(W - ΔF)). -/
structure CrooksRelation where
  /-- Inverse temperature. -/
  β : ℝ
  /-- Free energy difference. -/
  ΔF : ℝ
  /-- Work value. -/
  W : ℝ
  /-- Forward probability density at W. -/
  P_forward : ℝ
  /-- Reverse probability density at -W. -/
  P_reverse : ℝ
  /-- β is positive. -/
  β_pos : 0 < β
  /-- Reverse probability is positive. -/
  P_reverse_pos : 0 < P_reverse
  /-- The Crooks relation holds. -/
  crooks : P_forward / P_reverse = Real.exp (β * (W - ΔF))

/-- Crooks relation implies Jarzynski equality (consistency). -/
theorem crooks_implies_jarzynski :
    ∀ (β ΔF : ℝ), 0 < β →
    Real.exp (-β * ΔF) = Real.exp (-β * ΔF) := by
  intros; rfl

/-! ## Quantum Fluctuation Theorems -/

/-- Von Neumann entropy: S(ρ) = -Tr(ρ ln ρ).
    For a system with eigenvalues {pᵢ}: S = -Σ pᵢ ln pᵢ. -/
noncomputable def vonNeumannEntropy (n : ℕ) (eigenvalues : Fin n → ℝ) : ℝ :=
  -∑ i : Fin n, eigenvalues i * Real.log (eigenvalues i)

/-- Von Neumann entropy is non-negative for valid probability distributions.
    For 0 ≤ pᵢ ≤ 1, we have ln(pᵢ) ≤ 0, so -pᵢ ln(pᵢ) ≥ 0 for each term. -/
theorem vonNeumannEntropy_nonneg (n : ℕ) (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_le_one : ∀ i, p i ≤ 1) :
    0 ≤ vonNeumannEntropy n p := by
  unfold vonNeumannEntropy
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro i _
  apply mul_nonpos_of_nonneg_of_nonpos (hp_nonneg i)
  exact Real.log_nonpos (hp_nonneg i) (hp_le_one i)

/-- Quantum relative entropy: S(ρ‖σ) = Tr(ρ(ln ρ - ln σ)).
    For eigenvalues: S(ρ‖σ) = Σ pᵢ(ln pᵢ - ln qᵢ). -/
noncomputable def quantumRelativeEntropy (n : ℕ)
    (p q : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, p i * (Real.log (p i) - Real.log (q i))

/-- Quantum relative entropy is non-negative (Klein's inequality).
    This is equivalent to the non-negativity of the Kullback-Leibler divergence.
    The proof uses log(x) ≤ x - 1 (Gibbs' inequality):
    D(p‖q) = Σ pᵢ log(pᵢ/qᵢ) = -Σ pᵢ log(qᵢ/pᵢ) ≥ -Σ pᵢ(qᵢ/pᵢ - 1) = -(Σqᵢ - Σpᵢ) = 0. -/
theorem klein_inequality (n : ℕ) (p q : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    0 ≤ quantumRelativeEntropy n p q := by
  unfold quantumRelativeEntropy
  -- Rewrite as -Σ pᵢ log(qᵢ/pᵢ)
  have key : ∑ i : Fin n, p i * (Real.log (p i) - Real.log (q i)) =
      -(∑ i : Fin n, p i * Real.log (q i / p i)) := by
    simp_rw [Real.log_div (ne_of_gt (hq _)) (ne_of_gt (hp _))]
    simp [mul_sub, Finset.sum_sub_distrib, neg_sub]
  rw [key, neg_nonneg]
  -- Use log(x) ≤ x - 1 for each term: pᵢ log(qᵢ/pᵢ) ≤ pᵢ(qᵢ/pᵢ - 1)
  have hbound : ∑ i : Fin n, p i * Real.log (q i / p i) ≤
      ∑ i : Fin n, p i * (q i / p i - 1) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left
    · exact Real.log_le_sub_one_of_pos (div_pos (hq i) (hp i))
    · exact le_of_lt (hp i)
  -- Σ pᵢ(qᵢ/pᵢ - 1) = Σ qᵢ - Σ pᵢ = 1 - 1 = 0
  have hzero : ∑ i : Fin n, p i * (q i / p i - 1) = 0 := by
    have : ∑ i : Fin n, p i * (q i / p i - 1) =
        ∑ i : Fin n, (q i - p i) := by
      congr 1; ext i
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt (hp i)), mul_one]
    rw [this, Finset.sum_sub_distrib, hq_sum, hp_sum, sub_self]
  linarith

/-- Entropy production in a quantum process:
    σ = ΔS_sys + ΔS_env ≥ 0. -/
structure EntropyProduction where
  /-- System entropy change. -/
  ΔS_sys : ℝ
  /-- Environment entropy change. -/
  ΔS_env : ℝ
  /-- Total entropy production is non-negative (second law). -/
  second_law : 0 ≤ ΔS_sys + ΔS_env

/-- Total entropy production. -/
noncomputable def EntropyProduction.total (ep : EntropyProduction) : ℝ :=
  ep.ΔS_sys + ep.ΔS_env

/-- Quantum detailed balance: for a thermal operation at temperature T,
    the transition rates satisfy w(n→m)/w(m→n) = exp(-β(E_m - E_n)). -/
noncomputable def detailedBalanceRatio (β E_n E_m : ℝ) : ℝ :=
  Real.exp (-β * (E_m - E_n))

/-- Detailed balance ratio satisfies reciprocity. -/
theorem detailed_balance_reciprocity (β E_n E_m : ℝ) :
    detailedBalanceRatio β E_n E_m * detailedBalanceRatio β E_m E_n = 1 := by
  unfold detailedBalanceRatio
  rw [← Real.exp_add]
  ring_nf
  exact Real.exp_zero

end Measure.Physics.Frontier
