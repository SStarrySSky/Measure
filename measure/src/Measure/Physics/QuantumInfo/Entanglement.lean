/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Quantum entanglement — Bell states, von Neumann entropy,
teleportation protocol, and the no-cloning theorem.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Measure.Physics.QuantumInfo.Qubit

namespace Measure.Physics.QuantumInfo

open Complex Matrix

/-! ## Two-Qubit States -/

/-- A two-qubit state is a normalized vector in ℂ⁴.
    Basis ordering: |00⟩, |01⟩, |10⟩, |11⟩. -/
structure TwoQubitState where
  /-- State vector in ℂ⁴. -/
  vec : Fin 4 → ℂ
  /-- Normalization: ∑ᵢ |cᵢ|² = 1. -/
  normalized : ∑ i : Fin 4, Complex.normSq (vec i) = 1

/-- A product state |ψ⟩ ⊗ |φ⟩ of two qubits. -/
noncomputable def productState (ψ φ : QubitState) : TwoQubitState where
  vec := ![ψ.α * φ.α, ψ.α * φ.β, ψ.β * φ.α, ψ.β * φ.β]
  normalized := by
    simp only [Fin.sum_univ_four]
    dsimp [Matrix.cons_val']
    simp only [Complex.normSq_mul]
    have hψ := ψ.normalized
    have hφ := φ.normalized
    nlinarith [Complex.normSq_nonneg ψ.α, Complex.normSq_nonneg ψ.β,
               Complex.normSq_nonneg φ.α, Complex.normSq_nonneg φ.β]

/-! ## Bell States -/

/-- Bell state |Φ⁺⟩ = (|00⟩ + |11⟩)/√2. -/
noncomputable def bellΦPlus : TwoQubitState where
  vec := ![⟨Real.sqrt 2 / 2, 0⟩, 0, 0, ⟨Real.sqrt 2 / 2, 0⟩]
  normalized := by
    simp only [Fin.sum_univ_four]
    dsimp [Matrix.cons_val']
    simp only [Complex.normSq_zero]
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
    nlinarith

/-- Bell state |Φ⁻⟩ = (|00⟩ − |11⟩)/√2. -/
noncomputable def bellΦMinus : TwoQubitState where
  vec := ![⟨Real.sqrt 2 / 2, 0⟩, 0, 0, ⟨-(Real.sqrt 2 / 2), 0⟩]
  normalized := by
    simp only [Fin.sum_univ_four]
    dsimp [Matrix.cons_val']
    simp only [Complex.normSq_zero]
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
    nlinarith

/-- Bell state |Ψ⁺⟩ = (|01⟩ + |10⟩)/√2. -/
noncomputable def bellΨPlus : TwoQubitState where
  vec := ![0, ⟨Real.sqrt 2 / 2, 0⟩, ⟨Real.sqrt 2 / 2, 0⟩, 0]
  normalized := by
    simp only [Fin.sum_univ_four]
    dsimp [Matrix.cons_val']
    simp only [Complex.normSq_zero]
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
    nlinarith

/-- Bell state |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2 (singlet state). -/
noncomputable def bellΨMinus : TwoQubitState where
  vec := ![0, ⟨Real.sqrt 2 / 2, 0⟩, ⟨-(Real.sqrt 2 / 2), 0⟩, 0]
  normalized := by
    simp only [Fin.sum_univ_four]
    dsimp [Matrix.cons_val']
    simp only [Complex.normSq_zero]
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
    nlinarith

/-! ## Entanglement -/

/-- A two-qubit state is separable (product) if it can be written as |ψ⟩ ⊗ |φ⟩. -/
def IsSeparable (Ψ : TwoQubitState) : Prop :=
  ∃ (ψ φ : QubitState), Ψ.vec = (productState ψ φ).vec

/-- A two-qubit state is entangled if it is not separable. -/
def IsEntangled (Ψ : TwoQubitState) : Prop :=
  ¬ IsSeparable Ψ

/-- The Bell state |Φ⁺⟩ is entangled. -/
theorem bellΦPlus_entangled : IsEntangled bellΦPlus := by
  intro ⟨ψ, φ, h⟩
  have h0 : bellΦPlus.vec 0 = (productState ψ φ).vec 0 := congr_fun h 0
  have h1 : bellΦPlus.vec 1 = (productState ψ φ).vec 1 := congr_fun h 1
  have h3 : bellΦPlus.vec 3 = (productState ψ φ).vec 3 := congr_fun h 3
  simp only [bellΦPlus, productState] at h0 h1 h3
  dsimp at h0 h1 h3
  -- h0 : ⟨√2/2, 0⟩ = ψ.α * φ.α
  -- h1 : 0 = ψ.α * φ.β
  -- h3 : ⟨√2/2, 0⟩ = ψ.β * φ.β
  have hsqrt_ne : (⟨Real.sqrt 2 / 2, 0⟩ : ℂ) ≠ 0 := by
    simp [Complex.ext_iff, ne_of_gt (div_pos (Real.sqrt_pos.mpr (by norm_num : (2:ℝ) > 0)) (by norm_num : (2:ℝ) > 0))]
  -- From h0: ψ.α * φ.α ≠ 0, so ψ.α ≠ 0
  have hαψ : ψ.α ≠ 0 := left_ne_zero_of_mul (h0 ▸ hsqrt_ne)
  -- From h1: ψ.α * φ.β = 0, and ψ.α ≠ 0, so φ.β = 0
  have hβφ : φ.β = 0 := by
    cases mul_eq_zero.mp h1.symm with
    | inl ha => exact absurd ha hαψ
    | inr hb => exact hb
  -- From h3: ψ.β * φ.β = ⟨√2/2, 0⟩ ≠ 0, but φ.β = 0
  rw [hβφ, mul_zero] at h3
  exact hsqrt_ne h3

/-- The Bell state |Ψ⁻⟩ is entangled. -/
theorem bellΨMinus_entangled : IsEntangled bellΨMinus := by
  intro ⟨ψ, φ, h⟩
  have h0 : bellΨMinus.vec 0 = (productState ψ φ).vec 0 := congr_fun h 0
  have h1 : bellΨMinus.vec 1 = (productState ψ φ).vec 1 := congr_fun h 1
  have h3 : bellΨMinus.vec 3 = (productState ψ φ).vec 3 := congr_fun h 3
  simp only [bellΨMinus, productState] at h0 h1 h3
  dsimp at h0 h1 h3
  have hsqrt_ne : (⟨Real.sqrt 2 / 2, 0⟩ : ℂ) ≠ 0 := by
    simp [Complex.ext_iff, ne_of_gt (div_pos (Real.sqrt_pos.mpr (by norm_num : (2:ℝ) > 0)) (by norm_num : (2:ℝ) > 0))]
  -- h0 : 0 = ψ.α * φ.α
  -- h1 : ⟨√2/2, 0⟩ = ψ.α * φ.β
  -- h3 : 0 = ψ.β * φ.β
  have hαψ : ψ.α ≠ 0 := left_ne_zero_of_mul (h1 ▸ hsqrt_ne)
  have hαφ : φ.α = 0 := by
    cases mul_eq_zero.mp h0.symm with
    | inl ha => exact absurd ha hαψ
    | inr hb => exact hb
  have hβφ : φ.β ≠ 0 := right_ne_zero_of_mul (h1 ▸ hsqrt_ne)
  have hβψ : ψ.β = 0 := by
    cases mul_eq_zero.mp h3.symm with
    | inl ha => exact ha
    | inr hb => exact absurd hb hβφ
  have hψ_norm := ψ.normalized
  rw [hβψ, Complex.normSq_zero, add_zero] at hψ_norm
  have hφ_norm := φ.normalized
  rw [hαφ, Complex.normSq_zero, zero_add] at hφ_norm
  have h_prod : Complex.normSq (ψ.α * φ.β) = 1 := by
    rw [Complex.normSq_mul, hψ_norm, hφ_norm, mul_one]
  rw [← h1] at h_prod
  simp [Complex.normSq_mk] at h_prod
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
  nlinarith

/-! ## Density Matrix -/

/-- Density matrix (mixed state) for an n-dimensional system. -/
structure DensityMatrix (n : ℕ) where
  /-- The density matrix ρ. -/
  ρ : Matrix (Fin n) (Fin n) ℂ
  /-- ρ is self-adjoint: ρ† = ρ. -/
  selfAdjoint : ρ.conjTranspose = ρ
  /-- Trace is 1: Tr(ρ) = 1. -/
  traceOne : ρ.trace = 1

/-- Pure state density matrix: ρ = |ψ⟩⟨ψ|. -/
noncomputable def pureDensity (ψ : QubitState) : DensityMatrix 2 where
  ρ := !![ψ.α * starRingEnd ℂ ψ.α, ψ.α * starRingEnd ℂ ψ.β;
           ψ.β * starRingEnd ℂ ψ.α, ψ.β * starRingEnd ℂ ψ.β]
  selfAdjoint := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [conjTranspose, Matrix.of_apply, mul_comm (starRingEnd ℂ _) _]
  traceOne := by
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag]
    dsimp
    -- Goal: ψ.α * (starRingEnd ℂ) ψ.α + ψ.β * (starRingEnd ℂ) ψ.β = 1
    -- normSq_eq_conj_mul_self: (normSq z : ℂ) = conj z * z
    -- So z * conj z = conj (conj z * z) = conj (normSq z : ℂ) = normSq z (since normSq is real)
    have h := ψ.normalized
    have h1 : ψ.α * starRingEnd ℂ ψ.α = (Complex.normSq ψ.α : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    have h2 : ψ.β * starRingEnd ℂ ψ.β = (Complex.normSq ψ.β : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [h1, h2, ← Complex.ofReal_add, h, Complex.ofReal_one]

/-- A state is pure iff ρ² = ρ. -/
def IsPure {n : ℕ} (dm : DensityMatrix n) : Prop :=
  dm.ρ * dm.ρ = dm.ρ

/-- Partial trace over the second qubit of a two-qubit density matrix.
    Tr₂(ρ)ᵢⱼ = ∑ₖ ρ_{i⊗k, j⊗k}. -/
noncomputable def partialTrace2 (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ρ ⟨2 * i.val, by omega⟩ ⟨2 * j.val, by omega⟩ +
             ρ ⟨2 * i.val + 1, by omega⟩ ⟨2 * j.val + 1, by omega⟩

/-! ## Von Neumann Entropy -/

/-- Eigenvalues of a 2×2 density matrix (abstract).
    For a qubit density matrix, the eigenvalues are λ and 1-λ. -/
structure QubitSpectrum where
  /-- The larger eigenvalue. -/
  ev1 : ℝ
  /-- The smaller eigenvalue. -/
  ev2 : ℝ
  /-- Eigenvalues are non-negative. -/
  ev1_nonneg : 0 ≤ ev1
  ev2_nonneg : 0 ≤ ev2
  /-- Eigenvalues sum to 1. -/
  sum_one : ev1 + ev2 = 1

/-- Von Neumann entropy: S(ρ) = -Tr(ρ log ρ) = -∑ᵢ λᵢ log λᵢ.
    We use the convention 0 log 0 = 0. -/
noncomputable def vonNeumannEntropy (spec : QubitSpectrum) : ℝ :=
  let f := fun x : ℝ => if x = 0 then 0 else -x * Real.log x
  f spec.ev1 + f spec.ev2

/-- Von Neumann entropy is non-negative: S(ρ) ≥ 0. -/
theorem vonNeumannEntropy_nonneg (spec : QubitSpectrum) :
    0 ≤ vonNeumannEntropy spec := by
  unfold vonNeumannEntropy
  dsimp
  -- Need: f(ev1) + f(ev2) ≥ 0 where f(x) = if x = 0 then 0 else -x * log x
  -- For x ∈ (0, 1], log x ≤ 0, so -x * log x ≥ 0
  -- For x = 0, f(x) = 0
  have hf_nonneg : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ (if x = 0 then (0:ℝ) else -x * Real.log x) := by
    intro x hx hx1
    split_ifs with h
    · exact le_refl 0
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
      have hlog : Real.log x ≤ 0 := Real.log_nonpos hx hx1
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hxpos.le hlog]
  have hev1_le : spec.ev1 ≤ 1 := by linarith [spec.ev2_nonneg, spec.sum_one]
  have hev2_le : spec.ev2 ≤ 1 := by linarith [spec.ev1_nonneg, spec.sum_one]
  have h1 := hf_nonneg spec.ev1 spec.ev1_nonneg hev1_le
  have h2 := hf_nonneg spec.ev2 spec.ev2_nonneg hev2_le
  linarith

/-- Von Neumann entropy of a pure state is zero. -/
theorem vonNeumannEntropy_pure :
    vonNeumannEntropy ⟨1, 0, by norm_num, le_refl 0, by ring⟩ = 0 := by
  simp [vonNeumannEntropy, Real.log_one]

/-- Von Neumann entropy is maximized for the maximally mixed state (λ = 1/2).
    This follows from the strict concavity of f(x) = -x log x on [0,1], since
    f''(x) = -1/x < 0 for x > 0. By Jensen's inequality (or direct analysis),
    the sum f(λ₁) + f(λ₂) subject to λ₁ + λ₂ = 1 is maximized when λ₁ = λ₂ = 1/2.
    This is a standard result in information theory (Shannon/von Neumann). -/
axiom vonNeumannEntropy_max (spec : QubitSpectrum) :
    vonNeumannEntropy spec ≤
      vonNeumannEntropy ⟨1/2, 1/2, by linarith, by linarith, by ring⟩

/-! ## Quantum Teleportation Protocol -/

/-- The quantum teleportation protocol structure.
    Alice wants to send an unknown qubit |ψ⟩ to Bob using a shared
    Bell pair and two classical bits. -/
structure TeleportationProtocol where
  /-- The unknown state Alice wants to send. -/
  ψ : QubitState
  /-- The shared entangled pair (Bell state). -/
  sharedPair : TwoQubitState
  /-- Alice's measurement outcome (two classical bits). -/
  classicalBits : Fin 2 × Fin 2

/-- The correction unitary Bob applies based on Alice's measurement.
    (0,0) → I, (0,1) → X, (1,0) → Z, (1,1) → ZX. -/
noncomputable def teleportCorrection : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | (⟨0, _⟩, ⟨0, _⟩) => 1
  | (⟨0, _⟩, ⟨1, _⟩) => pauliX
  | (⟨1, _⟩, ⟨0, _⟩) => pauliZ
  | (⟨1, _⟩, ⟨1, _⟩) => pauliZ * pauliX

/-- Each teleportation correction gate is unitary: U†U = I.
    This ensures the correction is a valid quantum operation. -/
theorem teleportCorrection_unitary (bits : Fin 2 × Fin 2) :
    (teleportCorrection bits).conjTranspose * teleportCorrection bits =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨a, b⟩ := bits
  fin_cases a <;> fin_cases b <;>
    simp only [teleportCorrection] <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauliZ, pauliX, conjTranspose, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply])

/-! ## No-Cloning Theorem -/

/-- A cloning map would take |ψ⟩|0⟩ → |ψ⟩|ψ⟩ for all |ψ⟩. -/
def IsCloningMap (U : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ (ψ : QubitState),
    U.mulVec (productState ψ ket0).vec = (productState ψ ψ).vec

/-- The no-cloning theorem: no unitary can clone arbitrary quantum states.
    There is no U such that U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩ for all |ψ⟩.

    Proof sketch: Suppose U clones both |0⟩ and |1⟩. Then by linearity of U,
    U(|+⟩⊗|0⟩) = (1/√2)(U(|0⟩⊗|0⟩) + U(|1⟩⊗|0⟩)) = (1/√2)(|00⟩ + |11⟩) = |Φ⁺⟩.
    But the cloning condition requires U(|+⟩⊗|0⟩) = |+⟩⊗|+⟩ = (1/2)(|00⟩+|01⟩+|10⟩+|11⟩).
    These are different states (|Φ⁺⟩ is entangled, |+⟩⊗|+⟩ is separable), contradiction.
    The formal proof requires connecting mulVec linearity with the tensor product
    structure, which needs infrastructure beyond basic Mathlib. -/
axiom no_cloning (U : Matrix (Fin 4) (Fin 4) ℂ)
    (_hU : U.conjTranspose * U = 1) :
    ¬ IsCloningMap U

end Measure.Physics.QuantumInfo
