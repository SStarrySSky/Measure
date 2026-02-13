/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Quantum bits — states, Bloch sphere parametrization, quantum gates,
and projective measurement.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Measure.Physics.QuantumInfo

open Complex Matrix

/-! ## Qubit State -/

/-- A qubit state is a normalized vector in ℂ². -/
structure QubitState where
  /-- Amplitude of |0⟩. -/
  α : ℂ
  /-- Amplitude of |1⟩. -/
  β : ℂ
  /-- Normalization: |α|² + |β|² = 1. -/
  normalized : Complex.normSq α + Complex.normSq β = 1

/-- The computational basis state |0⟩. -/
noncomputable def ket0 : QubitState where
  α := 1
  β := 0
  normalized := by simp [Complex.normSq_one, Complex.normSq_zero]

/-- The computational basis state |1⟩. -/
noncomputable def ket1 : QubitState where
  α := 0
  β := 1
  normalized := by simp [Complex.normSq_one, Complex.normSq_zero]

/-- The |+⟩ state: (|0⟩ + |1⟩)/√2. -/
noncomputable def ketPlus : QubitState where
  α := ⟨Real.sqrt 2 / 2, 0⟩
  β := ⟨Real.sqrt 2 / 2, 0⟩
  normalized := by
    simp only [Complex.normSq_mk]
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
    nlinarith

/-- The |−⟩ state: (|0⟩ − |1⟩)/√2. -/
noncomputable def ketMinus : QubitState where
  α := ⟨Real.sqrt 2 / 2, 0⟩
  β := ⟨-(Real.sqrt 2 / 2), 0⟩
  normalized := by
    simp only [Complex.normSq_mk]
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
    nlinarith

/-- Convert a qubit state to a column vector in ℂ². -/
noncomputable def QubitState.toVec (ψ : QubitState) : Fin 2 → ℂ :=
  ![ψ.α, ψ.β]

/-! ## Bloch Sphere Parametrization -/

/-- Bloch sphere parametrization of a qubit state:
    |ψ⟩ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩
    where θ ∈ [0, π] and φ ∈ [0, 2π). -/
structure BlochCoords where
  /-- Polar angle θ ∈ [0, π]. -/
  θ : ℝ
  /-- Azimuthal angle φ ∈ [0, 2π). -/
  φ : ℝ
  /-- θ is in [0, π]. -/
  θ_range : 0 ≤ θ ∧ θ ≤ Real.pi
  /-- φ is in [0, 2π). -/
  φ_range : 0 ≤ φ ∧ φ < 2 * Real.pi

/-- Convert Bloch coordinates to a qubit state. -/
noncomputable def BlochCoords.toQubit (b : BlochCoords) : QubitState where
  α := ⟨Real.cos (b.θ / 2), 0⟩
  β := Complex.exp (↑b.φ * I) * ⟨Real.sin (b.θ / 2), 0⟩
  normalized := by
    simp only [Complex.normSq_mk]
    rw [Complex.normSq_mul]
    have hexp : Complex.normSq (Complex.exp (↑b.φ * I)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
    rw [hexp, one_mul]
    simp only [Complex.normSq_mk]
    have := Real.sin_sq_add_cos_sq (b.θ / 2)
    nlinarith

/-- Bloch vector components (x, y, z) on the unit sphere. -/
noncomputable def BlochCoords.toVector (b : BlochCoords) : Fin 3 → ℝ :=
  ![Real.sin b.θ * Real.cos b.φ,
    Real.sin b.θ * Real.sin b.φ,
    Real.cos b.θ]

/-! ## Quantum Gates (2×2 unitary matrices) -/

/-- Pauli-X gate (NOT gate):
    ⎛0 1⎞
    ⎝1 0⎠ -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli-Y gate:
    ⎛0 -i⎞
    ⎝i  0⎠ -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- Pauli-Z gate:
    ⎛1  0⎞
    ⎝0 -1⎠ -/
noncomputable def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Hadamard gate:
    (1/√2) ⎛1  1⎞
            ⎝1 -1⎠ -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  let s := (↑(Real.sqrt 2 / 2) : ℂ)
  !![s, s; s, -s]

/-- Phase gate (S gate):
    ⎛1 0⎞
    ⎝0 i⎠ -/
noncomputable def phaseGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, I]

/-- T gate (π/8 gate):
    ⎛1 0        ⎞
    ⎝0 e^{iπ/4} ⎠ -/
noncomputable def tGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (↑(Real.pi / 4) * I)]

/-- CNOT gate (4×4 matrix on two-qubit space):
    |00⟩ → |00⟩, |01⟩ → |01⟩, |10⟩ → |11⟩, |11⟩ → |10⟩. -/
noncomputable def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-! ## Gate Properties -/

/-- Pauli-X is self-adjoint (Hermitian). -/
theorem pauliX_selfAdjoint : pauliX.conjTranspose = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, conjTranspose, Matrix.of_apply]

/-- Pauli-Z is self-adjoint (Hermitian). -/
theorem pauliZ_selfAdjoint : pauliZ.conjTranspose = pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, conjTranspose, Matrix.of_apply]

/-- Pauli-X is unitary: X†X = I. -/
theorem pauliX_unitary : pauliX.conjTranspose * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli-Z is unitary: Z†Z = I. -/
theorem pauliZ_unitary : pauliZ.conjTranspose * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]

/-- Hadamard is self-inverse: H² = I. -/
theorem hadamard_sq : hadamard * hadamard = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp <;> nlinarith

/-- Pauli-X² = I. -/
theorem pauliX_sq : pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli-Y² = I. -/
theorem pauliY_sq : pauliY * pauliY = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli-Z² = I. -/
theorem pauliZ_sq : pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Gate Application -/

/-- Apply a single-qubit gate to a qubit state. -/
noncomputable def applyGate (G : Matrix (Fin 2) (Fin 2) ℂ) (ψ : QubitState) : Fin 2 → ℂ :=
  G.mulVec ψ.toVec

/-- Hadamard maps |0⟩ to |+⟩. -/
theorem hadamard_ket0 : applyGate hadamard ket0 = ketPlus.toVec := by
  ext i; fin_cases i <;>
    simp [applyGate, hadamard, ket0, ketPlus, QubitState.toVec, Matrix.mulVec] <;>
    apply Complex.ext <;> simp

/-! ## Projective Measurement -/

/-- Measurement outcome for a qubit in the computational basis. -/
inductive MeasurementOutcome where
  /-- Outcome |0⟩ with probability |α|². -/
  | zero
  /-- Outcome |1⟩ with probability |β|². -/
  | one

/-- Probability of measuring |0⟩. -/
noncomputable def prob0 (ψ : QubitState) : ℝ :=
  Complex.normSq ψ.α

/-- Probability of measuring |1⟩. -/
noncomputable def prob1 (ψ : QubitState) : ℝ :=
  Complex.normSq ψ.β

/-- Measurement probabilities sum to 1. -/
theorem prob_sum (ψ : QubitState) : prob0 ψ + prob1 ψ = 1 :=
  ψ.normalized

/-- Post-measurement state after obtaining outcome |0⟩. -/
noncomputable def postMeasure0 : QubitState := ket0

/-- Post-measurement state after obtaining outcome |1⟩. -/
noncomputable def postMeasure1 : QubitState := ket1

/-- A projector onto the |0⟩ subspace: P₀ = |0⟩⟨0|. -/
noncomputable def projector0 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 0]

/-- A projector onto the |1⟩ subspace: P₁ = |1⟩⟨1|. -/
noncomputable def projector1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, 1]

/-- Projectors are complete: P₀ + P₁ = I. -/
theorem projectors_complete :
    projector0 + projector1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [projector0, projector1]

/-- P₀ is idempotent: P₀² = P₀. -/
theorem projector0_idempotent : projector0 * projector0 = projector0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [projector0, Matrix.mul_apply, Fin.sum_univ_two]

/-- P₁ is idempotent: P₁² = P₁. -/
theorem projector1_idempotent : projector1 * projector1 = projector1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [projector1, Matrix.mul_apply, Fin.sum_univ_two]

end Measure.Physics.QuantumInfo
