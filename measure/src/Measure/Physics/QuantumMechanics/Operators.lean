/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Quantum mechanical operators: Pauli matrices, angular momentum,
and their algebraic properties.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Measure.Physics.QuantumMechanics.Schrodinger

namespace Measure.Physics.QuantumMechanics

open Complex Matrix

/-! ## Pauli matrices -/

/-- Pauli matrix σ₁ (σx):
    ⎛0 1⎞
    ⎝1 0⎠ -/
noncomputable def σ₁ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli matrix σ₂ (σy):
    ⎛0 -i⎞
    ⎝i  0⎠ -/
noncomputable def σ₂ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- Pauli matrix σ₃ (σz):
    ⎛1  0⎞
    ⎝0 -1⎠ -/
noncomputable def σ₃ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-! ## Pauli matrix properties -/

/-- σ₁² = I. -/
theorem σ₁_sq : σ₁ * σ₁ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ₂² = I. -/
theorem σ₂_sq : σ₂ * σ₂ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ₃² = I. -/
theorem σ₃_sq : σ₃ * σ₃ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ₁ is self-adjoint (Hermitian). -/
theorem σ₁_selfAdjoint : σ₁.conjTranspose = σ₁ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, conjTranspose, Matrix.of_apply]

/-- σ₃ is self-adjoint (Hermitian). -/
theorem σ₃_selfAdjoint : σ₃.conjTranspose = σ₃ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃, conjTranspose, Matrix.of_apply]

/-- Anticommutator {A, B} = AB + BA. -/
noncomputable def anticommutator {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A * B + B * A

/-- σ₁ and σ₂ anticommute: {σ₁, σ₂} = 0. -/
theorem σ₁_σ₂_anticommute : anticommutator σ₁ σ₂ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticommutator, σ₁, σ₂, Matrix.add_apply]

/-- σ₁ and σ₃ anticommute: {σ₁, σ₃} = 0. -/
theorem σ₁_σ₃_anticommute : anticommutator σ₁ σ₃ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticommutator, σ₁, σ₃, Matrix.add_apply]

/-- σ₂ and σ₃ anticommute: {σ₂, σ₃} = 0. -/
theorem σ₂_σ₃_anticommute : anticommutator σ₂ σ₃ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticommutator, σ₂, σ₃, Matrix.add_apply]

/-- Commutation relation: [σ₁, σ₂] = 2iσ₃. -/
theorem σ₁_σ₂_comm : commutator σ₁ σ₂ = (2 * I) • σ₃ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [commutator, σ₁, σ₂, σ₃, Matrix.sub_apply]
  · ring
  · ring

/-! ## Angular momentum operators -/

/-- Angular momentum operators for spin-1/2 particles: Lᵢ = (ℏ/2)σᵢ.
    We use the abstract ℏ from Schrodinger module. -/
noncomputable def Lx : Matrix (Fin 2) (Fin 2) ℂ := (↑(hbar / 2) : ℂ) • σ₁

noncomputable def Ly : Matrix (Fin 2) (Fin 2) ℂ := (↑(hbar / 2) : ℂ) • σ₂

noncomputable def Lz : Matrix (Fin 2) (Fin 2) ℂ := (↑(hbar / 2) : ℂ) • σ₃

/-- Angular momentum commutation relation: [Lx, Ly] = iℏLz. -/
theorem Lx_Ly_comm : commutator Lx Ly = (↑hbar * I) • Lz := by
  unfold commutator Lx Ly Lz
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, σ₃, Matrix.smul_apply, Matrix.sub_apply] <;>
    ring

/-- Pauli matrices as observables. -/
noncomputable def pauliX : Observable 2 where
  mat := σ₁
  selfAdjoint := σ₁_selfAdjoint

noncomputable def pauliZ : Observable 2 where
  mat := σ₃
  selfAdjoint := σ₃_selfAdjoint

/-- Spin-up state |↑⟩ = (1, 0). -/
noncomputable def spinUp : Fin 2 → ℂ := ![1, 0]

/-- Spin-down state |↓⟩ = (0, 1). -/
noncomputable def spinDown : Fin 2 → ℂ := ![0, 1]

/-- Spin-up is an eigenstate of σ₃ with eigenvalue +1. -/
theorem spinUp_eigenstate_σ₃ : IsEigenstate pauliZ spinUp 1 := by
  intro i; fin_cases i <;>
    simp [pauliZ, σ₃, spinUp, Fin.sum_univ_two]

/-- Spin-down is an eigenstate of σ₃ with eigenvalue -1. -/
theorem spinDown_eigenstate_σ₃ : IsEigenstate pauliZ spinDown (-1) := by
  intro i; fin_cases i <;>
    simp [pauliZ, σ₃, spinDown, Fin.sum_univ_two]

end Measure.Physics.QuantumMechanics
