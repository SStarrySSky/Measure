/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Hilbert space foundations for quantum mechanics.
Quantum states live in a complex Hilbert space.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace Measure.Physics.QuantumMechanics

/-- A quantum state is a unit vector in a complex Hilbert space.
    We use Mathlib's inner product space infrastructure. -/
structure QuantumState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The state vector. -/
  vec : H
  /-- Normalization: ⟨ψ|ψ⟩ = 1. -/
  normalized : ‖vec‖ = 1

/-- A quantum observable is a self-adjoint (Hermitian) operator.
    For finite-dimensional spaces, we use matrices. -/
structure Observable (n : ℕ) where
  /-- The matrix representation. -/
  mat : Matrix (Fin n) (Fin n) ℂ
  /-- Self-adjoint condition: A† = A. -/
  selfAdjoint : mat.conjTranspose = mat

/-- Expectation value ⟨ψ|A|ψ⟩ for a finite-dimensional observable. -/
noncomputable def expectation {n : ℕ} (obs : Observable n)
    (ψ : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (ψ i) * obs.mat i j * ψ j

/-- The commutator [A, B] = AB - BA. -/
noncomputable def commutator {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

/-- Two observables commute iff [A, B] = 0. -/
def Commutes {n : ℕ} (A B : Observable n) : Prop :=
  commutator A.mat B.mat = 0

/-- The identity operator. -/
def identityObs (n : ℕ) : Observable n where
  mat := 1
  selfAdjoint := by simp [Matrix.conjTranspose_one]

end Measure.Physics.QuantumMechanics
