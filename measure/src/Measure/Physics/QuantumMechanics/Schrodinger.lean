/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Schrödinger equation — fundamental equation of quantum mechanics.
iℏ ∂|ψ⟩/∂t = H|ψ⟩
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Measure.Physics.QuantumMechanics.Hilbert

namespace Measure.Physics.QuantumMechanics

/-- Planck constant h = 6.62607015 × 10⁻³⁴ J·s (exact, 2019 SI). -/
noncomputable def planckH : ℝ := 6.62607015e-34

/-- Reduced Planck constant ℏ = h / (2π).
    Derived from the exact SI value of h.
    Numerical value ≈ 1.054571817 × 10⁻³⁴ J·s. -/
noncomputable def hbar : ℝ := planckH / (2 * Real.pi)

/-- ℏ is positive (since h > 0 and π > 0). -/
theorem hbar_pos : 0 < hbar := by
  unfold hbar planckH
  apply div_pos
  · positivity
  · apply mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos

/-- A time-dependent quantum state (state vector as function of time). -/
abbrev TimeDepState (n : ℕ) := ℝ → (Fin n → ℂ)

/-- The time-dependent Schrödinger equation for finite-dimensional systems:
    iℏ d|ψ(t)⟩/dt = H|ψ(t)⟩.
    A state satisfies this equation if the time derivative equals H applied to the state. -/
noncomputable def SatisfiesSchrodinger {n : ℕ} (H : Observable n)
    (ψ : TimeDepState n) : Prop :=
  ∀ (t : ℝ) (i : Fin n),
    (↑(Complex.I * ↑hbar) : ℂ) * deriv (fun s => ψ s i) t =
      ∑ j : Fin n, H.mat i j * ψ t j

/-- Time-independent Schrödinger equation (eigenvalue problem):
    H|ψ⟩ = E|ψ⟩. -/
def IsEigenstate {n : ℕ} (H : Observable n) (ψ : Fin n → ℂ) (E : ℝ) : Prop :=
  ∀ (i : Fin n), ∑ j : Fin n, H.mat i j * ψ j = (↑E : ℂ) * ψ i

/-- The expectation value ⟨ψ|H|ψ⟩ of a Hermitian (self-adjoint) observable is real.
    This is the physically meaningful statement: Hermitian operators have real
    expectation values, which is why they represent physical observables.

    Proof: For self-adjoint A (A† = A),
      conj(⟨ψ|A|ψ⟩) = ∑ᵢⱼ conj(ψ̄ᵢ Aᵢⱼ ψⱼ)
                       = ∑ᵢⱼ ψᵢ conj(Aᵢⱼ) ψ̄ⱼ
                       = ∑ᵢⱼ ψ̄ⱼ (A†)ⱼᵢ ψᵢ     (reindex)
                       = ∑ᵢⱼ ψ̄ⱼ Aⱼᵢ ψᵢ         (A† = A)
                       = ⟨ψ|A|ψ⟩ -/
theorem expectation_real {n : ℕ} (H : Observable n) (ψ : Fin n → ℂ) :
    starRingEnd ℂ (expectation H ψ) = expectation H ψ := by
  unfold expectation
  simp only [map_sum, map_mul, starRingEnd_self_apply]
  -- LHS is now: ∑ i, ∑ j, ψ i * star(H.mat i j) * star(ψ j)
  -- Use self-adjointness: star(H.mat i j) = H.mat.conjTranspose j i = H.mat j i
  -- Then swap i ↔ j to recover the original sum.
  have hsym : ∀ i j, starRingEnd ℂ (H.mat i j) = H.mat j i := by
    intro i j
    have : H.mat.conjTranspose j i = H.mat j i := by rw [H.selfAdjoint]
    rw [← this]; rfl
  simp_rw [hsym]
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext i
  ring

/-- Stationary state: time evolution of an eigenstate is just a phase.
    |ψ(t)⟩ = e^{-iEt/ℏ} |ψ⟩. -/
noncomputable def stationaryState {n : ℕ} (ψ₀ : Fin n → ℂ) (E : ℝ) : TimeDepState n :=
  fun t i => Complex.exp (↑(-E * t / hbar) * Complex.I) * ψ₀ i

end Measure.Physics.QuantumMechanics
