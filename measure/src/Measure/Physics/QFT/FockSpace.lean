/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Fock space and creation/annihilation operators — the foundation of QFT.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Measure.Physics.QFT

/-- Occupation number representation: state |n₁, n₂, ..., nₖ⟩.
    Each nᵢ is the number of particles in mode i. -/
structure OccupationState (modes : ℕ) where
  /-- Occupation numbers for each mode. -/
  occupation : Fin modes → ℕ

/-- Creation operator a†ᵢ raises occupation of mode i by 1.
    a†ᵢ |...nᵢ...⟩ = √(nᵢ+1) |...nᵢ+1...⟩ -/
noncomputable def creationCoeff {modes : ℕ} (i : Fin modes)
    (state : OccupationState modes) : ℝ :=
  Real.sqrt ((state.occupation i : ℝ) + 1)

def creationState {modes : ℕ} (i : Fin modes)
    (state : OccupationState modes) : OccupationState modes where
  occupation := Function.update state.occupation i (state.occupation i + 1)

/-- Annihilation operator aᵢ lowers occupation of mode i by 1.
    aᵢ |...nᵢ...⟩ = √nᵢ |...nᵢ-1...⟩ (zero if nᵢ = 0) -/
noncomputable def annihilationCoeff {modes : ℕ} (i : Fin modes)
    (state : OccupationState modes) : ℝ :=
  Real.sqrt (state.occupation i : ℝ)

def annihilationState {modes : ℕ} (i : Fin modes)
    (state : OccupationState modes) : OccupationState modes where
  occupation := Function.update state.occupation i (state.occupation i - 1)

/-- Number operator N̂ᵢ = a†ᵢ aᵢ. Eigenvalue is nᵢ. -/
def numberOperatorEigenvalue {modes : ℕ} (i : Fin modes)
    (state : OccupationState modes) : ℕ :=
  state.occupation i

/-- Total particle number N = Σᵢ nᵢ. -/
def totalParticleNumber {modes : ℕ} (state : OccupationState modes) : ℕ :=
  ∑ i : Fin modes, state.occupation i

/-- Vacuum state |0⟩: all occupation numbers are zero. -/
def vacuum (modes : ℕ) : OccupationState modes where
  occupation := fun _ => 0

/-- Vacuum is annihilated by all annihilation operators. -/
theorem annihilation_vacuum {modes : ℕ} (i : Fin modes) :
    annihilationCoeff i (vacuum modes) = 0 := by
  simp [annihilationCoeff, vacuum, Real.sqrt_zero]

/-- Bosonic commutation relation: [aᵢ, a†ⱼ] = δᵢⱼ.
    This is encoded as: aᵢ a†ⱼ coefficient - a†ⱼ aᵢ coefficient = δᵢⱼ. -/
theorem bosonic_commutation {modes : ℕ} (i j : Fin modes)
    (state : OccupationState modes) :
    annihilationCoeff i (creationState j state) * creationCoeff j state -
    creationCoeff j (annihilationState i state) * annihilationCoeff i state =
    if i = j then 1 else 0 := by
  simp only [creationCoeff, annihilationCoeff, creationState, annihilationState]
  split_ifs with h
  · -- Case i = j: let n = state.occupation i
    -- Term 1 (a a†): √(n+1) * √(n+1) = n+1
    -- Term 2 (a† a): √((n-1)+1) * √n
    --   For ℕ subtraction: n-1+1 = n when n > 0, and 0-1+1 = 1 when n = 0
    --   But √0 = 0 in the n=0 case, so term 2 = 0
    --   For n > 0: term 2 = √n * √n = n
    -- LHS = (n+1) - n = 1 in both cases
    subst h
    simp only [Function.update_self]
    set n := state.occupation i
    have hnn : (0:ℝ) ≤ ↑n := Nat.cast_nonneg n
    have hn1 : (0:ℝ) ≤ ↑n + 1 := by linarith
    -- Goal: √↑(n+1) * √(↑n + 1) - √(↑(n-1) + 1) * √↑n = 1
    have hcast : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
    rw [hcast]
    rw [← Real.sqrt_mul hn1, Real.sqrt_mul_self hn1]
    -- Goal: ↑n + 1 - √(↑(n-1) + 1) * √↑n = 1
    have key : Real.sqrt (↑(n - 1) + 1) * Real.sqrt ↑n = ↑n := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn
      · simp [hn0, Real.sqrt_zero]
      · have : (↑(n - 1) : ℝ) + 1 = ↑n := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))]
          ring
        rw [this, ← Real.sqrt_mul hnn, Real.sqrt_mul_self hnn]
    linarith
  · -- Case i ≠ j: Function.update doesn't affect the other index
    simp only [Function.update_of_ne (Ne.symm h), Function.update_of_ne h]
    ring

end Measure.Physics.QFT
