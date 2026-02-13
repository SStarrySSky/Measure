/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Statistical mechanics — ensembles and partition functions.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Measure.Physics.Thermodynamics.Laws

namespace Measure.Physics.StatisticalMechanics

open Measure.Physics.Thermodynamics
open Real

/-- A discrete energy spectrum (finite system). -/
structure DiscreteSystem (n : ℕ) where
  /-- Energy levels. -/
  energies : Fin n → ℝ
  /-- Degeneracies (positive integers). -/
  degeneracies : Fin n → ℕ
  /-- All degeneracies are positive. -/
  deg_pos : ∀ i, 0 < degeneracies i

/-- Inverse temperature β = 1/(kB T). -/
noncomputable def beta (T : ℝ) : ℝ := 1 / (kB * T)

/-- Canonical partition function Z = Σᵢ gᵢ exp(-β Eᵢ). -/
noncomputable def partitionFunction {n : ℕ} (sys : DiscreteSystem n) (T : ℝ) : ℝ :=
  ∑ i : Fin n, (sys.degeneracies i : ℝ) * exp (-(beta T) * sys.energies i)

/-- Boltzmann probability of state i: pᵢ = gᵢ exp(-β Eᵢ) / Z. -/
noncomputable def boltzmannProb {n : ℕ} (sys : DiscreteSystem n) (T : ℝ)
    (i : Fin n) : ℝ :=
  (sys.degeneracies i : ℝ) * exp (-(beta T) * sys.energies i) / partitionFunction sys T

/-- Helmholtz free energy F = -kB T ln Z. -/
noncomputable def helmholtzFreeEnergy {n : ℕ} (sys : DiscreteSystem n) (T : ℝ) : ℝ :=
  -(kB * T) * log (partitionFunction sys T)

/-- Average energy ⟨E⟩ = Σᵢ pᵢ Eᵢ. -/
noncomputable def averageEnergy {n : ℕ} (sys : DiscreteSystem n) (T : ℝ) : ℝ :=
  ∑ i : Fin n, boltzmannProb sys T i * sys.energies i

/-- Entropy S = -kB Σᵢ pᵢ ln pᵢ (Gibbs entropy). -/
noncomputable def gibbsEntropy {n : ℕ} (sys : DiscreteSystem n) (T : ℝ) : ℝ :=
  -(kB) * ∑ i : Fin n, boltzmannProb sys T i * log (boltzmannProb sys T i)

/-- Probabilities sum to 1. -/
theorem prob_sum_one {n : ℕ} (sys : DiscreteSystem n) (T : ℝ)
    (_hT : 0 < T) (hZ : partitionFunction sys T ≠ 0) :
    ∑ i : Fin n, boltzmannProb sys T i = 1 := by
  simp only [boltzmannProb, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hZ

end Measure.Physics.StatisticalMechanics
