/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Classical and quantum fields.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Measure.Physics.QFT

/-- A classical scalar field φ(x, t) : ℝ³ × ℝ → ℝ. -/
abbrev ScalarField := (Fin 3 → ℝ) → ℝ → ℝ

/-- A classical complex scalar field φ(x, t) : ℝ³ × ℝ → ℂ. -/
abbrev ComplexScalarField := (Fin 3 → ℝ) → ℝ → ℂ

/-- A classical vector field Aμ(x, t) : ℝ³ × ℝ → ℝ⁴ (gauge field). -/
abbrev GaugeField := (Fin 3 → ℝ) → ℝ → (Fin 4 → ℝ)

/-- Lagrangian density ℒ(φ, ∂μφ) for a field theory. -/
structure LagrangianDensity where
  /-- The Lagrangian density function. -/
  ℒ : ScalarField → (Fin 4 → ScalarField) → (Fin 3 → ℝ) → ℝ → ℝ

/-- Klein-Gordon mass parameter. -/
structure KleinGordonParams where
  /-- Mass parameter m. -/
  m : ℝ
  /-- Mass is non-negative. -/
  m_nonneg : 0 ≤ m

/-- Klein-Gordon equation: (□ + m²)φ = 0
    where □ = -∂²/∂t² + ∇² is the d'Alembertian. -/
noncomputable def KleinGordonEq (params : KleinGordonParams) (φ : ScalarField) : Prop :=
  ∀ (x : Fin 3 → ℝ) (t : ℝ),
    -(deriv (fun s => deriv (fun r => φ x r) s) t) +
    (∑ i : Fin 3, deriv (fun s => deriv (fun r => φ (Function.update x i r) s) (x i)) (x i)) +
    params.m ^ 2 * φ x t = 0

/-- Dirac spinor (4-component complex). -/
abbrev DiracSpinor := Fin 4 → ℂ

/-- Minkowski metric diagonal entries for Clifford algebra. -/
def minkowskiDiag (μ ν : Fin 4) : ℝ :=
  if μ = ν then (if μ = ⟨0, by omega⟩ then -1 else 1) else 0

/-- Dirac gamma matrices γ⁰, γ¹, γ², γ³ (4×4 complex matrices).
    Satisfy the Clifford algebra: {γμ, γν} = 2ημν. -/
structure GammaMatrices where
  /-- The four gamma matrices. -/
  γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  /-- Clifford algebra relation. -/
  clifford : ∀ (μ ν : Fin 4),
    γ μ * γ ν + γ ν * γ μ = 2 * (↑(minkowskiDiag μ ν) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

end Measure.Physics.QFT
