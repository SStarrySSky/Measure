/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Lagrangian mechanics formalization.
The Lagrangian L = T - V is the foundation of analytical mechanics.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Measure.Physics.ClassicalMechanics

/-- A generalized coordinate path: a smooth function from time to configuration space ℝⁿ. -/
abbrev Path (n : ℕ) := ℝ → (Fin n → ℝ)

/-- Velocity along a path (time derivative of each coordinate). -/
noncomputable def velocity {n : ℕ} (q : Path n) (t : ℝ) : Fin n → ℝ :=
  fun i => deriv (fun s => q s i) t

/-- A Lagrangian is a function L(q, q̇, t) : ℝⁿ × ℝⁿ × ℝ → ℝ.
    Takes generalized coordinates, velocities, and time. -/
structure Lagrangian (n : ℕ) where
  /-- The Lagrangian function L(q, q̇, t). -/
  L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ

/-- The action functional S[q] = ∫ L(q, q̇, t) dt over [t₁, t₂]. -/
noncomputable def action {n : ℕ} (lag : Lagrangian n) (q : Path n)
    (t₁ t₂ : ℝ) : ℝ :=
  ∫ t in t₁..t₂, lag.L (q t) (velocity q t) t

/-- The Euler-Lagrange equation for coordinate i:
    d/dt (∂L/∂q̇ᵢ) - ∂L/∂qᵢ = 0.
    This is the fundamental equation of motion in Lagrangian mechanics. -/
noncomputable def eulerLagrangeRHS {n : ℕ} (lag : Lagrangian n) (q : Path n)
    (i : Fin n) (t : ℝ) : ℝ :=
  let dLdqi := deriv (fun qi => lag.L (Function.update (q t) i qi) (velocity q t) t) (q t i)
  let ddtdLdqdoti := deriv (fun s =>
    deriv (fun qdoti => lag.L (q s) (Function.update (velocity q s) i qdoti) s) (velocity q s i)) t
  ddtdLdqdoti - dLdqi

/-- A path satisfies the Euler-Lagrange equations if the RHS vanishes for all i and t. -/
def SatisfiesEulerLagrange {n : ℕ} (lag : Lagrangian n) (q : Path n) : Prop :=
  ∀ (i : Fin n) (t : ℝ), eulerLagrangeRHS lag q i t = 0

/-- Standard kinetic energy T = ½ Σᵢ mᵢ q̇ᵢ². -/
noncomputable def kineticEnergy {n : ℕ} (masses : Fin n → ℝ) (qdot : Fin n → ℝ) : ℝ :=
  (1/2) * ∑ i : Fin n, masses i * qdot i ^ 2

/-- Standard Lagrangian L = T - V for a conservative system. -/
noncomputable def standardLagrangian {n : ℕ} (masses : Fin n → ℝ)
    (V : (Fin n → ℝ) → ℝ) : Lagrangian n where
  L := fun q qdot _t => kineticEnergy masses qdot - V q

end Measure.Physics.ClassicalMechanics
