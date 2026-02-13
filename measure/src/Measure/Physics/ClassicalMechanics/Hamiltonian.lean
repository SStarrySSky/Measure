/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Hamiltonian mechanics formalization.
The Hamiltonian H(q, p, t) governs time evolution via Hamilton's equations.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Measure.Physics.ClassicalMechanics.Lagrangian

namespace Measure.Physics.ClassicalMechanics

/-- A Hamiltonian is a function H(q, p, t) : ℝⁿ × ℝⁿ × ℝ → ℝ.
    Takes generalized coordinates, conjugate momenta, and time. -/
structure Hamiltonian (n : ℕ) where
  /-- The Hamiltonian function H(q, p, t). -/
  H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ

/-- Phase space point: (q, p) pair. -/
structure PhasePoint (n : ℕ) where
  /-- Generalized coordinates. -/
  q : Fin n → ℝ
  /-- Conjugate momenta. -/
  p : Fin n → ℝ

/-- A phase space trajectory. -/
abbrev PhaseTrajectory (n : ℕ) := ℝ → PhasePoint n

/-- Hamilton's equation: dqᵢ/dt = ∂H/∂pᵢ. -/
noncomputable def hamiltonQ {n : ℕ} (ham : Hamiltonian n) (γ : PhaseTrajectory n)
    (i : Fin n) (t : ℝ) : Prop :=
  deriv (fun s => (γ s).q i) t =
    deriv (fun pi => ham.H (γ t).q (Function.update (γ t).p i pi) t) ((γ t).p i)

/-- Hamilton's equation: dpᵢ/dt = -∂H/∂qᵢ. -/
noncomputable def hamiltonP {n : ℕ} (ham : Hamiltonian n) (γ : PhaseTrajectory n)
    (i : Fin n) (t : ℝ) : Prop :=
  deriv (fun s => (γ s).p i) t =
    -(deriv (fun qi => ham.H (Function.update (γ t).q i qi) (γ t).p t) ((γ t).q i))

/-- A trajectory satisfies Hamilton's equations. -/
def SatisfiesHamiltonEqs {n : ℕ} (ham : Hamiltonian n) (γ : PhaseTrajectory n) : Prop :=
  ∀ (i : Fin n) (t : ℝ), hamiltonQ ham γ i t ∧ hamiltonP ham γ i t

/-- Poisson bracket {f, g} = Σᵢ (∂f/∂qᵢ ∂g/∂pᵢ - ∂f/∂pᵢ ∂g/∂qᵢ). -/
noncomputable def poissonBracket {n : ℕ}
    (f g : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (q p : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    (deriv (fun qi => f (Function.update q i qi) p) (q i) *
     deriv (fun pi => g q (Function.update p i pi)) (p i) -
     deriv (fun pi => f q (Function.update p i pi)) (p i) *
     deriv (fun qi => g (Function.update q i qi) p) (q i))

/-- Velocity-momentum map: recovers generalized velocities q̇ from (q, p, t).
    This is the inverse of the fiber derivative pᵢ = ∂L/∂q̇ᵢ. -/
abbrev VelocityFromMomentum (n : ℕ) := (Fin n → ℝ) → (Fin n → ℝ) → ℝ → (Fin n → ℝ)

/-- Legendre transform: convert Lagrangian to Hamiltonian.
    Given the inverse fiber derivative q̇ = q̇(q, p, t), we define
    H(q, p, t) = Σᵢ pᵢq̇ᵢ - L(q, q̇, t). -/
noncomputable def legendreTransform {n : ℕ} (lag : Lagrangian n)
    (qdotOf : VelocityFromMomentum n) : Hamiltonian n where
  H := fun q p t =>
    let qdot := qdotOf q p t
    ∑ i : Fin n, p i * qdot i - lag.L q qdot t

/-- Legendre transform for standard Lagrangian L = T - V with T = ½ Σ mᵢ q̇ᵢ².
    For this case pᵢ = mᵢq̇ᵢ, so q̇ᵢ = pᵢ/mᵢ, and
    H = Σᵢ pᵢ²/(2mᵢ) + V(q). -/
noncomputable def legendreTransformStandard {n : ℕ} (masses : Fin n → ℝ)
    (V : (Fin n → ℝ) → ℝ) : Hamiltonian n where
  H := fun q p _t =>
    ∑ i : Fin n, p i ^ 2 / (2 * masses i) + V q

end Measure.Physics.ClassicalMechanics
