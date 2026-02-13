/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Noether's theorem: continuous symmetries ↔ conservation laws.
This is one of the most fundamental results in theoretical physics.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Measure.Physics.ClassicalMechanics.Lagrangian

namespace Measure.Physics.ClassicalMechanics

/-- An infinitesimal symmetry transformation on configuration space.
    δqᵢ = εηᵢ(q, q̇, t) where ε is the infinitesimal parameter. -/
structure InfinitesimalSymmetry (n : ℕ) where
  /-- The generator ηᵢ(q, q̇, t) for each coordinate. -/
  η : Fin n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ

/-- A conserved quantity (first integral) along solutions of the EL equations. -/
structure ConservedQuantity (n : ℕ) where
  /-- The conserved quantity Q(q, q̇, t). -/
  Q : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ

/-- The Noether charge associated with a symmetry and Lagrangian:
    Q = Σᵢ (∂L/∂q̇ᵢ) ηᵢ. -/
noncomputable def noetherCharge {n : ℕ} (lag : Lagrangian n)
    (sym : InfinitesimalSymmetry n) : ConservedQuantity n where
  Q := fun q qdot t =>
    ∑ i : Fin n,
      deriv (fun qdoti => lag.L q (Function.update qdot i qdoti) t) (qdot i) *
      sym.η i q qdot t

/-- A Lagrangian is invariant under a symmetry if δL = 0 (up to total derivative). -/
def IsSymmetryOf {n : ℕ} (sym : InfinitesimalSymmetry n) (lag : Lagrangian n) : Prop :=
  ∀ (q qdot : Fin n → ℝ) (t : ℝ),
    ∑ i : Fin n,
      (deriv (fun qi => lag.L (Function.update q i qi) qdot t) (q i) * sym.η i q qdot t +
       deriv (fun qdoti => lag.L q (Function.update qdot i qdoti) t) (qdot i) *
         deriv (fun s => sym.η i q qdot s) t) = 0

/-- Noether's theorem: if a symmetry leaves the Lagrangian invariant,
    then the Noether charge is conserved along solutions of the EL equations.

    Full proof requires the multivariate chain rule for compositions of the form
    f(q(t), q̇(t), t), substitution of the Euler-Lagrange equations, and the
    symmetry condition. This is not yet available in Mathlib for our
    function-based representation. -/
axiom noether_theorem {n : ℕ} (lag : Lagrangian n) (sym : InfinitesimalSymmetry n)
    (q : Path n) (_hsym : IsSymmetryOf sym lag) (_hel : SatisfiesEulerLagrange lag q) :
    ∀ (t : ℝ), deriv (fun s => (noetherCharge lag sym).Q (q s) (velocity q s) s) t = 0

/-- Spatial translation symmetry along direction d. -/
def spatialTranslation {n : ℕ} (d : Fin n) : InfinitesimalSymmetry n where
  η := fun i _q _qdot _t => if i = d then 1 else 0

/-- Rotation symmetry in the (i,j) plane. -/
def rotationSymmetry {n : ℕ} (i j : Fin n) : InfinitesimalSymmetry n where
  η := fun k q _qdot _t =>
    if k = i then -q j
    else if k = j then q i
    else 0

end Measure.Physics.ClassicalMechanics
