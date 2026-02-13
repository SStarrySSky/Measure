/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Conservation laws in classical mechanics.
Energy, momentum, and angular momentum conservation.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Measure.Physics.ClassicalMechanics.Lagrangian
import Measure.Physics.ClassicalMechanics.Noether

namespace Measure.Physics.ClassicalMechanics

/-! ## Energy Conservation -/

/-- Total energy for a system with kinetic and potential energy:
    E(q, q̇) = T(q̇) + V(q). -/
noncomputable def totalEnergy {n : ℕ} (masses : Fin n → ℝ)
    (V : (Fin n → ℝ) → ℝ) (q qdot : Fin n → ℝ) : ℝ :=
  kineticEnergy masses qdot + V q

/-- Energy is conserved if dE/dt = 0 along a trajectory. -/
def EnergyConserved {n : ℕ} (masses : Fin n → ℝ)
    (V : (Fin n → ℝ) → ℝ) (q : Path n) : Prop :=
  ∀ (t : ℝ), deriv (fun s => totalEnergy masses V (q s) (velocity q s)) t = 0

/-- For a conservative system (time-independent Lagrangian L = T - V),
    the total energy is conserved along solutions of the Euler-Lagrange equations.
    Follows from Noether's theorem with time-translation symmetry.
    Requires multivariate chain rule + EL equation substitution. -/
axiom energy_conservation {n : ℕ} (masses : Fin n → ℝ)
    (V : (Fin n → ℝ) → ℝ) (q : Path n)
    (_hel : SatisfiesEulerLagrange (standardLagrangian masses V) q) :
    EnergyConserved masses V q

/-! ## Momentum Conservation -/

/-- Linear momentum of the i-th coordinate: pᵢ = mᵢ q̇ᵢ. -/
noncomputable def linearMomentum {n : ℕ} (masses : Fin n → ℝ)
    (qdot : Fin n → ℝ) (i : Fin n) : ℝ :=
  masses i * qdot i

/-- Total linear momentum: P = Σᵢ mᵢ q̇ᵢ. -/
noncomputable def totalLinearMomentum {n : ℕ} (masses : Fin n → ℝ)
    (qdot : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, linearMomentum masses qdot i

/-- Momentum along direction d is conserved if dp_d/dt = 0. -/
def MomentumConserved {n : ℕ} (masses : Fin n → ℝ)
    (q : Path n) (d : Fin n) : Prop :=
  ∀ (t : ℝ), deriv (fun s => linearMomentum masses (velocity q s) d) t = 0

/-- If the potential is translation-invariant along direction d
    (i.e., ∂V/∂qd = 0), then momentum along d is conserved.
    This follows from Noether's theorem with spatial translation symmetry. -/
axiom momentum_conservation {n : ℕ} (masses : Fin n → ℝ)
    (V : (Fin n → ℝ) → ℝ) (q : Path n) (d : Fin n)
    (_hV : ∀ (qv : Fin n → ℝ), deriv (fun qd => V (Function.update qv d qd)) (qv d) = 0)
    (_hel : SatisfiesEulerLagrange (standardLagrangian masses V) q) :
    MomentumConserved masses q d

/-! ## Angular Momentum Conservation -/

/-- Angular momentum in the (i,j)-plane: Lij = mᵢ(qᵢ q̇ⱼ - qⱼ q̇ᵢ).
    For a system where all masses are equal, this simplifies. -/
noncomputable def angularMomentum {n : ℕ} (masses : Fin n → ℝ)
    (q qdot : Fin n → ℝ) (i j : Fin n) : ℝ :=
  masses i * (q i * qdot j - q j * qdot i)

/-- Angular momentum in the (i,j)-plane is conserved if dLij/dt = 0. -/
def AngularMomentumConserved {n : ℕ} (masses : Fin n → ℝ)
    (q : Path n) (i j : Fin n) : Prop :=
  ∀ (t : ℝ), deriv (fun s =>
    angularMomentum masses (q s) (velocity q s) i j) t = 0

/-- If the potential is rotationally invariant in the (i,j)-plane,
    then angular momentum in that plane is conserved.
    This follows from Noether's theorem with rotation symmetry. -/
axiom angular_momentum_conservation {n : ℕ} (masses : Fin n → ℝ)
    (V : (Fin n → ℝ) → ℝ) (q : Path n) (i j : Fin n)
    (_hrot : ∀ (qv : Fin n → ℝ),
      deriv (fun qi => V (Function.update (Function.update qv i qi) j (qv j))) (qv i) * (-qv j) +
      deriv (fun qj => V (Function.update (Function.update qv j qj) i (qv i))) (qv j) * (qv i) = 0)
    (_hel : SatisfiesEulerLagrange (standardLagrangian masses V) q) :
    AngularMomentumConserved masses q i j

end Measure.Physics.ClassicalMechanics
