/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Bridge between Mathlib real analysis and Measure quantities.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Measure.Math

/-- A smooth scalar field over ℝⁿ, used as the base for physical scalar fields. -/
abbrev ScalarField (n : ℕ) := EuclideanSpace ℝ (Fin n) → ℝ

/-- A smooth vector field over ℝⁿ. -/
abbrev VectorField (n : ℕ) := EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)

/-- Time derivative of a real-valued function. -/
noncomputable def timeDeriv (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

/-- Partial derivative of a scalar field with respect to coordinate i. -/
noncomputable def partialDeriv {n : ℕ} (f : ScalarField n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  deriv (fun s => f (EuclideanSpace.equiv (Fin n) ℝ |>.symm
    (Function.update (EuclideanSpace.equiv (Fin n) ℝ x) i s))) (EuclideanSpace.equiv (Fin n) ℝ x i)

/-- Gradient of a scalar field (vector of partial derivatives). -/
noncomputable def gradient {n : ℕ} (f : ScalarField n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.equiv (Fin n) ℝ |>.symm (fun i => partialDeriv f i x)

end Measure.Math
