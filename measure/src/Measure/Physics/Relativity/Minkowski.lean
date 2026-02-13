/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Minkowski spacetime and special relativity foundations.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Measure.Physics.Relativity

/-- A four-vector in Minkowski spacetime (ct, x, y, z). -/
abbrev FourVector := Fin 4 → ℝ

/-- The Minkowski metric η = diag(-1, 1, 1, 1).
    Convention: signature (-,+,+,+). -/
noncomputable def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i =>
    match i with
    | ⟨0, _⟩ => -1
    | _ => 1)

/-- Minkowski inner product: η(u, v) = -u⁰v⁰ + u¹v¹ + u²v² + u³v³. -/
noncomputable def minkowskiInner (u v : FourVector) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, minkowskiMetric i j * u i * v j

/-- Spacetime interval s² = η(Δx, Δx). -/
noncomputable def spacetimeInterval (x y : FourVector) : ℝ :=
  minkowskiInner (fun i => x i - y i) (fun i => x i - y i)

/-- A four-vector is timelike if η(v,v) < 0. -/
def IsTimelike (v : FourVector) : Prop :=
  minkowskiInner v v < 0

/-- A four-vector is spacelike if η(v,v) > 0. -/
def IsSpacelike (v : FourVector) : Prop :=
  minkowskiInner v v > 0

/-- A four-vector is lightlike (null) if η(v,v) = 0. -/
def IsLightlike (v : FourVector) : Prop :=
  minkowskiInner v v = 0

/-- Speed of light (normalized to 1 in natural units, or 299792458 m/s). -/
noncomputable def c : ℝ := 299792458

/-- Lorentz factor γ = 1/√(1 - v²/c²). -/
noncomputable def lorentzFactor (v : ℝ) : ℝ :=
  1 / Real.sqrt (1 - v^2 / c^2)

/-- Proper time along a timelike worldline. -/
noncomputable def properTime (x : ℝ → FourVector) (t₁ t₂ : ℝ) : ℝ :=
  ∫ t in t₁..t₂, Real.sqrt (-(minkowskiInner (deriv x t) (deriv x t)))

end Measure.Physics.Relativity
