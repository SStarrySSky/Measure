/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Metric tensor — definitions, Schwarzschild metric, and geodesic equation.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Measure.Physics.GeneralRelativity

/-! ## Spacetime Coordinates -/

/-- Spacetime dimension (4D). -/
abbrev dim : ℕ := 4

/-- A spacetime event represented by coordinates xμ = (x⁰, x¹, x², x³). -/
abbrev Event := Fin dim → ℝ

/-- A worldline is a curve in spacetime parameterized by an affine parameter. -/
abbrev Worldline := ℝ → Event

/-! ## Metric Tensor -/

/-- A metric tensor gμν on a 4D spacetime manifold.
    The metric is a symmetric (0,2)-tensor field that defines distances and angles. -/
structure MetricTensor where
  /-- Components gμν(x) at each spacetime point. -/
  g : Event → Matrix (Fin dim) (Fin dim) ℝ
  /-- The metric is symmetric: gμν = gνμ. -/
  symmetric : ∀ (x : Event) (μ ν : Fin dim), g x μ ν = g x ν μ
  /-- The metric is non-degenerate (det g ≠ 0). -/
  nondegenerate : ∀ (x : Event), (g x).det ≠ 0

/-- The line element ds² = gμν dxμ dxν along a worldline. -/
noncomputable def MetricTensor.lineElement (met : MetricTensor) (γ : Worldline) (lam : ℝ) : ℝ :=
  ∑ μ : Fin dim, ∑ ν : Fin dim,
    met.g (γ lam) μ ν * deriv (fun s => γ s μ) lam * deriv (fun s => γ s ν) lam

/-- The inverse metric gμν (contravariant components). -/
noncomputable def MetricTensor.inverse (met : MetricTensor) (x : Event) : Matrix (Fin dim) (Fin dim) ℝ :=
  (met.g x)⁻¹

/-- The inverse metric satisfies gμα gαν = δμν. -/
theorem MetricTensor.inverse_spec (met : MetricTensor) (x : Event) :
    met.g x * met.inverse x = 1 := by
  unfold MetricTensor.inverse
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (met.nondegenerate x))

/-! ## Flat Minkowski Metric -/

/-- The flat Minkowski metric ημν = diag(-1, 1, 1, 1). -/
noncomputable def minkowskiMetric : MetricTensor where
  g := fun _x => Matrix.diagonal (fun i =>
    match i with
    | ⟨0, _⟩ => -1
    | _ => 1)
  symmetric := by
    intro x μ ν
    simp only [Matrix.diagonal, Matrix.of_apply]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd (h1.symm) h2
    · exact absurd (h2.symm) h1
    · rfl
  nondegenerate := by
    intro x
    simp only [Matrix.det_diagonal, Fin.prod_univ_four]
    norm_num

/-! ## Schwarzschild Metric -/

/-- Parameters for the Schwarzschild solution. -/
structure SchwarzschildParams where
  /-- Mass of the central body (in geometric units G = c = 1). -/
  M : ℝ
  /-- Mass is positive. -/
  M_pos : 0 < M

/-- Schwarzschild radius rₛ = 2GM/c² (in geometric units: rₛ = 2M). -/
noncomputable def SchwarzschildParams.schwarzschildRadius (p : SchwarzschildParams) : ℝ :=
  2 * p.M

/-- A point is outside the Schwarzschild horizon. -/
def SchwarzschildParams.outsideHorizon (p : SchwarzschildParams) (r : ℝ) : Prop :=
  p.schwarzschildRadius < r

/-- The Schwarzschild radius is positive. -/
theorem SchwarzschildParams.schwarzschildRadius_pos (p : SchwarzschildParams) :
    0 < p.schwarzschildRadius := by
  unfold schwarzschildRadius
  linarith [p.M_pos]

/-- The Schwarzschild metric components in Schwarzschild coordinates (t, r, θ, φ).
    ds² = -(1 - rₛ/r)dt² + (1 - rₛ/r)⁻¹dr² + r²dθ² + r²sin²θ dφ²

    Here x⁰ = t, x¹ = r, x² = θ, x³ = φ. -/
noncomputable def schwarzschildComponents (p : SchwarzschildParams) :
    Event → Matrix (Fin dim) (Fin dim) ℝ := fun x =>
  let r := x 1
  let θ := x 2
  let rₛ := p.schwarzschildRadius
  let f := 1 - rₛ / r
  Matrix.of (fun μ ν =>
    match μ, ν with
    | ⟨0, _⟩, ⟨0, _⟩ => -f
    | ⟨1, _⟩, ⟨1, _⟩ => 1 / f
    | ⟨2, _⟩, ⟨2, _⟩ => r ^ 2
    | ⟨3, _⟩, ⟨3, _⟩ => r ^ 2 * (Real.sin θ) ^ 2
    | _, _ => 0)

/-- The Schwarzschild metric components are symmetric. -/
theorem schwarzschildComponents_symmetric (p : SchwarzschildParams)
    (x : Event) (μ ν : Fin dim) :
    schwarzschildComponents p x μ ν = schwarzschildComponents p x ν μ := by
  simp only [schwarzschildComponents, Matrix.of_apply]
  fin_cases μ <;> fin_cases ν <;> simp

/-- The Schwarzschild metric determinant is non-degenerate outside the horizon.
    Requires r > rₛ (outside the event horizon) and sin θ ≠ 0 (away from poles).
    The determinant is det(g) = -r⁴ sin²θ, which is non-zero under these conditions.
    The matrix is diagonal, so det = ∏ diagonal entries = (-f)(1/f)(r²)(r²sin²θ) = -r⁴sin²θ,
    and each factor is nonzero given the hypotheses. -/
theorem schwarzschildComponents_nondegenerate (p : SchwarzschildParams)
    (x : Event) (hr : p.outsideHorizon (x 1)) (hθ : Real.sin (x 2) ≠ 0) :
    (schwarzschildComponents p x).det ≠ 0 := by
  have hdiag : schwarzschildComponents p x = Matrix.diagonal (fun i : Fin dim =>
      match i with
      | ⟨0, _⟩ => -(1 - p.schwarzschildRadius / x 1)
      | ⟨1, _⟩ => 1 / (1 - p.schwarzschildRadius / x 1)
      | ⟨2, _⟩ => (x 1) ^ 2
      | ⟨3, _⟩ => (x 1) ^ 2 * (Real.sin (x 2)) ^ 2) := by
    ext μ ν
    simp only [schwarzschildComponents, Matrix.of_apply, Matrix.diagonal]
    fin_cases μ <;> fin_cases ν <;> simp
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_four]
  simp only []
  unfold SchwarzschildParams.outsideHorizon SchwarzschildParams.schwarzschildRadius at hr
  have hM := p.M_pos
  have hr_pos : 0 < x 1 := by linarith
  have hf_pos : 0 < 1 - p.schwarzschildRadius / x 1 := by
    rw [sub_pos, div_lt_one hr_pos]
    unfold SchwarzschildParams.schwarzschildRadius
    exact hr
  apply mul_ne_zero
  apply mul_ne_zero
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (ne_of_gt hf_pos)
  · exact one_div_ne_zero (ne_of_gt hf_pos)
  · exact pow_ne_zero 2 (ne_of_gt hr_pos)
  · exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hr_pos)) (pow_ne_zero 2 hθ)

/-- The Schwarzschild metric in Schwarzschild coordinates (t, r, θ, φ),
    valid on a domain where r > rₛ and sin θ ≠ 0.

    The domain restriction `hdom` ensures the metric is non-degenerate at every
    event, which is physically correct: the Schwarzschild coordinates are singular
    at the horizon (r = rₛ) and at the poles (θ = 0, π). -/
noncomputable def schwarzschildMetric (p : SchwarzschildParams)
    (hdom : ∀ x : Event, p.outsideHorizon (x 1) ∧ Real.sin (x 2) ≠ 0) :
    MetricTensor where
  g := schwarzschildComponents p
  symmetric := schwarzschildComponents_symmetric p
  nondegenerate := fun x =>
    schwarzschildComponents_nondegenerate p x (hdom x).1 (hdom x).2

/-! ## Christoffel Symbols -/

/-- Christoffel symbols of the second kind: Γᵅμν = ½gᵅβ(∂μgβν + ∂νgβμ - ∂βgμν).
    These encode how the coordinate basis vectors change from point to point. -/
noncomputable def christoffelSymbol (met : MetricTensor) (x : Event)
    (α μ ν : Fin dim) : ℝ :=
  let gInv := met.inverse x
  (1 / 2) * ∑ β : Fin dim, gInv α β * (
    deriv (fun s => met.g (Function.update x μ s) β ν) (x μ) +
    deriv (fun s => met.g (Function.update x ν s) β μ) (x ν) -
    deriv (fun s => met.g (Function.update x β s) μ ν) (x β))

/-- Christoffel symbols are symmetric in the lower indices: Γᵅμν = Γᵅνμ. -/
theorem christoffel_symmetric (met : MetricTensor) (x : Event)
    (α μ ν : Fin dim) :
    christoffelSymbol met x α μ ν = christoffelSymbol met x α ν μ := by
  simp only [christoffelSymbol]
  congr 1
  apply Finset.sum_congr rfl
  intro β _
  have hsym : ∀ s, met.g (Function.update x β s) μ ν = met.g (Function.update x β s) ν μ :=
    fun s => met.symmetric _ μ ν
  have hderiv : deriv (fun s => met.g (Function.update x β s) μ ν) (x β) =
    deriv (fun s => met.g (Function.update x β s) ν μ) (x β) := by
    congr 1; ext s; exact hsym s
  congr 1
  linarith

/-! ## Geodesic Equation -/

/-- The geodesic equation: d²xᵅ/dλ² + Γᵅμν (dxμ/dλ)(dxν/dλ) = 0.
    Geodesics are curves that parallel-transport their own tangent vector. -/
noncomputable def geodesicEquation (met : MetricTensor) (γ : Worldline)
    (α : Fin dim) (lam : ℝ) : Prop :=
  deriv (fun s => deriv (fun u => γ u α) s) lam +
    ∑ μ : Fin dim, ∑ ν : Fin dim,
      christoffelSymbol met (γ lam) α μ ν *
        deriv (fun s => γ s μ) lam * deriv (fun s => γ s ν) lam = 0

/-- A worldline is a geodesic if the geodesic equation holds for all components
    and all values of the affine parameter. -/
def IsGeodesic (met : MetricTensor) (γ : Worldline) : Prop :=
  ∀ (α : Fin dim) (lam : ℝ), geodesicEquation met γ α lam

/-- Proper time along a timelike geodesic. -/
noncomputable def properTime (met : MetricTensor) (γ : Worldline) (lam1 lam2 : ℝ) : ℝ :=
  ∫ s in lam1..lam2, Real.sqrt (-(met.lineElement γ s))

end Measure.Physics.GeneralRelativity
