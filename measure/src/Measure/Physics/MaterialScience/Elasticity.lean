/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Elasticity theory — stress and strain tensors, Hooke's law,
elastic moduli, and elastic wave propagation.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace

namespace Measure.Physics.MaterialScience

/-- 3D position vector. -/
abbrev Pos := Fin 3 → ℝ

/-- A 3×3 symmetric tensor (used for stress and strain). -/
abbrev Tensor3 := Matrix (Fin 3) (Fin 3) ℝ

/-! ## Stress Tensor -/

/-- The Cauchy stress tensor σᵢⱼ as a field over space.
    σᵢⱼ represents the force per unit area on face j in direction i. -/
structure StressField where
  /-- The stress tensor field σ(x) : ℝ³ → ℝ³ˣ³. -/
  σ : Pos → Tensor3
  /-- Symmetry of the stress tensor: σᵢⱼ = σⱼᵢ (angular momentum conservation). -/
  symmetric : ∀ x, (σ x).IsSymm

/-- The hydrostatic pressure (negative mean normal stress):
    p = -⅓ tr(σ) = -⅓(σ₁₁ + σ₂₂ + σ₃₃). -/
noncomputable def StressField.pressure (S : StressField) (x : Pos) : ℝ :=
  -(1 / 3) * Matrix.trace (S.σ x)

/-- The deviatoric stress tensor: s = σ + pI (traceless part). -/
noncomputable def StressField.deviatoric (S : StressField) (x : Pos) : Tensor3 :=
  S.σ x - (S.pressure x) • (1 : Tensor3)

/-! ## Strain Tensor -/

/-- A displacement field u(x) : ℝ³ → ℝ³. -/
abbrev DisplacementField := Pos → Pos

/-- The infinitesimal (Cauchy) strain tensor:
    εᵢⱼ = ½(∂uᵢ/∂xⱼ + ∂uⱼ/∂xᵢ). -/
noncomputable def strainTensor (u : DisplacementField) (x : Pos) : Tensor3 :=
  fun i j =>
    (1 / 2) * (deriv (fun s => u (Function.update x j s) i) (x j) +
               deriv (fun s => u (Function.update x i s) j) (x i))

/-- The strain tensor is symmetric by construction. -/
theorem strainTensor_symmetric (u : DisplacementField) (x : Pos) :
    (strainTensor u x).IsSymm := by
  ext i j
  simp [strainTensor]
  ring

/-- Volumetric strain (dilatation): e = tr(ε) = ∇·u. -/
noncomputable def volumetricStrain (u : DisplacementField) (x : Pos) : ℝ :=
  Matrix.trace (strainTensor u x)

/-! ## Elastic Stiffness Tensor -/

/-- The fourth-order elastic stiffness tensor Cᵢⱼₖₗ using Voigt-like indexing.
    Maps strain to stress via σᵢⱼ = Σₖₗ Cᵢⱼₖₗ εₖₗ. -/
structure StiffnessTensor where
  /-- Components Cᵢⱼₖₗ. -/
  C : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ
  /-- Minor symmetry: Cᵢⱼₖₗ = Cⱼᵢₖₗ. -/
  sym_ij : ∀ i j k l, C i j k l = C j i k l
  /-- Minor symmetry: Cᵢⱼₖₗ = Cᵢⱼₗₖ. -/
  sym_kl : ∀ i j k l, C i j k l = C i j l k
  /-- Major symmetry: Cᵢⱼₖₗ = Cₖₗᵢⱼ. -/
  sym_major : ∀ i j k l, C i j k l = C k l i j

/-! ## Hooke's Law (Linear Elasticity) -/

/-- Hooke's law: σᵢⱼ = Σₖₗ Cᵢⱼₖₗ εₖₗ.
    The fundamental constitutive relation of linear elasticity. -/
noncomputable def hookeLaw (C : StiffnessTensor) (ε : Tensor3) : Tensor3 :=
  fun i j => ∑ k : Fin 3, ∑ l : Fin 3, C.C i j k l * ε k l

/-- Hooke's law produces a symmetric stress tensor when applied to a symmetric strain. -/
theorem hookeLaw_symmetric (C : StiffnessTensor) (ε : Tensor3) (_hε : ε.IsSymm) :
    (hookeLaw C ε).IsSymm := by
  ext i j
  simp [hookeLaw]
  congr 1; funext k; congr 1; funext l
  rw [C.sym_ij]

/-! ## Isotropic Elastic Moduli -/

/-- Young's modulus E: ratio of uniaxial stress to strain. -/
abbrev YoungsModulus := ℝ

/-- Poisson's ratio ν: ratio of transverse to axial strain. -/
abbrev PoissonsRatio := ℝ

/-- Shear modulus (modulus of rigidity) G = E / (2(1+ν)). -/
noncomputable def shearModulus (E : YoungsModulus) (ν : PoissonsRatio) : ℝ :=
  E / (2 * (1 + ν))

/-- Bulk modulus K = E / (3(1-2ν)). -/
noncomputable def bulkModulus (E : YoungsModulus) (ν : PoissonsRatio) : ℝ :=
  E / (3 * (1 - 2 * ν))

/-- First Lamé parameter λ = Eν / ((1+ν)(1-2ν)). -/
noncomputable def lameFirst (E : YoungsModulus) (ν : PoissonsRatio) : ℝ :=
  E * ν / ((1 + ν) * (1 - 2 * ν))

/-- Second Lamé parameter μ = G = E / (2(1+ν)). -/
noncomputable def lameSecond (E : YoungsModulus) (ν : PoissonsRatio) : ℝ :=
  shearModulus E ν

/-- Isotropic Hooke's law: σᵢⱼ = λ δᵢⱼ tr(ε) + 2μ εᵢⱼ. -/
noncomputable def isotropicHookeLaw (lam μ : ℝ) (ε : Tensor3) : Tensor3 :=
  fun i j => lam * Matrix.trace ε * (if i = j then 1 else 0) + 2 * μ * ε i j

/-- The isotropic stiffness tensor: Cᵢⱼₖₗ = λ δᵢⱼ δₖₗ + μ(δᵢₖ δⱼₗ + δᵢₗ δⱼₖ). -/
noncomputable def isotropicStiffness (lam μ : ℝ) : StiffnessTensor where
  C := fun i j k l =>
    lam * (if i = j then 1 else 0) * (if k = l then 1 else 0) +
    μ * ((if i = k then 1 else 0) * (if j = l then 1 else 0) +
         (if i = l then 1 else 0) * (if j = k then 1 else 0))
  sym_ij := by intros i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp
  sym_kl := by intros i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp
  sym_major := by intros i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp

/-- The general Hooke's law with isotropic stiffness reduces to the isotropic form. -/
theorem hookeLaw_isotropic (lam μ : ℝ) (ε : Tensor3) (hε : ε.IsSymm) :
    hookeLaw (isotropicStiffness lam μ) ε = isotropicHookeLaw lam μ ε := by
  have hsym : ∀ i j, ε j i = ε i j := fun i j => congr_fun (congr_fun hε i) j
  have h10 : ε 1 0 = ε 0 1 := hsym 0 1
  have h20 : ε 2 0 = ε 0 2 := hsym 0 2
  have h21 : ε 2 1 = ε 1 2 := hsym 1 2
  ext i j
  simp only [hookeLaw, isotropicStiffness, isotropicHookeLaw, Matrix.trace, Matrix.diag,
    Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) [h10, h20, h21] <;> ring

/-- Relationship between bulk and Lamé parameters: K = λ + 2μ/3. -/
theorem bulkModulus_lame (E : YoungsModulus) (ν : PoissonsRatio)
    (hν₁ : ν ≠ -1) (hν₂ : ν ≠ 1/2) :
    bulkModulus E ν = lameFirst E ν + (2 / 3) * lameSecond E ν := by
  unfold bulkModulus lameFirst lameSecond shearModulus
  have h1 : (1 : ℝ) + ν ≠ 0 := by intro h; apply hν₁; linarith
  have h2 : (1 : ℝ) - 2 * ν ≠ 0 := by intro h; apply hν₂; linarith
  have h3 : (3 : ℝ) * (1 - 2 * ν) ≠ 0 := mul_ne_zero (by norm_num) h2
  have h4 : (1 + ν) * (1 - 2 * ν) ≠ 0 := mul_ne_zero h1 h2
  have h5 : (2 : ℝ) * (1 + ν) ≠ 0 := mul_ne_zero (by norm_num) h1
  field_simp
  ring

/-! ## Elastic Wave Equation -/

/-- Divergence of a tensor field: (∇·σ)ᵢ = Σⱼ ∂σᵢⱼ/∂xⱼ. -/
noncomputable def tensorDivergence (σ : Pos → Tensor3) (x : Pos) : Pos :=
  fun i => ∑ j : Fin 3, deriv (fun s => σ (Function.update x j s) i j) (x j)

/-- Cauchy's equation of motion (Newton's second law for continua):
    ρ ∂²u/∂t² = ∇·σ + f, where f is the body force density. -/
noncomputable def CauchyEquationOfMotion (ρ : ℝ) (u : ℝ → DisplacementField)
    (σ : ℝ → Pos → Tensor3) (f : Pos → Pos) : Prop :=
  ∀ (x : Pos) (t : ℝ) (i : Fin 3),
    ρ * deriv (fun s => deriv (fun r => u r x i) s) t =
      tensorDivergence (σ t) x i + f x i

/-- The Navier-Cauchy equation for isotropic linear elasticity:
    ρ ∂²u/∂t² = (λ+μ) ∇(∇·u) + μ ∇²u + f. -/
noncomputable def NavierCauchyEquation (ρ lam μ : ℝ) (u : ℝ → DisplacementField)
    (f : Pos → Pos) : Prop :=
  ∀ (x : Pos) (t : ℝ) (i : Fin 3),
    ρ * deriv (fun s => deriv (fun r => u r x i) s) t =
      (lam + μ) * deriv (fun s =>
        ∑ j : Fin 3, deriv (fun r => u t (Function.update x j r) j) s) (x i) +
      μ * (∑ j : Fin 3, deriv (fun s =>
        deriv (fun r => u t (Function.update (Function.update x j r) j s) i) s) (x j)) +
      f x i

/-- P-wave (longitudinal/compressional) speed: cₚ = √((λ+2μ)/ρ). -/
noncomputable def pWaveSpeed (ρ lam μ : ℝ) : ℝ :=
  Real.sqrt ((lam + 2 * μ) / ρ)

/-- S-wave (transverse/shear) speed: cₛ = √(μ/ρ). -/
noncomputable def sWaveSpeed (ρ μ : ℝ) : ℝ :=
  Real.sqrt (μ / ρ)

/-- P-waves are always faster than S-waves (for λ > 0). -/
theorem pWave_faster_than_sWave (ρ lam μ : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) (hμ : 0 < μ) :
    sWaveSpeed ρ μ < pWaveSpeed ρ lam μ := by
  unfold sWaveSpeed pWaveSpeed
  apply Real.sqrt_lt_sqrt (le_of_lt (div_pos hμ hρ))
  apply div_lt_div_of_pos_right _ hρ
  linarith

end Measure.Physics.MaterialScience
