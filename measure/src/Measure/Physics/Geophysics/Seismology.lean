/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Seismology — seismic wave equations (P-waves and S-waves),
wave speed relations, Snell's law, and Earth interior models.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace Measure.Physics.Geophysics

/-- 3D position vector type. -/
abbrev Pos := Fin 3 → ℝ

/-- Scalar field type. -/
abbrev ScalarField := Pos → ℝ

/-- Vector field type. -/
abbrev VectorField := Pos → Pos

/-! ## Differential Operators -/

/-- Gradient of a scalar field: (∇φ)ᵢ = ∂φ/∂xᵢ. -/
noncomputable def gradient (φ : ScalarField) (x : Pos) : Pos :=
  fun i => deriv (fun s => φ (Function.update x i s)) (x i)

/-- Laplacian of a scalar field: ∇²φ = Σᵢ ∂²φ/∂xᵢ². -/
noncomputable def laplacian (φ : ScalarField) (x : Pos) : ℝ :=
  ∑ i : Fin 3, deriv (fun s =>
    deriv (fun r => φ (Function.update x i r)) s) (x i)

/-- Vector Laplacian: (∇²u)ᵢ = ∇²(uᵢ). -/
noncomputable def vectorLaplacian (u : VectorField) (x : Pos) : Pos :=
  fun i => laplacian (fun y => u y i) x

/-- Divergence of a vector field: ∇·u = Σᵢ ∂uᵢ/∂xᵢ. -/
noncomputable def divergence (u : VectorField) (x : Pos) : ℝ :=
  ∑ i : Fin 3, deriv (fun s => u (Function.update x i s) i) (x i)

/-- Gradient of divergence: (∇(∇·u))ᵢ = ∂(∇·u)/∂xᵢ. -/
noncomputable def gradDivergence (u : VectorField) (x : Pos) : Pos :=
  gradient (divergence u) x

/-! ## Elastic Medium Properties -/

/-- Properties of an elastic medium relevant to seismic wave propagation. -/
structure ElasticMedium where
  /-- Mass density ρ (kg/m³). -/
  ρ : ℝ
  /-- First Lamé parameter (Pa). -/
  lame1 : ℝ
  /-- Second Lamé parameter / shear modulus (Pa). -/
  shearMod : ℝ
  /-- Density is positive. -/
  ρ_pos : 0 < ρ
  /-- Shear modulus is non-negative. -/
  shearMod_nonneg : 0 ≤ shearMod

/-- Bulk modulus K = λ + 2μ/3. -/
noncomputable def ElasticMedium.bulkModulus (m : ElasticMedium) : ℝ :=
  m.lame1 + 2 * m.shearMod / 3

/-- Young's modulus E = μ(3λ + 2μ)/(λ + μ). -/
noncomputable def ElasticMedium.youngModulus (m : ElasticMedium) : ℝ :=
  m.shearMod * (3 * m.lame1 + 2 * m.shearMod) / (m.lame1 + m.shearMod)

/-- Poisson's ratio ν = λ / (2(λ + μ)). -/
noncomputable def ElasticMedium.poissonRatio (m : ElasticMedium) : ℝ :=
  m.lame1 / (2 * (m.lame1 + m.shearMod))

/-! ## P-Wave (Primary / Compressional Wave) -/

/-- P-wave speed: v_P = √((λ + 2μ) / ρ). -/
noncomputable def pWaveSpeed (m : ElasticMedium) : ℝ :=
  Real.sqrt ((m.lame1 + 2 * m.shearMod) / m.ρ)

/-- A time-dependent displacement field u(x, t). -/
abbrev DisplacementEvolution := ℝ → VectorField

/-- The scalar wave equation for P-waves (in terms of the dilatation φ = ∇·u):
    ∂²φ/∂t² = v_P² ∇²φ. -/
noncomputable def PWaveEquation (m : ElasticMedium)
    (u : DisplacementEvolution) : Prop :=
  let vp := pWaveSpeed m
  ∀ (x : Pos) (t : ℝ),
    deriv (fun s => deriv (fun r => divergence (u r) x) s) t =
      vp ^ 2 * laplacian (divergence (u t)) x

/-! ## S-Wave (Secondary / Shear Wave) -/

/-- S-wave speed: v_S = √(μ / ρ). -/
noncomputable def sWaveSpeed (m : ElasticMedium) : ℝ :=
  Real.sqrt (m.shearMod / m.ρ)

/-- S-waves do not propagate in fluids (μ = 0 implies v_S = 0). -/
theorem sWave_zero_in_fluid (m : ElasticMedium) (hfluid : m.shearMod = 0) :
    sWaveSpeed m = 0 := by
  simp [sWaveSpeed, hfluid]

/-- P-wave speed is always greater than or equal to S-wave speed. -/
theorem pWave_ge_sWave (m : ElasticMedium) (hlame : 0 ≤ m.lame1) :
    sWaveSpeed m ≤ pWaveSpeed m := by
  unfold sWaveSpeed pWaveSpeed
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (le_of_lt m.ρ_pos)
  linarith [m.shearMod_nonneg]

/-- The v_P / v_S ratio for a Poisson solid (λ = μ): v_P/v_S = √3. -/
theorem vp_vs_ratio_poisson_solid (m : ElasticMedium)
    (hpoisson : m.lame1 = m.shearMod) (hmu : 0 < m.shearMod) :
    pWaveSpeed m ^ 2 / sWaveSpeed m ^ 2 = 3 := by
  unfold pWaveSpeed sWaveSpeed
  have hρ : (0 : ℝ) < m.ρ := m.ρ_pos
  have hmu_div : 0 ≤ m.shearMod / m.ρ := div_nonneg (le_of_lt hmu) (le_of_lt hρ)
  have hlame_div : 0 ≤ (m.lame1 + 2 * m.shearMod) / m.ρ := by
    apply div_nonneg _ (le_of_lt hρ)
    linarith
  rw [Real.sq_sqrt hmu_div, Real.sq_sqrt hlame_div]
  rw [hpoisson]
  field_simp
  ring

/-! ## Elastodynamic Wave Equation -/

/-- The full elastodynamic equation (Navier-Cauchy):
    ρ ∂²u/∂t² = (λ + μ) ∇(∇·u) + μ ∇²u.
    This is the fundamental equation governing seismic wave propagation
    in a homogeneous isotropic elastic medium. -/
noncomputable def ElastodynamicEquation (m : ElasticMedium)
    (u : DisplacementEvolution) : Prop :=
  ∀ (x : Pos) (t : ℝ) (i : Fin 3),
    m.ρ * deriv (fun s => deriv (fun r => u r x i) s) t =
      (m.lame1 + m.shearMod) * gradDivergence (u t) x i +
        m.shearMod * vectorLaplacian (u t) x i

/-! ## Snell's Law in Seismology -/

/-- Snell's law for seismic waves at a layer boundary:
    sin(θ₁)/v₁ = sin(θ₂)/v₂.
    The ray parameter p = sin(θ)/v is constant along a ray. -/
noncomputable def rayParameter (θ v : ℝ) : ℝ :=
  Real.sin θ / v

/-- Snell's law: the ray parameter is conserved across an interface. -/
noncomputable def SnellLaw (θ₁ v₁ θ₂ v₂ : ℝ) : Prop :=
  rayParameter θ₁ v₁ = rayParameter θ₂ v₂

/-- Critical angle: total internal reflection occurs when sin(θ_c) = v₁/v₂. -/
noncomputable def criticalAngle (v₁ v₂ : ℝ) : ℝ :=
  Real.arcsin (v₁ / v₂)

/-- At the critical angle, the refracted ray is horizontal (θ₂ = π/2). -/
theorem snell_critical_angle (v₁ v₂ : ℝ) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hlt : v₁ < v₂) :
    SnellLaw (criticalAngle v₁ v₂) v₁ (Real.pi / 2) v₂ := by
  unfold SnellLaw rayParameter criticalAngle
  have hv₁₂ : v₁ / v₂ ≤ 1 := by
    rw [div_le_one hv₂]
    linarith
  have hv₁₂' : 0 ≤ v₁ / v₂ := div_nonneg (le_of_lt hv₁) (le_of_lt hv₂)
  have habs : |v₁ / v₂| ≤ 1 := by
    rw [abs_of_nonneg hv₁₂']
    exact hv₁₂
  rw [Real.sin_arcsin (by linarith : -(1 : ℝ) ≤ v₁ / v₂) hv₁₂, Real.sin_pi_div_two]
  field_simp

/-! ## Earth Interior Structure -/

/-- Layers of the Earth's interior. -/
inductive EarthLayer where
  /-- Inner core (solid iron-nickel). -/
  | innerCore
  /-- Outer core (liquid iron-nickel). -/
  | outerCore
  /-- Lower mantle. -/
  | lowerMantle
  /-- Upper mantle. -/
  | upperMantle
  /-- Crust. -/
  | crust

/-- Approximate depth range (km) for each Earth layer. -/
noncomputable def EarthLayer.depthRange : EarthLayer → ℝ × ℝ
  | .innerCore   => (5150, 6371)
  | .outerCore   => (2891, 5150)
  | .lowerMantle => (670, 2891)
  | .upperMantle => (35, 670)
  | .crust       => (0, 35)

/-- Approximate P-wave speed (km/s) in each layer. -/
noncomputable def EarthLayer.approxPWaveSpeed : EarthLayer → ℝ
  | .innerCore   => 11.0
  | .outerCore   => 8.0
  | .lowerMantle => 13.0
  | .upperMantle => 8.1
  | .crust       => 6.0

/-- Approximate S-wave speed (km/s) in each layer (0 in liquid outer core). -/
noncomputable def EarthLayer.approxSWaveSpeed : EarthLayer → ℝ
  | .innerCore   => 3.6
  | .outerCore   => 0    -- liquid: no S-waves
  | .lowerMantle => 7.0
  | .upperMantle => 4.5
  | .crust       => 3.5

/-- The outer core is liquid, so S-waves cannot propagate through it. -/
theorem outerCore_no_sWave : EarthLayer.approxSWaveSpeed .outerCore = 0 := by
  rfl

/-- A 1D radial Earth model: seismic velocities as functions of depth. -/
structure RadialEarthModel where
  /-- P-wave speed as a function of depth (km). -/
  vp : ℝ → ℝ
  /-- S-wave speed as a function of depth (km). -/
  vs : ℝ → ℝ
  /-- Density as a function of depth (km). -/
  ρ : ℝ → ℝ
  /-- P-wave speed is positive everywhere. -/
  vp_pos : ∀ d, 0 ≤ d → 0 < vp d
  /-- Density is positive everywhere. -/
  ρ_pos : ∀ d, 0 ≤ d → 0 < ρ d

/-- Travel time of a seismic ray through a layer of thickness h
    with constant velocity v at incidence angle θ:
    t = h / (v cos θ). -/
noncomputable def layerTravelTime (h v θ : ℝ) : ℝ :=
  h / (v * Real.cos θ)

end Measure.Physics.Geophysics
