/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Diffusion processes in biophysics — Fick's laws, Brownian motion,
Langevin equation, and random walks.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Measure.Physics.Biophysics

/-- 3D position vector type. -/
abbrev Pos := Fin 3 → ℝ

/-- Scalar field type (e.g., concentration). -/
abbrev ScalarField := Pos → ℝ

/-- Vector field type (e.g., flux). -/
abbrev VectorField := Pos → Pos

/-! ## Differential Operators -/

/-- Gradient of a scalar field: (∇c)ᵢ = ∂c/∂xᵢ. -/
noncomputable def gradient (c : ScalarField) (x : Pos) : Pos :=
  fun i => deriv (fun s => c (Function.update x i s)) (x i)

/-- Laplacian of a scalar field: ∇²c = Σᵢ ∂²c/∂xᵢ². -/
noncomputable def laplacian (c : ScalarField) (x : Pos) : ℝ :=
  ∑ i : Fin 3, deriv (fun s =>
    deriv (fun r => c (Function.update x i r)) s) (x i)

/-- Divergence of a vector field: ∇·J = Σᵢ ∂Jᵢ/∂xᵢ. -/
noncomputable def divergence (J : VectorField) (x : Pos) : ℝ :=
  ∑ i : Fin 3, deriv (fun s => J (Function.update x i s) i) (x i)

/-! ## Fick's First Law -/

/-- Diffusion coefficient D (material property, units m²/s). -/
abbrev DiffusionCoeff := ℝ

/-- Fick's first law: the diffusive flux is proportional to the negative
    concentration gradient. J = -D ∇c. -/
noncomputable def fickFirstLaw (D : DiffusionCoeff) (c : ScalarField) (x : Pos) : Pos :=
  fun i => -D * gradient c x i

/-- Fick's first law: flux points from high to low concentration.
    If ∂c/∂xᵢ > 0 then Jᵢ < 0 (flux opposes gradient). -/
theorem fick_first_law_opposes_gradient (D : DiffusionCoeff) (hD : 0 < D)
    (c : ScalarField) (x : Pos) (i : Fin 3)
    (hgrad : 0 < gradient c x i) :
    fickFirstLaw D c x i < 0 := by
  simp only [fickFirstLaw]
  nlinarith [mul_pos hD hgrad]

/-! ## Fick's Second Law (Diffusion Equation) -/

/-- A time-dependent concentration field c(x, t). -/
abbrev ConcentrationEvolution := ℝ → ScalarField

/-- Fick's second law (the diffusion equation): ∂c/∂t = D ∇²c.
    Describes how concentration evolves over time due to diffusion. -/
noncomputable def DiffusionEquation (D : DiffusionCoeff) (c : ConcentrationEvolution) : Prop :=
  ∀ (x : Pos) (t : ℝ),
    deriv (fun s => c s x) t = D * laplacian (c t) x

/-- The diffusion equation with a source/sink term: ∂c/∂t = D ∇²c + S(x,t). -/
noncomputable def DiffusionEquationWithSource (D : DiffusionCoeff)
    (c : ConcentrationEvolution) (S : ℝ → ScalarField) : Prop :=
  ∀ (x : Pos) (t : ℝ),
    deriv (fun s => c s x) t = D * laplacian (c t) x + S t x

/-- Conservation of mass: Fick's second law follows from Fick's first law
    combined with the continuity equation ∂c/∂t + ∇·J = 0. -/
theorem fick_second_from_first_and_continuity (D : DiffusionCoeff)
    (c : ConcentrationEvolution)
    (hcont : ∀ (x : Pos) (t : ℝ),
      deriv (fun s => c s x) t + divergence (fickFirstLaw D (c t)) x = 0)
    (hlap : ∀ (x : Pos) (t : ℝ),
      divergence (fickFirstLaw D (c t)) x = -D * laplacian (c t) x) :
    DiffusionEquation D c := by
  intro x t
  have h1 := hcont x t
  have h2 := hlap x t
  linarith

/-! ## Brownian Motion and Einstein Relation -/

/-- Physical constants for Brownian motion. -/
structure BrownianParams where
  /-- Boltzmann constant k_B (J/K). -/
  kB : ℝ
  /-- Absolute temperature T (K). -/
  T : ℝ
  /-- Dynamic viscosity η (Pa·s). -/
  eta : ℝ
  /-- Particle radius r (m). -/
  r : ℝ
  /-- All parameters are positive. -/
  kB_pos : 0 < kB
  T_pos : 0 < T
  eta_pos : 0 < eta
  r_pos : 0 < r

/-- Einstein relation for Brownian motion: D = k_B T / (6πηr).
    Relates the diffusion coefficient to thermal energy and friction. -/
noncomputable def einsteinRelation (p : BrownianParams) : DiffusionCoeff :=
  p.kB * p.T / (6 * Real.pi * p.eta * p.r)

/-- The Einstein diffusion coefficient is positive. -/
theorem einsteinRelation_pos (p : BrownianParams) : 0 < einsteinRelation p := by
  unfold einsteinRelation
  apply div_pos
  · exact mul_pos p.kB_pos p.T_pos
  · apply mul_pos
    apply mul_pos
    apply mul_pos
    · linarith [Real.pi_pos]
    · exact Real.pi_pos
    · exact p.eta_pos
    · exact p.r_pos

/-- Mean squared displacement in Brownian motion: ⟨r²⟩ = 2dDt
    where d is the spatial dimension. -/
noncomputable def meanSquaredDisplacement (D : DiffusionCoeff) (d : ℕ) (t : ℝ) : ℝ :=
  2 * d * D * t

/-- MSD grows linearly with time for normal diffusion. -/
theorem msd_linear_in_time (D : DiffusionCoeff) (d : ℕ) (t₁ t₂ : ℝ)
    (_hD : 0 < D) (_hd : 0 < d) (_ht : 0 < t₂ - t₁) :
    meanSquaredDisplacement D d t₂ - meanSquaredDisplacement D d t₁ =
      2 * d * D * (t₂ - t₁) := by
  simp [meanSquaredDisplacement]
  ring

/-! ## Langevin Equation -/

/-- Parameters for the Langevin equation describing a Brownian particle. -/
structure LangevinParams where
  /-- Particle mass m (kg). -/
  mass : ℝ
  /-- Friction coefficient γ (kg/s). -/
  friction : ℝ
  /-- Mass is positive. -/
  mass_pos : 0 < mass
  /-- Friction is positive. -/
  friction_pos : 0 < friction

/-- The Langevin equation: m dv/dt = -γv + F(t) + ξ(t)
    where ξ(t) is a stochastic force and F(t) is an external force.
    Here we model the deterministic part: m dv/dt = -γv + F(t). -/
noncomputable def LangevinDeterministic (p : LangevinParams)
    (v : ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, p.mass * deriv v t = -p.friction * v t + F t

/-- The relaxation time τ = m/γ of the Langevin equation. -/
noncomputable def relaxationTime (p : LangevinParams) : ℝ :=
  p.mass / p.friction

/-- The relaxation time is positive. -/
theorem relaxationTime_pos (p : LangevinParams) : 0 < relaxationTime p :=
  div_pos p.mass_pos p.friction_pos

/-- The fluctuation-dissipation relation: the stochastic force intensity
    is related to friction and temperature.
    ⟨ξ(t)ξ(t')⟩ = 2γk_BT δ(t-t'). Here we state the coefficient. -/
noncomputable def stochasticForceIntensity (friction kB T : ℝ) : ℝ :=
  2 * friction * kB * T

/-- Einstein relation from Langevin: D = k_BT/γ = k_BT/(6πηr).
    In the overdamped limit, the Langevin equation yields the same
    diffusion coefficient as the Einstein relation. -/
noncomputable def langevinDiffusion (kB T friction : ℝ) : ℝ :=
  kB * T / friction

/-! ## Random Walk -/

/-- A 1D symmetric random walk: at each step, move ±δ with equal probability.
    After N steps, the expected displacement is 0 and variance is Nδ². -/
structure RandomWalk1D where
  /-- Step size δ. -/
  stepSize : ℝ
  /-- Number of steps. -/
  N : ℕ
  /-- Step size is positive. -/
  stepSize_pos : 0 < stepSize

/-- Variance of a 1D symmetric random walk: Var = Nδ². -/
noncomputable def RandomWalk1D.variance (rw : RandomWalk1D) : ℝ :=
  rw.N * rw.stepSize ^ 2

/-- The diffusion coefficient from a random walk: D = δ²/(2τ)
    where τ is the time per step. -/
noncomputable def randomWalkDiffusion (stepSize timeStep : ℝ) : ℝ :=
  stepSize ^ 2 / (2 * timeStep)

/-- In the continuum limit, the random walk converges to diffusion.
    After time t = Nτ, the MSD from the random walk equals 2Dt. -/
theorem randomWalk_to_diffusion (stepSize timeStep : ℝ) (hτ : 0 < timeStep) (N : ℕ) :
    (N : ℝ) * stepSize ^ 2 = 2 * randomWalkDiffusion stepSize timeStep * (N * timeStep) := by
  simp only [randomWalkDiffusion]
  field_simp

end Measure.Physics.Biophysics
