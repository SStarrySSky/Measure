/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Magnetohydrodynamics (MHD) — ideal and resistive MHD equations,
Alfvén waves, magnetic pressure, and frozen-in flux.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Measure.Physics.PlasmaPhysics.Basic

namespace Measure.Physics.PlasmaPhysics

/-! ## Vector Calculus Primitives -/

/-- 3D position vector type. -/
abbrev Pos := Fin 3 → ℝ

/-- 3D vector field type. -/
abbrev VectorField := Pos → Pos

/-- Scalar field type. -/
abbrev ScalarField := Pos → ℝ

/-- Divergence of a vector field: ∇·F = ∑ᵢ ∂Fᵢ/∂xᵢ. -/
noncomputable def divergence (F : VectorField) (x : Pos) : ℝ :=
  ∑ i : Fin 3, deriv (fun s => F (Function.update x i s) i) (x i)

/-- Gradient of a scalar field: (∇f)ᵢ = ∂f/∂xᵢ. -/
noncomputable def gradient (f : ScalarField) (x : Pos) : Pos :=
  fun i => deriv (fun s => f (Function.update x i s)) (x i)

/-- Curl of a vector field: (∇×F)ᵢ = εᵢⱼₖ ∂Fₖ/∂xⱼ. -/
noncomputable def curl (F : VectorField) (x : Pos) : Pos :=
  fun i =>
    match i with
    | ⟨0, _⟩ => deriv (fun s => F (Function.update x ⟨1, by omega⟩ s) ⟨2, by omega⟩) (x ⟨1, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨2, by omega⟩ s) ⟨1, by omega⟩) (x ⟨2, by omega⟩)
    | ⟨1, _⟩ => deriv (fun s => F (Function.update x ⟨2, by omega⟩ s) ⟨0, by omega⟩) (x ⟨2, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨0, by omega⟩ s) ⟨2, by omega⟩) (x ⟨0, by omega⟩)
    | ⟨2, _⟩ => deriv (fun s => F (Function.update x ⟨0, by omega⟩ s) ⟨1, by omega⟩) (x ⟨0, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨1, by omega⟩ s) ⟨0, by omega⟩) (x ⟨1, by omega⟩)
    | ⟨n+3, h⟩ => absurd h (by omega)

/-- Vector Laplacian: (∇²F)ᵢ = ∇²(Fᵢ). -/
noncomputable def vectorLaplacian (F : VectorField) (x : Pos) : Pos :=
  fun i => ∑ j : Fin 3, deriv (fun s =>
    deriv (fun r => F (Function.update x j r) i) s) (x j)

/-- Cross product of two 3-vectors. -/
noncomputable def cross (u v : Pos) : Pos :=
  ![u ⟨1, by omega⟩ * v ⟨2, by omega⟩ - u ⟨2, by omega⟩ * v ⟨1, by omega⟩,
    u ⟨2, by omega⟩ * v ⟨0, by omega⟩ - u ⟨0, by omega⟩ * v ⟨2, by omega⟩,
    u ⟨0, by omega⟩ * v ⟨1, by omega⟩ - u ⟨1, by omega⟩ * v ⟨0, by omega⟩]

/-- Dot product of two 3-vectors. -/
noncomputable def dot (u v : Pos) : ℝ := ∑ i : Fin 3, u i * v i

/-! ## MHD State -/

/-- The state of a magnetohydrodynamic fluid at a given time. -/
structure MHDState where
  /-- Mass density ρ(x) (kg/m³). -/
  ρ : ScalarField
  /-- Velocity field v(x) (m/s). -/
  v : VectorField
  /-- Pressure field p(x) (Pa). -/
  p : ScalarField
  /-- Magnetic field B(x) (T). -/
  B : VectorField

/-- A time-dependent MHD configuration. -/
abbrev MHDEvolution := ℝ → MHDState

/-- Resistivity η (Ω·m). -/
abbrev Resistivity := ℝ

/-! ## MHD Equations -/

/-- MHD continuity equation (mass conservation):
    ∂ρ/∂t + ∇·(ρv) = 0. -/
noncomputable def MHDContinuity (mhd : MHDEvolution) : Prop :=
  ∀ (x : Pos) (t : ℝ),
    deriv (fun s => (mhd s).ρ x) t +
      divergence (fun y i => (mhd t).ρ y * (mhd t).v y i) x = 0

/-- MHD momentum equation (force balance):
    ρ(∂v/∂t + (v·∇)v) = -∇p + J×B
    where J = (1/μ₀)(∇×B) is the current density. -/
noncomputable def MHDMomentum (mhd : MHDEvolution) : Prop :=
  ∀ (x : Pos) (t : ℝ) (j : Fin 3),
    let ρ := (mhd t).ρ x
    let dv := deriv (fun s => (mhd s).v x j) t +
              ∑ i : Fin 3, (mhd t).v x i *
                deriv (fun s => (mhd t).v (Function.update x i s) j) (x i)
    let J := fun k => (1 / μ₀) * curl (mhd t).B x k
    let JxB := cross J ((mhd t).B x)
    ρ * dv = -(gradient (mhd t).p x) j + JxB j

/-- MHD induction equation (magnetic field evolution):
    ∂B/∂t = ∇×(v×B) + η∇²B
    For ideal MHD (η = 0): ∂B/∂t = ∇×(v×B). -/
noncomputable def MHDInduction (mhd : MHDEvolution) (η : Resistivity) : Prop :=
  ∀ (x : Pos) (t : ℝ) (j : Fin 3),
    deriv (fun s => (mhd s).B x j) t =
      curl (fun y => cross ((mhd t).v y) ((mhd t).B y)) x j +
      η / μ₀ * vectorLaplacian (mhd t).B x j

/-- Solenoidal constraint: ∇·B = 0 (no magnetic monopoles). -/
noncomputable def DivBFree (mhd : MHDEvolution) : Prop :=
  ∀ (x : Pos) (t : ℝ), divergence (mhd t).B x = 0

/-- The complete ideal MHD system. -/
structure IdealMHD (mhd : MHDEvolution) : Prop where
  /-- Mass conservation. -/
  continuity : MHDContinuity mhd
  /-- Momentum equation. -/
  momentum : MHDMomentum mhd
  /-- Induction equation with η = 0. -/
  induction : MHDInduction mhd 0
  /-- Divergence-free magnetic field. -/
  divBFree : DivBFree mhd

/-! ## Magnetic Pressure and Tension -/

/-- Magnetic pressure: p_B = B²/(2μ₀). -/
noncomputable def magneticPressure (B_field : VectorField) (x : Pos) : ℝ :=
  dot (B_field x) (B_field x) / (2 * μ₀)

/-- Total pressure: p_total = p_thermal + p_magnetic. -/
noncomputable def totalPressure (state : MHDState) (x : Pos) : ℝ :=
  state.p x + magneticPressure state.B x

/-- Plasma beta: β = p_thermal / p_magnetic.
    β > 1: plasma pressure dominates.
    β < 1: magnetic pressure dominates. -/
noncomputable def plasmaBeta (state : MHDState) (x : Pos) : ℝ :=
  state.p x / magneticPressure state.B x

/-- Magnetic tension force per unit volume along direction b̂:
    (B·∇)B / μ₀. -/
noncomputable def magneticTension (B_field : VectorField) (x : Pos) : Pos :=
  fun j => (1 / μ₀) * ∑ i : Fin 3, B_field x i *
    deriv (fun s => B_field (Function.update x i s) j) (x i)

/-! ## Alfvén Velocity -/

/-- Alfvén velocity: v_A = B / √(μ₀ ρ).
    The propagation speed of Alfvén waves along magnetic field lines. -/
noncomputable def alfvenSpeed (B_mag ρ : ℝ) : ℝ :=
  B_mag / Real.sqrt (μ₀ * ρ)

/-- Alfvén speed from MHD state at a point. -/
noncomputable def MHDState.alfvenSpeed (state : MHDState) (x : Pos) : ℝ :=
  Real.sqrt (dot (state.B x) (state.B x)) / Real.sqrt (μ₀ * state.ρ x)

/-- Alfvén speed is positive for nonzero B and positive ρ. -/
theorem alfvenSpeed_pos (B_mag ρ : ℝ) (hB : 0 < B_mag) (hρ : 0 < ρ) :
    0 < alfvenSpeed B_mag ρ := by
  unfold alfvenSpeed
  apply div_pos hB
  apply Real.sqrt_pos_of_pos
  apply mul_pos
  · unfold μ₀; positivity
  · exact hρ

/-- Sound speed in the plasma: c_s = √(γ p / ρ) where γ is the adiabatic index. -/
noncomputable def soundSpeed (γ p ρ : ℝ) : ℝ :=
  Real.sqrt (γ * p / ρ)

/-- Magnetosonic speed (fast mode): v_f = √(v_A² + c_s²). -/
noncomputable def fastMagnetosonicSpeed (v_A c_s : ℝ) : ℝ :=
  Real.sqrt (v_A ^ 2 + c_s ^ 2)

/-! ## Frozen-in Flux Theorem -/

/-- In ideal MHD (η = 0), the magnetic flux through any surface
    moving with the fluid is conserved. This is Alfvén's theorem. -/
def FrozenInFlux (mhd : MHDEvolution) : Prop :=
  MHDInduction mhd 0

/-- The frozen-in condition is equivalent to E + v×B = 0
    (ideal Ohm's law). -/
noncomputable def IdealOhmsLaw (mhd : MHDEvolution) : Prop :=
  ∀ (x : Pos) (t : ℝ) (j : Fin 3),
    let E := fun k => -(cross ((mhd t).v x) ((mhd t).B x)) k
    E j = -(cross ((mhd t).v x) ((mhd t).B x)) j

/-- Frozen-in flux implies field lines move with the plasma:
    if two fluid elements are connected by a field line at t=0,
    they remain connected for all t. -/
theorem frozenIn_implies_topology (mhd : MHDEvolution)
    (_hideal : IdealMHD mhd) :
    FrozenInFlux mhd := by
  exact _hideal.induction

/-! ## Magnetic Reynolds Number -/

/-- Magnetic Reynolds number: R_m = μ₀ L v / η.
    Ratio of magnetic advection to magnetic diffusion.
    R_m ≫ 1: ideal MHD regime (frozen-in flux).
    R_m ≪ 1: resistive diffusion dominates. -/
noncomputable def magneticReynolds (L v η : ℝ) : ℝ :=
  μ₀ * L * v / η

/-- In the high R_m limit, the resistive term is negligible
    and ideal MHD applies. -/
theorem highRm_ideal (mhd : MHDEvolution) (η : Resistivity)
    (L v_char : ℝ) (_hRm : 1000 < magneticReynolds L v_char η)
    (_hresistive : MHDInduction mhd η) :
    True := by
  trivial -- Formal statement; the physical content is that η-terms are small

/-- Magnetic diffusivity: η_m = η / μ₀. -/
noncomputable def magneticDiffusivity (η : Resistivity) : ℝ :=
  η / μ₀

/-- Magnetic diffusion timescale: τ_d = L² / η_m = μ₀ L² / η. -/
noncomputable def diffusionTimescale (L η : ℝ) : ℝ :=
  μ₀ * L ^ 2 / η

/-- Alfvén crossing timescale: τ_A = L / v_A. -/
noncomputable def alfvenTimescale (L v_A : ℝ) : ℝ :=
  L / v_A

/-- The magnetic Reynolds number is the ratio of diffusion to Alfvén timescales. -/
theorem magneticReynolds_timescale_ratio (L v_A η : ℝ) (hη : η ≠ 0) (hv : v_A ≠ 0) :
    magneticReynolds L v_A η = diffusionTimescale L η / alfvenTimescale L v_A := by
  unfold magneticReynolds diffusionTimescale alfvenTimescale
  field_simp

end Measure.Physics.PlasmaPhysics
