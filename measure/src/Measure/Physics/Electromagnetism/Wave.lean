/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Electromagnetic waves, energy density, Poynting vector, and Lorentz force.
Derived from Maxwell's equations in vacuum.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Measure.Physics.Electromagnetism.Maxwell

namespace Measure.Physics.Electromagnetism

/-! ## Speed of light -/

/-- Speed of light in vacuum: c = 1/√(μ₀ε₀). -/
noncomputable def speedOfLight : ℝ := 1 / Real.sqrt (μ₀ * ε₀)

/-- c² = 1/(μ₀ε₀). -/
noncomputable def speedOfLightSq : ℝ := 1 / (μ₀ * ε₀)

/-! ## Electromagnetic wave equation -/

/-- Laplacian of a scalar field: ∇²f = ∂²f/∂x₁² + ∂²f/∂x₂² + ∂²f/∂x₃². -/
noncomputable def laplacian (f : Pos → ℝ) (x : Pos) : ℝ :=
  ∑ i : Fin 3, deriv (fun s => deriv (fun r => f (Function.update (Function.update x i r) i s)) s) (x i)

/-- The wave equation for a scalar component:
    ∇²f = (1/c²) ∂²f/∂t². -/
noncomputable def SatisfiesWaveEquation (f : Pos → ℝ → ℝ) : Prop :=
  ∀ (x : Pos) (t : ℝ),
    laplacian (fun y => f y t) x =
      (1 / speedOfLightSq) * deriv (fun s => deriv (fun r => f x r) s) t

/-- Each component of E satisfies the wave equation in vacuum. -/
noncomputable def ESatisfiesWaveEq (em : EMField) : Prop :=
  ∀ (i : Fin 3), SatisfiesWaveEquation (fun x t => em.E x t i)

/-- Each component of B satisfies the wave equation in vacuum. -/
noncomputable def BSatisfiesWaveEq (em : EMField) : Prop :=
  ∀ (i : Fin 3), SatisfiesWaveEquation (fun x t => em.B x t i)

/-- In vacuum, Maxwell's equations imply the wave equation for E and B.
    Proof requires the vector calculus identity ∇×(∇×F) = ∇(∇·F) - ∇²F,
    combined with ∇·E = 0 and ∇·B = 0 in vacuum.
    This identity is not yet available in Mathlib for function-based vector fields. -/
axiom maxwell_implies_wave_eq (em : EMField)
    (_hmax : SatisfiesMaxwell em vacuumSource) :
    ESatisfiesWaveEq em ∧ BSatisfiesWaveEq em

/-! ## Electromagnetic energy density -/

/-- Dot product of two 3-vectors. -/
noncomputable def dot (u v : Pos) : ℝ := ∑ i : Fin 3, u i * v i

/-- Electromagnetic energy density: u = ½(ε₀E² + B²/μ₀). -/
noncomputable def energyDensity (em : EMField) (x : Pos) (t : ℝ) : ℝ :=
  (1 / 2) * (ε₀ * dot (em.E x t) (em.E x t) + dot (em.B x t) (em.B x t) / μ₀)

/-- Energy density is non-negative (assuming ε₀ > 0 and μ₀ > 0). -/
theorem energyDensity_nonneg (em : EMField) (x : Pos) (t : ℝ) :
    energyDensity em x t ≥ 0 := by
  unfold energyDensity dot
  have hε₀ : ε₀ > 0 := by unfold ε₀; norm_num
  have hμ₀ : μ₀ > 0 := by unfold μ₀; norm_num
  have hE : ∑ i : Fin 3, em.E x t i * em.E x t i ≥ 0 :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (em.E x t i))
  have hB : ∑ i : Fin 3, em.B x t i * em.B x t i ≥ 0 :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (em.B x t i))
  have h1 : ε₀ * (∑ i : Fin 3, em.E x t i * em.E x t i) ≥ 0 :=
    mul_nonneg hε₀.le hE
  have h2 : (∑ i : Fin 3, em.B x t i * em.B x t i) / μ₀ ≥ 0 :=
    div_nonneg hB hμ₀.le
  linarith

/-! ## Cross product and Poynting vector -/

/-- Cross product of two 3-vectors: u × v. -/
noncomputable def cross (u v : Pos) : Pos := fun i =>
  match i with
  | ⟨0, _⟩ => u ⟨1, by omega⟩ * v ⟨2, by omega⟩ - u ⟨2, by omega⟩ * v ⟨1, by omega⟩
  | ⟨1, _⟩ => u ⟨2, by omega⟩ * v ⟨0, by omega⟩ - u ⟨0, by omega⟩ * v ⟨2, by omega⟩
  | ⟨2, _⟩ => u ⟨0, by omega⟩ * v ⟨1, by omega⟩ - u ⟨1, by omega⟩ * v ⟨0, by omega⟩
  | ⟨n+3, h⟩ => absurd h (by omega)

/-- Poynting vector: S = E × B / μ₀.
    Represents the directional energy flux (power per unit area). -/
noncomputable def poyntingVector (em : EMField) (x : Pos) (t : ℝ) : Pos :=
  fun i => cross (em.E x t) (em.B x t) i / μ₀

/-! ## Lorentz force -/

/-- Velocity vector type. -/
abbrev Velocity := Pos

/-- Lorentz force on a charged particle: F = q(E + v × B). -/
noncomputable def lorentzForce (q : ℝ) (em : EMField) (x : Pos) (v : Velocity) (t : ℝ) : Pos :=
  fun i => q * (em.E x t i + cross v (em.B x t) i)

/-- Lorentz force on a neutral particle is zero. -/
theorem lorentzForce_neutral (em : EMField) (x : Pos) (v : Velocity) (t : ℝ) :
    lorentzForce 0 em x v t = fun _ => 0 := by
  funext i
  simp [lorentzForce]

/-- Poynting's theorem (energy conservation):
    ∂u/∂t + ∇·S = -J·E. -/
noncomputable def PoyntingTheorem (em : EMField) (src : EMSource) : Prop :=
  ∀ (x : Pos) (t : ℝ),
    deriv (fun s => energyDensity em x s) t +
      divergence (fun y => poyntingVector em y t) x =
        -(dot (src.J x t) (em.E x t))

/-- Poynting's theorem follows from Maxwell's equations.
    Proof requires the vector identity ∇·(E×B) = B·(∇×E) - E·(∇×B),
    then substituting Faraday's and Ampere's laws from Maxwell's equations.
    Depends on vector calculus identities not yet formalized in Mathlib. -/
axiom maxwell_implies_poynting (em : EMField) (src : EMSource)
    (_hmax : SatisfiesMaxwell em src) :
    PoyntingTheorem em src

end Measure.Physics.Electromagnetism
