/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Maxwell's equations in differential form.
These four equations describe all classical electromagnetic phenomena.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Measure.Physics.Electromagnetism

/-- 3D position vector type. -/
abbrev Pos := Fin 3 → ℝ

/-- Electric field E(x, t) : ℝ³ × ℝ → ℝ³. -/
abbrev ElectricField := Pos → ℝ → Pos

/-- Magnetic field B(x, t) : ℝ³ × ℝ → ℝ³. -/
abbrev MagneticField := Pos → ℝ → Pos

/-- Charge density ρ(x, t) : ℝ³ × ℝ → ℝ. -/
abbrev ChargeDensity := Pos → ℝ → ℝ

/-- Current density J(x, t) : ℝ³ × ℝ → ℝ³. -/
abbrev CurrentDensity := Pos → ℝ → Pos

/-- Divergence of a vector field: ∇·F = ∂F₁/∂x₁ + ∂F₂/∂x₂ + ∂F₃/∂x₃. -/
noncomputable def divergence (F : Pos → Pos) (x : Pos) : ℝ :=
  ∑ i : Fin 3, deriv (fun s => F (Function.update x i s) i) (x i)

/-- Curl of a vector field: (∇×F)ᵢ = εᵢⱼₖ ∂Fₖ/∂xⱼ. -/
noncomputable def curl (F : Pos → Pos) (x : Pos) : Pos :=
  fun i =>
    match i with
    | ⟨0, _⟩ => deriv (fun s => F (Function.update x ⟨1, by omega⟩ s) ⟨2, by omega⟩) (x ⟨1, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨2, by omega⟩ s) ⟨1, by omega⟩) (x ⟨2, by omega⟩)
    | ⟨1, _⟩ => deriv (fun s => F (Function.update x ⟨2, by omega⟩ s) ⟨0, by omega⟩) (x ⟨2, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨0, by omega⟩ s) ⟨2, by omega⟩) (x ⟨0, by omega⟩)
    | ⟨2, _⟩ => deriv (fun s => F (Function.update x ⟨0, by omega⟩ s) ⟨1, by omega⟩) (x ⟨0, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨1, by omega⟩ s) ⟨0, by omega⟩) (x ⟨1, by omega⟩)
    | ⟨n+3, h⟩ => absurd h (by omega)

/-- An electromagnetic field configuration. -/
structure EMField where
  /-- Electric field. -/
  E : ElectricField
  /-- Magnetic field. -/
  B : MagneticField

/-- Source terms for Maxwell's equations. -/
structure EMSource where
  /-- Charge density. -/
  ρ : ChargeDensity
  /-- Current density. -/
  J : CurrentDensity

/-- Vacuum permittivity ε₀ ≈ 8.854 187 8128 × 10⁻¹² F/m.
    CODATA 2022 value. No longer exact after 2019 SI redefinition.
    For the dimension-typed version with uncertainty, see `Measure.Constants.ε₀`. -/
noncomputable def ε₀ : ℝ := 8.8541878128e-12

/-- Vacuum permeability μ₀ ≈ 1.256 637 062 12 × 10⁻⁶ N/A².
    CODATA 2022 value. No longer exact after 2019 SI redefinition.
    For the dimension-typed version with uncertainty, see `Measure.Constants.μ₀`. -/
noncomputable def μ₀ : ℝ := 1.25663706212e-6

/-- Gauss's law: ∇·E = ρ/ε₀. -/
def GaussLaw (em : EMField) (src : EMSource) : Prop :=
  ∀ (x : Pos) (t : ℝ), divergence (fun y => em.E y t) x = src.ρ x t / ε₀

/-- Gauss's law for magnetism: ∇·B = 0 (no magnetic monopoles). -/
def GaussMagnetism (em : EMField) : Prop :=
  ∀ (x : Pos) (t : ℝ), divergence (fun y => em.B y t) x = 0

/-- Faraday's law: ∇×E = -∂B/∂t. -/
noncomputable def FaradayLaw (em : EMField) : Prop :=
  ∀ (x : Pos) (t : ℝ) (i : Fin 3),
    curl (fun y => em.E y t) x i = -(deriv (fun s => em.B x s i) t)

/-- Ampère-Maxwell law: ∇×B = μ₀J + μ₀ε₀ ∂E/∂t. -/
noncomputable def AmpereLaw (em : EMField) (src : EMSource) : Prop :=
  ∀ (x : Pos) (t : ℝ) (i : Fin 3),
    curl (fun y => em.B y t) x i =
      μ₀ * src.J x t i + μ₀ * ε₀ * deriv (fun s => em.E x s i) t

/-- A field satisfies all four Maxwell equations. -/
structure SatisfiesMaxwell (em : EMField) (src : EMSource) : Prop where
  gauss : GaussLaw em src
  gaussMag : GaussMagnetism em
  faraday : FaradayLaw em
  ampere : AmpereLaw em src

/-- In vacuum (no sources), Maxwell's equations simplify. -/
def vacuumSource : EMSource where
  ρ := fun _ _ => 0
  J := fun _ _ => fun _ => 0

end Measure.Physics.Electromagnetism
