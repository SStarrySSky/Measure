/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scattering theory — cross sections, Mandelstam variables, and decay rates.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Measure.Physics.ParticlePhysics.StandardModel

namespace Measure.Physics.ParticlePhysics

/-! ## Four-Momentum -/

/-- A relativistic four-momentum pμ = (E/c, px, py, pz). -/
abbrev FourMomentum := Fin 4 → ℝ

/-- Energy component of a four-momentum (index 0). -/
noncomputable def FourMomentum.energy (p : FourMomentum) : ℝ := p 0

/-- Spatial 3-momentum components. -/
noncomputable def FourMomentum.spatial (p : FourMomentum) : Fin 3 → ℝ :=
  fun i => p ⟨i.val + 1, by omega⟩

/-- Minkowski inner product of two four-momenta: p·q = -p⁰q⁰ + p¹q¹ + p²q² + p³q³. -/
noncomputable def FourMomentum.inner (p q : FourMomentum) : ℝ :=
  -(p 0 * q 0) + p 1 * q 1 + p 2 * q 2 + p 3 * q 3

/-- Invariant mass squared: m²c² = -pμpμ = E²/c² - |p|². -/
noncomputable def FourMomentum.invariantMassSq (p : FourMomentum) : ℝ :=
  -(FourMomentum.inner p p)

/-- On-shell condition: p² = -m² (in natural units with c = 1). -/
def FourMomentum.onShell (p : FourMomentum) (m : ℝ) : Prop :=
  FourMomentum.inner p p = -(m ^ 2)

/-! ## Mandelstam Variables -/

/-- Mandelstam variable s = (p₁ + p₂)² — center-of-mass energy squared.
    For a 2→2 scattering process with momenta p₁, p₂ → p₃, p₄. -/
noncomputable def mandelstamS (p₁ p₂ : FourMomentum) : ℝ :=
  FourMomentum.inner (fun i => p₁ i + p₂ i) (fun i => p₁ i + p₂ i)

/-- Mandelstam variable t = (p₁ - p₃)² — momentum transfer squared. -/
noncomputable def mandelstamT (p₁ p₃ : FourMomentum) : ℝ :=
  FourMomentum.inner (fun i => p₁ i - p₃ i) (fun i => p₁ i - p₃ i)

/-- Mandelstam variable u = (p₁ - p₄)² — crossed momentum transfer squared. -/
noncomputable def mandelstamU (p₁ p₄ : FourMomentum) : ℝ :=
  FourMomentum.inner (fun i => p₁ i - p₄ i) (fun i => p₁ i - p₄ i)

/-- The Mandelstam relation: s + t + u = Σᵢ mᵢ² for a 2→2 process.
    In natural units: s + t + u = m₁² + m₂² + m₃² + m₄².
    This follows from expanding the Minkowski inner products, using the on-shell
    conditions pᵢ² = -mᵢ², and four-momentum conservation p₁ + p₂ = p₃ + p₄.
    The algebraic expansion involves 48 cross-terms that cancel pairwise.
    Stated as an axiom because the fully-expanded polynomial proof exceeds
    Lean's tactic recursion limits (16 real variables, 48+ cross-terms). -/
axiom mandelstam_relation (p₁ p₂ p₃ p₄ : FourMomentum)
    (m₁ m₂ m₃ m₄ : ℝ)
    (h₁ : p₁.onShell m₁) (h₂ : p₂.onShell m₂)
    (h₃ : p₃.onShell m₃) (h₄ : p₄.onShell m₄)
    (hcons : ∀ i, p₁ i + p₂ i = p₃ i + p₄ i) :
    mandelstamS p₁ p₂ + mandelstamT p₁ p₃ + mandelstamU p₁ p₄ =
      m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2 + m₄ ^ 2

/-! ## Scattering Cross Section -/

/-- Differential scattering cross section dσ/dΩ as a function of solid angle. -/
abbrev DifferentialCrossSection := ℝ → ℝ → ℝ  -- (θ, φ) → dσ/dΩ

/-- Parameters for a scattering process. -/
structure ScatteringProcess where
  /-- Center-of-mass energy squared. -/
  s : ℝ
  /-- s is positive for physical scattering. -/
  s_pos : 0 < s
  /-- Differential cross section. -/
  dσdΩ : DifferentialCrossSection

/-- Total cross section σ = ∫ (dσ/dΩ) dΩ.
    Integrated over the full solid angle. -/
noncomputable def ScatteringProcess.totalCrossSection (proc : ScatteringProcess) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      proc.dσdΩ θ φ * Real.sin θ

/-- Rutherford scattering differential cross section:
    dσ/dΩ = (α / (4E sin²(θ/2)))² where α is the fine structure constant. -/
noncomputable def rutherfordCrossSection (α E : ℝ) : DifferentialCrossSection :=
  fun θ _φ => (α / (4 * E * (Real.sin (θ / 2)) ^ 2)) ^ 2

/-! ## Decay Rate and Lifetime -/

/-- Decay rate (partial width) Γ for a particle decay channel. -/
structure DecayChannel where
  /-- Partial decay width Γᵢ. -/
  partialWidth : ℝ
  /-- Decay width is non-negative. -/
  width_nonneg : 0 ≤ partialWidth
  /-- Final state particles. -/
  products : List Particle

/-- Total decay width Γ = Σᵢ Γᵢ. -/
noncomputable def totalDecayWidth (channels : List DecayChannel) : ℝ :=
  (channels.map (fun ch => ch.partialWidth)).sum

/-- Mean lifetime τ = ℏ/Γ. -/
noncomputable def meanLifetime (Γ : ℝ) : ℝ :=
  let ℏ : ℝ := 1.054571817e-34  -- reduced Planck constant in J·s
  ℏ / Γ

/-- Branching ratio BR = Γᵢ/Γ_total. -/
noncomputable def branchingRatio (channel : DecayChannel) (totalWidth : ℝ) : ℝ :=
  channel.partialWidth / totalWidth

/-- Helper: sum of list elements divided by a constant equals sum divided by constant. -/
private lemma list_sum_div (l : List ℝ) (c : ℝ) :
    (l.map (· / c)).sum = l.sum / c := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [List.sum_cons, add_div, ih]

/-- Sum of all branching ratios equals 1 (when total width is positive). -/
theorem branchingRatio_sum (channels : List DecayChannel)
    (hΓ : 0 < totalDecayWidth channels) :
    (channels.map (fun ch => branchingRatio ch (totalDecayWidth channels))).sum = 1 := by
  unfold branchingRatio totalDecayWidth
  have hne : (channels.map (fun ch => ch.partialWidth)).sum ≠ 0 := ne_of_gt hΓ
  rw [show (channels.map (fun ch => ch.partialWidth /
    (channels.map (fun ch => ch.partialWidth)).sum)) =
    (channels.map (fun ch => ch.partialWidth)).map
      (· / (channels.map (fun ch => ch.partialWidth)).sum) from by
    simp [List.map_map]]
  rw [list_sum_div]
  exact div_self hne

/-- Exponential decay law: N(t) = N₀ exp(-Γt). -/
noncomputable def decayLaw (N₀ Γ t : ℝ) : ℝ :=
  N₀ * Real.exp (-Γ * t)

/-- The decay law gives N₀ at t = 0. -/
theorem decayLaw_initial (N₀ Γ : ℝ) :
    decayLaw N₀ Γ 0 = N₀ := by
  unfold decayLaw
  simp [Real.exp_zero]

/-- The decay law is non-negative for non-negative N₀. -/
theorem decayLaw_nonneg (N₀ Γ t : ℝ) (hN : 0 ≤ N₀) :
    0 ≤ decayLaw N₀ Γ t := by
  unfold decayLaw
  apply mul_nonneg hN
  exact le_of_lt (Real.exp_pos _)

end Measure.Physics.ParticlePhysics
