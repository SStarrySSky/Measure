/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Superconductivity — BCS theory, Cooper pairs, critical temperature,
Meissner effect, London equations, and Ginzburg-Landau theory.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Measure.Physics.MaterialScience

/-! ## Superconducting State -/

/-- 3D vector type for superconductivity calculations. -/
abbrev Vec3SC := Fin 3 → ℝ

/-- Scalar field over 3D space. -/
abbrev ScalarFieldSC := Vec3SC → ℝ

/-- Vector field over 3D space. -/
abbrev VectorFieldSC := Vec3SC → Vec3SC

/-- A superconducting material characterized by its critical parameters. -/
structure Superconductor where
  /-- Critical temperature T_c (K). -/
  T_c : ℝ
  /-- Critical temperature is positive. -/
  hTc : 0 < T_c
  /-- London penetration depth (m) at T = 0. -/
  lamL0 : ℝ
  /-- Penetration depth is positive. -/
  hLam : 0 < lamL0

/-- Classification of superconductors. -/
inductive SuperconductorType where
  /-- Type I: single critical field, complete Meissner effect. -/
  | typeI
  /-- Type II: two critical fields, allows vortex state. -/
  | typeII

/-! ## BCS Theory — Cooper Pairs -/

/-- A Cooper pair: two electrons with opposite momentum and spin
    bound by phonon-mediated attraction. -/
structure CooperPair where
  /-- Momentum of electron 1: k↑. -/
  k : Vec3SC
  /-- BCS energy gap Δ at temperature T. -/
  Δ : ℝ
  /-- The gap is non-negative. -/
  hΔ : 0 ≤ Δ

/-- The BCS ground state energy gap at T = 0:
    Δ(0) ≈ 2 ℏω_D exp(-1/(N(0)V)). -/
noncomputable def bcsGapZeroTemp (ℏω_D : ℝ) (N₀V : ℝ) : ℝ :=
  2 * ℏω_D * Real.exp (-1 / N₀V)

/-- The BCS gap equation (simplified, near T_c):
    Δ(T) ≈ Δ(0) √(1 - T/T_c) for T near T_c. -/
noncomputable def bcsGapNearTc (Δ₀ : ℝ) (T T_c : ℝ) : ℝ :=
  Δ₀ * Real.sqrt (1 - T / T_c)

/-- The gap vanishes at T_c (requires T_c ≠ 0, since T_c is a physical critical temperature). -/
theorem bcsGap_at_Tc (Δ₀ T_c : ℝ) (hTc : T_c ≠ 0) :
    bcsGapNearTc Δ₀ T_c T_c = 0 := by
  unfold bcsGapNearTc
  simp [div_self hTc]

/-- BCS universal ratio: 2Δ(0) / (k_B T_c) ≈ 3.528 (weak coupling). -/
noncomputable def bcsRatio : ℝ := 3.528

/-- The BCS relation between gap and critical temperature:
    Δ(0) = (π/γ) k_B T_c ≈ 1.764 k_B T_c
    where γ ≈ 1.781 is the exponential of the Euler-Mascheroni constant. -/
noncomputable def bcsGapFromTc (kB T_c : ℝ) : ℝ :=
  (bcsRatio / 2) * kB * T_c

/-! ## Critical Temperature -/

/-- The BCS critical temperature:
    T_c = (ℏω_D / 1.14 k_B) exp(-1/(N(0)V)). -/
noncomputable def bcsCriticalTemp (ℏω_D kB : ℝ) (N₀V : ℝ) : ℝ :=
  (ℏω_D / (1.14 * kB)) * Real.exp (-1 / N₀V)

/-- McMillan formula for T_c (strong coupling correction):
    T_c = (Θ_D/1.45) exp(-1.04(1+λ)/(λ-μ*(1+0.62λ))).
    lam is the electron-phonon coupling, μ* is the Coulomb pseudopotential. -/
noncomputable def mcMillanTc (Θ_D : ℝ) (lam μ_star : ℝ) : ℝ :=
  (Θ_D / 1.45) * Real.exp (-1.04 * (1 + lam) / (lam - μ_star * (1 + 0.62 * lam)))

/-! ## Meissner Effect -/

/-- The Meissner effect: a superconductor expels magnetic flux from its interior.
    B_internal = 0 in the bulk of a superconductor. -/
def MeissnerEffect (B : VectorFieldSC) (interior : Set Vec3SC) : Prop :=
  ∀ x ∈ interior, ∀ i : Fin 3, B x i = 0

/-- The critical magnetic field H_c(T) below which the Meissner effect holds:
    H_c(T) = H_c(0)(1 - (T/T_c)²). -/
noncomputable def criticalField (H_c0 : ℝ) (T T_c : ℝ) : ℝ :=
  H_c0 * (1 - (T / T_c) ^ 2)

/-- The critical field vanishes at T_c. -/
theorem criticalField_at_Tc (H_c0 T_c : ℝ) (_hTc : T_c ≠ 0) :
    criticalField H_c0 T_c T_c = 0 := by
  unfold criticalField
  rw [div_self _hTc]
  ring

/-- The critical field at T = 0 equals H_c(0). -/
theorem criticalField_at_zero (H_c0 T_c : ℝ) :
    criticalField H_c0 0 T_c = H_c0 := by
  simp [criticalField]

/-- For Type II superconductors: lower and upper critical fields. -/
structure TypeIICriticalFields where
  /-- Lower critical field H_c1. -/
  H_c1 : ℝ
  /-- Upper critical field H_c2. -/
  H_c2 : ℝ
  /-- H_c1 < H_c2. -/
  h_order : H_c1 < H_c2

/-! ## London Equations -/

/-- Gradient of a scalar field. -/
noncomputable def gradientSC (f : ScalarFieldSC) (x : Vec3SC) : Vec3SC :=
  fun i => deriv (fun s => f (Function.update x i s)) (x i)

/-- Curl of a vector field. -/
noncomputable def curlSC (F : VectorFieldSC) (x : Vec3SC) : Vec3SC :=
  fun i =>
    match i with
    | ⟨0, _⟩ => deriv (fun s => F (Function.update x ⟨1, by omega⟩ s) ⟨2, by omega⟩) (x ⟨1, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨2, by omega⟩ s) ⟨1, by omega⟩) (x ⟨2, by omega⟩)
    | ⟨1, _⟩ => deriv (fun s => F (Function.update x ⟨2, by omega⟩ s) ⟨0, by omega⟩) (x ⟨2, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨0, by omega⟩ s) ⟨2, by omega⟩) (x ⟨0, by omega⟩)
    | ⟨2, _⟩ => deriv (fun s => F (Function.update x ⟨0, by omega⟩ s) ⟨1, by omega⟩) (x ⟨0, by omega⟩) -
                 deriv (fun s => F (Function.update x ⟨1, by omega⟩ s) ⟨0, by omega⟩) (x ⟨1, by omega⟩)
    | ⟨n+3, h⟩ => absurd h (by omega)

/-- The first London equation:
    ∂J_s/∂t = (n_s e² / m) E.
    Relates the supercurrent acceleration to the electric field. -/
noncomputable def FirstLondonEquation (J_s : ℝ → VectorFieldSC)
    (E : VectorFieldSC) (n_s e m : ℝ) : Prop :=
  ∀ (x : Vec3SC) (t : ℝ) (i : Fin 3),
    deriv (fun s => J_s s x i) t = (n_s * e ^ 2 / m) * E x i

/-- The second London equation:
    ∇ × J_s = -(n_s e² / m) B.
    Implies the Meissner effect — magnetic field is expelled. -/
noncomputable def SecondLondonEquation (J_s : VectorFieldSC)
    (B : VectorFieldSC) (n_s e m : ℝ) : Prop :=
  ∀ (x : Vec3SC) (i : Fin 3),
    curlSC J_s x i = -(n_s * e ^ 2 / m) * B x i

/-- The London penetration depth: lamL = √(m / (μ₀ n_s e²)). -/
noncomputable def londonPenetrationDepth (m μ₀ n_s e : ℝ) : ℝ :=
  Real.sqrt (m / (μ₀ * n_s * e ^ 2))

/-- Temperature dependence of penetration depth:
    lamL(T) = lamL(0) / √(1 - (T/T_c)⁴). -/
noncomputable def penetrationDepthTemp (lamL0 T T_c : ℝ) : ℝ :=
  lamL0 / Real.sqrt (1 - (T / T_c) ^ 4)

/-- At T = 0, the penetration depth equals lamL(0). -/
theorem penetrationDepth_at_zero (lamL0 T_c : ℝ) :
    penetrationDepthTemp lamL0 0 T_c = lamL0 := by
  simp [penetrationDepthTemp]

/-! ## Ginzburg-Landau Theory -/

/-- The Ginzburg-Landau order parameter ψ(x) : ℝ³ → ℂ.
    |ψ|² is proportional to the superconducting electron density n_s. -/
structure GLOrderParameter where
  /-- The complex order parameter field. -/
  ψ : Vec3SC → ℂ

/-- The superfluid density from the order parameter: n_s = |ψ|². -/
noncomputable def GLOrderParameter.superfluidDensity (op : GLOrderParameter) (x : Vec3SC) : ℝ :=
  Complex.normSq (op.ψ x)

/-- Superfluid density is non-negative. -/
theorem GLOrderParameter.superfluidDensity_nonneg (op : GLOrderParameter) (x : Vec3SC) :
    0 ≤ op.superfluidDensity x :=
  Complex.normSq_nonneg (op.ψ x)

/-- The GL free energy density (without magnetic field):
    f = α|ψ|² + (β/2)|ψ|⁴ + (ℏ²/2m*)|∇ψ|².
    α changes sign at T_c: α = α₀(T - T_c). -/
noncomputable def glFreeEnergyDensity (α β : ℝ) (ψ_norm_sq grad_ψ_norm_sq : ℝ)
    (hbar m_star : ℝ) : ℝ :=
  α * ψ_norm_sq + (β / 2) * ψ_norm_sq ^ 2 +
    (hbar ^ 2 / (2 * m_star)) * grad_ψ_norm_sq

/-- The GL coherence length: ξ(T) = ℏ / √(2m*|α|).
    Characterizes the spatial variation of the order parameter. -/
noncomputable def glCoherenceLength (hbar m_star α : ℝ) : ℝ :=
  hbar / Real.sqrt (2 * m_star * |α|)

/-- The Ginzburg-Landau parameter: κ = lamL / ξ.
    κ < 1/√2 → Type I, κ > 1/√2 → Type II. -/
noncomputable def glParameter (lamL ξ : ℝ) : ℝ :=
  lamL / ξ

/-- Classify superconductor type based on the GL parameter. -/
noncomputable def classifySuperconductor (κ : ℝ) : SuperconductorType :=
  if κ < 1 / Real.sqrt 2 then .typeI else .typeII

/-- Equilibrium order parameter magnitude in the bulk (below T_c):
    |ψ₀|² = -α/β = α₀(T_c - T)/β. -/
noncomputable def equilibriumOrderParam (α β : ℝ) : ℝ :=
  Real.sqrt (-α / β)

/-- The equilibrium order parameter minimizes the bulk free energy. -/
theorem equilibrium_minimizes_bulk_free_energy (α β : ℝ) (_hα : α < 0) (_hβ : 0 < β) :
    ∀ ψ_sq : ℝ, ψ_sq ≥ 0 →
      α * (-α / β) + (β / 2) * (-α / β) ^ 2 ≤
        α * ψ_sq + (β / 2) * ψ_sq ^ 2 := by
  intro ψ_sq _hψ
  have hβ_ne : β ≠ 0 := ne_of_gt _hβ
  -- f(x) - f(x₀) = (β/2)(x + α/β)² ≥ 0
  have key : α * ψ_sq + (β / 2) * ψ_sq ^ 2 - (α * (-α / β) + (β / 2) * (-α / β) ^ 2) =
    (β / 2) * (ψ_sq + α / β) ^ 2 := by field_simp; ring
  nlinarith [sq_nonneg (ψ_sq + α / β)]

/-- Magnetic flux quantization: Φ = n Φ₀ where Φ₀ = h/(2e). -/
noncomputable def fluxQuantum (h e : ℝ) : ℝ :=
  h / (2 * e)

/-- Quantized magnetic flux through a superconducting loop. -/
noncomputable def quantizedFlux (n : ℤ) (h e : ℝ) : ℝ :=
  n * fluxQuantum h e

end Measure.Physics.MaterialScience
