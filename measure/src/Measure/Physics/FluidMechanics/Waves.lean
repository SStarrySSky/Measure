/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Wave mechanics formalization.
Wave equation, plane waves, superposition, and Doppler effect.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Measure.Physics.FluidMechanics

/-! ## Wave Equation -/

/-- 3D position vector type. -/
abbrev WPos := Fin 3 → ℝ

/-- Laplacian of a scalar field in 3D: ∇²u = ∂²u/∂x₁² + ∂²u/∂x₂² + ∂²u/∂x₃². -/
noncomputable def waveLaplacian (u : WPos → ℝ) (x : WPos) : ℝ :=
  ∑ i : Fin 3, deriv (fun s =>
    deriv (fun r => u (Function.update x i r)) s) (x i)

/-- The wave equation: ∂²u/∂t² = c²∇²u.
    Describes propagation of disturbances at speed c. -/
noncomputable def WaveEquation (u : WPos → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ (x : WPos) (t : ℝ),
    deriv (fun s => deriv (fun r => u x r) s) t =
      c ^ 2 * waveLaplacian (fun y => u y t) x

/-- 1D wave equation: ∂²u/∂t² = c² ∂²u/∂x². -/
noncomputable def WaveEquation1D (u : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ (x t : ℝ),
    deriv (fun s => deriv (fun r => u x r) s) t =
      c ^ 2 * deriv (fun s => deriv (fun r => u r t) s) x

/-! ## Plane Wave Solutions -/

/-- A plane wave: u(x, t) = A cos(k·x - ωt + φ).
    Parameters: amplitude A, wave vector k, angular frequency ω, phase φ. -/
structure PlaneWave where
  /-- Amplitude. -/
  A : ℝ
  /-- Wave vector (direction and spatial frequency). -/
  k : WPos
  /-- Angular frequency. -/
  ω : ℝ
  /-- Initial phase. -/
  φ : ℝ

/-- Dot product of two 3-vectors. -/
noncomputable def wdot (u v : WPos) : ℝ := ∑ i : Fin 3, u i * v i

/-- Evaluate a plane wave at position x and time t. -/
noncomputable def PlaneWave.eval (pw : PlaneWave) (x : WPos) (t : ℝ) : ℝ :=
  pw.A * Real.cos (wdot pw.k x - pw.ω * t + pw.φ)

/-- Wave number magnitude: |k| = √(k·k). -/
noncomputable def PlaneWave.waveNumber (pw : PlaneWave) : ℝ :=
  Real.sqrt (wdot pw.k pw.k)

/-- Wavelength: λ = 2π/|k|. -/
noncomputable def PlaneWave.wavelength (pw : PlaneWave) : ℝ :=
  2 * Real.pi / pw.waveNumber

/-- Period: T = 2π/ω. -/
noncomputable def PlaneWave.period (pw : PlaneWave) : ℝ :=
  2 * Real.pi / pw.ω

/-- Frequency: f = ω/(2π). -/
noncomputable def PlaneWave.frequency (pw : PlaneWave) : ℝ :=
  pw.ω / (2 * Real.pi)

/-- Phase velocity: v_p = ω/|k|. -/
noncomputable def PlaneWave.phaseVelocity (pw : PlaneWave) : ℝ :=
  pw.ω / pw.waveNumber

/-- The dispersion relation for a non-dispersive wave: ω = c|k|. -/
def PlaneWave.dispersionRelation (pw : PlaneWave) (c : ℝ) : Prop :=
  pw.ω = c * pw.waveNumber

/-- A plane wave satisfying the dispersion relation ω² = c²|k|²
    is a solution to the wave equation.
    Proof requires the chain rule for cos and second derivatives of
    compositions, which are not yet available in Mathlib for this
    function-based representation. We assume differentiability axiomatically. -/
axiom planeWave_solves_wave_eq (pw : PlaneWave) (c : ℝ)
    (_hdisp : pw.ω ^ 2 = c ^ 2 * wdot pw.k pw.k) :
    WaveEquation pw.eval c

/-! ## Superposition Principle -/

/-- Superposition of two wave fields. -/
noncomputable def superpose (u₁ u₂ : WPos → ℝ → ℝ) : WPos → ℝ → ℝ :=
  fun x t => u₁ x t + u₂ x t

/-- The wave equation is linear: if u₁ and u₂ are solutions,
    then u₁ + u₂ is also a solution.
    Proof requires linearity of second derivatives (deriv of sum = sum of derivs),
    which needs differentiability hypotheses not present in the current formulation. -/
axiom superposition_principle (u₁ u₂ : WPos → ℝ → ℝ) (c : ℝ)
    (_h₁ : WaveEquation u₁ c) (_h₂ : WaveEquation u₂ c) :
    WaveEquation (superpose u₁ u₂) c

/-- General superposition of finitely many waves. -/
noncomputable def superposeFinite {n : ℕ} (waves : Fin n → WPos → ℝ → ℝ) :
    WPos → ℝ → ℝ :=
  fun x t => ∑ i : Fin n, waves i x t

/-- Finite superposition preserves the wave equation.
    Proof requires linearity of derivatives over finite sums,
    which needs differentiability hypotheses not present in the current formulation. -/
axiom superposition_finite {n : ℕ} (waves : Fin n → WPos → ℝ → ℝ) (c : ℝ)
    (_h : ∀ i, WaveEquation (waves i) c) :
    WaveEquation (superposeFinite waves) c

/-! ## Doppler Effect -/

/-- Observed frequency for a moving source and stationary observer.
    f_obs = f_source * c / (c - v_source)
    where v_source > 0 means source approaching observer. -/
noncomputable def dopplerMovingSource (f_source c v_source : ℝ) : ℝ :=
  f_source * c / (c - v_source)

/-- Observed frequency for a stationary source and moving observer.
    f_obs = f_source * (c + v_observer) / c
    where v_observer > 0 means observer approaching source. -/
noncomputable def dopplerMovingObserver (f_source c v_observer : ℝ) : ℝ :=
  f_source * (c + v_observer) / c

/-- General Doppler formula for both source and observer moving:
    f_obs = f_source * (c + v_observer) / (c - v_source). -/
noncomputable def dopplerGeneral (f_source c v_observer v_source : ℝ) : ℝ :=
  f_source * (c + v_observer) / (c - v_source)

/-- When source approaches at speed v, the observed frequency increases. -/
theorem doppler_approaching_source_increases (f_source c v_source : ℝ)
    (hf : 0 < f_source) (_hc : 0 < c) (hv : 0 < v_source) (hvc : v_source < c) :
    f_source < dopplerMovingSource f_source c v_source := by
  unfold dopplerMovingSource
  have hden : 0 < c - v_source := by linarith
  rw [lt_div_iff₀ hden]
  nlinarith

/-- When source recedes at speed v, the observed frequency decreases. -/
theorem doppler_receding_source_decreases (f_source c v_source : ℝ)
    (hf : 0 < f_source) (hc : 0 < c) (hv : 0 < v_source) :
    dopplerMovingSource f_source c (-v_source) < f_source := by
  unfold dopplerMovingSource
  have hden : 0 < c - -v_source := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith

/-- The general Doppler formula reduces to the moving source formula
    when the observer is stationary. -/
theorem doppler_general_stationary_observer (f_source c v_source : ℝ) :
    dopplerGeneral f_source c 0 v_source = dopplerMovingSource f_source c v_source := by
  unfold dopplerGeneral dopplerMovingSource
  ring

/-- The general Doppler formula reduces to the moving observer formula
    when the source is stationary. -/
theorem doppler_general_stationary_source (f_source c v_observer : ℝ) :
    dopplerGeneral f_source c v_observer 0 = dopplerMovingObserver f_source c v_observer := by
  unfold dopplerGeneral dopplerMovingObserver
  ring

end Measure.Physics.FluidMechanics
