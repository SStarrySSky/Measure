/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Wave optics — interference, diffraction, polarization (Jones calculus).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Exponential

namespace Measure.Physics.Optics

/-! ## Fundamental wave properties -/

/-- A monochromatic light wave characterized by wavelength, frequency, and amplitude. -/
structure LightWave where
  /-- Wavelength λ in meters. -/
  wavelength : ℝ
  /-- Frequency ν in Hz. -/
  frequency : ℝ
  /-- Amplitude. -/
  amplitude : ℝ
  /-- Phase φ in radians. -/
  phase : ℝ
  /-- Wavelength is positive. -/
  wavelength_pos : 0 < wavelength
  /-- Frequency is positive. -/
  frequency_pos : 0 < frequency

/-- Speed of light in vacuum. -/
noncomputable def c_light : ℝ := 2.99792458e8

/-- Wave number k = 2π/λ. -/
noncomputable def waveNumber (w : LightWave) : ℝ :=
  2 * Real.pi / w.wavelength

/-- Angular frequency ω = 2πν. -/
noncomputable def angularFrequency (w : LightWave) : ℝ :=
  2 * Real.pi * w.frequency

/-- Dispersion relation in vacuum: c = λν. -/
noncomputable def DispersionRelation (w : LightWave) : Prop :=
  c_light = w.wavelength * w.frequency

/-- Electric field of a plane wave: E(x,t) = A cos(kx - ωt + φ). -/
noncomputable def planeWaveField (w : LightWave) (x t : ℝ) : ℝ :=
  w.amplitude * Real.cos (waveNumber w * x - angularFrequency w * t + w.phase)

/-! ## Interference -/

/-- Path difference between two waves. -/
noncomputable def pathDifference (d sinθ : ℝ) : ℝ :=
  d * sinθ

/-- Phase difference from path difference: Δφ = 2π Δx / λ. -/
noncomputable def phaseDifference (Δx wl : ℝ) : ℝ :=
  2 * Real.pi * Δx / wl

/-- Constructive interference condition: Δx = mλ for integer m. -/
def ConstructiveInterference (Δx wl : ℝ) (m : ℤ) : Prop :=
  Δx = ↑m * wl

/-- Destructive interference condition: Δx = (m + ½)λ for integer m. -/
noncomputable def DestructiveInterference (Δx wl : ℝ) (m : ℤ) : Prop :=
  Δx = (↑m + 1 / 2) * wl

/-- Resultant intensity of two coherent waves:
    I = I₁ + I₂ + 2√(I₁I₂) cos(Δφ). -/
noncomputable def coherentIntensity (I₁ I₂ Δφ : ℝ) : ℝ :=
  I₁ + I₂ + 2 * Real.sqrt (I₁ * I₂) * Real.cos Δφ

/-- For equal intensities, I = 4I₀ cos²(Δφ/2). -/
noncomputable def equalIntensityInterference (I₀ Δφ : ℝ) : ℝ :=
  4 * I₀ * (Real.cos (Δφ / 2)) ^ 2

/-! ## Diffraction -/

/-- Single-slit diffraction: intensity pattern.
    I(θ) = I₀ (sin α / α)² where α = πa sin θ / λ. -/
noncomputable def singleSlitAlpha (a wl sinθ : ℝ) : ℝ :=
  Real.pi * a * sinθ / wl

/-- Single-slit diffraction intensity (normalized). -/
noncomputable def singleSlitIntensity (I₀ α : ℝ) : ℝ :=
  if α = 0 then I₀
  else I₀ * (Real.sin α / α) ^ 2

/-- Single-slit minima condition: a sin θ = mλ, m ≠ 0. -/
def SingleSlitMinimum (a sinθ wl : ℝ) (m : ℤ) : Prop :=
  a * sinθ = ↑m * wl ∧ m ≠ 0

/-- Double-slit (Young's) interference maxima: d sin θ = mλ. -/
def DoubleSlitMaximum (d sinθ wl : ℝ) (m : ℤ) : Prop :=
  d * sinθ = ↑m * wl

/-- Double-slit fringe spacing: Δy = λL/d. -/
noncomputable def fringeSpacing (wl L d : ℝ) : ℝ :=
  wl * L / d

/-- Rayleigh criterion for resolution: sin θ_min = 1.22 λ/D. -/
noncomputable def rayleighCriterion (wl D : ℝ) : ℝ :=
  1.22 * wl / D

/-! ## Diffraction grating -/

/-- Diffraction grating equation: d sin θ = mλ. -/
def GratingEquation (d sinθ wl : ℝ) (m : ℤ) : Prop :=
  d * sinθ = ↑m * wl

/-- Resolving power of a grating: R = mN where N is the number of slits. -/
def gratingResolvingPower (m : ℤ) (N : ℕ) : ℤ :=
  m * ↑N

/-! ## Polarization — Jones calculus -/

/-- Jones vector: a 2×1 complex vector representing polarization state. -/
abbrev JonesVector := Fin 2 → ℂ

/-- Jones matrix: a 2×2 complex matrix representing an optical element. -/
abbrev JonesMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Horizontal linear polarization. -/
def horizontalPolarization : JonesVector :=
  ![1, 0]

/-- Vertical linear polarization. -/
def verticalPolarization : JonesVector :=
  ![0, 1]

/-- Linear horizontal polarizer Jones matrix. -/
def horizontalPolarizer : JonesMatrix :=
  !![1, 0; 0, 0]

/-- Linear vertical polarizer Jones matrix. -/
def verticalPolarizer : JonesMatrix :=
  !![0, 0; 0, 1]

/-- Quarter-wave plate (fast axis horizontal) Jones matrix. -/
noncomputable def quarterWavePlate : JonesMatrix :=
  !![1, 0; 0, Complex.I]

/-- Half-wave plate (fast axis horizontal) Jones matrix. -/
def halfWavePlate : JonesMatrix :=
  !![1, 0; 0, -1]

/-- Apply a Jones matrix to a Jones vector. -/
noncomputable def applyJones (M : JonesMatrix) (v : JonesVector) : JonesVector :=
  M.mulVec v

/-- Horizontal polarizer kills vertical polarization. -/
theorem horizontal_polarizer_kills_vertical :
    applyJones horizontalPolarizer verticalPolarization = ![0, 0] := by
  unfold applyJones horizontalPolarizer verticalPolarization
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Vertical polarizer kills horizontal polarization. -/
theorem vertical_polarizer_kills_horizontal :
    applyJones verticalPolarizer horizontalPolarization = ![0, 0] := by
  unfold applyJones verticalPolarizer horizontalPolarization
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Malus's law: I = I₀ cos²θ for polarized light through a polarizer. -/
noncomputable def malusLaw (I₀ θ : ℝ) : ℝ :=
  I₀ * (Real.cos θ) ^ 2

/-- Brewster's angle: tan θ_B = n₂/n₁.
    Returns the ratio n₂/n₁ which equals tan(θ_B). -/
noncomputable def brewsterTanAngle (n₁ n₂ : ℝ) : ℝ :=
  n₂ / n₁

/-! ## Malus's law properties -/

/-- Malus's law at θ = 0: full transmission, I = I₀. -/
theorem malusLaw_zero (I₀ : ℝ) : malusLaw I₀ 0 = I₀ := by
  unfold malusLaw
  simp [Real.cos_zero]

/-- Malus's law is non-negative when I₀ ≥ 0. -/
theorem malusLaw_nonneg (I₀ θ : ℝ) (h : 0 ≤ I₀) : 0 ≤ malusLaw I₀ θ := by
  unfold malusLaw
  exact mul_nonneg h (sq_nonneg _)

/-! ## Interference properties -/

/-- Constructive interference at zero path difference (m = 0). -/
theorem constructive_at_zero_path (wl : ℝ) :
    ConstructiveInterference 0 wl 0 := by
  unfold ConstructiveInterference
  simp

/-- Coherent intensity of two equal waves with zero phase difference
    gives four times the individual intensity. -/
theorem coherent_max_intensity (I₀ : ℝ) (h : 0 ≤ I₀) :
    coherentIntensity I₀ I₀ 0 = 4 * I₀ := by
  unfold coherentIntensity
  simp [Real.cos_zero, Real.sqrt_mul_self h]
  ring

end Measure.Physics.Optics
