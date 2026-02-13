/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Newtonian mechanics formalization.
Newton's second law F = ma and the simple harmonic oscillator.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Measure.Physics.ClassicalMechanics.Lagrangian

namespace Measure.Physics.ClassicalMechanics

/-! ## Newton's Second Law -/

/-- Newton's second law: F = ma for a single particle in ℝⁿ.
    The net force equals mass times acceleration along each coordinate. -/
noncomputable def newtonsSecondLaw {n : ℕ} (m : ℝ) (F : Fin n → ℝ → ℝ)
    (q : Path n) (i : Fin n) (t : ℝ) : Prop :=
  F i t = m * deriv (fun s => deriv (fun u => q u i) s) t

/-- A particle satisfies Newton's second law if F = ma holds for all coordinates and times. -/
def SatisfiesNewtonII {n : ℕ} (m : ℝ) (F : Fin n → ℝ → ℝ) (q : Path n) : Prop :=
  ∀ (i : Fin n) (t : ℝ), newtonsSecondLaw m F q i t

/-! ## Simple Harmonic Oscillator -/

/-- A one-dimensional simple harmonic oscillator with mass m and spring constant k. -/
structure SimpleHarmonicOscillator where
  /-- Mass of the oscillator. -/
  m : ℝ
  /-- Spring constant. -/
  k : ℝ
  /-- Mass is positive. -/
  m_pos : 0 < m
  /-- Spring constant is positive. -/
  k_pos : 0 < k

/-- Angular frequency ω = √(k/m) of a simple harmonic oscillator. -/
noncomputable def SimpleHarmonicOscillator.omega (osc : SimpleHarmonicOscillator) : ℝ :=
  Real.sqrt (osc.k / osc.m)

/-- The angular frequency is positive. -/
theorem SimpleHarmonicOscillator.omega_pos (osc : SimpleHarmonicOscillator) :
    0 < osc.omega := by
  unfold omega
  apply Real.sqrt_pos_of_pos
  exact div_pos osc.k_pos osc.m_pos

/-- ω² = k/m. -/
theorem SimpleHarmonicOscillator.omega_sq (osc : SimpleHarmonicOscillator) :
    osc.omega ^ 2 = osc.k / osc.m := by
  unfold omega
  rw [sq]
  exact Real.mul_self_sqrt (le_of_lt (div_pos osc.k_pos osc.m_pos))

/-- Kinetic energy of the SHO: T = ½mv². -/
noncomputable def SimpleHarmonicOscillator.kineticEnergy
    (osc : SimpleHarmonicOscillator) (v : ℝ) : ℝ :=
  (1/2) * osc.m * v ^ 2

/-- Potential energy of the SHO: V = ½kx². -/
noncomputable def SimpleHarmonicOscillator.potentialEnergy
    (osc : SimpleHarmonicOscillator) (x : ℝ) : ℝ :=
  (1/2) * osc.k * x ^ 2

/-- Total energy of the SHO: E = T + V = ½mv² + ½kx². -/
noncomputable def SimpleHarmonicOscillator.totalEnergy
    (osc : SimpleHarmonicOscillator) (x v : ℝ) : ℝ :=
  osc.kineticEnergy v + osc.potentialEnergy x

/-- The total energy is non-negative. -/
theorem SimpleHarmonicOscillator.totalEnergy_nonneg
    (osc : SimpleHarmonicOscillator) (x v : ℝ) :
    0 ≤ osc.totalEnergy x v := by
  unfold totalEnergy kineticEnergy potentialEnergy
  apply add_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · linarith
      · linarith [osc.m_pos]
    · exact sq_nonneg v
  · apply mul_nonneg
    · apply mul_nonneg
      · linarith
      · linarith [osc.k_pos]
    · exact sq_nonneg x

/-- The equation of motion for the SHO: x''(t) = -ω²x(t). -/
noncomputable def SimpleHarmonicOscillator.equationOfMotion
    (osc : SimpleHarmonicOscillator) (x : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (fun s => deriv x s) t = -(osc.omega ^ 2) * x t

/-- The SHO Lagrangian: L = ½mẋ² - ½kx². -/
noncomputable def SimpleHarmonicOscillator.lagrangian
    (osc : SimpleHarmonicOscillator) : Lagrangian 1 where
  L := fun q qdot _t =>
    (1/2) * osc.m * (qdot 0) ^ 2 - (1/2) * osc.k * (q 0) ^ 2

/-- The force on the SHO: F = -kx (Hooke's law). -/
noncomputable def SimpleHarmonicOscillator.force
    (osc : SimpleHarmonicOscillator) (x : ℝ) : ℝ :=
  -osc.k * x

end Measure.Physics.ClassicalMechanics
