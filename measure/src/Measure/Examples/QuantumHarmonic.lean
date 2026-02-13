/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Example: Quantum harmonic oscillator.

Demonstrates:
  - Defining quantum-mechanical dimensions (action, angular frequency, etc.)
  - The harmonic oscillator Hamiltonian: H = p^2/(2m) + (1/2) m omega^2 x^2
  - Energy level quantization: E_n = hbar * omega * (n + 1/2)
  - Zero-point energy E_0 = (1/2) hbar * omega
  - Heisenberg uncertainty principle dimensional check
  - All dimensional checks via native_decide

The `theory` block triggers the 6-phase self-consistency pipeline.
If this file compiles, the theory is self-consistent.
-/
import Measure.Syntax.Theory
import Measure.Syntax.Tactics
import Measure.Dim.Basic
import Measure.Quantity.Basic
import Measure.Quantity.Ops
import Measure.Physics.Dimensional

open Measure.Dim
open Measure.Quantity
open Measure.Physics

-- ============================================================
-- Domain-specific dimension shorthands for quantum mechanics
-- (Base/derived dims reuse canonical definitions from Measure.Physics.Dimensional)
-- ============================================================

/-- Angular frequency dimension: T^{-1} (rad/s) -/
def qmDimAngularFreq : Dim := { T := QExp.mk' (-1) 1 }

/-- Action dimension: M L^2 T^{-1} (J s = kg m^2 s^{-1})
    This is the dimension of hbar (reduced Planck constant). -/
def qmDimAction : Dim := { M := QExp.one, L := QExp.mk' 2 1, T := -QExp.one }

/-- Spring constant dimension: M T^{-2} (N/m = kg s^{-2})
    From F = -kx, so [k] = [F]/[L] = M L T^{-2} / L = M T^{-2}. -/
def qmDimSpringConst : Dim := { M := QExp.one, T := QExp.mk' (-2) 1 }

/-- Dimensionless: for quantum numbers, pure ratios, etc. -/
def qmDimless : Dim := {}

-- ============================================================
-- The theory: Quantum Harmonic Oscillator
-- ============================================================

theory QuantumHarmonic where

  /-- Reduced Planck constant hbar = h / (2 pi).
      SI value: 1.054 571 817 x 10^{-34} J s.
      Dimension: M L^2 T^{-1} (action). -/
  axiom hbar : ExactQ qmDimAction

  /-- Particle mass m.
      Dimension: M (mass). -/
  axiom mass : ExactQ dimMass

  /-- Angular frequency omega of the oscillator.
      Related to the spring constant by omega = sqrt(k/m).
      Dimension: T^{-1}. -/
  axiom omega : ExactQ qmDimAngularFreq

  /-- Spring constant k = m * omega^2.
      Dimension: M T^{-2}. -/
  axiom springConst (m : ExactQ dimMass) (w : ExactQ qmDimAngularFreq)
    : ExactQ qmDimSpringConst

  /-- Kinetic energy term: T = p^2 / (2m).
      [p^2 / m] = (M L T^{-1})^2 / M = M L^2 T^{-2} = [Energy].
      Result has energy dimension. -/
  axiom kineticEnergy (p : ExactQ dimMomentum) (m : ExactQ dimMass)
    : ExactQ dimEnergy

  /-- Potential energy term: V = (1/2) m omega^2 x^2.
      [m * omega^2 * x^2] = M * T^{-2} * L^2 = M L^2 T^{-2} = [Energy].
      Result has energy dimension. -/
  axiom potentialEnergy
    (m : ExactQ dimMass)
    (w : ExactQ qmDimAngularFreq)
    (x : ExactQ dimLength)
    : ExactQ dimEnergy

  /-- Hamiltonian: H = T + V = p^2/(2m) + (1/2) m omega^2 x^2.
      Both terms have energy dimension, so the sum is well-typed.
      Result has energy dimension M L^2 T^{-2}. -/
  axiom hamiltonian
    (ke : ExactQ dimEnergy)
    (pe : ExactQ dimEnergy)
    : ExactQ dimEnergy

  /-- Energy quantization: E_n = hbar * omega * (n + 1/2).
      The quantum number n is dimensionless (natural number).
      [hbar * omega] = (M L^2 T^{-1})(T^{-1}) = M L^2 T^{-2} = [Energy].
      This is the fundamental result of the quantum harmonic oscillator. -/
  axiom energyLevel
    (hb : ExactQ qmDimAction)
    (w : ExactQ qmDimAngularFreq)
    : ExactQ dimEnergy

  /-- Zero-point energy: E_0 = (1/2) hbar * omega.
      Even at n = 0, the oscillator has nonzero energy.
      This is a purely quantum effect with no classical analogue.
      Result has energy dimension. -/
  axiom zeroPointEnergy
    (hb : ExactQ qmDimAction)
    (w : ExactQ qmDimAngularFreq)
    : ExactQ dimEnergy

  /-- Energy spacing: Delta E = hbar * omega.
      All energy levels are equally spaced.
      Result has energy dimension. -/
  axiom energySpacing
    (hb : ExactQ qmDimAction)
    (w : ExactQ qmDimAngularFreq)
    : ExactQ dimEnergy

  /-- Heisenberg uncertainty principle: Delta x * Delta p >= hbar / 2.
      [Delta x * Delta p] = L * (M L T^{-1}) = M L^2 T^{-1} = [action] = [hbar].
      The ground state of the harmonic oscillator saturates this bound.
      This is a fundamental quantum bound, not derivable from classical mechanics. -/
  axiom uncertaintyPrinciple
    (dx : ExactQ dimLength)
    (dp : ExactQ dimMomentum)
    (hb : ExactQ qmDimAction)
    : dx.value * dp.value >= hb.value / 2.0

  /-- Noether symmetry: time-translation invariance implies energy conservation
      for a time-independent Hamiltonian. -/
  symmetry time_translation

-- ============================================================
-- If we reach here, the theory compiled successfully.
-- Phase 6 verified:
--   All axioms are dimensionally consistent
--   No conservation law violations detected
--   Conservation laws derived from declared symmetries:
--     time_translation -> energy conservation
--   Theory 'QuantumHarmonic' is self-consistent
-- ============================================================

-- Dimensional consistency proofs:

/-- hbar * omega has energy dimension.
    [hbar * omega] = (M L^2 T^{-1})(T^{-1}) = M L^2 T^{-2} = [Energy]. -/
theorem hbar_omega_is_energy :
    Dim.mul qmDimAction qmDimAngularFreq = dimEnergy := by
  native_decide

/-- p^2 / m has energy dimension.
    [p^2 / m] = (M L T^{-1})^2 / M = M^2 L^2 T^{-2} / M = M L^2 T^{-2} = [Energy]. -/
theorem kinetic_energy_dim :
    Dim.div (Dim.mul dimMomentum dimMomentum) dimMass = dimEnergy := by
  native_decide

/-- m * omega^2 * x^2 has energy dimension.
    [m * omega^2 * x^2] = M * T^{-2} * L^2 = M L^2 T^{-2} = [Energy]. -/
theorem potential_energy_dim :
    Dim.mul (Dim.mul dimMass (Dim.mul qmDimAngularFreq qmDimAngularFreq))
            (Dim.mul dimLength dimLength) = dimEnergy := by
  native_decide

/-- Spring constant k = m * omega^2 has the correct dimension.
    [m * omega^2] = M * T^{-2} = [spring constant]. -/
theorem spring_const_dim :
    Dim.mul dimMass (Dim.mul qmDimAngularFreq qmDimAngularFreq) = qmDimSpringConst := by
  native_decide

/-- omega = sqrt(k/m) is dimensionally consistent.
    [k/m] = (M T^{-2}) / M = T^{-2}, so [sqrt(k/m)] = T^{-1} = [angular frequency]. -/
theorem omega_from_spring_dim :
    Dim.div qmDimSpringConst dimMass =
      Dim.mul qmDimAngularFreq qmDimAngularFreq := by
  native_decide

/-- Uncertainty product Delta x * Delta p has action dimension.
    [Delta x * Delta p] = L * (M L T^{-1}) = M L^2 T^{-1} = [hbar]. -/
theorem uncertainty_product_dim :
    Dim.mul dimLength dimMomentum = qmDimAction := by
  native_decide

/-- Restoring force F = -k x has force dimension.
    [k * x] = (M T^{-2}) * L = M L T^{-2} = [Force]. -/
theorem restoring_force_dim :
    Dim.mul qmDimSpringConst dimLength = dimForce := by
  native_decide

/-- Energy divided by angular frequency has action dimension.
    [E / omega] = (M L^2 T^{-2}) / T^{-1} = M L^2 T^{-1} = [hbar]. -/
theorem energy_over_omega_is_action :
    Dim.div dimEnergy qmDimAngularFreq = qmDimAction := by
  native_decide

/-- Momentum divided by mass has velocity dimension (de Broglie relation context).
    [p / m] = (M L T^{-1}) / M = L T^{-1}. -/
theorem momentum_over_mass_is_velocity :
    Dim.div dimMomentum dimMass =
      { L := QExp.one, T := -QExp.one } := by
  native_decide
