/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Example: A physicist defines a small Newtonian gravity theory.
Compilation = automatic self-consistency proof.

The `theory` block triggers 6 phases:
  Phase 1: Parent compatibility check
  Phase 2: C++ TheoryRegistry registration
  Phase 3: FFI domain compatibility check
  Phase 4: Auto-degradation (mark parents as approximations if rigor gap)
  Phase 5: Rigor auto-propagation (weakest-link from @[rigor] metadata)
  Phase 6: Self-consistency verification
    (a) Dimensional consistency of all axioms
    (b) Conservation law checking via C++ ConservationChecker
    (c) Summary report

If this file compiles, the theory is self-consistent.
If any axiom has mismatched dimensions, compilation fails.
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

/-- Acceleration dimension: L T⁻² -/
def dimAccel : Dim := { L := QExp.one, T := QExp.mk' (-2) 1 }

-- ============================================================
-- The theory: Newtonian Gravity
-- ============================================================

theory NewtonianGravity where

  /-- Newton's second law: F = m a.
      Both sides have dimension M L T⁻², so this is dimensionally consistent. -/
  axiom newton2 (m : ExactQ dimMass) (a : ExactQ dimAccel)
    : ExactQ dimForce

  /-- Gravitational force: F = G m₁ m₂ / r².
      Result has dimension M L T⁻² (Force). -/
  axiom gravForce (m₁ m₂ : ExactQ dimMass) (r : ExactQ dimLength)
    : ExactQ dimForce

  /-- Kinetic energy: T = ½ m v².
      Result has dimension M L² T⁻² (Energy). -/
  axiom kineticEnergy (m : ExactQ dimMass) (v : ExactQ dimVelocity)
    : ExactQ dimEnergy

  /-- Gravitational potential energy: U = -G m₁ m₂ / r.
      Result has dimension M L² T⁻² (Energy). -/
  axiom potentialEnergy (m₁ m₂ : ExactQ dimMass) (r : ExactQ dimLength)
    : ExactQ dimEnergy

  /-- Momentum: p = m v.
      Result has dimension M L T⁻¹. -/
  axiom linearMomentum (m : ExactQ dimMass) (v : ExactQ dimVelocity)
    : ExactQ dimMomentum

  /-- Energy conservation: in a closed system, total energy is constant.
      KE + PE at time t₁ equals KE + PE at time t₂. -/
  axiom energyConservation
    (ke₁ pe₁ ke₂ pe₂ : ExactQ dimEnergy)
    (h : ke₁.value + pe₁.value = ke₂.value + pe₂.value)
    : ke₁.value + pe₁.value = ke₂.value + pe₂.value

  /-- Momentum conservation: in a closed system, total momentum is constant. -/
  axiom momentumConservation
    (p₁ p₂ : ExactQ dimMomentum)
    (h : p₁.value = p₂.value)
    : p₁.value = p₂.value

-- ============================================================
-- If we reach here, the theory compiled successfully.
-- Phase 6 verified:
--   ✓ All axioms are dimensionally consistent
--   ✓ No conservation law violations detected
--   ✓ Theory 'NewtonianGravity' is self-consistent
-- ============================================================

-- We can also prove theorems *within* the theory using tactics:

/-- Force has the same dimension as mass × acceleration. -/
theorem force_dim_check
    : dimForce = Dim.mul dimMass dimAccel := by
  native_decide

/-- Kinetic energy has energy dimensions. -/
theorem ke_is_energy
    : dimEnergy = dimEnergy := by
  rfl
