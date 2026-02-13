/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Bridge between Mathlib group theory and Measure physics symmetries.
Symmetry groups are fundamental to physics: Noether's theorem connects
continuous symmetries to conservation laws.
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace Measure.Math

/-- A symmetry transformation acting on a physical state space. -/
structure SymmetryGroup (α : Type*) where
  /-- The group of transformations. -/
  group : Type*
  /-- Group instance. -/
  [instGroup : Group group]
  /-- Action of the group on the state space. -/
  [instAction : MulAction group α]

/-- The general linear group GL(n, ℝ) — linear symmetries. -/
abbrev GLn (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) ℝ

/-- The orthogonal group O(n) — rotations and reflections.
    Defined as matrices M where M * Mᵀ = 1. -/
def IsOrthogonal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M * M.transpose = 1

/-- A Lie algebra element represented as a matrix (infinitesimal generator). -/
abbrev LieAlgElem (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Antisymmetric matrix condition (generators of SO(n)). -/
def IsAntisymmetric {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M.transpose = -M

end Measure.Math
