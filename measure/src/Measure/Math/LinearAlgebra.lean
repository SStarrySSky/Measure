/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Bridge between Mathlib linear algebra and Measure physics types.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Measure.Math

/-- A physical vector in n-dimensional real space. -/
abbrev PhysVec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- 3D physical vector (most common in classical physics). -/
abbrev Vec3 := PhysVec 3

/-- 4D physical vector (spacetime in special/general relativity). -/
abbrev Vec4 := PhysVec 4

/-- A real square matrix of dimension n. -/
abbrev PhysMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- 3x3 matrix (rotation, inertia tensor, etc.). -/
abbrev Mat3 := PhysMat 3

/-- 4x4 matrix (Lorentz transformation, metric tensor, etc.). -/
abbrev Mat4 := PhysMat 4

/-- Cross product for 3D vectors. -/
noncomputable def cross (u v : Vec3) : Vec3 :=
  let ue := EuclideanSpace.equiv (Fin 3) ℝ u
  let ve := EuclideanSpace.equiv (Fin 3) ℝ v
  EuclideanSpace.equiv (Fin 3) ℝ |>.symm (fun i =>
    match i with
    | ⟨0, _⟩ => ue ⟨1, by omega⟩ * ve ⟨2, by omega⟩ - ue ⟨2, by omega⟩ * ve ⟨1, by omega⟩
    | ⟨1, _⟩ => ue ⟨2, by omega⟩ * ve ⟨0, by omega⟩ - ue ⟨0, by omega⟩ * ve ⟨2, by omega⟩
    | ⟨2, _⟩ => ue ⟨0, by omega⟩ * ve ⟨1, by omega⟩ - ue ⟨1, by omega⟩ * ve ⟨0, by omega⟩
    | ⟨n+3, h⟩ => absurd h (by omega))

/-- Dot product for physical vectors (delegates to Mathlib inner product). -/
noncomputable def dot {n : ℕ} (u v : PhysVec n) : ℝ :=
  @inner ℝ (EuclideanSpace ℝ (Fin n)) _ u v

end Measure.Math
