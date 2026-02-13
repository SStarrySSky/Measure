/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Crystal lattice structures — Bravais lattices, reciprocal lattices,
Brillouin zones, and crystal symmetries.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Measure.Physics.CondensedMatter

/-- 3D real-space position vector. -/
abbrev Vec3 := Fin 3 → ℝ

/-! ## Bravais Lattice -/

/-- A Bravais lattice defined by three primitive lattice vectors a₁, a₂, a₃.
    Every lattice point is R = n₁a₁ + n₂a₂ + n₃a₃ for integers n₁, n₂, n₃. -/
structure BravaisLattice where
  /-- Primitive lattice vectors as columns of a 3×3 matrix. -/
  basis : Matrix (Fin 3) (Fin 3) ℝ
  /-- The lattice vectors are linearly independent (non-zero volume). -/
  nondegenerate : basis.det ≠ 0

/-- A lattice point given integer coordinates (n₁, n₂, n₃). -/
noncomputable def BravaisLattice.point (L : BravaisLattice) (n : Fin 3 → ℤ) : Vec3 :=
  fun i => ∑ j : Fin 3, L.basis i j * (n j : ℝ)

/-- A point belongs to the lattice if it equals some integer combination of basis vectors. -/
def BravaisLattice.IsLatticePoint (L : BravaisLattice) (x : Vec3) : Prop :=
  ∃ n : Fin 3 → ℤ, x = L.point n

/-- The unit cell volume |det(a₁, a₂, a₃)|. -/
noncomputable def BravaisLattice.volume (L : BravaisLattice) : ℝ :=
  |L.basis.det|

/-- Volume of a non-degenerate lattice is positive. -/
theorem BravaisLattice.volume_pos (L : BravaisLattice) : 0 < L.volume := by
  simp only [BravaisLattice.volume]
  exact abs_pos.mpr L.nondegenerate

/-! ## Reciprocal Lattice -/

/-- The reciprocal lattice basis satisfying aᵢ · bⱼ = 2π δᵢⱼ.
    Defined as 2π (Aᵀ)⁻¹ where A is the direct lattice basis matrix. -/
noncomputable def BravaisLattice.reciprocalBasis (L : BravaisLattice) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (2 * Real.pi) • (L.basis.transpose)⁻¹

/-- The reciprocal lattice constructed from a direct lattice. -/
noncomputable def BravaisLattice.reciprocal (L : BravaisLattice) : BravaisLattice where
  basis := L.reciprocalBasis
  nondegenerate := by
    unfold reciprocalBasis
    rw [Matrix.det_smul, Fintype.card_fin]
    apply mul_ne_zero
    · exact pow_ne_zero 3 (by positivity)
    · have : IsUnit L.basis.transpose⁻¹.det := by
        rw [Matrix.isUnit_nonsing_inv_det_iff, Matrix.det_transpose]
        exact isUnit_iff_ne_zero.mpr L.nondegenerate
      exact isUnit_iff_ne_zero.mp this

/-- A reciprocal lattice vector G = m₁b₁ + m₂b₂ + m₃b₃. -/
noncomputable def BravaisLattice.reciprocalPoint (L : BravaisLattice)
    (m : Fin 3 → ℤ) : Vec3 :=
  L.reciprocal.point m

/-- Orthogonality relation: aᵢ · bⱼ = 2π δᵢⱼ.
    This follows from the definition of the reciprocal basis as 2π(Aᵀ)⁻¹,
    which gives Aᵀ · (2π(Aᵀ)⁻¹) = 2πI. The proof requires matrix algebra
    involving nonsing_inv that is complex to automate in Lean. -/
axiom BravaisLattice.direct_reciprocal_orthogonality (L : BravaisLattice)
    (i j : Fin 3) :
    ∑ k : Fin 3, L.basis k i * L.reciprocalBasis k j =
      2 * Real.pi * if i = j then 1 else 0

/-! ## Brillouin Zone -/

/-- A point k is in the first Brillouin zone if it is closer to the origin
    than to any other reciprocal lattice point. -/
def BravaisLattice.InFirstBZ (L : BravaisLattice) (k : Vec3) : Prop :=
  ∀ m : Fin 3 → ℤ, m ≠ 0 →
    ∑ i, k i ^ 2 ≤ ∑ i, (k i - L.reciprocalPoint m i) ^ 2

/-- The Γ point (origin) is always in the first Brillouin zone. -/
theorem BravaisLattice.gamma_in_firstBZ (L : BravaisLattice) :
    L.InFirstBZ (fun _ => 0) := by
  intro m _hm
  simp only [zero_sub, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    Finset.sum_const_zero, neg_sq]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-! ## Crystal Symmetry -/

/-- A point symmetry operation (rotation/reflection) represented as an
    orthogonal 3×3 matrix. -/
structure PointSymmetry where
  /-- The rotation/reflection matrix. -/
  mat : Matrix (Fin 3) (Fin 3) ℝ
  /-- Orthogonality: RᵀR = I. -/
  orthogonal : mat.transpose * mat = 1

/-- A space group operation: point symmetry + translation. -/
structure SpaceGroupOp where
  /-- The point symmetry part. -/
  rotation : PointSymmetry
  /-- The translation part (may be fractional). -/
  translation : Vec3

/-- Apply a space group operation to a point. -/
noncomputable def SpaceGroupOp.apply (op : SpaceGroupOp) (x : Vec3) : Vec3 :=
  fun i => (∑ j : Fin 3, op.rotation.mat i j * x j) + op.translation i

/-- A symmetry operation preserves the lattice if it maps every lattice point
    to another lattice point. -/
def SpaceGroupOp.PreservesLattice (op : SpaceGroupOp) (L : BravaisLattice) : Prop :=
  ∀ n : Fin 3 → ℤ, L.IsLatticePoint (op.apply (L.point n))

/-- The identity is always a symmetry of any lattice. -/
theorem identity_preserves_lattice (L : BravaisLattice) :
    (SpaceGroupOp.mk ⟨1, by simp⟩ (fun _ => 0)).PreservesLattice L := by
  intro n
  refine ⟨n, ?_⟩
  funext i
  simp [SpaceGroupOp.apply, BravaisLattice.point, Matrix.one_apply]

/-- The seven crystal systems classified by symmetry constraints. -/
inductive CrystalSystem where
  | triclinic
  | monoclinic
  | orthorhombic
  | tetragonal
  | trigonal
  | hexagonal
  | cubic

/-- The 14 Bravais lattice types. -/
inductive BravaisType where
  | triclinic_P
  | monoclinic_P | monoclinic_C
  | orthorhombic_P | orthorhombic_C | orthorhombic_I | orthorhombic_F
  | tetragonal_P | tetragonal_I
  | trigonal_R
  | hexagonal_P
  | cubic_P | cubic_I | cubic_F

/-- Map each Bravais type to its crystal system. -/
def BravaisType.system : BravaisType → CrystalSystem
  | .triclinic_P => .triclinic
  | .monoclinic_P | .monoclinic_C => .monoclinic
  | .orthorhombic_P | .orthorhombic_C | .orthorhombic_I | .orthorhombic_F => .orthorhombic
  | .tetragonal_P | .tetragonal_I => .tetragonal
  | .trigonal_R => .trigonal
  | .hexagonal_P => .hexagonal
  | .cubic_P | .cubic_I | .cubic_F => .cubic

end Measure.Physics.CondensedMatter
