/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Lorentz transformations and the Lorentz group.
-/
import Measure.Physics.Relativity.Minkowski

namespace Measure.Physics.Relativity

/-- A Lorentz transformation is a 4×4 matrix that preserves the Minkowski metric:
    Λᵀ η Λ = η. -/
def IsLorentzTransformation (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  Λ.transpose * minkowskiMetric * Λ = minkowskiMetric

/-- A Lorentz boost along the x-axis with velocity v. -/
noncomputable def boostX (v : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let γ := lorentzFactor v
  let β := v / c
  Matrix.of (fun i j =>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => γ
    | ⟨0, _⟩, ⟨1, _⟩ => -γ * β
    | ⟨1, _⟩, ⟨0, _⟩ => -γ * β
    | ⟨1, _⟩, ⟨1, _⟩ => γ
    | ⟨2, _⟩, ⟨2, _⟩ => 1
    | ⟨3, _⟩, ⟨3, _⟩ => 1
    | _, _ => 0)

/-- Apply a Lorentz transformation to a four-vector. -/
noncomputable def applyLorentz (Λ : Matrix (Fin 4) (Fin 4) ℝ) (v : FourVector) : FourVector :=
  fun i => ∑ j : Fin 4, Λ i j * v j

/-- Lorentz boost preserves the Minkowski metric. -/
theorem boostX_is_lorentz (v : ℝ) (hv : v^2 < c^2) :
    IsLorentzTransformation (boostX v) := by
  unfold IsLorentzTransformation boostX minkowskiMetric lorentzFactor
  set γ := 1 / Real.sqrt (1 - v ^ 2 / c ^ 2) with hγ_def
  set β := v / c with hβ_def
  have hc : c ≠ 0 := by unfold c; norm_num
  have hc2 : (c : ℝ) ^ 2 > 0 := by unfold c; norm_num
  have hpos : 1 - v ^ 2 / c ^ 2 > 0 := by
    have : v ^ 2 / c ^ 2 < 1 := by rwa [div_lt_one hc2]
    linarith
  have hsqrt_pos : Real.sqrt (1 - v ^ 2 / c ^ 2) > 0 := Real.sqrt_pos.mpr hpos
  have hsqrt_ne : Real.sqrt (1 - v ^ 2 / c ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  have hsq : Real.sqrt (1 - v ^ 2 / c ^ 2) ^ 2 = 1 - v ^ 2 / c ^ 2 :=
    Real.sq_sqrt hpos.le
  -- Key: γ² = 1/(1 - β²) and γ²(1 - β²) = 1
  have hγ_sq : γ ^ 2 = 1 / (1 - v ^ 2 / c ^ 2) := by
    rw [hγ_def, one_div, inv_pow, hsq, one_div]
  have hγβ_sq : (γ * β) ^ 2 = v ^ 2 / c ^ 2 / (1 - v ^ 2 / c ^ 2) := by
    rw [mul_pow, hγ_sq, hβ_def]; field_simp
  -- The (0,0) entry: -γ² + γ²β² = -1
  have h00 : -γ ^ 2 + (γ * β) ^ 2 = -1 := by
    rw [hγ_sq, hγβ_sq]
    have hne : 1 - v ^ 2 / c ^ 2 ≠ 0 := ne_of_gt hpos
    rw [show -(1 / (1 - v ^ 2 / c ^ 2)) = (-1) / (1 - v ^ 2 / c ^ 2) from by ring]
    rw [show v ^ 2 / c ^ 2 / (1 - v ^ 2 / c ^ 2) = (v ^ 2 / c ^ 2) / (1 - v ^ 2 / c ^ 2) from rfl]
    rw [← add_div]
    rw [show (-1 : ℝ) + v ^ 2 / c ^ 2 = -(1 - v ^ 2 / c ^ 2) from by ring]
    rw [neg_div_self hne]
  -- The (1,1) entry: γ²β² - γ² = ... wait, it's γ² - γ²β² = 1
  have h11 : γ ^ 2 - (γ * β) ^ 2 = 1 := by linarith
  set_option maxHeartbeats 400000 in
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
          Matrix.diagonal_apply, Fin.sum_univ_four] <;>
    nlinarith

/-- Relativistic velocity addition: u ⊕ v = (u + v)/(1 + uv/c²). -/
noncomputable def velocityAddition (u v : ℝ) : ℝ :=
  (u + v) / (1 + u * v / c^2)

/-- Velocity addition is commutative. -/
theorem velocityAddition_comm (u v : ℝ) :
    velocityAddition u v = velocityAddition v u := by
  unfold velocityAddition
  ring

/-- Velocity addition with zero: v ⊕ 0 = v. -/
theorem velocityAddition_zero_right (v : ℝ) :
    velocityAddition v 0 = v := by
  unfold velocityAddition
  simp

/-- Velocity addition with zero: 0 ⊕ v = v. -/
theorem velocityAddition_zero_left (v : ℝ) :
    velocityAddition 0 v = v := by
  unfold velocityAddition
  simp

/-! ## Lorentz factor properties -/

/-- The Lorentz factor at rest (v = 0) is 1. -/
theorem lorentzFactor_zero : lorentzFactor 0 = 1 := by
  unfold lorentzFactor c
  simp [Real.sqrt_one]

/-- The argument of the square root in the Lorentz factor is positive when |v| < c. -/
theorem lorentzFactor_sqrt_arg_pos (v : ℝ) (hv : v ^ 2 < c ^ 2) :
    0 < 1 - v ^ 2 / c ^ 2 := by
  have hc2 : (c : ℝ) ^ 2 > 0 := by unfold c; norm_num
  have : v ^ 2 / c ^ 2 < 1 := by rwa [div_lt_one hc2]
  linarith

/-- The Lorentz factor is positive when |v| < c. -/
theorem lorentzFactor_pos (v : ℝ) (hv : v ^ 2 < c ^ 2) :
    0 < lorentzFactor v := by
  unfold lorentzFactor
  rw [one_div]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (lorentzFactor_sqrt_arg_pos v hv))

/-- The Lorentz factor satisfies γ ≥ 1 when |v| < c. -/
theorem lorentzFactor_ge_one (v : ℝ) (hv : v ^ 2 < c ^ 2) :
    1 ≤ lorentzFactor v := by
  have hpos := lorentzFactor_sqrt_arg_pos v hv
  have hγ_pos := lorentzFactor_pos v hv
  -- Suffices to show γ * sqrt(...) = 1 and sqrt(...) ≤ 1
  suffices h : lorentzFactor v * Real.sqrt (1 - v ^ 2 / c ^ 2) = 1 by
    have hsqrt_le : Real.sqrt (1 - v ^ 2 / c ^ 2) ≤ 1 := by
      calc Real.sqrt (1 - v ^ 2 / c ^ 2)
          ≤ Real.sqrt 1 := by
            apply Real.sqrt_le_sqrt
            have : 0 ≤ v ^ 2 / c ^ 2 := div_nonneg (sq_nonneg v) (sq_nonneg c)
            linarith
        _ = 1 := Real.sqrt_one
    nlinarith
  unfold lorentzFactor
  have hsqrt_ne : Real.sqrt (1 - v ^ 2 / c ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp

/-- Rest mass energy E₀ = mc². -/
noncomputable def restEnergy (m : ℝ) : ℝ := m * c^2

/-- Relativistic energy E = γmc². -/
noncomputable def relativisticEnergy (m v : ℝ) : ℝ :=
  lorentzFactor v * m * c^2

/-- Relativistic momentum p = γmv. -/
noncomputable def relativisticMomentum (m v : ℝ) : ℝ :=
  lorentzFactor v * m * v

/-- Energy-momentum relation: E² = (pc)² + (mc²)². -/
theorem energy_momentum_relation (m v : ℝ) (hv : v^2 < c^2) :
    (relativisticEnergy m v)^2 =
      (relativisticMomentum m v * c)^2 + (restEnergy m)^2 := by
  unfold relativisticEnergy relativisticMomentum restEnergy lorentzFactor
  have hc : c ≠ 0 := by unfold c; norm_num
  have hc2 : (c : ℝ) ^ 2 > 0 := by unfold c; norm_num
  have hpos : 1 - v ^ 2 / c ^ 2 > 0 := by
    have : v ^ 2 / c ^ 2 < 1 := by rwa [div_lt_one hc2]
    linarith
  have hsqrt_sq : Real.sqrt (1 - v ^ 2 / c ^ 2) ^ 2 = 1 - v ^ 2 / c ^ 2 :=
    Real.sq_sqrt hpos.le
  have hne : (1 - v ^ 2 / c ^ 2) ≠ 0 := ne_of_gt hpos
  simp only [mul_pow, one_div]
  rw [inv_pow, hsqrt_sq]
  -- Goal: (1 - v²/c²)⁻¹ * m² * (c²)² = (1 - v²/c²)⁻¹ * m² * v² * c² + m² * (c²)²
  field_simp
  -- Goal: c² * m² * (c² - v²)⁻¹ = m² + m² * v² * (c² - v²)⁻¹
  have hcv : c ^ 2 - v ^ 2 ≠ 0 := by nlinarith
  rw [eq_comm, ← sub_eq_zero]
  field_simp
  ring

end Measure.Physics.Relativity
