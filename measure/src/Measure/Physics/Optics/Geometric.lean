/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Geometric optics — Snell's law, reflection, thin lens equation, magnification.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Measure.Physics.Optics

/-! ## Refractive index -/

/-- A medium characterized by its refractive index. -/
structure Medium where
  /-- Refractive index n ≥ 1. -/
  n : ℝ
  /-- Refractive index is positive. -/
  n_pos : 0 < n

/-! ## Snell's law (refraction) -/

/-- Snell's law: n₁ sin θ₁ = n₂ sin θ₂.
    Relates the angles of incidence and refraction at an interface. -/
noncomputable def SnellsLaw (m₁ m₂ : Medium) (θ₁ θ₂ : ℝ) : Prop :=
  m₁.n * Real.sin θ₁ = m₂.n * Real.sin θ₂

/-- The refracted angle given incident angle and two media.
    sin θ₂ = (n₁/n₂) sin θ₁. -/
noncomputable def refractedSinAngle (m₁ m₂ : Medium) (θ₁ : ℝ) : ℝ :=
  (m₁.n / m₂.n) * Real.sin θ₁

/-- Snell's law holds for the computed refracted angle. -/
theorem snells_law_refracted (m₁ m₂ : Medium) (θ₁ : ℝ) (h : m₂.n ≠ 0) :
    m₁.n * Real.sin θ₁ = m₂.n * refractedSinAngle m₁ m₂ θ₁ := by
  unfold refractedSinAngle
  field_simp

/-- Total internal reflection occurs when sin θ₂ > 1. -/
noncomputable def totalInternalReflection (m₁ m₂ : Medium) (θ₁ : ℝ) : Prop :=
  refractedSinAngle m₁ m₂ θ₁ > 1

/-- Critical angle: sin θ_c = n₂/n₁ (for n₁ > n₂). -/
noncomputable def criticalAngleSin (m₁ m₂ : Medium) : ℝ :=
  m₂.n / m₁.n

/-- Snell's law is symmetric: swapping the two sides gives an equivalent statement. -/
theorem snells_law_symm (m₁ m₂ : Medium) (θ₁ θ₂ : ℝ) :
    SnellsLaw m₁ m₂ θ₁ θ₂ ↔ SnellsLaw m₂ m₁ θ₂ θ₁ := by
  unfold SnellsLaw
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- At normal incidence (θ₁ = 0), Snell's law gives θ₂ = 0 (sin θ₂ = 0). -/
theorem snells_law_normal_incidence (m₁ m₂ : Medium) :
    SnellsLaw m₁ m₂ 0 0 := by
  unfold SnellsLaw
  simp [Real.sin_zero]

/-- Snell's law in the same medium implies equal sines of angles. -/
theorem snells_law_same_medium (m : Medium) (θ₁ θ₂ : ℝ)
    (h : SnellsLaw m m θ₁ θ₂) : Real.sin θ₁ = Real.sin θ₂ := by
  unfold SnellsLaw at h
  have hpos : m.n ≠ 0 := ne_of_gt m.n_pos
  exact mul_left_cancel₀ hpos h

/-- The critical angle sine is positive when both media have positive refractive indices. -/
theorem criticalAngleSin_pos (m₁ m₂ : Medium) :
    0 < criticalAngleSin m₁ m₂ := by
  unfold criticalAngleSin
  exact div_pos m₂.n_pos m₁.n_pos

/-- When n₁ > n₂, the critical angle sine is less than 1 (total internal reflection possible). -/
theorem criticalAngleSin_lt_one (m₁ m₂ : Medium) (h : m₂.n < m₁.n) :
    criticalAngleSin m₁ m₂ < 1 := by
  unfold criticalAngleSin
  rwa [div_lt_one m₁.n_pos]

/-- When n₁ = n₂, the critical angle sine equals 1 (no total internal reflection). -/
theorem criticalAngleSin_eq_one (m₁ m₂ : Medium) (h : m₁.n = m₂.n) :
    criticalAngleSin m₁ m₂ = 1 := by
  unfold criticalAngleSin
  rw [← h]
  exact div_self (ne_of_gt m₁.n_pos)

/-! ## Law of reflection -/

/-- Law of reflection: angle of incidence equals angle of reflection.
    θ_i = θ_r. -/
def ReflectionLaw (θ_incidence θ_reflection : ℝ) : Prop :=
  θ_incidence = θ_reflection

/-! ## Thin lens equation -/

/-- A thin lens characterized by its focal length. -/
structure ThinLens where
  /-- Focal length f. -/
  f : ℝ
  /-- Focal length is nonzero. -/
  f_ne_zero : f ≠ 0

/-- Thin lens equation: 1/f = 1/dₒ + 1/dᵢ
    where dₒ is object distance and dᵢ is image distance. -/
noncomputable def ThinLensEquation (lens : ThinLens) (d_obj d_img : ℝ) : Prop :=
  1 / lens.f = 1 / d_obj + 1 / d_img

/-- Image distance from the thin lens equation: dᵢ = f·dₒ/(dₒ - f). -/
noncomputable def imageDistance (lens : ThinLens) (d_obj : ℝ) : ℝ :=
  lens.f * d_obj / (d_obj - lens.f)

/-- The computed image distance satisfies the thin lens equation. -/
theorem thinLens_imageDistance (lens : ThinLens) (d_obj : ℝ)
    (hobj : d_obj ≠ 0) (_hdiff : d_obj - lens.f ≠ 0) (_himg : imageDistance lens d_obj ≠ 0) :
    ThinLensEquation lens d_obj (imageDistance lens d_obj) := by
  unfold ThinLensEquation imageDistance
  field_simp
  ring_nf
  have hf := lens.f_ne_zero
  field_simp at *
  ring

/-! ## Magnification -/

/-- Lateral magnification: M = -dᵢ/dₒ = hᵢ/hₒ. -/
noncomputable def magnification (d_obj d_img : ℝ) : ℝ :=
  -(d_img / d_obj)

/-- Magnification in terms of image and object heights. -/
noncomputable def magnificationHeight (h_obj h_img : ℝ) : ℝ :=
  h_img / h_obj

/-- |M| > 1 means the image is enlarged. -/
def isEnlarged (d_obj d_img : ℝ) : Prop :=
  |magnification d_obj d_img| > 1

/-- |M| < 1 means the image is diminished. -/
def isDiminished (d_obj d_img : ℝ) : Prop :=
  |magnification d_obj d_img| < 1

/-- M > 0 means the image is upright. -/
def isUpright (d_obj d_img : ℝ) : Prop :=
  magnification d_obj d_img > 0

/-- M < 0 means the image is inverted. -/
def isInverted (d_obj d_img : ℝ) : Prop :=
  magnification d_obj d_img < 0

/-! ## Lensmaker's equation -/

/-- Lensmaker's equation: 1/f = (n - 1)(1/R₁ - 1/R₂)
    where n is the refractive index and R₁, R₂ are radii of curvature. -/
noncomputable def LensmakersEquation (n f R₁ R₂ : ℝ) : Prop :=
  1 / f = (n - 1) * (1 / R₁ - 1 / R₂)

/-! ## Thin lens equation properties -/

/-- The thin lens equation is symmetric in object and image distances
    (swapping dₒ and dᵢ gives the same constraint). -/
theorem thinLens_symm (lens : ThinLens) (d_obj d_img : ℝ) :
    ThinLensEquation lens d_obj d_img ↔ ThinLensEquation lens d_img d_obj := by
  unfold ThinLensEquation
  constructor <;> intro h <;> linarith

/-- For an object at 2f, the image is also at 2f. -/
theorem thinLens_at_2f (lens : ThinLens) :
    ThinLensEquation lens (2 * lens.f) (2 * lens.f) := by
  unfold ThinLensEquation
  have hf : lens.f ≠ 0 := lens.f_ne_zero
  field_simp
  ring

/-- Magnification negates when object and image distances are swapped. -/
theorem magnification_swap (d_obj d_img : ℝ) (hobj : d_obj ≠ 0) (himg : d_img ≠ 0) :
    magnification d_obj d_img * magnification d_img d_obj = 1 := by
  unfold magnification
  field_simp

/-- Magnification at equal distances: M = -1 (inverted, same size). -/
theorem magnification_equal_distances (d : ℝ) (hd : d ≠ 0) :
    magnification d d = -1 := by
  unfold magnification
  rw [div_self hd]

/-- The image is inverted when object and image distances have the same sign. -/
theorem magnification_inverted_same_sign (d_obj d_img : ℝ)
    (hobj : 0 < d_obj) (himg : 0 < d_img) :
    isInverted d_obj d_img := by
  unfold isInverted magnification
  linarith [div_pos himg hobj]

end Measure.Physics.Optics
