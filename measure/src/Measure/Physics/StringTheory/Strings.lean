/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

String theory foundations — worldsheet actions, boundary conditions, vibrational modes.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Measure.Physics.StringTheory

/-! ## Spacetime and worldsheet coordinates -/

/-- Target spacetime dimension. -/
abbrev SpacetimeDim := ℕ

/-- A point in D-dimensional target spacetime X^mu(sigma, tau). -/
abbrev TargetMap (D : SpacetimeDim) := ℝ → ℝ → (Fin D → ℝ)

/-- Worldsheet coordinates (sigma, tau). -/
structure WorldsheetPoint where
  /-- Spatial coordinate along the string. -/
  sigma : ℝ
  /-- Worldsheet time coordinate. -/
  tau : ℝ

/-! ## String tension and Regge slope -/

/-- String tension T and Regge slope alpha' with the relation T = 1/(2 pi alpha'). -/
structure StringParams where
  /-- Regge slope alpha' (dimension length squared). -/
  alphaPrime : ℝ
  /-- Regge slope is positive. -/
  alphaPrime_pos : 0 < alphaPrime

/-- String tension T = 1/(2 pi alpha'). -/
noncomputable def StringParams.tension (p : StringParams) : ℝ :=
  1 / (2 * Real.pi * p.alphaPrime)

/-- String length ls = sqrt(2 alpha'). -/
noncomputable def StringParams.stringLength (p : StringParams) : ℝ :=
  Real.sqrt (2 * p.alphaPrime)

/-- Tension is positive. -/
theorem StringParams.tension_pos (p : StringParams) : 0 < p.tension := by
  unfold StringParams.tension
  apply div_pos one_pos
  apply mul_pos
  · apply mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos
  · exact p.alphaPrime_pos

/-! ## Critical dimensions -/

/-- Bosonic string critical dimension D = 26. -/
def bosonicCriticalDim : SpacetimeDim := 26

/-- Superstring critical dimension D = 10. -/
def superstringCriticalDim : SpacetimeDim := 10

/-- M-theory dimension D = 11. -/
def mTheoryDim : SpacetimeDim := 11

/-! ## Worldsheet actions -/

/-- Nambu-Goto integrand: sqrt of minus the determinant of the induced worldsheet metric. -/
noncomputable def nambuGotoIntegrand {D : SpacetimeDim}
    (X : TargetMap D) (t s : ℝ) : ℝ :=
  let dXdt := fun mu => deriv (fun t' => X t' s mu) t
  let dXds := fun mu => deriv (fun s' => X t s' mu) s
  let dotTT := ∑ mu : Fin D, dXdt mu * dXdt mu
  let dotSS := ∑ mu : Fin D, dXds mu * dXds mu
  let dotTS := ∑ mu : Fin D, dXdt mu * dXds mu
  Real.sqrt (-(dotTT * dotSS - dotTS ^ 2))

/-- The Nambu-Goto action for a string propagating in D-dimensional spacetime.
    S_NG = -T integral d tau d sigma sqrt(-det h_ab)
    where h_ab = partial_a X^mu partial_b X_mu is the induced metric on the worldsheet. -/
noncomputable def nambuGotoAction (p : StringParams) {D : SpacetimeDim}
    (X : TargetMap D) (t1 t2 s1 s2 : ℝ) : ℝ :=
  -p.tension * (∫ t in t1..t2, ∫ s in s1..s2, nambuGotoIntegrand X t s)

/-- The worldsheet metric for the Polyakov action. -/
abbrev WorldsheetMetric := Matrix (Fin 2) (Fin 2) ℝ

/-- Polyakov integrand at a worldsheet point. -/
noncomputable def polyakovIntegrand {D : SpacetimeDim}
    (X : TargetMap D) (h : ℝ → ℝ → WorldsheetMetric) (t s : ℝ) : ℝ :=
  let dXdt := fun mu => deriv (fun t' => X t' s mu) t
  let dXds := fun mu => deriv (fun s' => X t s' mu) s
  let partialX := fun (a : Fin 2) (mu : Fin D) =>
    match a with
    | ⟨0, _⟩ => dXdt mu
    | ⟨1, _⟩ => dXds mu
  let hMat : Matrix (Fin 2) (Fin 2) ℝ := h t s
  let hInv := hMat⁻¹
  Real.sqrt (-Matrix.det hMat) *
    (∑ a : Fin 2, ∑ b : Fin 2, hInv a b *
      ∑ mu : Fin D, partialX a mu * partialX b mu)

/-- The Polyakov action: S_P = -(T/2) integral d tau d sigma sqrt(-det h) h^ab partial_a X^mu partial_b X_mu.
    Classically equivalent to Nambu-Goto but easier to quantize. -/
noncomputable def polyakovAction (p : StringParams) {D : SpacetimeDim}
    (X : TargetMap D) (h : ℝ → ℝ → WorldsheetMetric) (t1 t2 s1 s2 : ℝ) : ℝ :=
  -(p.tension / 2) * (∫ t in t1..t2, ∫ s in s1..s2, polyakovIntegrand X h t s)

/-! ## Boundary conditions -/

/-- Open string with Neumann boundary conditions: partial_sigma X^mu = 0 at endpoints. -/
def NeumannBC {D : SpacetimeDim} (X : TargetMap D) (s0 : ℝ) : Prop :=
  ∀ t : ℝ, ∀ mu : Fin D, deriv (fun s => X t s mu) s0 = 0

/-- Open string with Dirichlet boundary conditions: X^mu = const at endpoints.
    The string endpoint is fixed on a D-brane. -/
def DirichletBC {D : SpacetimeDim} (X : TargetMap D) (s0 : ℝ) (pos : Fin D → ℝ) : Prop :=
  ∀ t : ℝ, ∀ mu : Fin D, X t s0 mu = pos mu

/-- Closed string periodic boundary conditions: X^mu(sigma + pi, tau) = X^mu(sigma, tau). -/
def ClosedStringBC {D : SpacetimeDim} (X : TargetMap D) : Prop :=
  ∀ t s : ℝ, X t (s + Real.pi) = X t s

/-- Open string boundary conditions: Neumann at both endpoints sigma = 0 and sigma = pi. -/
structure OpenStringNeumann {D : SpacetimeDim} (X : TargetMap D) : Prop where
  /-- Neumann at sigma = 0. -/
  left : NeumannBC X 0
  /-- Neumann at sigma = pi. -/
  right : NeumannBC X Real.pi

/-- A Dp-brane is a (p+1)-dimensional hypersurface on which open strings can end.
    Directions 0..p have Neumann BC, directions (p+1)..D-1 have Dirichlet BC. -/
structure DpBrane (D : SpacetimeDim) where
  /-- Spatial dimension of the brane. -/
  p : ℕ
  /-- p < D. -/
  p_lt : p < D
  /-- Position of the brane in transverse directions. -/
  transversePos : Fin D → ℝ

/-! ## Vibrational modes and mode expansion -/

/-- Mode coefficients for the string expansion.
    X^mu(sigma,tau) = x^mu + p^mu tau + i sqrt(alpha'/2) Sum (alpha_n/n) e^{-in tau} cos(n sigma). -/
structure ModeExpansion (D : SpacetimeDim) where
  /-- Center of mass position x^mu. -/
  x0 : Fin D → ℝ
  /-- Center of mass momentum p^mu. -/
  p0 : Fin D → ℝ
  /-- Oscillator modes alpha_n^mu (n in Z, n != 0). -/
  oscModes : ℤ → Fin D → ℝ

/-- Closed string has independent left-movers and right-movers. -/
structure ClosedStringModes (D : SpacetimeDim) where
  /-- Center of mass position. -/
  x0 : Fin D → ℝ
  /-- Center of mass momentum. -/
  p0 : Fin D → ℝ
  /-- Right-moving oscillator modes. -/
  alphaR : ℤ → Fin D → ℝ
  /-- Left-moving oscillator modes. -/
  alphaL : ℤ → Fin D → ℝ

/-- Mass-shell condition for open bosonic string:
    M^2 = (1/alpha')(N - 1) where N is the level number. -/
noncomputable def openStringMassSq (p : StringParams) (N : ℕ) : ℝ :=
  (1 / p.alphaPrime) * ((N : ℝ) - 1)

/-- Mass-shell condition for closed bosonic string:
    M^2 = (2/alpha')(N + Ntilde - 2) with level matching N = Ntilde. -/
noncomputable def closedStringMassSq (p : StringParams) (N Ntilde : ℕ) : ℝ :=
  (2 / p.alphaPrime) * ((N : ℝ) + (Ntilde : ℝ) - 2)

/-- Level matching condition for closed strings: N = Ntilde. -/
def LevelMatching {D : SpacetimeDim} (_modes : ClosedStringModes D) (N Ntilde : ℕ) : Prop :=
  N = Ntilde

/-- The open string tachyon at N = 0 has M^2 = -1/alpha' < 0. -/
theorem openString_tachyon (p : StringParams) :
    openStringMassSq p 0 < 0 := by
  unfold openStringMassSq
  simp
  exact p.alphaPrime_pos

/-- The first excited state N = 1 is massless (gauge boson). -/
theorem openString_massless_level (p : StringParams) :
    openStringMassSq p 1 = 0 := by
  unfold openStringMassSq
  simp

/-! ## String spectrum classification -/

/-- Classification of string states by mass. -/
inductive StringState where
  /-- Tachyonic state (M^2 < 0), signals instability. -/
  | tachyon
  /-- Massless state (M^2 = 0), includes gauge bosons and graviton. -/
  | massless
  /-- Massive state (M^2 > 0), tower of massive excitations. -/
  | massive (level : ℕ)

/-- The closed string massless sector contains the graviton (spin-2),
    the Kalb-Ramond B-field (antisymmetric tensor), and the dilaton (scalar). -/
inductive MasslessClosedState where
  /-- Graviton g_mn: symmetric traceless tensor. -/
  | graviton
  /-- Kalb-Ramond field B_mn: antisymmetric tensor. -/
  | kalbRamond
  /-- Dilaton: scalar field. -/
  | dilaton

end Measure.Physics.StringTheory
