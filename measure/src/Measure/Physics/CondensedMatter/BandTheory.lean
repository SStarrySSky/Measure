/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Band theory of solids — Bloch's theorem, energy bands, effective mass,
and classification of conductors, insulators, and semiconductors.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Measure.Physics.CondensedMatter.Crystal

namespace Measure.Physics.CondensedMatter

/-! ## Bloch's Theorem -/

/-- A Bloch wave function ψ_k(r) = e^{ik·r} u_k(r) where u_k has the
    periodicity of the lattice. -/
structure BlochWave (L : BravaisLattice) where
  /-- Crystal momentum vector k. -/
  k : Vec3
  /-- The periodic part u_k(r) : ℝ³ → ℂ. -/
  u : Vec3 → ℂ
  /-- Periodicity: u_k(r + R) = u_k(r) for all lattice vectors R. -/
  periodic : ∀ (n : Fin 3 → ℤ) (r : Vec3),
    u (fun i => r i + L.point n i) = u r

/-- The full Bloch wave function ψ_k(r) = e^{ik·r} u_k(r). -/
noncomputable def BlochWave.eval {L : BravaisLattice} (ψ : BlochWave L) (r : Vec3) : ℂ :=
  Complex.exp (↑(∑ i : Fin 3, ψ.k i * r i) * Complex.I) * ψ.u r

/-- Bloch's theorem: the wave function picks up a phase e^{ik·R} under
    lattice translation. This follows from the periodicity of u_k and
    the factorization of the complex exponential e^{ik·(r+R)} = e^{ik·R} · e^{ik·r}. -/
theorem bloch_theorem (L : BravaisLattice) (ψ : BlochWave L)
    (n : Fin 3 → ℤ) (r : Vec3) :
    ψ.eval (fun i => r i + L.point n i) =
      Complex.exp (↑(∑ i : Fin 3, ψ.k i * L.point n i) * Complex.I) * ψ.eval r := by
  unfold BlochWave.eval
  rw [ψ.periodic n r]
  have hsum : (∑ i : Fin 3, ψ.k i * (r i + L.point n i)) =
    (∑ i : Fin 3, ψ.k i * L.point n i) + (∑ i : Fin 3, ψ.k i * r i) := by
    rw [← Finset.sum_add_distrib]; congr 1; ext i; ring
  rw [show (fun i => r i + L.point n i) = (fun i => r i + L.point n i) from rfl]
  simp only [hsum]
  push_cast
  rw [add_mul, Complex.exp_add, mul_assoc]

/-! ## Energy Band Structure -/

/-- An energy band: for each crystal momentum k in the BZ, gives an energy E_n(k).
    The band index n labels different bands. -/
structure EnergyBand (L : BravaisLattice) where
  /-- Band index. -/
  index : ℕ
  /-- Energy as a function of crystal momentum: E_n(k). -/
  energy : Vec3 → ℝ

/-- The band gap between two bands is the minimum energy difference. -/
noncomputable def bandGap (L : BravaisLattice) (lower upper : EnergyBand L) : ℝ :=
  ⨅ k : Vec3, upper.energy k - ⨆ k : Vec3, lower.energy k

/-- A band gap is direct if the minimum of the upper band and maximum of the
    lower band occur at the same k-point. -/
def IsDirectGap (L : BravaisLattice) (lower upper : EnergyBand L)
    (k₀ : Vec3) : Prop :=
  (∀ k, lower.energy k ≤ lower.energy k₀) ∧
  (∀ k, upper.energy k₀ ≤ upper.energy k)

/-- A band gap is indirect if it is not direct at any k-point. -/
def IsIndirectGap (L : BravaisLattice) (lower upper : EnergyBand L) : Prop :=
  ¬ ∃ k₀, IsDirectGap L lower upper k₀

/-! ## Material Classification -/

/-- Classification of crystalline solids by their electronic band structure. -/
inductive MaterialType where
  /-- Conductor: partially filled band or overlapping bands. -/
  | conductor
  /-- Insulator: large band gap (> ~4 eV). -/
  | insulator
  /-- Semiconductor: small band gap (< ~4 eV). -/
  | semiconductor
  /-- Semimetal: small overlap between valence and conduction bands. -/
  | semimetal

/-- A band structure consisting of a valence band and conduction band. -/
structure BandStructure (L : BravaisLattice) where
  /-- The highest occupied (valence) band. -/
  valence : EnergyBand L
  /-- The lowest unoccupied (conduction) band. -/
  conduction : EnergyBand L

/-- The fundamental gap of a band structure. -/
noncomputable def BandStructure.gap {L : BravaisLattice} (bs : BandStructure L) : ℝ :=
  bandGap L bs.valence bs.conduction

/-- Classify a material based on its band gap (in eV).
    Gap > 4 eV → insulator, 0 < gap ≤ 4 eV → semiconductor,
    gap ≤ 0 → conductor. -/
noncomputable def BandStructure.classify {L : BravaisLattice} (bs : BandStructure L) :
    MaterialType :=
  if bs.gap > 4 then .insulator
  else if bs.gap > 0 then .semiconductor
  else .conductor

/-! ## Effective Mass -/

/-- The inverse effective mass tensor (1/m*)ᵢⱼ = (1/ℏ²) ∂²E/∂kᵢ∂kⱼ.
    Evaluated at a specific k-point. -/
noncomputable def invEffectiveMassTensor {L : BravaisLattice} (band : EnergyBand L)
    (k₀ : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    deriv (fun ki =>
      deriv (fun kj =>
        band.energy (Function.update (Function.update k₀ j kj) i ki)
      ) (k₀ j)
    ) (k₀ i)

/-- Scalar effective mass for an isotropic band at a band extremum.
    m* = ℏ² / (∂²E/∂k²). -/
noncomputable def effectiveMass {L : BravaisLattice} (band : EnergyBand L) (k₀ : Vec3)
    (dir : Fin 3) : ℝ :=
  1 / invEffectiveMassTensor band k₀ dir dir

/-- Positive effective mass at a band minimum (conduction band). -/
def IsEffectiveMassPositive {L : BravaisLattice} (band : EnergyBand L) (k₀ : Vec3) : Prop :=
  ∀ i : Fin 3, 0 < invEffectiveMassTensor band k₀ i i

/-- Negative effective mass at a band maximum (valence band / holes). -/
def IsEffectiveMassNegative {L : BravaisLattice} (band : EnergyBand L) (k₀ : Vec3) : Prop :=
  ∀ i : Fin 3, invEffectiveMassTensor band k₀ i i < 0

/-! ## Fermi Level -/

/-- The Fermi-Dirac distribution f(E) = 1 / (1 + exp((E - μ) / k_B T)). -/
noncomputable def fermiDirac (μ T kB E : ℝ) : ℝ :=
  1 / (1 + Real.exp ((E - μ) / (kB * T)))

/-- Boltzmann constant k_B. -/
noncomputable def kB : ℝ := 1.380649e-23

/-- At zero temperature, the Fermi-Dirac distribution becomes a step function.
    For E < μ, as T → 0⁺, f(E) → 1. As T → 0⁺ with E < μ, the exponent
    (E - μ)/(kB T) → -∞, so exp → 0 and 1/(1 + exp) → 1.
    The proof bounds |f - 1| ≤ exp((E-μ)/(kB T)) and uses monotonicity of exp. -/
theorem fermiDirac_zero_temp_below (μ E : ℝ) (hE : E < μ) :
    ∀ ε > 0, ∃ T₀ > 0, ∀ T : ℝ, 0 < T → T < T₀ →
      |fermiDirac μ T kB E - 1| < ε := by
  intro ε hε
  have hkB : (0 : ℝ) < kB := by unfold kB; norm_num
  have hμE : 0 < μ - E := by linarith
  -- We need exp((E - μ)/(kB * T)) < ε.
  -- Choose T₀ so that (E - μ)/(kB * T₀) = log(min ε 1 / 2), ensuring exp < ε.
  -- Simpler: choose T₀ = (μ - E) / (kB * |log(min ε 1)|) but let's use a direct bound.
  -- For T small enough, exp((E-μ)/(kB*T)) < ε. We need (E-μ)/(kB*T) < log ε (when ε < 1)
  -- or just exp < 1 < ε (when ε ≥ 1). Use min to handle both cases.
  set ε' := min ε (1/2) with hε'_def
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hε'_lt_one : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  -- log(ε') < 0 since ε' < 1
  have hlog_neg : Real.log ε' < 0 := Real.log_neg hε' hε'_lt_one
  have hlog_neg' : 0 < -Real.log ε' := neg_pos.mpr hlog_neg
  -- Choose T₀ = (μ - E) / (kB * (-log ε'))
  set T₀ := (μ - E) / (kB * (-Real.log ε')) with hT₀_def
  have hT₀ : 0 < T₀ := div_pos hμE (mul_pos hkB hlog_neg')
  refine ⟨T₀, hT₀, fun T hT hTT₀ => ?_⟩
  -- First simplify |fermiDirac - 1|
  have hkBT : 0 < kB * T := mul_pos hkB hT
  have hexp_pos := Real.exp_pos ((E - μ) / (kB * T))
  have hdenom_pos : 0 < 1 + Real.exp ((E - μ) / (kB * T)) := by linarith
  have hfrac : fermiDirac μ T kB E - 1 =
      -Real.exp ((E - μ) / (kB * T)) / (1 + Real.exp ((E - μ) / (kB * T))) := by
    unfold fermiDirac
    field_simp
    ring
  rw [hfrac, abs_div, abs_neg, abs_of_pos hexp_pos, abs_of_pos hdenom_pos]
  -- exp(x)/(1 + exp(x)) < exp(x) since 1 + exp(x) > 1
  have hbound : Real.exp ((E - μ) / (kB * T)) / (1 + Real.exp ((E - μ) / (kB * T))) <
      Real.exp ((E - μ) / (kB * T)) := by
    apply div_lt_self hexp_pos
    linarith
  apply lt_of_lt_of_le hbound
  -- Now show exp((E - μ)/(kB * T)) ≤ ε
  -- From T < T₀ = (μ - E)/(kB * (-log ε')), we get kB * T * (-log ε') < μ - E
  -- i.e., (E - μ)/(kB * T) < log ε', so exp((E-μ)/(kB*T)) < ε' ≤ ε
  have hT_bound : T < (μ - E) / (kB * (-Real.log ε')) := hTT₀
  have hkBnlog : 0 < kB * (-Real.log ε') := mul_pos hkB hlog_neg'
  have h1 : T * (kB * (-Real.log ε')) < μ - E := by
    rwa [lt_div_iff₀ hkBnlog] at hT_bound
  have h2 : (E - μ) / (kB * T) < Real.log ε' := by
    rw [div_lt_iff₀ hkBT]
    nlinarith
  have h3 : Real.exp ((E - μ) / (kB * T)) < ε' :=
    (Real.exp_lt_exp.mpr h2).trans_le (Real.exp_log hε').le
  linarith

/-- The Fermi energy of a free electron gas with density n.
    E_F = (ℏ²/2m)(3π²n)^{2/3}. -/
noncomputable def fermiEnergy (n m hbar : ℝ) : ℝ :=
  (hbar ^ 2 / (2 * m)) * (3 * Real.pi ^ 2 * n) ^ ((2 : ℝ) / 3)

/-- The density of states for a 3D free electron gas: g(E) = (V/2π²)(2m/ℏ²)^{3/2} √E. -/
noncomputable def densityOfStates3D (V m hbar E : ℝ) : ℝ :=
  (V / (2 * Real.pi ^ 2)) * (2 * m / hbar ^ 2) ^ ((3 : ℝ) / 2) * Real.sqrt E

end Measure.Physics.CondensedMatter
