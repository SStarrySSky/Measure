/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Semiconductor physics — Fermi-Dirac statistics, carrier concentrations,
pn junctions, diode equation, and energy band structure.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Measure.Physics.MaterialScience

/-! ## Physical Constants -/

/-- Boltzmann constant k_B ≈ 1.381 × 10⁻²³ J/K. -/
noncomputable def kB : ℝ := 1.380649e-23

/-- Elementary charge e ≈ 1.602 × 10⁻¹⁹ C. -/
noncomputable def elementaryCharge : ℝ := 1.602176634e-19

/-- Thermal voltage V_T = k_B T / q. -/
noncomputable def thermalVoltage (T : ℝ) : ℝ :=
  kB * T / elementaryCharge

/-! ## Fermi-Dirac Distribution -/

/-- The Fermi-Dirac distribution function:
    f(E) = 1 / (1 + exp((E - E_F) / (k_B T))).
    Gives the probability of occupation of a state at energy E. -/
noncomputable def fermiDirac (E_F : ℝ) (T : ℝ) (E : ℝ) : ℝ :=
  1 / (1 + Real.exp ((E - E_F) / (kB * T)))

/-- At the Fermi level, the occupation probability is exactly 1/2. -/
theorem fermiDirac_at_fermiLevel (E_F : ℝ) (T : ℝ) (_hT : 0 < T) :
    fermiDirac E_F T E_F = 1 / 2 := by
  simp [fermiDirac]
  norm_num

/-- The Fermi-Dirac distribution is bounded between 0 and 1. -/
theorem fermiDirac_bounded (E_F T E : ℝ) (_hT : 0 < T) :
    0 < fermiDirac E_F T E ∧ fermiDirac E_F T E < 1 := by
  constructor
  · unfold fermiDirac
    apply div_pos one_pos
    linarith [Real.exp_pos ((E - E_F) / (kB * T))]
  · unfold fermiDirac
    rw [div_lt_one (by linarith [Real.exp_pos ((E - E_F) / (kB * T))])]
    linarith [Real.exp_pos ((E - E_F) / (kB * T))]

/-- The Maxwell-Boltzmann approximation for E - E_F >> k_B T:
    f(E) ≈ exp(-(E - E_F) / (k_B T)). -/
noncomputable def boltzmannApprox (E_F : ℝ) (T : ℝ) (E : ℝ) : ℝ :=
  Real.exp (-(E - E_F) / (kB * T))

/-! ## Energy Band Structure -/

/-- A semiconductor band structure characterized by key energy levels. -/
structure SemiconductorBand where
  /-- Conduction band minimum energy E_c. -/
  E_c : ℝ
  /-- Valence band maximum energy E_v. -/
  E_v : ℝ
  /-- Band gap: E_c > E_v. -/
  gap_pos : E_v < E_c

/-- The band gap energy E_g = E_c - E_v. -/
noncomputable def SemiconductorBand.bandGap (band : SemiconductorBand) : ℝ :=
  band.E_c - band.E_v

/-- The band gap is positive. -/
theorem SemiconductorBand.bandGap_pos (band : SemiconductorBand) :
    0 < band.bandGap := by
  simp [SemiconductorBand.bandGap]
  linarith [band.gap_pos]

/-- The intrinsic Fermi level (midgap): E_i ≈ (E_c + E_v) / 2. -/
noncomputable def SemiconductorBand.intrinsicFermiLevel (band : SemiconductorBand) : ℝ :=
  (band.E_c + band.E_v) / 2

/-! ## Carrier Concentrations -/

/-- Effective density of states in the conduction band:
    N_c = 2(2π m_e* k_B T / h²)^{3/2}. -/
noncomputable def effectiveDOS_conduction (m_e_star : ℝ) (T : ℝ) (h : ℝ) : ℝ :=
  2 * (2 * Real.pi * m_e_star * kB * T / h ^ 2) ^ (3 / 2 : ℝ)

/-- Effective density of states in the valence band:
    N_v = 2(2π m_h* k_B T / h²)^{3/2}. -/
noncomputable def effectiveDOS_valence (m_h_star : ℝ) (T : ℝ) (h : ℝ) : ℝ :=
  2 * (2 * Real.pi * m_h_star * kB * T / h ^ 2) ^ (3 / 2 : ℝ)

/-- Electron concentration in the conduction band (non-degenerate approximation):
    n = N_c exp(-(E_c - E_F) / (k_B T)). -/
noncomputable def electronConcentration (N_c : ℝ) (band : SemiconductorBand)
    (E_F : ℝ) (T : ℝ) : ℝ :=
  N_c * Real.exp (-(band.E_c - E_F) / (kB * T))

/-- Hole concentration in the valence band (non-degenerate approximation):
    p = N_v exp(-(E_F - E_v) / (k_B T)). -/
noncomputable def holeConcentration (N_v : ℝ) (band : SemiconductorBand)
    (E_F : ℝ) (T : ℝ) : ℝ :=
  N_v * Real.exp (-(E_F - band.E_v) / (kB * T))

/-- The mass action law: np = n_i², independent of Fermi level.
    n_i² = N_c N_v exp(-E_g / (k_B T)). -/
noncomputable def intrinsicCarrierConcentrationSq (N_c N_v : ℝ)
    (band : SemiconductorBand) (T : ℝ) : ℝ :=
  N_c * N_v * Real.exp (-band.bandGap / (kB * T))

/-- The mass action law: n * p = n_i². -/
theorem massActionLaw (N_c N_v : ℝ) (band : SemiconductorBand) (E_F T : ℝ)
    (_hT : 0 < T) :
    electronConcentration N_c band E_F T * holeConcentration N_v band E_F T =
      intrinsicCarrierConcentrationSq N_c N_v band T := by
  simp only [electronConcentration, holeConcentration, intrinsicCarrierConcentrationSq,
    SemiconductorBand.bandGap]
  rw [show N_c * Real.exp (-(band.E_c - E_F) / (kB * T)) *
    (N_v * Real.exp (-(E_F - band.E_v) / (kB * T))) =
    N_c * N_v * (Real.exp (-(band.E_c - E_F) / (kB * T)) *
    Real.exp (-(E_F - band.E_v) / (kB * T))) from by ring]
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- Intrinsic carrier concentration: n_i = √(N_c N_v) exp(-E_g / (2 k_B T)). -/
noncomputable def intrinsicCarrierConcentration (N_c N_v : ℝ)
    (band : SemiconductorBand) (T : ℝ) : ℝ :=
  Real.sqrt (N_c * N_v) * Real.exp (-band.bandGap / (2 * kB * T))

/-! ## Doping -/

/-- Doping type classification. -/
inductive DopingType where
  /-- n-type: donor impurities, excess electrons. -/
  | nType
  /-- p-type: acceptor impurities, excess holes. -/
  | pType
  /-- Intrinsic: undoped semiconductor. -/
  | intrinsic

/-- A doped semiconductor with donor and acceptor concentrations. -/
structure DopedSemiconductor where
  /-- The underlying band structure. -/
  band : SemiconductorBand
  /-- Donor concentration N_D (cm⁻³). -/
  N_D : ℝ
  /-- Acceptor concentration N_A (cm⁻³). -/
  N_A : ℝ
  /-- Non-negative concentrations. -/
  hND : 0 ≤ N_D
  hNA : 0 ≤ N_A

/-- Classify doping type based on donor/acceptor concentrations. -/
noncomputable def DopedSemiconductor.dopingType (sc : DopedSemiconductor) : DopingType :=
  if sc.N_D > sc.N_A then .nType
  else if sc.N_A > sc.N_D then .pType
  else .intrinsic

/-- Majority carrier concentration for n-type (complete ionization):
    n ≈ N_D - N_A. -/
noncomputable def DopedSemiconductor.majorityElectrons (sc : DopedSemiconductor) : ℝ :=
  sc.N_D - sc.N_A

/-! ## PN Junction -/

/-- A pn junction formed by joining p-type and n-type regions. -/
structure PNJunction where
  /-- The semiconductor band structure. -/
  band : SemiconductorBand
  /-- Donor concentration on the n-side. -/
  N_D : ℝ
  /-- Acceptor concentration on the p-side. -/
  N_A : ℝ
  /-- Positive donor concentration. -/
  hND : 0 < N_D
  /-- Positive acceptor concentration. -/
  hNA : 0 < N_A

/-- Built-in potential of a pn junction:
    V_bi = (k_B T / q) ln(N_A N_D / n_i²). -/
noncomputable def PNJunction.builtInPotential (pn : PNJunction) (n_i : ℝ) (T : ℝ) : ℝ :=
  thermalVoltage T * Real.log (pn.N_A * pn.N_D / n_i ^ 2)

/-- Depletion width of a pn junction:
    W = √(2 ε_s V_bi (1/N_A + 1/N_D) / q). -/
noncomputable def PNJunction.depletionWidth (pn : PNJunction) (ε_s V_bi : ℝ) : ℝ :=
  Real.sqrt (2 * ε_s * V_bi * (1 / pn.N_A + 1 / pn.N_D) / elementaryCharge)

/-! ## Diode Equation -/

/-- The ideal diode (Shockley) equation:
    I = I₀ (exp(V / V_T) - 1).
    I₀ is the reverse saturation current, V is the applied voltage. -/
noncomputable def diodeCurrent (I₀ : ℝ) (V : ℝ) (T : ℝ) : ℝ :=
  I₀ * (Real.exp (V / thermalVoltage T) - 1)

/-- At zero bias, the diode current is zero. -/
theorem diodeCurrent_zero_bias (I₀ : ℝ) (T : ℝ) :
    diodeCurrent I₀ 0 T = 0 := by
  simp [diodeCurrent, thermalVoltage]

/-- Under large reverse bias (V << -V_T), I approaches -I₀.
    This is a fundamental property of the Shockley diode equation:
    as V → -∞, exp(V/V_T) → 0, so I → I₀(0-1) = -I₀.
    The proof shows |I - (-I₀)| = |I₀| · exp(V/V_T) → 0 using
    monotonicity of exp and the logarithm to find the cutoff V₀. -/
theorem diodeCurrent_reverse_limit (I₀ : ℝ) (T : ℝ) (hT : 0 < T) :
    ∀ ε > 0, ∃ V₀ < 0, ∀ V < V₀,
      |diodeCurrent I₀ V T - (-I₀)| < ε := by
  intro ε hε
  have hkB : (0 : ℝ) < kB := by unfold kB; norm_num
  have hVT : 0 < thermalVoltage T := by
    unfold thermalVoltage; unfold elementaryCharge
    apply div_pos (mul_pos hkB hT); norm_num
  by_cases hI₀ : I₀ = 0
  · refine ⟨-1, by linarith, fun V _ => ?_⟩
    simp [diodeCurrent, hI₀, hε]
  · have habs_pos : 0 < |I₀| := abs_pos.mpr hI₀
    have hdenom : 0 < |I₀| + 1 := by linarith
    set bound := ε / (|I₀| + 1) with hbound_def
    have hbound : 0 < bound := div_pos hε hdenom
    -- Use min to guarantee V₀ < 0
    set V₀ := min (-1) (thermalVoltage T * Real.log bound) with hV₀_def
    refine ⟨V₀, ?_, fun V hV => ?_⟩
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · have key : diodeCurrent I₀ V T - (-I₀) = I₀ * Real.exp (V / thermalVoltage T) := by
        unfold diodeCurrent; ring
      rw [key, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hV_le : V < thermalVoltage T * Real.log bound :=
        lt_of_lt_of_le hV (min_le_right _ _)
      have hVdiv : V / thermalVoltage T < Real.log bound := by
        rwa [div_lt_iff₀ hVT, mul_comm]
      have hexp_lt : Real.exp (V / thermalVoltage T) < bound := by
        calc Real.exp (V / thermalVoltage T)
            < Real.exp (Real.log bound) := Real.exp_lt_exp.mpr hVdiv
          _ = bound := Real.exp_log hbound
      have h_frac : |I₀| / (|I₀| + 1) < 1 := by
        rw [div_lt_one hdenom]; linarith
      calc |I₀| * Real.exp (V / thermalVoltage T)
          < |I₀| * bound := mul_lt_mul_of_pos_left hexp_lt habs_pos
        _ = |I₀| * (ε / (|I₀| + 1)) := by rw [hbound_def]
        _ = ε * (|I₀| / (|I₀| + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left h_frac hε
        _ = ε := mul_one ε

/-- The generalized diode equation with ideality factor n:
    I = I₀ (exp(V / (n V_T)) - 1). -/
noncomputable def diodeCurrentGeneral (I₀ : ℝ) (V : ℝ) (n : ℝ) (T : ℝ) : ℝ :=
  I₀ * (Real.exp (V / (n * thermalVoltage T)) - 1)

/-- The ideal diode equation is the special case n = 1. -/
theorem diodeCurrent_ideality_one (I₀ V T : ℝ) :
    diodeCurrentGeneral I₀ V 1 T = diodeCurrent I₀ V T := by
  simp [diodeCurrentGeneral, diodeCurrent]

/-! ## Semiconductor Classification -/

/-- Common semiconductor types by band gap. -/
inductive SemiconductorFamily where
  /-- Elemental: Si, Ge. -/
  | elemental
  /-- III-V compound: GaAs, InP, GaN. -/
  | iiiV
  /-- II-VI compound: ZnO, CdTe. -/
  | iiVI
  /-- IV-IV compound: SiC, SiGe. -/
  | ivIV

/-- Temperature dependence of band gap (Varshni equation):
    E_g(T) = E_g(0) - αT² / (T + β). -/
noncomputable def varshniGap (E_g0 α β T : ℝ) : ℝ :=
  E_g0 - α * T ^ 2 / (T + β)

/-- The Varshni gap at T = 0 equals E_g(0). -/
theorem varshniGap_zero_temp (E_g0 α β : ℝ) :
    varshniGap E_g0 α β 0 = E_g0 := by
  simp [varshniGap]

end Measure.Physics.MaterialScience
