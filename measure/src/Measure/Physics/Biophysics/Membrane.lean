/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Membrane biophysics — Nernst equation, Goldman equation,
Hodgkin-Huxley model, and ion channel dynamics.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Measure.Physics.Biophysics

/-! ## Physical Constants and Ion Properties -/

/-- Physical constants for membrane biophysics. -/
structure MembraneConstants where
  /-- Gas constant R (J/(mol·K)). -/
  R : ℝ
  /-- Faraday constant F (C/mol). -/
  F : ℝ
  /-- Absolute temperature T (K). -/
  T : ℝ
  /-- R is positive. -/
  R_pos : 0 < R
  /-- F is positive. -/
  F_pos : 0 < F
  /-- T is positive. -/
  T_pos : 0 < T

/-- Standard physiological constants. -/
noncomputable def physiologicalConstants : MembraneConstants where
  R := 8.314
  F := 96485
  T := 310  -- 37°C in Kelvin
  R_pos := by norm_num
  F_pos := by norm_num
  T_pos := by norm_num

/-- Ion species with valence and concentrations. -/
structure IonSpecies where
  /-- Name of the ion (for documentation). -/
  name : String
  /-- Valence z (charge number, e.g., +1 for Na⁺, -1 for Cl⁻). -/
  z : ℤ
  /-- Extracellular concentration (mM). -/
  c_out : ℝ
  /-- Intracellular concentration (mM). -/
  c_in : ℝ
  /-- Valence is nonzero. -/
  z_ne_zero : z ≠ 0
  /-- Concentrations are positive. -/
  c_out_pos : 0 < c_out
  c_in_pos : 0 < c_in

/-! ## Nernst Equation -/

/-- The Nernst equation: E = (RT/zF) ln(c_out/c_in).
    Gives the equilibrium (reversal) potential for a single ion species. -/
noncomputable def nernstPotential (mc : MembraneConstants) (ion : IonSpecies) : ℝ :=
  (mc.R * mc.T / (ion.z * mc.F)) * Real.log (ion.c_out / ion.c_in)

/-- If extracellular concentration equals intracellular, the Nernst potential is zero. -/
theorem nernst_equal_concentrations (mc : MembraneConstants) (ion : IonSpecies)
    (heq : ion.c_out = ion.c_in) :
    nernstPotential mc ion = 0 := by
  simp [nernstPotential, heq]

/-- For a positive ion (z > 0), higher outside concentration gives positive Nernst potential. -/
theorem nernst_positive_ion_higher_outside (mc : MembraneConstants) (ion : IonSpecies)
    (hz : 0 < ion.z) (hc : ion.c_in < ion.c_out) :
    0 < nernstPotential mc ion := by
  unfold nernstPotential
  apply mul_pos
  · apply div_pos
    · exact mul_pos mc.R_pos mc.T_pos
    · exact mul_pos (Int.cast_pos.mpr hz) mc.F_pos
  · exact Real.log_pos ((one_lt_div ion.c_in_pos).mpr hc)

/-! ## Goldman Equation -/

/-- Permeability data for the Goldman equation. Each entry is
    (permeability, extracellular conc, intracellular conc, valence). -/
structure IonPermeability where
  /-- Membrane permeability P (m/s). -/
  P : ℝ
  /-- The ion species. -/
  ion : IonSpecies
  /-- Permeability is non-negative. -/
  P_nonneg : 0 ≤ P

/-- The Goldman-Hodgkin-Katz voltage equation for monovalent cations and anions.
    V_m = (RT/F) ln((Σ P_cation · c_out + Σ P_anion · c_in) /
                     (Σ P_cation · c_in + Σ P_anion · c_out)).
    Here we provide the general form with separate cation and anion lists. -/
noncomputable def goldmanEquation (mc : MembraneConstants)
    (cations : List IonPermeability) (anions : List IonPermeability) : ℝ :=
  let numerator := (cations.map fun ip => ip.P * ip.ion.c_out).sum +
                   (anions.map fun ip => ip.P * ip.ion.c_in).sum
  let denominator := (cations.map fun ip => ip.P * ip.ion.c_in).sum +
                     (anions.map fun ip => ip.P * ip.ion.c_out).sum
  (mc.R * mc.T / mc.F) * Real.log (numerator / denominator)

/-- When only one ion is permeable, the Goldman equation reduces to the Nernst equation. -/
theorem goldman_single_ion_is_nernst (mc : MembraneConstants)
    (ip : IonPermeability) (hz : ip.ion.z = 1) (hP : 0 < ip.P) :
    goldmanEquation mc [ip] [] = nernstPotential mc ip.ion := by
  unfold goldmanEquation nernstPotential
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  · rw [hz]; simp
  · congr 1
    rw [mul_div_mul_left _ _ (ne_of_gt hP)]

/-! ## Hodgkin-Huxley Model -/

/-- The state of a Hodgkin-Huxley neuron model. -/
structure HHState where
  /-- Membrane potential V (mV). -/
  V : ℝ
  /-- Na⁺ activation gating variable m ∈ [0,1]. -/
  m : ℝ
  /-- Na⁺ inactivation gating variable h ∈ [0,1]. -/
  h : ℝ
  /-- K⁺ activation gating variable n ∈ [0,1]. -/
  n : ℝ

/-- Parameters for the Hodgkin-Huxley model. -/
structure HHParams where
  /-- Membrane capacitance C_m (μF/cm²). -/
  C_m : ℝ
  /-- Maximum Na⁺ conductance g_Na (mS/cm²). -/
  g_Na : ℝ
  /-- Maximum K⁺ conductance g_K (mS/cm²). -/
  g_K : ℝ
  /-- Leak conductance g_L (mS/cm²). -/
  g_L : ℝ
  /-- Na⁺ reversal potential E_Na (mV). -/
  E_Na : ℝ
  /-- K⁺ reversal potential E_K (mV). -/
  E_K : ℝ
  /-- Leak reversal potential E_L (mV). -/
  E_L : ℝ
  /-- Capacitance is positive. -/
  C_m_pos : 0 < C_m

/-- Standard Hodgkin-Huxley parameters (squid giant axon). -/
noncomputable def hhStandardParams : HHParams where
  C_m := 1.0
  g_Na := 120.0
  g_K := 36.0
  g_L := 0.3
  E_Na := 50.0
  E_K := -77.0
  E_L := -54.387
  C_m_pos := by norm_num

/-- Na⁺ current: I_Na = g_Na · m³ · h · (V - E_Na). -/
noncomputable def naCurrentHH (p : HHParams) (s : HHState) : ℝ :=
  p.g_Na * s.m ^ 3 * s.h * (s.V - p.E_Na)

/-- K⁺ current: I_K = g_K · n⁴ · (V - E_K). -/
noncomputable def kCurrentHH (p : HHParams) (s : HHState) : ℝ :=
  p.g_K * s.n ^ 4 * (s.V - p.E_K)

/-- Leak current: I_L = g_L · (V - E_L). -/
noncomputable def leakCurrentHH (p : HHParams) (s : HHState) : ℝ :=
  p.g_L * (s.V - p.E_L)

/-- Total ionic current in the HH model. -/
noncomputable def totalIonicCurrentHH (p : HHParams) (s : HHState) : ℝ :=
  naCurrentHH p s + kCurrentHH p s + leakCurrentHH p s

/-- The Hodgkin-Huxley membrane equation:
    C_m dV/dt = I_ext - I_ion = I_ext - (I_Na + I_K + I_L). -/
noncomputable def HHMembraneEquation (p : HHParams)
    (state : ℝ → HHState) (I_ext : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    p.C_m * deriv (fun s => (state s).V) t =
      I_ext t - totalIonicCurrentHH p (state t)

/-! ## Ion Channel Gating Kinetics -/

/-- Rate functions α(V) and β(V) for a gating variable.
    The gating variable x satisfies dx/dt = α(V)(1-x) - β(V)x. -/
structure GatingRates where
  /-- Opening rate α(V). -/
  α : ℝ → ℝ
  /-- Closing rate β(V). -/
  β : ℝ → ℝ

/-- The gating variable ODE: dx/dt = α(V)(1-x) - β(V)x. -/
noncomputable def GatingEquation (rates : GatingRates)
    (V : ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    deriv x t = rates.α (V t) * (1 - x t) - rates.β (V t) * x t

/-- Steady-state value of a gating variable: x_∞(V) = α(V) / (α(V) + β(V)). -/
noncomputable def steadyStateGating (rates : GatingRates) (V : ℝ) : ℝ :=
  rates.α V / (rates.α V + rates.β V)

/-- Time constant of a gating variable: τ(V) = 1 / (α(V) + β(V)). -/
noncomputable def gatingTimeConstant (rates : GatingRates) (V : ℝ) : ℝ :=
  1 / (rates.α V + rates.β V)

/-- The gating equation can be rewritten as: dx/dt = (x_∞ - x) / τ. -/
theorem gating_equation_relaxation (rates : GatingRates) (V : ℝ) (x : ℝ)
    (hsum : rates.α V + rates.β V ≠ 0) :
    rates.α V * (1 - x) - rates.β V * x =
      (steadyStateGating rates V - x) / gatingTimeConstant rates V := by
  simp [steadyStateGating, gatingTimeConstant]
  field_simp
  ring

/-- The HH gating equations for all four variables (m, h, n). -/
noncomputable def HHGatingEquations (_p : HHParams)
    (state : ℝ → HHState)
    (m_rates h_rates n_rates : GatingRates) : Prop :=
  GatingEquation m_rates (fun t => (state t).V) (fun t => (state t).m) ∧
  GatingEquation h_rates (fun t => (state t).V) (fun t => (state t).h) ∧
  GatingEquation n_rates (fun t => (state t).V) (fun t => (state t).n)

/-- The full Hodgkin-Huxley system: membrane equation + gating equations. -/
noncomputable def HHSystem (p : HHParams) (state : ℝ → HHState)
    (I_ext : ℝ → ℝ) (m_rates h_rates n_rates : GatingRates) : Prop :=
  HHMembraneEquation p state I_ext ∧
  HHGatingEquations p state m_rates h_rates n_rates

/-- At rest (dV/dt = 0, no external current), the ionic currents balance. -/
theorem hh_resting_current_balance (p : HHParams) (s : HHState)
    (state : ℝ → HHState) (t₀ : ℝ)
    (hstate : state t₀ = s)
    (hmem : HHMembraneEquation p state (fun _ => 0))
    (hrest : deriv (fun s => (state s).V) t₀ = 0) :
    totalIonicCurrentHH p s = 0 := by
  have h := hmem t₀
  rw [hrest, mul_zero, hstate] at h
  linarith

end Measure.Physics.Biophysics
