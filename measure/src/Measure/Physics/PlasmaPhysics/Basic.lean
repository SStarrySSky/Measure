/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Plasma physics fundamentals — Debye length, plasma frequency,
cyclotron motion, and plasma parameter.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Measure.Physics.PlasmaPhysics

/-! ## Physical Constants -/

/-- Vacuum permittivity ε₀ (F/m). -/
noncomputable def ε₀ : ℝ := 8.854187817e-12

/-- Boltzmann constant k_B (J/K). -/
noncomputable def k_B : ℝ := 1.380649e-23

/-- Vacuum permeability μ₀ (H/m). -/
noncomputable def μ₀ : ℝ := 1.2566370614e-6

/-- Elementary charge e (C). -/
noncomputable def e_charge : ℝ := 1.602176634e-19

/-- Electron mass m_e (kg). -/
noncomputable def m_e : ℝ := 9.1093837015e-31

/-- Proton mass m_p (kg). -/
noncomputable def m_p : ℝ := 1.67262192369e-27

/-! ## Plasma Parameters -/

/-- A plasma is characterized by its temperature, density, and magnetic field. -/
structure PlasmaParams where
  /-- Electron temperature T_e (K). -/
  T_e : ℝ
  /-- Electron number density n_e (m⁻³). -/
  n_e : ℝ
  /-- Ion number density n_i (m⁻³). -/
  n_i : ℝ
  /-- Magnetic field strength B (T). -/
  B : ℝ
  /-- Ion charge number Z. -/
  Z : ℕ
  /-- Ion mass m_i (kg). -/
  m_i : ℝ
  /-- Temperature is positive. -/
  T_pos : 0 < T_e
  /-- Electron density is positive. -/
  n_e_pos : 0 < n_e
  /-- Ion density is positive. -/
  n_i_pos : 0 < n_i
  /-- Ion mass is positive. -/
  m_i_pos : 0 < m_i

/-! ## Debye Length -/

/-- Debye length: λ_D = √(ε₀ k_B T / n q²).
    The characteristic screening distance in a plasma. -/
noncomputable def debyeLength (p : PlasmaParams) : ℝ :=
  Real.sqrt (ε₀ * k_B * p.T_e / (p.n_e * e_charge ^ 2))

/-- Debye length is positive for valid plasma parameters. -/
theorem debyeLength_pos (p : PlasmaParams) : 0 < debyeLength p := by
  unfold debyeLength
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · apply mul_pos (mul_pos _ _) p.T_pos
    · exact by unfold ε₀; positivity
    · exact by unfold k_B; positivity
  · exact mul_pos p.n_e_pos (by unfold e_charge; positivity)

/-! ## Plasma Frequency -/

/-- Electron plasma frequency: ω_pe = √(n_e e² / ε₀ m_e).
    The natural oscillation frequency of electrons in a plasma. -/
noncomputable def plasmaFreqElectron (p : PlasmaParams) : ℝ :=
  Real.sqrt (p.n_e * e_charge ^ 2 / (ε₀ * m_e))

/-- Ion plasma frequency: ω_pi = √(n_i (Ze)² / ε₀ m_i). -/
noncomputable def plasmaFreqIon (p : PlasmaParams) : ℝ :=
  Real.sqrt (p.n_i * (↑p.Z * e_charge) ^ 2 / (ε₀ * p.m_i))

/-- Plasma frequency is positive. -/
theorem plasmaFreqElectron_pos (p : PlasmaParams) : 0 < plasmaFreqElectron p := by
  unfold plasmaFreqElectron
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · exact mul_pos p.n_e_pos (by unfold e_charge; positivity)
  · exact mul_pos (by unfold ε₀; positivity) (by unfold m_e; positivity)

/-- Relation between Debye length and plasma frequency:
    λ_D · ω_pe = √(k_B T_e / m_e) (thermal velocity). -/
theorem debye_plasmaFreq_relation (p : PlasmaParams) :
    debyeLength p * plasmaFreqElectron p = Real.sqrt (k_B * p.T_e / m_e) := by
  unfold debyeLength plasmaFreqElectron
  rw [← Real.sqrt_mul (le_of_lt (div_pos (mul_pos (mul_pos (by unfold ε₀; positivity)
    (by unfold k_B; positivity)) p.T_pos) (mul_pos p.n_e_pos (by unfold e_charge; positivity))))]
  congr 1
  have hne : p.n_e ≠ 0 := ne_of_gt p.n_e_pos
  have he : (e_charge : ℝ) ≠ 0 := by unfold e_charge; positivity
  have he2 : e_charge ^ 2 ≠ 0 := pow_ne_zero _ he
  have hε₀ : (ε₀ : ℝ) ≠ 0 := by unfold ε₀; positivity
  have hme : (m_e : ℝ) ≠ 0 := by unfold m_e; positivity
  have hne_e2 : p.n_e * e_charge ^ 2 ≠ 0 := mul_ne_zero hne he2
  have hε₀_me : ε₀ * m_e ≠ 0 := mul_ne_zero hε₀ hme
  field_simp

/-! ## Cyclotron (Gyro) Frequency and Radius -/

/-- Electron cyclotron (gyro) frequency: ω_ce = eB / m_e. -/
noncomputable def cyclotronFreqElectron (p : PlasmaParams) : ℝ :=
  e_charge * p.B / m_e

/-- Ion cyclotron frequency: ω_ci = ZeB / m_i. -/
noncomputable def cyclotronFreqIon (p : PlasmaParams) : ℝ :=
  ↑p.Z * e_charge * p.B / p.m_i

/-- Electron gyroradius (Larmor radius): r_Le = v_⊥ / ω_ce.
    For thermal electrons, v_⊥ ~ √(k_B T_e / m_e). -/
noncomputable def gyroradiusElectron (p : PlasmaParams) : ℝ :=
  Real.sqrt (k_B * p.T_e / m_e) / cyclotronFreqElectron p

/-- Ion gyroradius: r_Li = v_⊥ / ω_ci. -/
noncomputable def gyroradiusIon (p : PlasmaParams) : ℝ :=
  Real.sqrt (k_B * p.T_e / p.m_i) / cyclotronFreqIon p

/-- The ion gyroradius is larger than the electron gyroradius
    (for same temperature and singly charged ions).
    Note: requires m_e < m_i which is physically always true but not
    captured in PlasmaParams. We add it as an additional hypothesis. -/
theorem gyroradius_ion_gt_electron (p : PlasmaParams)
    (hZ : p.Z = 1) (hB : 0 < p.B) (hm : m_e < p.m_i) :
    gyroradiusElectron p < gyroradiusIon p := by
  unfold gyroradiusElectron gyroradiusIon cyclotronFreqElectron cyclotronFreqIon
  simp only [hZ, Nat.cast_one, one_mul]
  have hme : (0 : ℝ) < m_e := by unfold m_e; positivity
  have he : (0 : ℝ) < e_charge := by unfold e_charge; positivity
  have hkT : 0 < k_B * p.T_e := mul_pos (by unfold k_B; positivity) p.T_pos
  have heB : 0 < e_charge * p.B := mul_pos he hB
  have hωe : 0 < e_charge * p.B / m_e := div_pos heB hme
  have hωi : 0 < e_charge * p.B / p.m_i := div_pos heB p.m_i_pos
  rw [div_lt_div_iff₀ hωe hωi]
  rw [mul_div_assoc', mul_div_assoc']
  rw [div_lt_div_iff₀ p.m_i_pos hme]
  -- Goal: √(kT/m_e) * (eB) * m_e < √(kT/m_i) * (eB) * m_i
  suffices h : Real.sqrt (k_B * p.T_e / m_e) * m_e < Real.sqrt (k_B * p.T_e / p.m_i) * p.m_i by
    nlinarith
  have hkT_nn := le_of_lt hkT
  rw [Real.sqrt_div hkT_nn, Real.sqrt_div hkT_nn, div_mul_comm, div_mul_comm (Real.sqrt (k_B * p.T_e))]
  apply mul_lt_mul_of_pos_right _ (Real.sqrt_pos_of_pos hkT)
  rw [div_lt_div_iff₀ (Real.sqrt_pos_of_pos hme) (Real.sqrt_pos_of_pos p.m_i_pos)]
  nlinarith [Real.sq_sqrt (le_of_lt hme), Real.sq_sqrt (le_of_lt p.m_i_pos),
    Real.sqrt_lt_sqrt (le_of_lt hme) hm,
    Real.sqrt_pos_of_pos hme, Real.sqrt_pos_of_pos p.m_i_pos,
    mul_pos (Real.sqrt_pos_of_pos hme) (Real.sqrt_pos_of_pos p.m_i_pos)]

/-! ## Plasma Parameter -/

/-- Plasma parameter: Λ = n_e λ_D³.
    The number of particles in a Debye sphere.
    For a valid plasma, Λ ≫ 1. -/
noncomputable def plasmaParameter (p : PlasmaParams) : ℝ :=
  p.n_e * debyeLength p ^ 3

/-- Coulomb logarithm: ln Λ. Appears in collision rates. -/
noncomputable def coulombLogarithm (p : PlasmaParams) : ℝ :=
  Real.log (plasmaParameter p)

/-- A system is a valid plasma if Λ ≫ 1 (we use Λ > 1 as minimum). -/
def IsPlasma (p : PlasmaParams) : Prop :=
  1 < plasmaParameter p

/-- Electron-electron collision frequency: ν_ee ~ ω_pe / Λ. -/
noncomputable def collisionFreq (p : PlasmaParams) : ℝ :=
  plasmaFreqElectron p / plasmaParameter p

/-- In a valid plasma, the collision frequency is much less than
    the plasma frequency. -/
theorem collision_lt_plasma (p : PlasmaParams) (hp : IsPlasma p) :
    collisionFreq p < plasmaFreqElectron p := by
  unfold collisionFreq IsPlasma at *
  have hω := plasmaFreqElectron_pos p
  have hΛ : 0 < plasmaParameter p := by linarith
  rw [div_lt_iff₀ hΛ]
  nlinarith

/-! ## Thermal Velocity -/

/-- Electron thermal velocity: v_te = √(k_B T_e / m_e). -/
noncomputable def thermalVelocityElectron (p : PlasmaParams) : ℝ :=
  Real.sqrt (k_B * p.T_e / m_e)

/-- Ion thermal velocity: v_ti = √(k_B T_e / m_i). -/
noncomputable def thermalVelocityIon (p : PlasmaParams) : ℝ :=
  Real.sqrt (k_B * p.T_e / p.m_i)

/-- Electron thermal velocity exceeds ion thermal velocity. -/
theorem thermal_electron_gt_ion (p : PlasmaParams)
    (hm : m_e < p.m_i) :
    thermalVelocityIon p < thermalVelocityElectron p := by
  unfold thermalVelocityIon thermalVelocityElectron
  apply Real.sqrt_lt_sqrt
  · apply le_of_lt; apply div_pos
    · exact mul_pos (by unfold k_B; positivity) p.T_pos
    · exact p.m_i_pos
  · apply div_lt_div_of_pos_left
    · exact mul_pos (by unfold k_B; positivity) p.T_pos
    · exact by unfold m_e; positivity
    · exact hm

end Measure.Physics.PlasmaPhysics
