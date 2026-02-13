/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Historical classical physics models that have been superseded by modern theories.
Each model is annotated with its originator, core assumptions, successor theory,
and the regime in which it remains a valid approximation.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Measure.Physics.Historical

/-! ## Luminiferous Aether Theory

Proposed to explain light propagation as a mechanical wave through a medium.
Superseded by special relativity (Einstein, 1905) after the Michelson-Morley
experiment (1887) found no evidence of aether drag. -/

/-- The luminiferous aether theory posited a universal medium for light waves.
    Proposed by Fresnel, Young, and others (early 19th century).
    Superseded by special relativity. No valid approximation regime. -/
structure AetherTheory where
  /-- Assumed aether density (kg/m³). -/
  aetherDensity : ℝ
  /-- Assumed aether rigidity (Pa), needed to support transverse waves. -/
  aetherRigidity : ℝ
  /-- Predicted speed of light through aether: v = √(rigidity/density). -/
  aetherDensity_pos : 0 < aetherDensity
  aetherRigidity_pos : 0 < aetherRigidity

/-- Predicted light speed in the aether frame. -/
noncomputable def AetherTheory.predictedLightSpeed (a : AetherTheory) : ℝ :=
  Real.sqrt (a.aetherRigidity / a.aetherDensity)

/-- Aether wind velocity: the velocity of the lab relative to the aether.
    Michelson-Morley predicted a fringe shift proportional to (v/c)².
    The null result refuted this prediction. -/
noncomputable def AetherTheory.fringeShift (a : AetherTheory) (v : ℝ) (L : ℝ) (wl : ℝ) : ℝ :=
  let cAether := a.predictedLightSpeed
  2 * L * v ^ 2 / (wl * cAether ^ 2)

/-! ## Caloric Theory

Heat was modeled as a self-repulsive, massless fluid ("caloric") that flows
from hot to cold bodies. Proposed by Lavoisier (1783).
Superseded by the mechanical theory of heat (Joule, Clausius, 1840s-1850s)
and modern thermodynamics. -/

/-- The caloric theory modeled heat as a conserved fluid.
    Proposed by Lavoisier (1783). Superseded by thermodynamics.
    Approximately valid for heat conduction problems where no work is done
    (pure conduction in Fourier's law). -/
structure CaloricTheory where
  /-- Amount of caloric fluid (analogous to heat content, in joules). -/
  caloricContent : ℝ
  /-- Temperature of the body (K). -/
  temperature : ℝ
  /-- Heat capacity (J/K), relating caloric to temperature. -/
  heatCapacity : ℝ
  heatCapacity_pos : 0 < heatCapacity
  temperature_pos : 0 < temperature

/-- Caloric flow rate between two bodies (Fourier-like conduction).
    This prediction remains valid as Fourier's law: Q̇ = k·A·(T₁-T₂)/d. -/
noncomputable def caloricFlowRate (k A T₁ T₂ d : ℝ) : ℝ :=
  k * A * (T₁ - T₂) / d

/-! ## Absolute Space and Time (Newton)

Newton's Principia (1687) assumed space and time are absolute, universal,
and independent of the observer. Superseded by special relativity (1905)
and general relativity (1915).
Valid approximation: v ≪ c and weak gravitational fields. -/

/-- Newtonian absolute spacetime: space and time are independent and universal.
    Proposed by Newton (1687). Superseded by special and general relativity.
    Valid when v ≪ c and gravitational potential Φ ≪ c². -/
structure AbsoluteSpacetime where
  /-- Spatial position in absolute space (ℝ³). -/
  position : Fin 3 → ℝ
  /-- Absolute time, universal for all observers. -/
  time : ℝ

/-- Galilean transformation between inertial frames.
    x' = x - vt, t' = t. Valid only when v ≪ c. -/
noncomputable def galileanTransform (x : Fin 3 → ℝ) (t : ℝ)
    (v : Fin 3 → ℝ) : AbsoluteSpacetime where
  position := fun i => x i - v i * t
  time := t

/-- Galilean velocity addition: u' = u - v.
    Approximate form of relativistic velocity addition when u, v ≪ c. -/
noncomputable def galileanVelocityAddition (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => u i + v i

/-! ## Ptolemaic Epicycle Model

Geocentric model using deferents and epicycles to describe planetary motion.
Proposed by Ptolemy (~150 CE), refined through the Middle Ages.
Superseded by Kepler's laws (1609-1619) and Newtonian gravity (1687).
As a Fourier-like decomposition, epicycles can approximate any periodic orbit
to arbitrary precision. -/

/-- An epicycle: a circle whose center moves on another circle (deferent).
    Ptolemy (~150 CE). Superseded by Kepler's elliptical orbits.
    Epicycles are equivalent to a Fourier series decomposition of periodic motion. -/
structure Epicycle where
  /-- Radius of the deferent (main circle). -/
  deferentRadius : ℝ
  /-- Angular frequency of the deferent (rad/s). -/
  deferentFreq : ℝ
  /-- Radius of the epicycle (secondary circle). -/
  epicycleRadius : ℝ
  /-- Angular frequency of the epicycle (rad/s). -/
  epicycleFreq : ℝ
  deferentRadius_pos : 0 < deferentRadius
  epicycleRadius_nonneg : 0 ≤ epicycleRadius

/-- Position predicted by a single epicycle model at time t.
    Returns (x, y) coordinates in the ecliptic plane. -/
noncomputable def Epicycle.position (e : Epicycle) (t : ℝ) : ℝ × ℝ :=
  let xDef := e.deferentRadius * Real.cos (e.deferentFreq * t)
  let yDef := e.deferentRadius * Real.sin (e.deferentFreq * t)
  let xEpi := e.epicycleRadius * Real.cos (e.epicycleFreq * t)
  let yEpi := e.epicycleRadius * Real.sin (e.epicycleFreq * t)
  (xDef + xEpi, yDef + yEpi)

/-- A general Ptolemaic model with N epicycles (Fourier decomposition). -/
structure PtolemaicModel (N : ℕ) where
  /-- Radii of each circular component. -/
  radii : Fin N → ℝ
  /-- Angular frequencies of each component. -/
  frequencies : Fin N → ℝ
  /-- Initial phases. -/
  phases : Fin N → ℝ

/-- Position from a general Ptolemaic model (sum of circular motions). -/
noncomputable def PtolemaicModel.position {N : ℕ} (m : PtolemaicModel N) (t : ℝ) : ℝ × ℝ :=
  (∑ k : Fin N, m.radii k * Real.cos (m.frequencies k * t + m.phases k),
   ∑ k : Fin N, m.radii k * Real.sin (m.frequencies k * t + m.phases k))

/-! ## Wave-Particle Duality (Historical Debate)

Newton's corpuscular theory (1704) vs Huygens' wave theory (1678).
Both were partially correct; unified by quantum mechanics (1920s)
through wave-particle duality and the de Broglie relation. -/

/-- Newton's corpuscular model: light as a stream of particles.
    Proposed by Newton (1704). Predicted wrong refraction behavior
    (faster in denser media). Partially vindicated by photon concept. -/
structure CorpuscularModel where
  /-- Particle mass (kg). -/
  mass : ℝ
  /-- Particle velocity (m/s). -/
  velocity : ℝ
  mass_pos : 0 < mass
  velocity_pos : 0 < velocity

/-- Corpuscular prediction for refraction: n = v₂/v₁ (wrong sign).
    Newton predicted light speeds up in denser media.
    Actual: n = v₁/v₂ (light slows down). -/
noncomputable def CorpuscularModel.refractionIndex (v₁ v₂ : ℝ) : ℝ :=
  v₂ / v₁

/-- Huygens' wave model: light as a wave in a medium.
    Proposed by Huygens (1678). Correctly predicted refraction.
    Superseded by electromagnetic wave theory (Maxwell, 1865)
    and quantum electrodynamics. -/
structure WaveModel where
  /-- Wavelength (m). -/
  wavelength : ℝ
  /-- Frequency (Hz). -/
  frequency : ℝ
  /-- Wave speed in the medium (m/s). -/
  speed : ℝ
  wavelength_pos : 0 < wavelength
  frequency_pos : 0 < frequency

/-- Wave model refraction: n = v₁/v₂ (correct). -/
noncomputable def WaveModel.refractionIndex (v₁ v₂ : ℝ) : ℝ :=
  v₁ / v₂

/-- De Broglie relation unifying wave and particle: λ = h/p.
    This relation from quantum mechanics (1924) resolved the debate. -/
noncomputable def deBroglieWavelength (h p : ℝ) : ℝ :=
  h / p

end Measure.Physics.Historical
