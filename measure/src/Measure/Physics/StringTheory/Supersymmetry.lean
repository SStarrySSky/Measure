/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Supersymmetry — super-Poincare algebra, superpartners, SUSY breaking, MSSM spectrum.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Measure.Physics.StringTheory

/-! ## Super-Poincare algebra -/

/-- Number of supercharges N (N=1 minimal SUSY, N=2 extended, etc.). -/
abbrev SUSYOrder := ℕ

/-- A Weyl spinor index (2-component). -/
abbrev WeylIndex := Fin 2

/-- Supercharge Q_α (left-handed Weyl spinor). -/
structure Supercharge where
  /-- Spinor components of the supercharge. -/
  components : WeylIndex → ℂ

/-- Conjugate supercharge Q-bar (right-handed Weyl spinor). -/
structure ConjSupercharge where
  /-- Spinor components of the conjugate supercharge. -/
  components : WeylIndex → ℂ

/-- The super-Poincare algebra relations.
    Key anticommutation relation: {Q_α, Q-bar_β} = 2 σ^μ_{αβ} P_μ
    where σ^μ are the Pauli matrices and P_μ is the 4-momentum. -/
structure SuperPoincareAlgebra where
  /-- Number of supercharges. -/
  susyN : SUSYOrder
  /-- Supercharges Q^I_α, I = 1..N. -/
  charges : Fin susyN → Supercharge
  /-- Conjugate supercharges. -/
  conjCharges : Fin susyN → ConjSupercharge
  /-- Central charges Z^{IJ} (antisymmetric, relevant for N >= 2). -/
  centralZ : Fin susyN → Fin susyN → ℂ
  /-- Central charges are antisymmetric. -/
  Z_antisymm : ∀ I J, centralZ I J = -centralZ J I

/-- The SUSY algebra anticommutation relation (schematic):
    {Q_α, Q-bar_β} = 2 σ^μ_{αβ} P_μ.
    This encodes that SUSY is the "square root" of translations. -/
def susyAnticommRelation (P : Fin 4 → ℝ) (sigma : Fin 4 → Matrix WeylIndex WeylIndex ℂ)
    (q : Supercharge) (qbar : ConjSupercharge) : Prop :=
  ∀ a b : WeylIndex,
    q.components a * qbar.components b + qbar.components b * q.components a =
    2 * ∑ mu : Fin 4, sigma mu a b * (P mu : ℂ)

/-- Pauli matrices σ^μ = (I, σ1, σ2, σ3). -/
noncomputable def pauliMatrices : Fin 4 → Matrix WeylIndex WeylIndex ℂ :=
  fun mu => match mu with
  | ⟨0, _⟩ => 1  -- identity
  | ⟨1, _⟩ => Matrix.of (fun i j =>
      match i, j with | ⟨0,_⟩, ⟨1,_⟩ => 1 | ⟨1,_⟩, ⟨0,_⟩ => 1 | _, _ => 0)
  | ⟨2, _⟩ => Matrix.of (fun i j =>
      match i, j with | ⟨0,_⟩, ⟨1,_⟩ => -Complex.I | ⟨1,_⟩, ⟨0,_⟩ => Complex.I | _, _ => 0)
  | ⟨3, _⟩ => Matrix.of (fun i j =>
      match i, j with | ⟨0,_⟩, ⟨0,_⟩ => 1 | ⟨1,_⟩, ⟨1,_⟩ => -1 | _, _ => 0)

/-! ## Superpartners -/

/-- Spin of a particle (in units of hbar). -/
abbrev ParticleSpin := ℚ

/-- A particle in the SUSY spectrum. -/
structure SUSYParticle where
  /-- Name of the particle. -/
  name : String
  /-- Spin. -/
  spin : ParticleSpin
  /-- Mass (GeV). -/
  mass : ℝ
  /-- Electric charge (units of e). -/
  charge : ℚ
  /-- Color representation dimension (1 = singlet, 3 = triplet, 8 = octet). -/
  colorDim : ℕ
  /-- R-parity: +1 for SM particles, -1 for superpartners. -/
  rParity : Int

/-- A SUSY multiplet pairs a boson with a fermion. -/
structure Supermultiplet where
  /-- The Standard Model particle. -/
  smParticle : SUSYParticle
  /-- The superpartner. -/
  superpartner : SUSYParticle
  /-- Spins differ by 1/2. -/
  spin_relation : superpartner.spin = smParticle.spin + 1/2 ∨
                  superpartner.spin = smParticle.spin - 1/2
  /-- R-parity is opposite. -/
  rParity_opposite : superpartner.rParity = -smParticle.rParity

/-! ## MSSM particle spectrum -/

/-- Chiral supermultiplet: pairs a Weyl fermion with a complex scalar. -/
structure ChiralMultiplet where
  /-- Fermion (spin 1/2). -/
  fermion : SUSYParticle
  /-- Scalar superpartner (spin 0). -/
  scalar : SUSYParticle
  /-- Fermion has spin 1/2. -/
  fermion_spin : fermion.spin = 1/2
  /-- Scalar has spin 0. -/
  scalar_spin : scalar.spin = 0

/-- Gauge (vector) supermultiplet: pairs a gauge boson with a gaugino. -/
structure GaugeMultiplet where
  /-- Gauge boson (spin 1). -/
  gaugeBoson : SUSYParticle
  /-- Gaugino superpartner (spin 1/2). -/
  gaugino : SUSYParticle
  /-- Gauge boson has spin 1. -/
  boson_spin : gaugeBoson.spin = 1
  /-- Gaugino has spin 1/2. -/
  gaugino_spin : gaugino.spin = 1/2

/-- The MSSM (Minimal Supersymmetric Standard Model) particle content. -/
structure MSSM where
  /-- Squarks: scalar partners of quarks (6 flavors x 2 chiralities). -/
  squarks : Fin 12 → ChiralMultiplet
  /-- Sleptons: scalar partners of leptons (3 charged + 3 neutrinos x 2 chiralities). -/
  sleptons : Fin 9 → ChiralMultiplet
  /-- Gluino: fermionic partner of the gluon. -/
  gluino : GaugeMultiplet
  /-- Wino: fermionic partner of W bosons. -/
  wino : GaugeMultiplet
  /-- Bino: fermionic partner of B boson. -/
  bino : GaugeMultiplet
  /-- Two Higgs doublets Hu and Hd. -/
  higgsUp : ChiralMultiplet
  higgsDown : ChiralMultiplet

/-- Example: the stop squark (partner of top quark). -/
noncomputable def stopSquark : SUSYParticle where
  name := "stop"
  spin := 0
  mass := 1000  -- ~1 TeV (typical SUSY scale)
  charge := 2/3
  colorDim := 3
  rParity := -1

/-- Example: the gluino (partner of gluon). -/
noncomputable def gluinoParticle : SUSYParticle where
  name := "gluino"
  spin := 1/2
  mass := 2000  -- ~2 TeV
  charge := 0
  colorDim := 8
  rParity := -1

/-! ## SUSY breaking -/

/-- Mechanisms of supersymmetry breaking. -/
inductive SUSYBreakingMechanism where
  /-- F-term breaking: <F> != 0 (O'Raifeartaigh model). -/
  | fTerm
  /-- D-term breaking: <D> != 0 (Fayet-Iliopoulos). -/
  | dTerm
  /-- Gravity-mediated SUSY breaking (mSUGRA/CMSSM). -/
  | gravityMediated
  /-- Gauge-mediated SUSY breaking (GMSB). -/
  | gaugeMediated
  /-- Anomaly-mediated SUSY breaking (AMSB). -/
  | anomalyMediated

/-- Soft SUSY breaking parameters preserve the cancellation of quadratic divergences. -/
structure SoftBreakingParams where
  /-- Gaugino masses M1, M2, M3. -/
  gauginoMasses : Fin 3 → ℝ
  /-- Scalar mass-squared parameters. -/
  scalarMassSq : ℝ
  /-- Trilinear A-terms. -/
  aTerms : ℝ
  /-- Bilinear B-term (B mu). -/
  bTerm : ℝ

/-- The SUSY breaking scale sqrt(F) or equivalently the soft mass scale m_soft. -/
noncomputable def susyBreakingScale (params : SoftBreakingParams) : ℝ :=
  Real.sqrt params.scalarMassSq

/-- In unbroken SUSY, superpartners have equal mass.
    SUSY breaking lifts superpartner masses above SM masses. -/
def UnbrokenSUSY (mult : Supermultiplet) : Prop :=
  mult.smParticle.mass = mult.superpartner.mass

/-- SUSY is broken if any superpartner mass differs from its SM partner. -/
def BrokenSUSY (mult : Supermultiplet) : Prop :=
  mult.smParticle.mass ≠ mult.superpartner.mass

/-- The supertrace mass formula: STr M^2 = Sum (-1)^{2s} (2s+1) m^2_s = 0
    holds at tree level even after SUSY breaking. -/
def supertraceCondition (particles : List SUSYParticle) : Prop :=
  (particles.map (fun p =>
    (-1 : ℝ)^(2 * p.spin.num.natAbs / p.spin.den) *
    (2 * (p.spin : ℝ) + 1) * p.mass^2)).sum = 0

/-! ## Extended SUSY -/

/-- N = 2 SUSY has a vector multiplet containing a gauge boson,
    two Weyl fermions, and a complex scalar. -/
structure N2VectorMultiplet where
  /-- Gauge boson (spin 1). -/
  gaugeBoson : SUSYParticle
  /-- Two gauginos (spin 1/2). -/
  gauginos : Fin 2 → SUSYParticle
  /-- Complex scalar (spin 0). -/
  scalar : SUSYParticle

/-- N = 4 Super Yang-Mills: maximally supersymmetric gauge theory in 4D.
    Contains 1 gauge boson, 4 Weyl fermions, 6 real scalars. -/
structure N4SYMContent where
  /-- Gauge boson. -/
  gaugeBoson : SUSYParticle
  /-- Four Weyl fermions. -/
  fermions : Fin 4 → SUSYParticle
  /-- Six real scalars. -/
  scalars : Fin 6 → SUSYParticle

/-- N = 4 SYM is conformally invariant (beta-function vanishes exactly). -/
def n4SYMBetaFunction : ℝ := 0

end Measure.Physics.StringTheory
