/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Standard Model of particle physics — particle classification, quantum numbers,
and conservation laws.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic

namespace Measure.Physics.ParticlePhysics

/-! ## Particle Classification -/

/-- The three generations of fermions. -/
inductive Generation where
  | first
  | second
  | third
  deriving DecidableEq, Repr

/-- Color charge carried by quarks and gluons. -/
inductive ColorCharge where
  | red
  | green
  | blue
  | antiRed
  | antiGreen
  | antiBlue
  | colorless
  deriving DecidableEq, Repr

/-- Quark flavors. -/
inductive QuarkFlavor where
  | up
  | down
  | charm
  | strange
  | top
  | bottom
  deriving DecidableEq, Repr

/-- Lepton flavors. -/
inductive LeptonFlavor where
  | electron
  | muon
  | tau
  | electronNeutrino
  | muonNeutrino
  | tauNeutrino
  deriving DecidableEq, Repr

/-- Gauge bosons of the Standard Model. -/
inductive GaugeBoson where
  | photon
  | wPlus
  | wMinus
  | zBoson
  | gluon
  deriving DecidableEq, Repr

/-- All elementary particles in the Standard Model. -/
inductive Particle where
  | quark (flavor : QuarkFlavor)
  | antiquark (flavor : QuarkFlavor)
  | lepton (flavor : LeptonFlavor)
  | antilepton (flavor : LeptonFlavor)
  | gauge (boson : GaugeBoson)
  | higgs
  deriving DecidableEq, Repr

/-! ## Quantum Numbers -/

/-- Quantum numbers characterizing a particle. -/
structure QuantumNumbers where
  /-- Electric charge in units of e. -/
  charge : ℚ
  /-- Spin quantum number (0, 1/2, 1, ...). -/
  spin : ℚ
  /-- Weak isospin third component T₃. -/
  isospinT3 : ℚ
  /-- Baryon number. -/
  baryonNumber : ℚ
  /-- Lepton number. -/
  leptonNumber : ℚ
  /-- Strangeness. -/
  strangeness : ℤ
  /-- Color charge. -/
  color : ColorCharge
  deriving Repr

/-- Generation of a quark flavor. -/
def QuarkFlavor.generation : QuarkFlavor → Generation
  | .up | .down => .first
  | .charm | .strange => .second
  | .top | .bottom => .third

/-- Generation of a lepton flavor. -/
def LeptonFlavor.generation : LeptonFlavor → Generation
  | .electron | .electronNeutrino => .first
  | .muon | .muonNeutrino => .second
  | .tau | .tauNeutrino => .third

/-- Electric charge of a quark flavor (in units of e). -/
def QuarkFlavor.electricCharge : QuarkFlavor → ℚ
  | .up | .charm | .top => 2 / 3
  | .down | .strange | .bottom => -(1 / 3)

/-- Electric charge of a lepton flavor (in units of e). -/
def LeptonFlavor.electricCharge : LeptonFlavor → ℚ
  | .electron | .muon | .tau => -1
  | .electronNeutrino | .muonNeutrino | .tauNeutrino => 0

/-- Electric charge of a gauge boson (in units of e). -/
def GaugeBoson.electricCharge : GaugeBoson → ℚ
  | .wPlus => 1
  | .wMinus => -1
  | .photon | .zBoson | .gluon => 0

/-- Spin of a quark flavor. -/
def QuarkFlavor.spin : QuarkFlavor → ℚ
  | _ => 1 / 2

/-- Spin of a lepton flavor. -/
def LeptonFlavor.spin : LeptonFlavor → ℚ
  | _ => 1 / 2

/-- Spin of a gauge boson. -/
def GaugeBoson.spin : GaugeBoson → ℚ
  | _ => 1

/-- Assign quantum numbers to a particle. -/
def Particle.quantumNumbers : Particle → QuantumNumbers
  | .quark f => {
      charge := f.electricCharge
      spin := f.spin
      isospinT3 := match f with
        | .up | .charm | .top => 1 / 2
        | .down | .strange | .bottom => -(1 / 2)
      baryonNumber := 1 / 3
      leptonNumber := 0
      strangeness := match f with | .strange => -1 | _ => 0
      color := .red  -- placeholder; quarks carry color
    }
  | .antiquark f => {
      charge := -f.electricCharge
      spin := f.spin
      isospinT3 := match f with
        | .up | .charm | .top => -(1 / 2)
        | .down | .strange | .bottom => 1 / 2
      baryonNumber := -(1 / 3)
      leptonNumber := 0
      strangeness := match f with | .strange => 1 | _ => 0
      color := .antiRed  -- placeholder; antiquarks carry anticolor
    }
  | .lepton f => {
      charge := f.electricCharge
      spin := f.spin
      isospinT3 := match f with
        | .electron | .muon | .tau => -(1 / 2)
        | .electronNeutrino | .muonNeutrino | .tauNeutrino => 1 / 2
      baryonNumber := 0
      leptonNumber := 1
      strangeness := 0
      color := .colorless
    }
  | .antilepton f => {
      charge := -f.electricCharge
      spin := f.spin
      isospinT3 := match f with
        | .electron | .muon | .tau => 1 / 2
        | .electronNeutrino | .muonNeutrino | .tauNeutrino => -(1 / 2)
      baryonNumber := 0
      leptonNumber := -1
      strangeness := 0
      color := .colorless
    }
  | .gauge b => {
      charge := b.electricCharge
      spin := b.spin
      isospinT3 := match b with
        | .wPlus => 1
        | .wMinus => -1
        | _ => 0
      baryonNumber := 0
      leptonNumber := 0
      strangeness := 0
      color := .colorless
    }
  | .higgs => {
      charge := 0
      spin := 0
      isospinT3 := -(1 / 2)
      baryonNumber := 0
      leptonNumber := 0
      strangeness := 0
      color := .colorless
    }

/-! ## Conservation Laws -/

/-- Total electric charge of a list of particles is conserved in a reaction. -/
def chargeConserved (initial final_ : List Particle) : Prop :=
  (initial.map (fun p => p.quantumNumbers.charge)).sum =
  (final_.map (fun p => p.quantumNumbers.charge)).sum

/-- Total baryon number is conserved. -/
def baryonNumberConserved (initial final_ : List Particle) : Prop :=
  (initial.map (fun p => p.quantumNumbers.baryonNumber)).sum =
  (final_.map (fun p => p.quantumNumbers.baryonNumber)).sum

/-- Total lepton number is conserved. -/
def leptonNumberConserved (initial final_ : List Particle) : Prop :=
  (initial.map (fun p => p.quantumNumbers.leptonNumber)).sum =
  (final_.map (fun p => p.quantumNumbers.leptonNumber)).sum

/-- A reaction is valid if all additive quantum numbers are conserved. -/
structure ValidReaction (initial final_ : List Particle) : Prop where
  charge : chargeConserved initial final_
  baryon : baryonNumberConserved initial final_
  lepton : leptonNumberConserved initial final_

/-- The up quark has charge +2/3. -/
theorem up_quark_charge :
    (Particle.quark .up).quantumNumbers.charge = 2 / 3 := by
  rfl

/-- The electron has charge -1. -/
theorem electron_charge :
    (Particle.lepton .electron).quantumNumbers.charge = -1 := by
  rfl

/-- The photon has zero charge. -/
theorem photon_charge :
    (Particle.gauge .photon).quantumNumbers.charge = 0 := by
  rfl

end Measure.Physics.ParticlePhysics
