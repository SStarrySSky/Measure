/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Natural unit system (hbar = c = k_B = 1).
See docs/type-system.md Section 3.4 and Section 7.
-/
import Measure.Unit.Basic
import Measure.Dim.Basic

namespace Measure.Unit.Natural

open Measure.Dim
open Measure.Unit

/-- Natural unit dimension: everything expressed as powers of Energy. -/
structure NaturalDim where
  E : QExp
  I : QExp := QExp.zero
  N : QExp := QExp.zero
  J : QExp := QExp.zero
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Project 7-dim SI space to 4-dim natural unit space.
    E = M - L - T + Theta (see type-system.md Section 7.2.2). -/
def projectNatural (d : Dim) : NaturalDim :=
  { E := d.M - d.L - d.T + d.Θ
  , I := d.I
  , N := d.N
  , J := d.J }

/-- Check if a dimension difference is in ker(pi). -/
def inKernel (delta : Dim) : Bool :=
  let proj := projectNatural delta
  proj.E.isZero && proj.I.isZero && proj.N.isZero && proj.J.isZero

-- Natural unit definitions
def eV : Unit Energy :=
  ⟨"electronvolt", "eV", 1.602176634e-19, 0.0, .Natural⟩

def MeV : Unit Energy :=
  ⟨"megaelectronvolt", "MeV", 1.602176634e-13, 0.0, .Natural⟩

def GeV : Unit Energy :=
  ⟨"gigaelectronvolt", "GeV", 1.602176634e-10, 0.0, .Natural⟩

def TeV : Unit Energy :=
  ⟨"teraelectronvolt", "TeV", 1.602176634e-7, 0.0, .Natural⟩

def keV : Unit Energy :=
  ⟨"kiloelectronvolt", "keV", 1.602176634e-16, 0.0, .Natural⟩

end Measure.Unit.Natural
