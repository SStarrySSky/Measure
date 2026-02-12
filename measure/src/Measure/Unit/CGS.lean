/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

CGS unit system definitions.
See docs/type-system.md Section 3.5.
-/
import Measure.Unit.Basic
import Measure.Dim.Basic

namespace Measure.Unit.CGS

open Measure.Dim
open Measure.Unit

def cm : Unit ⟨QExp.one, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero⟩ :=
  ⟨"centimeter", "cm", 1e-2, 0.0, .CGS⟩

def g : Unit ⟨QExp.zero, QExp.one, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero⟩ :=
  ⟨"gram", "g", 1e-3, 0.0, .CGS⟩

def s : Unit ⟨QExp.zero, QExp.zero, QExp.one, QExp.zero, QExp.zero, QExp.zero, QExp.zero⟩ :=
  ⟨"second", "s", 1.0, 0.0, .CGS⟩

def dyn : Unit Force :=
  ⟨"dyne", "dyn", 1e-5, 0.0, .CGS⟩

def erg : Unit Energy :=
  ⟨"erg", "erg", 1e-7, 0.0, .CGS⟩

end Measure.Unit.CGS
