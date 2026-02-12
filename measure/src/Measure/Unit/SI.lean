/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

SI unit definitions: 7 base units + derived units + prefixes.
See docs/type-system.md Section 3.3.
-/
import Measure.Unit.Basic
import Measure.Dim.Basic

namespace Measure.Unit.SI

open Measure.Dim
open Measure.Unit

-- 7 SI base units
def m   : Unit ⟨QExp.one, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero⟩ :=
  ⟨"meter", "m", 1.0, 0.0, .SI⟩

def kg  : Unit ⟨QExp.zero, QExp.one, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero⟩ :=
  ⟨"kilogram", "kg", 1.0, 0.0, .SI⟩

def s   : Unit ⟨QExp.zero, QExp.zero, QExp.one, QExp.zero, QExp.zero, QExp.zero, QExp.zero⟩ :=
  ⟨"second", "s", 1.0, 0.0, .SI⟩

def ampere : Unit ⟨QExp.zero, QExp.zero, QExp.zero, QExp.one, QExp.zero, QExp.zero, QExp.zero⟩ :=
  ⟨"ampere", "A", 1.0, 0.0, .SI⟩

def kelvin : Unit ⟨QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.one, QExp.zero, QExp.zero⟩ :=
  ⟨"kelvin", "K", 1.0, 0.0, .SI⟩

def mol : Unit ⟨QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.one, QExp.zero⟩ :=
  ⟨"mole", "mol", 1.0, 0.0, .SI⟩

def cd  : Unit ⟨QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.zero, QExp.one⟩ :=
  ⟨"candela", "cd", 1.0, 0.0, .SI⟩

-- Derived units
def N  : Unit Force    := ⟨"newton",  "N",  1.0, 0.0, .SI⟩
def J  : Unit Energy   := ⟨"joule",   "J",  1.0, 0.0, .SI⟩
def W  : Unit Power    := ⟨"watt",    "W",  1.0, 0.0, .SI⟩
def Pa : Unit Pressure := ⟨"pascal",  "Pa", 1.0, 0.0, .SI⟩
def C  : Unit Charge   := ⟨"coulomb", "C",  1.0, 0.0, .SI⟩

-- Electromagnetic derived units
def V  : Unit Voltage          := ⟨"volt",    "V",  1.0, 0.0, .SI⟩
def Ω  : Unit Resistance       := ⟨"ohm",     "Ω",  1.0, 0.0, .SI⟩
def F  : Unit Capacitance      := ⟨"farad",   "F",  1.0, 0.0, .SI⟩
def H  : Unit Inductance       := ⟨"henry",   "H",  1.0, 0.0, .SI⟩
def T  : Unit MagneticFluxDens := ⟨"tesla",   "T",  1.0, 0.0, .SI⟩
def Wb : Unit MagneticFlux     := ⟨"weber",   "Wb", 1.0, 0.0, .SI⟩

end Measure.Unit.SI
