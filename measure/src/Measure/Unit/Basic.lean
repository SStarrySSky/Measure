/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Unit type and UnitSystem definitions.
See docs/type-system.md Section 3.
-/
import Measure.Dim.Basic

namespace Measure.Unit

open Measure.Dim

/-- Unit system enumeration. -/
inductive UnitSystem where
  | SI
  | CGS
  | Natural
  | Planck
  | Gaussian
  | HeavisideLorentz
  | Custom (name : String)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A concrete unit bound to a specific dimension. -/
structure Unit (d : Dim) where
  name   : String
  symbol : String
  toSI   : Float
  offset : Float := 0.0
  system : UnitSystem := .SI
  deriving Repr, Inhabited

namespace Unit

/-- Conversion factor between two units of the same dimension. -/
def conversionFactor {d : Dim} (from_ to_ : Unit d) : Float :=
  from_.toSI / to_.toSI

/-- Affine unit conversion (e.g., Celsius <-> Kelvin). -/
def convertAffine {d : Dim} (from_ to_ : Unit d) (value : Float) : Float :=
  (value * from_.toSI + from_.offset - to_.offset) / to_.toSI

end Unit

end Measure.Unit
