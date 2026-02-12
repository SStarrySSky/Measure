/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

UnitSystemConversion typeclass and Unit operations.
See docs/type-system.md Section 3.7.
-/
import Measure.Unit.Basic
import Measure.Dim.Basic

namespace Measure.Unit

open Measure.Dim

/-- Typeclass for converting between unit systems. -/
class UnitSystemConversion (from_ to_ : UnitSystem) where
  /-- Remap dimension representation (e.g., CGS electromagnetic). -/
  remapDim : Dim → Dim
  /-- Scale factor for a given dimension. -/
  scaleFactor : Dim → Float

/-- Unit multiplication: combines two units with dimension product. -/
def Unit.mul {d1 d2 : Dim} (a : Unit d1) (b : Unit d2)
    : Unit (Dim.mul d1 d2) :=
  { name   := a.name ++ "·" ++ b.name
  , symbol := a.symbol ++ "·" ++ b.symbol
  , toSI   := a.toSI * b.toSI
  , offset := 0.0
  , system := a.system }

/-- Unit division: combines two units with dimension quotient. -/
def Unit.div {d1 d2 : Dim} (a : Unit d1) (b : Unit d2)
    : Unit (Dim.div d1 d2) :=
  { name   := a.name ++ "/" ++ b.name
  , symbol := a.symbol ++ "/" ++ b.symbol
  , toSI   := a.toSI / b.toSI
  , offset := 0.0
  , system := a.system }

/-- Unit power: raises a unit to a rational exponent. -/
def Unit.pow {d : Dim} (u : Unit d) (n : QExp)
    : Unit (Dim.pow d n) :=
  { name   := u.name ++ "^" ++ toString (repr n)
  , symbol := u.symbol ++ "^" ++ toString (repr n)
  , toSI   := Float.pow u.toSI n.toFloat
  , offset := 0.0
  , system := u.system }

/-- SI prefix application. -/
def Unit.withPrefix {d : Dim} (u : Unit d) (prefixName prefixSym : String) (factor : Float)
    : Unit d :=
  { u with
    name   := prefixName ++ u.name
  , symbol := prefixSym ++ u.symbol
  , toSI   := u.toSI * factor }

/-- SI → CGS conversion.
    Length: m → cm (×100), Mass: kg → g (×1000), Time: s → s (×1).
    Current and thermodynamic quantities use Gaussian CGS conventions. -/
instance : UnitSystemConversion .SI .CGS where
  remapDim := id
  scaleFactor := fun d =>
    let lFactor := Float.pow 100.0 d.L.toFloat       -- m → cm
    let mFactor := Float.pow 1000.0 d.M.toFloat      -- kg → g
    let tFactor := Float.pow 1.0 d.T.toFloat         -- s → s
    lFactor * mFactor * tFactor

/-- SI → Natural units conversion (c = ℏ = k_B = 1).
    All dimensions collapse: Length = Time = 1/Mass = 1/Energy.
    Scale factors express SI values in terms of GeV-based natural units. -/
instance : UnitSystemConversion .SI .Natural where
  remapDim := fun d =>
    -- In natural units, everything reduces to powers of energy (Mass dimension)
    -- L → M^(-1), T → M^(-1), I → M, Θ → M
    { L := QExp.zero
    , M := QExp.sub (QExp.sub (QExp.add d.M (QExp.neg d.L)) d.T) d.Θ
    , T := QExp.zero
    , I := QExp.zero
    , Θ := QExp.zero
    , N := d.N
    , J := d.J }
  scaleFactor := fun d =>
    -- c  = 2.998e8 m/s       → L T^(-1)
    -- ℏ  = 1.055e-34 J·s     → M L^2 T^(-1)
    -- k_B = 1.381e-23 J/K    → M L^2 T^(-2) Θ^(-1)
    let c   := 2.99792458e8
    let hbar := 1.054571817e-34
    let kB  := 1.380649e-23
    let cExp  := d.L.toFloat - d.T.toFloat
    let hbarExp := d.M.toFloat + 2.0 * d.L.toFloat - d.T.toFloat
    let kBExp := d.Θ.toFloat
    Float.pow c cExp * Float.pow hbar hbarExp * Float.pow kB kBExp

end Measure.Unit
