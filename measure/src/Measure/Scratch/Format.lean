/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode runtime: output formatting for values.
Reuses Measure.Dim.Dim (QExp-based dimensions).
-/
import Measure.Scratch.Value

namespace Measure.Scratch

open Measure.Dim
open Measure.Error

namespace Format

/-- Format a UnitExpr to a human-readable string. -/
partial def formatUnit : UnitExpr → String
  | .base name => name
  | .mul a b => s!"{formatUnit a}*{formatUnit b}"
  | .div a b => s!"{formatUnit a}/{formatUnit b}"
  | .pow u n =>
    if n == 1 then formatUnit u
    else if n == -1 then s!"{formatUnit u}^(-1)"
    else s!"{formatUnit u}^{n}"

/-- Format a QExp as a string (e.g., "1", "-2", "1/2"). -/
def formatQExp (q : QExp) : String :=
  if q.den == 1 then s!"{q.num}"
  else s!"{q.num}/{q.den}"

/-- Format a Dim to a human-readable string using SI dimension symbols. -/
def formatDim (d : Dim) : String :=
  if d.isDimensionless then "dimensionless"
  else
    let parts := #[
      if !d.L.isZero then some s!"L^{formatQExp d.L}" else none,
      if !d.M.isZero then some s!"M^{formatQExp d.M}" else none,
      if !d.T.isZero then some s!"T^{formatQExp d.T}" else none,
      if !d.I.isZero then some s!"I^{formatQExp d.I}" else none,
      if !d.Θ.isZero then some s!"Θ^{formatQExp d.Θ}" else none,
      if !d.N.isZero then some s!"N^{formatQExp d.N}" else none,
      if !d.J.isZero then some s!"J^{formatQExp d.J}" else none
    ]
    let filtered := parts.filterMap id
    String.intercalate " " filtered.toList

/-- Format a Float with scientific notation for very small/large values. -/
def formatFloat (f : Float) : String :=
  if f == 0.0 then "0.0"
  else
    let abs := Float.abs f
    -- Use scientific notation for very small or very large numbers
    if abs < 1.0e-4 || abs ≥ 1.0e10 then
      formatSci f
    else
      let s := toString f
      if (s.splitOn ".").length > 1 then
        let trimmed := String.ofList (s.toList.reverse.dropWhile (· == '0') |>.reverse)
        if trimmed.endsWith "." then trimmed ++ "0"
        else trimmed
      else s
where
  /-- Left-pad a string with zeros to a given width. -/
  padLeft (s : String) (width : Nat) : String :=
    let deficit := if width > s.length then width - s.length else 0
    String.ofList (List.replicate deficit '0') ++ s
  /-- Format in scientific notation: d.ddddddeSdd -/
  formatSci (f : Float) : String :=
    let neg := f < 0.0
    let abs := Float.abs f
    -- Use Float.log10 to get exponent
    let logVal := Float.log abs / Float.log 10.0
    let exp : Int := if logVal ≥ 0.0 then logVal.toUInt64.toNat else -((-logVal).ceil.toUInt64.toNat : Int)
    -- mantissa = abs / 10^exp, should be in [1, 10)
    let pow10 := Float.pow 10.0 (Float.ofInt exp)
    let mantissa := if pow10 != 0.0 then abs / pow10 else abs
    -- Correct if mantissa drifted out of [1, 10)
    let (mantissa, exp) :=
      if mantissa ≥ 10.0 then (mantissa / 10.0, exp + 1)
      else if mantissa < 1.0 && mantissa > 0.0 then (mantissa * 10.0, exp - 1)
      else (mantissa, exp)
    -- Round mantissa to 6 significant digits
    let shifted := Float.round (mantissa * 1000000.0)
    let intPart := shifted.toUInt64.toNat
    let whole := intPart / 1000000
    let frac := intPart % 1000000
    let fracStr := padLeft (toString frac) 6
    -- Trim trailing zeros from fraction
    let fracTrimmed := String.ofList (fracStr.toList.reverse.dropWhile (· == '0') |>.reverse)
    let fracFinal := if fracTrimmed.isEmpty then "0" else fracTrimmed
    let sign := if neg then "-" else ""
    let expSign := if exp ≥ 0 then "+" else ""
    s!"{sign}{whole}.{fracFinal}e{expSign}{exp}"

end Format

namespace Value

/-- Format a Value for display to the user. -/
partial def format : Value → String
  | .number v => Format.formatFloat v
  | .withUnit v u _ => s!"{Format.formatFloat v} {Format.formatUnit u}"
  | .withUncertainty v err u _ =>
    let sigma := err.halfWidth
    let base := s!"{Format.formatFloat v} ± {Format.formatFloat sigma}"
    match u with
    | some ue => s!"{base} {Format.formatUnit ue}"
    | none => base
  | .quantity v d err =>
    let dimStr := if d.isDimensionless then "" else s!" [{Format.formatDim d}]"
    match err with
    | some iv => s!"{Format.formatFloat v} ± {Format.formatFloat iv.halfWidth}{dimStr}"
    | none => s!"{Format.formatFloat v}{dimStr}"
  | .vector elems =>
    let inner := elems.toList.map format
    s!"[{String.intercalate ", " inner}]"
  | .matrix rows =>
    let fmtRow r := String.intercalate ", " (r.toList.map format)
    let inner := rows.toList.map fun r => s!"[{fmtRow r}]"
    s!"[{String.intercalate "; " inner}]"
  | .bool b => if b then "true" else "false"
  | .string s => s!"\"{s}\""
  | .closure params _ _ =>
    let ps := params.map (·.name)
    s!"<closure({String.intercalate ", " ps})>"
  | .unit => "()"

end Value

end Measure.Scratch
