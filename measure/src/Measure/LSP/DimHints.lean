/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dimensional inlay hints for the Measure LSP server.
Uses LSP 3.17 textDocument/inlayHint with Measure-specific hint kinds.
See docs/syntax-and-integration.md Section 6.1.
-/
import Lean
import Measure.Dim.Basic

namespace Measure.LSP

open Lean Measure.Dim

/-- Kind of Measure-specific inlay hint. -/
inductive MeasureHintKind where
  | dimension
  | uncertainty
  | provenance
  | rigor
  | custom (kind : String)  -- User-defined hint kind
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Position in source file. -/
structure Position where
  line      : Nat
  character : Nat
  deriving Repr, Inhabited, BEq

/-- Range in source file. -/
structure Range where
  start : Position
  stop  : Position
  deriving Repr, Inhabited, BEq

/-- A dimensional inlay hint to display in the editor. -/
structure DimHint where
  position     : Position
  dim          : Dim
  dimLabel     : String
  value        : Option Float := none
  uncertainty  : Option Float := none
  unit         : Option String := none
  hintKind     : MeasureHintKind := .dimension
  deriving Repr, Inhabited

namespace DimHint

/-- Format a Dim as a human-readable label like "M*L^2*T^{-2}". -/
def formatDim (d : Dim) : String :=
  let components := [
    ("L", d.L), ("M", d.M), ("T", d.T),
    ("I", d.I), ("Theta", d.Θ), ("N", d.N), ("J", d.J)
  ]
  let nonZero := components.filter fun (_, q) => !q.isZero
  if nonZero.isEmpty then "Dimensionless"
  else
    nonZero.map (fun (name, q) =>
      if q == QExp.one then name
      else if q.den == 1 then s!"{name}^{q.num}"
      else s!"{name}^({q.num}/{q.den})"
    ) |>.intersperse "*" |> String.join

/-- Format the tooltip markdown for a dimension hint. -/
def formatTooltip (h : DimHint) : String :=
  let dimLine := s!"**Dimension**: {h.dimLabel}"
  let valueLine := match h.value, h.uncertainty, h.unit with
    | some v, some u, some unit => s!"\n**Value**: {v} +/- {u} {unit}"
    | some v, none, some unit   => s!"\n**Value**: {v} {unit}"
    | some v, some u, none      => s!"\n**Value**: {v} +/- {u}"
    | some v, none, none        => s!"\n**Value**: {v}"
    | _, _, _                   => ""
  dimLine ++ valueLine

/-- Create a hint from a Dim and optional value info. -/
def mk' (pos : Position) (d : Dim)
    (value : Option Float := none)
    (uncertainty : Option Float := none)
    (unit : Option String := none) : DimHint :=
  { position := pos
    dim := d
    dimLabel := formatDim d
    value := value
    uncertainty := uncertainty
    unit := unit }

end DimHint

end Measure.LSP
