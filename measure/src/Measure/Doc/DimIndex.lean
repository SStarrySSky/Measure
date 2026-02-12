/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Physical dimension index generator for documentation.
Catalogs all Quantity types with their dimensions.
See ARCHITECTURE.md Section 10.5 Phase 5.
-/
import Measure.Dim.Basic
import Measure.Syntax.Attributes

namespace Measure.Doc

open Measure.Dim Measure.Syntax

/-- An entry in the dimension index. -/
structure DimIndexEntry where
  name       : String
  dim        : Dim
  dimLabel   : String
  rigor      : Option RigorLevel := none
  module     : String := ""
  docstring  : String := ""
  deriving Repr, Inhabited

namespace DimIndexEntry

/-- Format dimension as SI base unit expression. -/
def formatSI (d : Dim) : String :=
  let components := [
    ("m", d.L), ("kg", d.M), ("s", d.T),
    ("A", d.I), ("K", d.Θ), ("mol", d.N), ("cd", d.J)
  ]
  let nonZero := components.filter fun (_, q) => !q.isZero
  if nonZero.isEmpty then "dimensionless"
  else
    nonZero.map (fun (unit, q) =>
      if q == QExp.one then unit
      else if q.den == 1 then s!"{unit}^{q.num}"
      else s!"{unit}^({q.num}/{q.den})"
    ) |>.intersperse " " |> String.join

end DimIndexEntry

/-- A complete dimension index for documentation. -/
structure DimIndex where
  entries : List DimIndexEntry := []
  deriving Repr, Inhabited

namespace DimIndex

/-- Add a new entry to the index. -/
def addEntry (idx : DimIndex) (e : DimIndexEntry) : DimIndex :=
  { entries := idx.entries ++ [e] }

/-- Find entries by dimension. -/
def findByDim (idx : DimIndex) (d : Dim) : List DimIndexEntry :=
  idx.entries.filter fun e => e.dim == d

/-- Find entries by module. -/
def findByModule (idx : DimIndex) (mod : String) : List DimIndexEntry :=
  idx.entries.filter fun e => e.module == mod

/-- Generate a markdown table of all dimensions. -/
def toMarkdown (idx : DimIndex) : String :=
  let header := "| Name | Dimension | SI Units | Module | Rigor |\n"
  let sep    := "|------|-----------|----------|--------|-------|\n"
  let rows := idx.entries.map fun e =>
    let rigorStr := match e.rigor with
      | some r => RigorLevel.toString r
      | none   => "-"
    s!"| {e.name} | {e.dimLabel} | {DimIndexEntry.formatSI e.dim} | {e.module} | {rigorStr} |\n"
  header ++ sep ++ String.join rows

/-- Build a default index with common physical dimensions. -/
def defaultIndex : DimIndex :=
  { entries := [
    { name := "Length", dim := { L := QExp.one },
      dimLabel := "L", module := "Measure.Dim" },
    { name := "Mass", dim := { M := QExp.one },
      dimLabel := "M", module := "Measure.Dim" },
    { name := "Time", dim := { T := QExp.one },
      dimLabel := "T", module := "Measure.Dim" },
    { name := "Velocity", dim := Velocity,
      dimLabel := "L*T^{-1}", module := "Measure.Dim" },
    { name := "Acceleration", dim := Acceleration,
      dimLabel := "L*T^{-2}", module := "Measure.Dim" },
    { name := "Force", dim := Force,
      dimLabel := "M*L*T^{-2}", module := "Measure.Dim" },
    { name := "Energy", dim := Energy,
      dimLabel := "M*L^2*T^{-2}", module := "Measure.Dim" },
    { name := "Power", dim := Power,
      dimLabel := "M*L^2*T^{-3}", module := "Measure.Dim" },
    { name := "Pressure", dim := Pressure,
      dimLabel := "M*L^{-1}*T^{-2}", module := "Measure.Dim" },
    { name := "Charge", dim := Charge,
      dimLabel := "T*I", module := "Measure.Dim" }
  ] }

end DimIndex

end Measure.Doc
