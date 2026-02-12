/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Desugar: simulation block expansion to Lean4 do-block with conservation checks.
See docs/syntax-and-integration.md Section 7.3.
-/
import Measure.Scratch.DesugarExpr

namespace Measure.Scratch.Desugar

/-- Extract conserved quantities from simulation attributes.
    @[conserve energy, momentum] has args = ["energy", "momentum"]. -/
def extractConserved (attrs : List Scratch.AttrEntry) : List String :=
  attrs.foldl (fun acc a =>
    if a.name == "conserve" then acc ++ a.args
    else acc) []

/-- Extract tolerance from simulation attributes. -/
def extractTolerance (attrs : List Scratch.AttrEntry) : Float :=
  match attrs.find? fun a => a.name == "tolerance" with
  | some a => match a.args.head? with
    | some s => match s.toNat? with
      | some n => Float.ofNat n
      | none => 1e-10
    | none => 1e-10
  | none => 1e-10

/-- Collect primed variable names from simulation body. -/
def collectPrimedVars (body : List Scratch.SimStep) : List String :=
  body.filterMap fun s =>
    match s with
    | .primedUpdate var _ => some var
    | _ => none

/-- Collect emit variable names from simulation body. -/
def collectEmitVars (body : List Scratch.SimStep) : List String :=
  body.filterMap fun s =>
    match s with
    | .emitStep name _ => some name
    | _ => none
