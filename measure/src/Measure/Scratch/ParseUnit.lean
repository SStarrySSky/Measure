/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode parser: expression parsing with Pratt algorithm.
Handles atoms, unary/binary operators, juxtaposition, function calls.
See docs/syntax-and-integration.md Section 1.3.
-/
import Measure.Scratch.Parser

namespace Measure.Scratch.Parser

/-- Convert a Float to Int by rounding toward zero. -/
private def floatToInt (f : Float) : Int :=
  if f >= 0 then Int.ofNat f.toUInt64.toNat
  else -Int.ofNat (-f).toUInt64.toNat

/-- Parse a unit atom: base-unit with optional ^exponent. -/
partial def parseUnitAtom (s : ParserState) : Except String (ParserState × UnitExpr) :=
  match peekKind s with
  | some (.unitToken name) | some (.ident name) =>
    let s := advance s
    -- Check for ^exponent
    match peekKind s with
    | some .caret =>
      let s := advance s
      match peekKind s with
      | some (.number val) =>
        let s := advance s
        .ok (s, .pow (.base name) (floatToInt val))
      | some .minus =>
        let s := advance s
        match peekKind s with
        | some (.number val) =>
          .ok (advance s, .pow (.base name) (-(floatToInt val)))
        | _ => .error "expected exponent after ^-"
      | _ => .error "expected exponent after ^"
    | _ => .ok (s, .base name)
  | _ => .error "expected unit name"

/-- Parse a unit expression: unit_atom (('*' | '/') unit_atom)*. -/
partial def parseUnitExpr (s : ParserState) : Except String (ParserState × UnitExpr) := do
  let (s, first) ← parseUnitAtom s
  go s first
where
  go (s : ParserState) (acc : UnitExpr) : Except String (ParserState × UnitExpr) := do
    match peekKind s with
    | some .star =>
      let s := advance s
      let (s, rhs) ← parseUnitAtom s
      go s (.mul acc rhs)
    | some .slash =>
      let s := advance s
      let (s, rhs) ← parseUnitAtom s
      go s (.div acc rhs)
    | _ => .ok (s, acc)

/-- Check if current token looks like the start of a unit expression. -/
def looksLikeUnit (s : ParserState) : Bool :=
  match peekKind s with
  | some (.unitToken _) => true
  | _ => false

end Parser
end Measure.Scratch
