/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode parser: declaration and statement parsing.
Handles let, def, import, simulation, compute, verify, if, for, lambda.
See docs/syntax-and-integration.md Section 1.4-1.6.
-/
import Measure.Scratch.ParseExpr

namespace Measure.Scratch.Parser

/-- Parse a parameter: ident (':' type)? -/
def parseParam (s : ParserState) : Except String (ParserState × Param) :=
  match peekKind s with
  | some (.ident name) =>
    let s := advance s
    match peekKind s with
    | some .colon =>
      let s := advance s
      match peekKind s with
      | some (.ident ty) => .ok (advance s, { name, type := some ty })
      | _ => .error "expected type after ':'"
    | _ => .ok (s, { name })
  | _ => .error "expected parameter name"

/-- Parse a parenthesized parameter list: '(' param (',' param)* ')'. -/
partial def parseParamList (s : ParserState)
    : Except String (ParserState × List Param) := do
  let (s, _) ← expect s .lparen "'('"
  match peekKind s with
  | some .rparen => .ok (advance s, [])
  | _ =>
    let (s, first) ← parseParam s
    let (s, rest) ← parseParamListTail s
    .ok (s, first :: rest)
where
  parseParamListTail (s : ParserState)
      : Except String (ParserState × List Param) :=
    match peekKind s with
    | some .comma =>
      let s := advance s
      match parseParam s with
      | .ok (s, p) =>
        match parseParamListTail s with
        | .ok (s, rest) => .ok (s, p :: rest)
        | .error e => .error e
      | .error e => .error e
    | some .rparen => .ok (advance s, [])
    | _ => .error "expected ',' or ')' in parameter list"

end Parser
end Measure.Scratch
