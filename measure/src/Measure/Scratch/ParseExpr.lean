/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode parser: Pratt expression parser core.
Handles atoms, prefix/infix operators, juxtaposition multiplication,
function calls, if/for/lambda, ± literals, and unit annotations.
See docs/syntax-and-integration.md Section 1.3.
-/
import Measure.Scratch.ParseUnit

namespace Measure.Scratch.Parser

-- Forward declarations for mutual recursion
mutual

/-- Parse an atom (the tightest-binding expression forms). -/
partial def parseAtom (s : ParserState) : Except String (ParserState × Expr) :=
  let pos := currentPos s
  match peekKind s with
  -- Number literal
  | some (.number val) =>
    .ok (advance s, .number val pos)

  -- Identifier
  | some (.ident name) =>
    .ok (advance s, .ident name pos)

  -- Greek identifier
  | some (.greekIdent name) =>
    .ok (advance s, .greekIdent name pos)

  -- Known function: parse as call with parenthesized args or single juxtaposed arg
  | some (.knownFunc name) =>
    let s := advance s
    parseKnownFuncCall s name pos

  -- Parenthesized expression
  | some .lparen =>
    let s := advance s
    match parseExpr s 0 with
    | .ok (s, inner) =>
      match expect s .rparen "')'" with
      | .ok (s, _) => .ok (s, .grouped inner)
      | .error e => .error e
    | .error e => .error e

  -- Absolute value: |expr|
  | some .pipe =>
    let s := advance s
    match parseExpr s 0 with
    | .ok (s, inner) =>
      match expect s .pipe "'|'" with
      | .ok (s, _) => .ok (s, .abs inner)
      | .error e => .error e
    | .error e => .error e

  -- Vector/matrix literal: [...]
  | some .lbracket =>
    parseVectorOrMatrix s

  | _ =>
    let p := currentPos s
    .error s!"expected expression at line {p.line}:{p.column}"

/-- Parse a known function call: either f(args) or f atom (juxtaposition). -/
partial def parseKnownFuncCall (s : ParserState) (name : String) (pos : SourcePos)
    : Except String (ParserState × Expr) :=
  match peekKind s with
  | some .lparen =>
    -- f(a, b, c)
    let s := advance s
    match parseArgList s with
    | .ok (s, args) =>
      match expect s .rparen "')'" with
      | .ok (s, _) => .ok (s, .call name args)
      | .error e => .error e
    | .error e => .error e
  | some k =>
    if isAtomStart k then
      -- f x  =>  f(x)  (single juxtaposed argument)
      match parseAtom s with
      | .ok (s, arg) =>
        -- Handle power after the argument: sin x^2 => sin(x^2)
        match parsePowerSuffix s arg with
        | .ok (s, arg') => .ok (s, .call name [arg'])
        | .error e => .error e
      | .error e => .error e
    else
      -- Known function with no argument: treat as identifier
      .ok (s, .ident name pos)
  | none =>
    .ok (s, .ident name pos)

/-- Parse a comma-separated argument list. -/
partial def parseArgList (s : ParserState) : Except String (ParserState × List Expr) :=
  match peekKind s with
  | some .rparen => .ok (s, [])  -- empty arg list
  | _ =>
    match parseExpr s 0 with
    | .ok (s, first) => parseArgListTail s [first]
    | .error e => .error e

partial def parseArgListTail (s : ParserState) (acc : List Expr)
    : Except String (ParserState × List Expr) :=
  match peekKind s with
  | some .comma =>
    let s := advance s
    match parseExpr s 0 with
    | .ok (s, e) => parseArgListTail s (acc ++ [e])
    | .error e => .error e
  | _ => .ok (s, acc)

/-- Parse vector [a, b, c] or matrix [[a,b];[c,d]]. -/
partial def parseVectorOrMatrix (s : ParserState)
    : Except String (ParserState × Expr) :=
  let s := advance s  -- consume '['
  -- Check for nested bracket (matrix)
  match peekKind s with
  | some .lbracket => parseMatrix s
  | some .rbracket => .ok (advance s, .vector [])  -- empty vector
  | _ =>
    -- Parse first element
    match parseExpr s 0 with
    | .ok (s, first) =>
      match peekKind s with
      -- Semicolon means matrix row separator
      | some (.ident ";") => parseMatrixRows s first
      | _ => parseVectorTail s [first]
    | .error e => .error e

partial def parseVectorTail (s : ParserState) (acc : List Expr)
    : Except String (ParserState × Expr) :=
  match peekKind s with
  | some .comma =>
    let s := advance s
    match parseExpr s 0 with
    | .ok (s, e) => parseVectorTail s (acc ++ [e])
    | .error e => .error e
  | some .rbracket =>
    .ok (advance s, .vector acc)
  | _ =>
    let p := currentPos s
    .error s!"expected ',' or ']' in vector at line {p.line}:{p.column}"

partial def parseMatrix (s : ParserState)
    : Except String (ParserState × Expr) :=
  -- Parse rows as nested vectors
  match parseMatrixRow s with
  | .ok (s, firstRow) =>
    parseMatrixRowsTail s [firstRow]
  | .error e => .error e

partial def parseMatrixRow (s : ParserState)
    : Except String (ParserState × List Expr) :=
  match expect s .lbracket "'['" with
  | .ok (s, _) =>
    match parseArgList s with
    | .ok (s, elems) =>
      match expect s .rbracket "']'" with
      | .ok (s, _) => .ok (s, elems)
      | .error e => .error e
    | .error e => .error e
  | .error e => .error e

partial def parseMatrixRowsTail (s : ParserState) (acc : List (List Expr))
    : Except String (ParserState × Expr) :=
  let s := skipNewlines s
  match peekKind s with
  | some .lbracket =>
    match parseMatrixRow s with
    | .ok (s, row) => parseMatrixRowsTail s (acc ++ [row])
    | .error e => .error e
  | some .rbracket =>
    .ok (advance s, .matrix acc)
  | _ =>
    let p := currentPos s
    .error s!"expected '[' or ']' in matrix at line {p.line}:{p.column}"

partial def parseMatrixRows (s : ParserState) (firstRow : Expr)

    : Except String (ParserState × Expr) :=
  -- Simple matrix: [a, b; c, d] style (semicolon-separated rows)
  -- firstRow is actually just the first element; collect the rest of row 1
  -- For now, treat as vector (full matrix parsing is complex)
  parseVectorTail s [firstRow]

/-- Parse power suffix: ^exponent or Unicode superscript. -/
partial def parsePowerSuffix (s : ParserState) (base : Expr)
    : Except String (ParserState × Expr) :=
  match peekKind s with
  | some .caret =>
    let s := advance s
    match parseAtom s with
    | .ok (s, exp) => .ok (s, .pow base exp)
    | .error e => .error e
  | _ => .ok (s, base)

/-- Pratt parser: parse expression with minimum precedence `minPrec`. -/
partial def parseExpr (s : ParserState) (minPrec : Nat)
    : Except String (ParserState × Expr) := do
  -- Parse prefix (unary minus or atom)
  let (s, lhs) ← parsePrefixExpr s
  -- Parse infix operators and juxtaposition
  parseInfix s lhs minPrec

/-- Parse prefix expression: unary minus or atom with power suffix. -/
partial def parsePrefixExpr (s : ParserState)
    : Except String (ParserState × Expr) :=
  match peekKind s with
  | some .minus =>
    let s := advance s
    match parseExpr s precUnary with
    | .ok (s, e) => .ok (s, .neg e)
    | .error e => .error e
  | _ =>
    match parseAtom s with
    | .ok (s, atom) => parsePowerSuffix s atom
    | .error e => .error e

/-- Parse infix operators with Pratt precedence climbing. -/
partial def parseInfix (s : ParserState) (lhs : Expr) (minPrec : Nat)
    : Except String (ParserState × Expr) :=
  match peekKind s with
  -- Addition: +
  | some .plus =>
    if precPlusMinus ≥ minPrec then
      let s := advance s
      match parseExpr s (precPlusMinus + 1) with
      | .ok (s, rhs) => parseInfix s (.add lhs rhs) minPrec
      | .error e => .error e
    else .ok (s, lhs)

  -- Subtraction: -
  | some .minus =>
    if precPlusMinus ≥ minPrec then
      let s := advance s
      match parseExpr s (precPlusMinus + 1) with
      | .ok (s, rhs) => parseInfix s (.sub lhs rhs) minPrec
      | .error e => .error e
    else .ok (s, lhs)

  -- Multiplication: *
  | some .star =>
    if precMulDiv ≥ minPrec then
      let s := advance s
      match parseExpr s (precMulDiv + 1) with
      | .ok (s, rhs) => parseInfix s (.mul lhs rhs) minPrec
      | .error e => .error e
    else .ok (s, lhs)

  -- Division: /
  | some .slash =>
    if precMulDiv ≥ minPrec then
      let s := advance s
      match parseExpr s (precMulDiv + 1) with
      | .ok (s, rhs) => parseInfix s (.div lhs rhs) minPrec
      | .error e => .error e
    else .ok (s, lhs)

  -- Power: ^ (right-associative)
  | some .caret =>
    if precPower ≥ minPrec then
      let s := advance s
      match parseExpr s precPower with  -- same prec for right-assoc
      | .ok (s, rhs) => parseInfix s (.pow lhs rhs) minPrec
      | .error e => .error e
    else .ok (s, lhs)

  -- Plus-minus: ± uncertainty
  | some .pmOp =>
    if precPm ≥ minPrec then
      let s := advance s
      match parseExpr s (precPm + 1) with
      | .ok (s, sigma) =>
        -- Check for trailing unit
        if looksLikeUnit s then
          match parseUnitExpr s with
          | .ok (s, unit) =>
            parseInfix s (.pmLiteral lhs sigma (some unit)) minPrec
          | .error e => .error e
        else
          parseInfix s (.pmLiteral lhs sigma none) minPrec
      | .error e => .error e
    else .ok (s, lhs)

  -- Comparison operators
  | some .eqEq =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .eq lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  | some .neq =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .neq lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  | some .lt =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .lt lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  | some .gt =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .gt lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  | some .leq =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .leq lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  | some .geq =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .geq lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  | some .approxEq =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .approx lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  -- Much-less-than: <<
  | some .muchLt =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .muchLt lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  -- Much-greater-than: >>
  | some .muchGt =>
    if precComparison ≥ minPrec then
      let s := advance s
      match parseExpr s (precComparison + 1) with
      | .ok (s, rhs) => .ok (s, .cmp .muchGt lhs rhs)
      | .error e => .error e
    else .ok (s, lhs)

  -- Approximate-equal with tolerance: ≈[ε]
  | some .approxEqBrack =>
    if precComparison ≥ minPrec then
      let s := advance s  -- consume '≈['
      -- Parse tolerance expression inside brackets
      match parseExpr s 0 with
      | .ok (s, _tol) =>
        match expect s .rbracket "']'" with
        | .ok (s, _) =>
          match parseExpr s (precComparison + 1) with
          | .ok (s, rhs) => .ok (s, .cmp .approx lhs rhs)
          | .error e => .error e
        | .error e => .error e
      | .error e => .error e
    else .ok (s, lhs)

  -- Juxtaposition multiplication: ident/number/')' followed by atom-start
  | some k =>
    if precJuxtapose ≥ minPrec && isAtomStart k then
      -- Use classifySpace to determine if this is multiply or apply
      let prevKind := match s.tokens[s.pos - 1]? with
        | some tok => tok.kind
        | none => .eof
      match classifySpace prevKind k with
      | .multiply =>
        match parseExpr s (precJuxtapose + 1) with
        | .ok (s, rhs) => parseInfix s (.juxtapose lhs rhs) minPrec
        | .error e => .error e
      | .apply =>
        -- Function application via juxtaposition (shouldn't normally reach here
        -- since known functions are handled in parseAtom)
        match parseExpr s (precJuxtapose + 1) with
        | .ok (s, rhs) => parseInfix s (.juxtapose lhs rhs) minPrec
        | .error e => .error e
      | .error _ =>
        -- Ambiguous juxtaposition: stop parsing infix
        .ok (s, lhs)
    else
      -- Check for trailing unit annotation
      if looksLikeUnit s && precPm ≥ minPrec then
        match parseUnitExpr s with
        | .ok (s, unit) => parseInfix s (.withUnit lhs unit) minPrec
        | .error e => .error e
      else
        .ok (s, lhs)

  | none => .ok (s, lhs)

end -- mutual

end Parser
end Measure.Scratch
