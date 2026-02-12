/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode parser: List LocToken → Expr / Stmt / Program.
Pratt parser with operator precedence, juxtaposition multiplication,
function calls, if/for/lambda, and simulation blocks.
See docs/syntax-and-integration.md Section 1.3-1.6.
-/
import Measure.Scratch.Lexer
import Measure.Scratch.Juxtapose
import Measure.Scratch.Decl

namespace Measure.Scratch

/-- Parser state: a cursor over a token list. -/
structure ParserState where
  tokens : Array LocToken
  pos    : Nat := 0
  deriving Repr, Inhabited

namespace Parser

/-- Operator precedence levels (higher binds tighter).
    See docs/syntax-and-integration.md Section 7.2.3. -/
def precComparison : Nat := 10
def precPlusMinus  : Nat := 20
def precPm         : Nat := 15  -- ± uncertainty
def precMulDiv     : Nat := 30
def precJuxtapose  : Nat := 35  -- space-multiply above explicit * /
def precUnary      : Nat := 40
def precPower      : Nat := 50

/-- Check if we've reached end of tokens. -/
def atEnd (s : ParserState) : Bool :=
  s.pos ≥ s.tokens.size

/-- Peek at the current token. -/
def peek (s : ParserState) : Option LocToken :=
  s.tokens[s.pos]?

/-- Peek at the token kind. -/
def peekKind (s : ParserState) : Option TokenKind :=
  (peek s).map (·.kind)

/-- Get current source position for error reporting. -/
def currentPos (s : ParserState) : SourcePos :=
  match peek s with
  | some tok => tok.pos
  | none => { line := 0, column := 0, offset := 0 }

/-- Advance the parser by one token. -/
def advance (s : ParserState) : ParserState :=
  { s with pos := s.pos + 1 }

/-- Skip newline tokens. -/
partial def skipNewlines (s : ParserState) : ParserState :=
  match peekKind s with
  | some .newline => skipNewlines (advance s)
  | _ => s

/-- Expect and consume a specific token kind. -/
def expect (s : ParserState) (kind : TokenKind) (msg : String)
    : Except String (ParserState × LocToken) :=
  match peek s with
  | some tok =>
    if tok.kind == kind then .ok (advance s, tok)
    else .error s!"expected {msg} at line {tok.pos.line}:{tok.pos.column}, got '{tok.text}'"
  | none => .error s!"unexpected end of input, expected {msg}"

/-- Check if a token kind can start an atom expression. -/
def isAtomStart (k : TokenKind) : Bool :=
  match k with
  | .number _ | .ident _ | .greekIdent _ | .knownFunc _
  | .lparen | .lbracket | .pipe => true
  | _ => false

end Parser
end Measure.Scratch
