/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Juxtaposition disambiguation: ClassifySpace algorithm.
Determines whether a space between two tokens means multiplication or function application.
See docs/syntax-and-integration.md Section 7.2.
-/
import Measure.Scratch.Token
import Measure.Scratch.LexerDefs

namespace Measure.Scratch

/-- Result of space classification between two adjacent tokens. -/
inductive SpaceClass where
  | multiply
  | apply
  | error (msg : String)
  deriving Repr, Inhabited, BEq

/-- Classify what a space between two tokens means.
    See docs/syntax-and-integration.md Section 7.2.1 for the full algorithm. -/
def classifySpace (tok1 tok2 : TokenKind) : SpaceClass :=
  match tok1, tok2 with
  -- Rule 1: Known function + anything => function application
  | .knownFunc _, _ => .apply
  -- Rule 2: Ident/Greek + '(' => function call
  | .ident _, .lparen => .apply
  | .greekIdent _, .lparen => .apply
  -- Number + '(' => multiply: (2)(x+1) = 2*(x+1)
  | .number _, .lparen => .multiply
  -- ')' + '(' => multiply: (a+b)(c+d)
  | .rparen, .lparen => .multiply
  -- Rule 3: Number + Ident/Greek => multiply (2m, 3kg)
  | .number _, .ident _ => .multiply
  | .number _, .greekIdent _ => .multiply
  | .number _, .unitToken _ => .multiply
  -- Rule 4: Ident + Ident => multiply (m v)
  | .ident _, .ident _ => .multiply
  | .ident _, .greekIdent _ => .multiply
  | .greekIdent _, .ident _ => .multiply
  | .greekIdent _, .greekIdent _ => .multiply
  -- Ident + unit => multiply
  | .ident _, .unitToken _ => .multiply
  | .greekIdent _, .unitToken _ => .multiply
  -- Rule 5: ')'/']' + Ident/Number/'(' => multiply
  | .rparen, .ident _ => .multiply
  | .rparen, .greekIdent _ => .multiply
  | .rparen, .number _ => .multiply
  | .rparen, .unitToken _ => .multiply
  | .rbracket, .ident _ => .multiply
  | .rbracket, .greekIdent _ => .multiply
  | .rbracket, .number _ => .multiply
  | .rbracket, .lparen => .multiply
  -- Rule 7: Number + Number => error
  | .number _, .number _ => .error "ambiguous: two adjacent numbers"
  -- Unit + anything => error (use explicit * for unit products)
  | .unitToken _, _ => .error "unit token cannot be followed by juxtaposition"
  -- Default: error
  | _, _ => .error "cannot determine juxtaposition meaning"

end Measure.Scratch
