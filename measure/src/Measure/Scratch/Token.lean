/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode lexer: tokenizes .msr files with physics-aware rules.
Handles space-multiply, +- uncertainty, Unicode superscripts, Greek letters.
See docs/syntax-and-integration.md Section 1.2.
-/

namespace Measure.Scratch

/-- Token types for Scratch Mode lexer. -/
inductive TokenKind where
  | number (val : Float)
  | ident (name : String)
  | greekIdent (name : String)
  | knownFunc (name : String)
  | unitToken (name : String)
  | lparen | rparen
  | lbracket | rbracket
  | lbrace | rbrace
  | plus | minus | star | slash
  | caret
  | pmOp          -- +- or +/- or U+00B1
  | eq | eqEq | neq | lt | gt | leq | geq
  | approxEq      -- U+2248
  | muchLt        -- << (much less than)
  | muchGt        -- >> (much greater than)
  | approxEqBrack -- ≈[ (approx-equal with tolerance bracket)
  | assign        -- =
  | colon | comma | dot | dotDot
  | arrow         -- ->
  | fatArrow      -- =>
  | prime         -- '
  | pipe          -- |
  | underscore    -- _
  | newline
  | indent (depth : Nat)
  | kwLet | kwDef | kwIf | kwElif | kwElse
  | kwFor | kwIn | kwStep | kwDo
  | kwFun | kwImport | kwFrom | kwModule
  | kwSimulation | kwAssert | kwEmit
  | kwCompute | kwVerify | kwWhere | kwVia
  | kwTheory | kwAxiom | kwTheorem | kwBy
  | attrOpen      -- @[
  | attrClose     -- ]
  | comment (text : String)
  | eof
  deriving Repr, Inhabited, BEq
