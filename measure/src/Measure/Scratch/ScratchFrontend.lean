/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode frontend: top-level entry point.
parseScratch : String → Except String Expr
parseScratchProgram : String → Except String Program
evalScratch : Env → String → IO (Env × String)
evalScratchProgram : Env → String → IO (Env × List String)
See docs/syntax-and-integration.md Section 1.
-/
import Measure.Scratch.ParseStmt
import Measure.Scratch.Eval

namespace Measure.Scratch

/-- Tokenize and parse a string into a single Scratch expression. -/
def parseScratch (input : String) : Except String Expr :=
  let tokens := Lexer.tokenize input
  let arr := tokens.toArray
  if arr.isEmpty then
    .error "empty input"
  else
    let s : ParserState := { tokens := arr }
    match Parser.parseExpr s 0 with
    | .ok (_, expr) => .ok expr
    | .error e => .error e

/-- Tokenize and parse a string into a complete Scratch program. -/
def parseScratchProgram (input : String) : Except String Program :=
  let tokens := Lexer.tokenize input
  let arr := tokens.toArray
  if arr.isEmpty then
    .error "empty input"
  else
    let s : ParserState := { tokens := arr }
    match Parser.parseProgram s with
    | .ok (_, prog) => .ok prog
    | .error e => .error e

/-- Tokenize and parse a string into a list of top-level statements. -/
def parseScratchStmts (input : String) : Except String (List Stmt) :=
  match parseScratchProgram input with
  | .ok prog => .ok prog.stmts
  | .error e => .error e

/-- Tokenize only: return the token list for debugging. -/
def tokenizeScratch (input : String) : List LocToken :=
  Lexer.tokenize input

end Measure.Scratch
