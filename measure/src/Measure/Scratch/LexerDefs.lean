/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode lexer implementation.
See docs/syntax-and-integration.md Section 1.2.
-/
import Measure.Scratch.LocToken

namespace Measure.Scratch

/-- Known built-in function names for juxtaposition disambiguation. -/
def knownFunctions : List String :=
  ["sin", "cos", "tan", "exp", "log", "ln", "sqrt", "abs",
   "cross", "dot", "norm",
   "div", "curl", "grad", "laplacian", "det", "tr", "fft", "ifft"]

/-- Known SI unit tokens. -/
def knownUnits : List String :=
  ["kg", "m", "s", "A", "K", "mol", "cd",
   "N", "J", "W", "Pa", "Hz", "C", "V",
   "eV", "GeV", "MeV", "keV", "TeV"]

/-- Keywords map. -/
def keywords : List (String × TokenKind) :=
  [("let", .kwLet), ("def", .kwDef), ("if", .kwIf),
   ("elif", .kwElif), ("else", .kwElse), ("for", .kwFor),
   ("in", .kwIn), ("step", .kwStep), ("do", .kwDo),
   ("fun", .kwFun), ("import", .kwImport), ("from", .kwFrom),
   ("module", .kwModule), ("simulation", .kwSimulation),
   ("assert", .kwAssert), ("emit", .kwEmit),
   ("compute", .kwCompute), ("verify", .kwVerify),
   ("where", .kwWhere), ("via", .kwVia), ("theory", .kwTheory),
   ("axiom", .kwAxiom), ("theorem", .kwTheorem), ("by", .kwBy)]

end Measure.Scratch
