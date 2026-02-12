/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode lexer: source position and token with location.
-/
import Measure.Scratch.Token

namespace Measure.Scratch

/-- Source position for error reporting. -/
structure SourcePos where
  line   : Nat
  column : Nat
  offset : Nat
  deriving Repr, Inhabited, BEq

/-- Token with source location. -/
structure LocToken where
  kind : TokenKind
  pos  : SourcePos
  text : String
  deriving Repr, Inhabited

end Measure.Scratch
