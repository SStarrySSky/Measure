/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dimension inference algorithm.
Walks expression ASTs and infers/checks dimension annotations.
See docs/type-system.md Section 1.5.
-/
import Std
import Measure.Dim.Basic
import Measure.Dim.Unify

namespace Measure.Dim

/-- Dimension inference context: maps variable names to their dimensions. -/
abbrev DimEnv := Std.HashMap Lean.Name Dim

/-- Result of dimension inference on an expression. -/
inductive InferResult where
  | ok (dim : Dim) (subst : DimSubst)
  | error (msg : String)
  deriving Repr

/-- Dimension signature for a function. -/
structure DimSignature where
  /-- Dimension of each parameter -/
  params : Array DimTerm
  /-- Dimension of the return type -/
  ret : DimTerm
  /-- Generic dimension variables -/
  dimVars : Array DimVar
  deriving Repr, Inhabited

/-- Registry of known function dimension signatures. -/
abbrev SigRegistry := Std.HashMap Lean.Name DimSignature

end Measure.Dim
