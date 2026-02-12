/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dimension unification algorithm.
Implements the unify(d1, d2) operation for dimension type checking.
See docs/type-system.md Section 1.5.
-/
import Std
import Measure.Dim.Basic

namespace Measure.Dim

/-- A dimension variable, used in generic dimension parameters. -/
structure DimVar where
  id : Nat
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- A dimension term: either a concrete Dim or a variable. -/
inductive DimTerm where
  | concrete (d : Dim)
  | var (v : DimVar)
  | mul (a b : DimTerm)
  | div (a b : DimTerm)
  | pow (a : DimTerm) (n : QExp)
  deriving Repr, Inhabited

/-- Substitution map: DimVar -> Dim -/
abbrev DimSubst := Std.HashMap DimVar Dim

/-- Result of dimension unification. -/
inductive UnifyResult where
  | success (subst : DimSubst)
  | failure (lhs rhs : DimTerm) (msg : String)
  deriving Repr, Nonempty

namespace DimTerm

/-- Evaluate a DimTerm to a concrete Dim under a substitution. -/
def eval (t : DimTerm) (σ : DimSubst) : Option Dim :=
  match t with
  | .concrete d => some d
  | .var v => σ.get? v
  | .mul a b => do
    let da ← a.eval σ
    let db ← b.eval σ
    pure (Dim.mul da db)
  | .div a b => do
    let da ← a.eval σ
    let db ← b.eval σ
    pure (Dim.div da db)
  | .pow a n => do
    let da ← a.eval σ
    pure (Dim.pow da n)

/-- Check if a DimVar occurs in a DimTerm (occurs check). -/
def containsVar (t : DimTerm) (v : DimVar) : Bool :=
  match t with
  | .concrete _ => false
  | .var w => v == w
  | .mul a b => a.containsVar v || b.containsVar v
  | .div a b => a.containsVar v || b.containsVar v
  | .pow a _ => a.containsVar v

end DimTerm

/-- Unify two dimension terms, producing a substitution or failure. -/
partial def unify (lhs rhs : DimTerm) (σ : DimSubst := ∅) : UnifyResult :=
  match lhs, rhs with
  -- Both concrete: check equality
  | .concrete d1, .concrete d2 =>
    if d1 == d2 then .success σ
    else .failure lhs rhs s!"Dimension mismatch: {repr d1} vs {repr d2}"
  -- Variable on left: bind
  | .var v, t =>
    match σ.get? v with
    | some d => unify (.concrete d) t σ
    | none =>
      match t.eval σ with
      | some d => .success (σ.insert v d)
      | none =>
        if t.containsVar v then
          .failure lhs rhs "Occurs check failed"
        else .failure lhs rhs "Cannot resolve dimension variable"
  -- Variable on right: symmetric
  | t, .var v => unify (.var v) t σ
  -- Structural: mul
  | .mul a1 b1, .mul a2 b2 =>
    match unify a1 a2 σ with
    | .success σ' => unify b1 b2 σ'
    | f => f
  -- Structural: div
  | .div a1 b1, .div a2 b2 =>
    match unify a1 a2 σ with
    | .success σ' => unify b1 b2 σ'
    | f => f
  -- Structural: pow
  | .pow a1 n1, .pow a2 n2 =>
    if n1 == n2 then unify a1 a2 σ
    else .failure lhs rhs s!"Power exponent mismatch: {repr n1} vs {repr n2}"
  -- Try evaluating both sides
  | _, _ =>
    match lhs.eval σ, rhs.eval σ with
    | some d1, some d2 =>
      if d1 == d2 then .success σ
      else .failure lhs rhs s!"Dimension mismatch: {repr d1} vs {repr d2}"
    | _, _ => .failure lhs rhs "Cannot unify dimension terms"

end Measure.Dim
