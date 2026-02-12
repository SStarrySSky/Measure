/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode AST: expression and declaration nodes.
See docs/syntax-and-integration.md Section 1.3-1.6.
-/
import Measure.Scratch.LocToken

namespace Measure.Scratch

/-- Comparison operators. -/
inductive CmpOp where
  | eq | neq | lt | gt | leq | geq | approx | muchLt | muchGt
  deriving Repr, Inhabited, BEq

/-- Unit expression (e.g., m/s^2, kg*m). -/
inductive UnitExpr where
  | base (name : String)
  | mul (a b : UnitExpr)
  | div (a b : UnitExpr)
  | pow (u : UnitExpr) (n : Int)
  deriving Repr, Inhabited

/-- Function parameter. -/
structure Param where
  name : String
  type : Option String := none
  deriving Repr, Inhabited

/-- Scratch Mode expression AST.
    Note: ifExpr/forExpr use `List Expr` for their bodies instead of `List Stmt`
    to avoid a circular dependency with Decl.lean. The Stmt wrapper is applied
    at the Decl level.
    forExpr embeds range components (start/stop/step) directly to avoid
    a mutual dependency with RangeExpr. -/
inductive Expr where
  | number (val : Float) (pos : SourcePos)
  | ident (name : String) (pos : SourcePos)
  | greekIdent (name : String) (pos : SourcePos)
  | add (lhs rhs : Expr)
  | sub (lhs rhs : Expr)
  | mul (lhs rhs : Expr)
  | div (lhs rhs : Expr)
  | neg (e : Expr)
  | pow (base : Expr) (exp : Expr)
  | abs (e : Expr)
  | call (fn : String) (args : List Expr)
  | juxtapose (lhs rhs : Expr)
  | pmLiteral (value sigma : Expr) (unit : Option UnitExpr)
  | withUnit (value : Expr) (unit : UnitExpr)
  | grouped (e : Expr)
  | vector (elems : List Expr)
  | matrix (rows : List (List Expr))
  | cmp (op : CmpOp) (lhs rhs : Expr)
  | ifExpr (cond : Expr) (then_ : List Expr)
      (elifs : List (Expr × List Expr)) (else_ : Option (List Expr))
  | forExpr (var : String) (start stop : Expr) (step : Option Expr)
      (body : List Expr)
  | lambda (params : List Param) (body : Expr)
  | letExpr (name : String) (type : Option String) (rhs : Expr)
  deriving Repr, Inhabited

/-- Range expression for loops (used at the Decl/SimulationNode level). -/
structure RangeExpr where
  start : Expr
  stop  : Expr
  step  : Option Expr
  deriving Repr, Inhabited

end Measure.Scratch
