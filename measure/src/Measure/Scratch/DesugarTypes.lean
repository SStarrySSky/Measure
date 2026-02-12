/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Desugar: Scratch Mode AST -> Lean4 core expressions.
See docs/syntax-and-integration.md Section 7.3-7.5.
-/
import Measure.Scratch.Decl

namespace Measure.Scratch.Desugar

-- Lean4 target expression and statement types (mutually recursive).
mutual
/-- Lean4 target expression (simplified IR for desugar output). -/
inductive LeanExpr where
  | float (val : Float)
  | var (name : String)
  | app (fn : String) (args : List LeanExpr)
  | hAdd (lhs rhs : LeanExpr)
  | hSub (lhs rhs : LeanExpr)
  | hMul (lhs rhs : LeanExpr)
  | hDiv (lhs rhs : LeanExpr)
  | hPow (base exp : LeanExpr)
  | neg (e : LeanExpr)
  | abs (e : LeanExpr)
  | quantityMk (value : LeanExpr) (error : LeanExpr)
      (unit : LeanExpr) (prov : LeanExpr)
  | quantityExact (value : LeanExpr) (unit : LeanExpr)
  | letBind (name : String) (type : Option String)
      (val : LeanExpr) (body : LeanExpr)
  | doBlock (stmts : List LeanStmt)
  | structLit (name : String) (fields : List (String × LeanExpr))
  | structUpdate (base : LeanExpr) (fields : List (String × LeanExpr))
  | ifThenElse (cond body else_ : LeanExpr)
  | forIn (var : String) (range body : LeanExpr)
  | strLit (s : String)
  | unit

/-- Lean4 target statement (inside do blocks). -/
inductive LeanStmt where
  | letMut (name : String) (val : LeanExpr)
  | letImm (name : String) (val : LeanExpr)
  | assign (name : String) (val : LeanExpr)
  | expr (e : LeanExpr)
  | ifStmt (cond : LeanExpr) (body : List LeanStmt)
  | ret (e : LeanExpr)
end

instance : Inhabited LeanExpr := ⟨.unit⟩
instance : Inhabited LeanStmt := ⟨.expr .unit⟩

end Measure.Scratch.Desugar
