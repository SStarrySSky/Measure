/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode AST: top-level declarations and simulation blocks.
See docs/syntax-and-integration.md Section 1.4-1.6.
-/
import Measure.Scratch.Expr

namespace Measure.Scratch

/-- Attribute entry (e.g., rigor strict, conserve energy). -/
structure AttrEntry where
  name : String
  args : List String := []
  deriving Repr, Inhabited

/-- Verify clause. -/
structure VerifyClause where
  name : String
  expr : Option Expr := none  -- none for anonymous expression clauses
  deriving Repr, Inhabited

/-- Simulation step (inside a simulation loop body). -/
inductive SimStep where
  | primedUpdate (var : String) (rhs : Expr)
  | letBinding (var : String) (rhs : Expr)
  | funcCall (fn : String) (args : List Expr)
  | assertStep (cond : Expr) (msg : Option String)
  | emitStep (name : String) (value : Expr)
  deriving Repr, Inhabited

/-- Simulation block node. -/
structure SimulationNode where
  name      : String
  attrs     : List AttrEntry
  initStmts : List (String × Expr)
  loopVar   : String
  loopRange : RangeExpr
  loopBody  : List SimStep
  deriving Repr, Inhabited

/-- Top-level statement in Scratch Mode. -/
inductive Stmt where
  | letDecl (name : String) (type : Option String) (rhs : Expr)
  | defDecl (name : String) (params : List Param)
      (retType : Option String) (body : List Stmt)
  | importStmt (path : List String)
  | fromImport (path : List String) (names : List String)
  | simulation (sim : SimulationNode)
  | compute (name : String) (engine : String) (body : Expr)
      (rawBody : Option String := none)  -- raw block for multi-line external code
  | verify (name : String) (clauses : List VerifyClause)
  | assertStmt (cond : Expr) (msg : Option String)
  | emitStmt (name : String) (value : Expr)
  | exprStmt (e : Expr)
  | attributed (attrs : List AttrEntry) (inner : Stmt)
  deriving Repr, Inhabited

/-- Complete Scratch Mode program. -/
structure Program where
  moduleName : Option String := none
  stmts      : List Stmt
  deriving Repr, Inhabited

end Measure.Scratch
