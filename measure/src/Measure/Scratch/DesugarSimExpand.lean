/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Desugar: simulation block full expansion algorithm.
See docs/syntax-and-integration.md Section 7.3.3.
-/
import Measure.Scratch.DesugarSim

namespace Measure.Scratch.Desugar

/-- Desugar a single simulation step to Lean4 statements. -/
def desugarSimStep (step : Scratch.SimStep) : List LeanStmt :=
  match step with
  | .primedUpdate var rhs =>
    [.letImm ("__" ++ var ++ "_next") (desugarExpr rhs)]
  | .letBinding var rhs =>
    [.letImm var (desugarExpr rhs)]
  | .funcCall fn args =>
    [.expr (.app fn (args.map desugarExpr))]
  | .assertStep cond msg =>
    let msgExpr := match msg with
      | some m => .strLit m
      | none => .strLit "assertion failed"
    [.expr (.app "Measure.Runtime.assert" [desugarExpr cond, msgExpr])]
  | .emitStep name value =>
    [.letImm ("_" ++ name) (desugarExpr value),
     .expr (.app "Measure.Runtime.emit" [.strLit name, .var ("_" ++ name)])]

/-- Generate state update statement from primed variables. -/
def genStateUpdate (primedVars : List String) : LeanStmt :=
  let fields := primedVars.map fun v => (v, LeanExpr.var ("__" ++ v ++ "_next"))
  .assign "state" (.structUpdate (.var "state") fields)

/-- Generate conservation check statements. -/
def genConservationCheck (qty : String) (tolerance : Float) : List LeanStmt :=
  let afterVar := "__conserve_" ++ qty ++ "_after"
  let beforeVar := "__conserve_" ++ qty ++ "_before"
  let deltaVar := "__delta_" ++ qty
  [ .letImm afterVar (.app ("genConservedExpr_" ++ qty) [.var "state"])
  , .letImm deltaVar
      (.app "Float.abs" [.hSub (.var afterVar) (.var beforeVar)])
  , .ifStmt (.app "GT.gt" [.var deltaVar, .float tolerance])
      [.expr (.app "Measure.Runtime.handleConservationViolation"
        [.strLit qty, .var "t", .var deltaVar, .float tolerance])]
  ]

end Measure.Scratch.Desugar
