/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Desugar: expression translation rules.
See docs/syntax-and-integration.md Section 7.5.
-/
import Measure.Scratch.DesugarTypes
import Measure.Scratch.Expr

namespace Measure.Scratch.Desugar

/-- Desugar a Scratch expression to Lean4 IR. -/
partial def desugarExpr (e : Scratch.Expr) : LeanExpr :=
  match e with
  | .number val _ => .float val
  | .ident name _ => .var name
  | .greekIdent name _ => .var name
  | .add lhs rhs => .hAdd (desugarExpr lhs) (desugarExpr rhs)
  | .sub lhs rhs => .hSub (desugarExpr lhs) (desugarExpr rhs)
  | .mul lhs rhs => .hMul (desugarExpr lhs) (desugarExpr rhs)
  | .div lhs rhs => .hDiv (desugarExpr lhs) (desugarExpr rhs)
  | .neg e => .neg (desugarExpr e)
  | .pow base exp => .hPow (desugarExpr base) (desugarExpr exp)
  | .abs e => .abs (desugarExpr e)
  | .call fn args => .app ("Measure." ++ fn) (args.map desugarExpr)
  | .juxtapose lhs rhs => .hMul (desugarExpr lhs) (desugarExpr rhs)
  | .grouped e => desugarExpr e
  | .pmLiteral value sigma unit =>
    let v := desugarExpr value
    let s := desugarExpr sigma
    let u := match unit with
      | some ue => desugarUnit ue
      | none => .var "Unit.dimensionless"
    .quantityMk v (.app "Gaussian.mk" [v, s]) u (.var "Provenance.none")
  | .withUnit value unit =>
    .quantityExact (desugarExpr value) (desugarUnit unit)
  | .vector elems => .app "Vector.mk" (elems.map desugarExpr)
  | .matrix rows =>
    .app "Matrix.mk" (rows.map fun row =>
      .app "Vector.mk" (row.map desugarExpr))
  | .cmp op lhs rhs => desugarCmp op lhs rhs
  | .ifExpr cond then_ _ _ =>
    .ifThenElse (desugarExpr cond)
      (.doBlock (then_.map desugarExprToLeanStmt))
      .unit
  | .forExpr var start stop step body =>
    let rangeExpr := match step with
      | some s => .app "Measure.Range.mk"
          [desugarExpr start, desugarExpr stop, desugarExpr s]
      | none => .app "Measure.Range.mk"
          [desugarExpr start, desugarExpr stop, .float 1.0]
    .forIn var rangeExpr
      (.doBlock (body.map desugarExprToLeanStmt))
  | .letExpr name _ rhs =>
    .letBind name none (desugarExpr rhs) .unit
  | .lambda _params body =>
    .app "fun" [desugarExpr body]

where
  desugarUnit : Scratch.UnitExpr → LeanExpr
    | .base name => .var ("SI." ++ name)
    | .mul a b => .app "Unit.mul" [desugarUnit a, desugarUnit b]
    | .div a b => .app "Unit.div" [desugarUnit a, desugarUnit b]
    | .pow u n => .app "Unit.pow" [desugarUnit u, .float (Float.ofInt n)]

  desugarCmp : Scratch.CmpOp → Scratch.Expr → Scratch.Expr → LeanExpr
    | .eq, l, r => .app "BEq.beq" [desugarExpr l, desugarExpr r]
    | .neq, l, r => .app "bne" [desugarExpr l, desugarExpr r]
    | .lt, l, r => .app "LT.lt" [desugarExpr l, desugarExpr r]
    | .gt, l, r => .app "GT.gt" [desugarExpr l, desugarExpr r]
    | .leq, l, r => .app "LE.le" [desugarExpr l, desugarExpr r]
    | .geq, l, r => .app "GE.ge" [desugarExpr l, desugarExpr r]
    | .approx, l, r => .app "Measure.approxEq" [desugarExpr l, desugarExpr r]
    | .muchLt, l, r => .app "Measure.muchLt" [desugarExpr l, desugarExpr r]
    | .muchGt, l, r => .app "Measure.muchGt" [desugarExpr l, desugarExpr r]

  desugarExprToLeanStmt : Scratch.Expr → LeanStmt
    | .letExpr name _ rhs => .letImm name (desugarExpr rhs)
    | e => .expr (desugarExpr e)

end Measure.Scratch.Desugar
