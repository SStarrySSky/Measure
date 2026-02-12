/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode runtime: value types for the AST interpreter.
Reuses Measure.Dim.Dim, Measure.Error.Interval, and Measure.Quantity.Quantity.
-/
import Measure.Scratch.Expr
import Measure.Dim.Basic
import Measure.Error.IntervalInstance
import Measure.Quantity.Basic

namespace Measure.Scratch

open Measure.Dim
open Measure.Error
open Measure.Quantity

/-- Runtime value for the Scratch Mode interpreter.
    Wraps Quantity where possible, with extensions for vectors/matrices/closures.
    Closures capture a snapshot of the environment as a flat variable map
    to implement lexical scoping without circular dependency on Env. -/
inductive Value where
  | number (val : Float)
  | withUnit (val : Float) (unit : UnitExpr) (dim : Dim)
  | withUncertainty (val : Float) (err : Interval) (unit : Option UnitExpr) (dim : Dim)
  | quantity (val : Float) (dim : Dim) (err : Option Interval)
  | vector (elems : Array Value)
  | matrix (rows : Array (Array Value))
  | bool (val : Bool)
  | string (val : String)
  | closure (params : List Param) (body : Expr) (envSnapshot : List (String × Value))
  | unit
  deriving Repr, Inhabited

namespace Value

/-- Extract the numeric value from a Value, if possible. -/
def toFloat? : Value → Option Float
  | .number v => some v
  | .withUnit v _ _ => some v
  | .withUncertainty v _ _ _ => some v
  | .quantity v _ _ => some v
  | _ => none

/-- Extract the dimension from a Value. -/
def getDim : Value → Dim
  | .number _ => Dim.dimensionless
  | .withUnit _ _ d => d
  | .withUncertainty _ _ _ d => d
  | .quantity _ d _ => d
  | _ => Dim.dimensionless

/-- Extract the Interval error from a Value, if any. -/
def getInterval? : Value → Option Interval
  | .withUncertainty _ err _ _ => some err
  | .quantity _ _ (some err) => some err
  | _ => none

/-- Extract the uncertainty (sigma = half-width) from a Value, defaulting to 0. -/
def getSigma : Value → Float
  | .withUncertainty _ err _ _ => err.halfWidth
  | .quantity _ _ (some err) => err.halfWidth
  | _ => 0.0

/-- Check if two values have compatible dimensions for addition/subtraction. -/
def dimCompatible (a b : Value) : Bool :=
  a.getDim == b.getDim

/-- Wrap a Quantity into a Value. -/
def fromExactQ (d : Dim) (q : ExactQ d) : Value :=
  .quantity q.value d none

end Value

end Measure.Scratch
