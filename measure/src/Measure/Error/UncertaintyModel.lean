/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

UncertaintyModel typeclass: unified interface for all error propagation models.
See docs/type-system.md Section 5.
-/
import Measure.Dim.Basic

namespace Measure.Error

/-- Unified interface for uncertainty propagation models.
    All three built-in models (Interval, Gaussian, Affine) implement this. -/
class UncertaintyModel (α : Type) where
  /-- Create from independent measurement (new internal tag). -/
  fromIndependent (value sigma : Float) : α
  /-- Create from exact value (zero uncertainty). -/
  fromExact (value : Float) : α
  /-- Addition: f = x + y -/
  add : α → α → α
  /-- Subtraction: f = x - y -/
  sub : α → α → α
  /-- Multiplication: f = x * y (needs center values for derivative). -/
  mul (x y : α) (xVal yVal : Float) : α
  /-- Division: f = x / y (needs center values). -/
  div (x y : α) (xVal yVal : Float) : α
  /-- Power: f = x^n (needs center value and exponent). -/
  pow (x : α) (xVal n : Float) : α
  /-- Negation: f = -x -/
  neg : α → α
  /-- Apply arbitrary differentiable function via chain rule. -/
  applyFunc (x : α) (xVal : Float) (f f' : Float → Float) : α
  /-- Central value / best estimate. -/
  centralValue : α → Float
  /-- Standard uncertainty (1-sigma or half-width). -/
  uncertainty : α → Float
  /-- Convert to conservative interval [lo, hi]. -/
  toInterval : α → Float × Float
  /-- Scalar scaling (for unit conversion). -/
  scale (c : Float) : α → α

end Measure.Error
