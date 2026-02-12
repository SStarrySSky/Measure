/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Gaussian arithmetic operations and UncertaintyModel instance.
See docs/type-system.md Section 4.2.
-/
import Measure.Error.Gaussian

namespace Measure.Error

namespace Gaussian

/-- f = x + y: derivatives add linearly. -/
def add (x y : Gaussian) : Gaussian :=
  let newDerivs := mergeDerivs (· + ·) x.derivs y.derivs
  let sumSq := newDerivs.fold (init := 0.0) fun acc _ d => acc + d * d
  { mean := x.mean + y.mean
  , sigma := Float.sqrt sumSq
  , derivs := newDerivs }

/-- f = x - y: derivatives subtract. x - x => sigma = 0 (correct). -/
def sub (x y : Gaussian) : Gaussian :=
  let newDerivs := mergeDerivs (· - ·) x.derivs y.derivs
  let sumSq := newDerivs.fold (init := 0.0) fun acc _ d => acc + d * d
  { mean := x.mean - y.mean
  , sigma := Float.sqrt sumSq
  , derivs := newDerivs }

/-- f = x * y: first-order product rule. -/
def mul (x y : Gaussian) : Gaussian :=
  let newDerivs := mergeDerivs
    (fun dx dy => y.mean * dx + x.mean * dy)
    x.derivs y.derivs
  let sumSq := newDerivs.fold (init := 0.0) fun acc _ d => acc + d * d
  { mean := x.mean * y.mean
  , sigma := Float.sqrt sumSq
  , derivs := newDerivs }

/-- f = x / y: first-order quotient rule. -/
def div (x y : Gaussian) : Gaussian :=
  let yInv := 1.0 / y.mean
  let yInvSq := yInv * yInv
  let newDerivs := mergeDerivs
    (fun dx dy => dx * yInv - x.mean * yInvSq * dy)
    x.derivs y.derivs
  let sumSq := newDerivs.fold (init := 0.0) fun acc _ d => acc + d * d
  { mean := x.mean / y.mean
  , sigma := Float.sqrt sumSq
  , derivs := newDerivs }

/-- f = x^n: power rule. -/
def pow (x : Gaussian) (n : Float) : Gaussian :=
  let coeff := n * Float.pow x.mean (n - 1.0)
  let newDerivs := x.derivs.fold (init := (∅ : Derivatives)) fun acc tag d =>
    acc.insert tag (coeff * d)
  let sumSq := newDerivs.fold (init := 0.0) fun acc _ d => acc + d * d
  { mean := Float.pow x.mean n
  , sigma := Float.sqrt sumSq
  , derivs := newDerivs }

/-- Apply unary function via chain rule: f'(x.mean) * dx/dzi. -/
def applyUnary (x : Gaussian) (f f' : Float → Float) : Gaussian :=
  let coeff := f' x.mean
  let newDerivs := x.derivs.fold (init := (∅ : Derivatives)) fun acc tag d =>
    acc.insert tag (coeff * d)
  let sumSq := newDerivs.fold (init := 0.0) fun acc _ d => acc + d * d
  { mean := f x.mean
  , sigma := Float.sqrt sumSq
  , derivs := newDerivs }

end Gaussian
