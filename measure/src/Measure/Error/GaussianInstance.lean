/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Gaussian UncertaintyModel instance.
-/
import Measure.Error.GaussianOps

namespace Measure.Error

instance : UncertaintyModel Gaussian where
  fromIndependent := Gaussian.independent
  fromExact val :=
    { mean := val, sigma := 0.0, derivs := ∅ }
  add := Gaussian.add
  sub := Gaussian.sub
  mul x y _xv _yv := Gaussian.mul x y
  div x y _xv _yv := Gaussian.div x y
  pow x _xVal n := Gaussian.pow x n
  neg x :=
    { mean := -x.mean
    , sigma := x.sigma
    , derivs := x.derivs.fold (init := (∅ : Derivatives)) fun acc t d =>
        acc.insert t (-d)
    , warnings := x.warnings }
  applyFunc x _ f f' := Gaussian.applyUnary x f f'
  centralValue x := x.mean
  uncertainty x := x.sigma
  toInterval x :=
    (x.mean - 3.0 * x.sigma, x.mean + 3.0 * x.sigma)
  scale c x :=
    { mean := c * x.mean
    , sigma := Float.abs c * x.sigma
    , derivs := x.derivs.fold (init := (∅ : Derivatives)) fun acc t d =>
        acc.insert t (c * d)
    , warnings := x.warnings }

end Measure.Error
