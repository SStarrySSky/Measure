/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Affine Arithmetic: general nonlinear function approximation and UncertaintyModel instance.
See docs/type-system.md Section 4.3.4.
-/
import Measure.Error.AffineNonlinear

namespace Measure.Error

namespace Affine

/-- Apply a nonlinear function via Chebyshev affine approximation.
    f(x_hat) ~ alpha * x_hat + zeta + delta * e_new -/
def applyNonlinear (x : Affine) (f _f' : Float → Float) : Affine :=
  let (a, b) := x.toInterval
  if b - a < 1e-300 then
    { exact (f x.center) with nextId := x.nextId }
  else
    let alpha := (f b - f a) / (b - a)
    let fa := f a
    let fb := f b
    let fMid := f ((a + b) / 2.0)
    let linMid := alpha * ((a + b) / 2.0)
    let zetaMid := (fa + fb) / 2.0 - alpha * (a + b) / 2.0
    let delta := Float.abs (fMid - linMid - zetaMid)
    let linear := scale alpha x |>.shift zetaMid
    let eid : NoiseId := ⟨linear.nextId⟩
    { linear with terms := linear.terms.insert eid delta, nextId := linear.nextId + 1 }

end Affine

instance : UncertaintyModel Affine where
  fromIndependent val sigma := Affine.fromUncertain val sigma
  fromExact val := Affine.exact val
  add := Affine.add
  sub := Affine.sub
  mul x y _ _ := Affine.mul x y
  div x y _ _ := Affine.div x y
  pow x _xVal n := Affine.applyNonlinear x
    (fun v => Float.pow v n)
    (fun v => n * Float.pow v (n - 1.0))
  neg x := Affine.scale (-1.0) x
  applyFunc x _ f f' := Affine.applyNonlinear x f f'
  centralValue x := x.center
  uncertainty x := x.radius
  toInterval := Affine.toInterval
  scale := Affine.scale

end Measure.Error
