/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Interval UncertaintyModel instance.
-/
import Measure.Error.IntervalOps

namespace Measure.Error

instance : UncertaintyModel Interval where
  fromIndependent val sigma :=
    { lo := val - sigma, hi := val + sigma }
  fromExact val :=
    { lo := val, hi := val }
  add := Interval.add
  sub := Interval.sub
  mul x y _ _ := Interval.mul x y
  div x y _ _ := Interval.div x y
  pow x _xVal n :=
    let lo := Float.pow x.lo n
    let hi := Float.pow x.hi n
    if n == Float.floor n && (n.toUInt64.toNat % 2 == 0) then
      if x.lo ≥ 0.0 then { lo, hi }
      else if x.hi ≤ 0.0 then { lo := hi, hi := lo }
      else { lo := 0.0, hi := max lo hi }
    else Interval.mk' lo hi
  neg x := { lo := -x.hi, hi := -x.lo }
  applyFunc x _ f _ :=
    let a := f x.lo
    let b := f x.hi
    Interval.mk' a b
  centralValue x := x.midpoint
  uncertainty x := x.halfWidth
  toInterval x := (x.lo, x.hi)
  scale c x :=
    if c ≥ 0.0 then { lo := c * x.lo, hi := c * x.hi }
    else { lo := c * x.hi, hi := c * x.lo }

end Measure.Error
