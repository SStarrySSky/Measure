/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Interval Arithmetic operations and UncertaintyModel instance.
See docs/type-system.md Section 4.1.
-/
import Measure.Error.Interval

namespace Measure.Error

namespace Interval

/-- [a,b] + [c,d] = [a+c, b+d] -/
def add (x y : Interval) : Interval :=
  { lo := x.lo + y.lo, hi := x.hi + y.hi }

/-- [a,b] - [c,d] = [a-d, b-c] -/
def sub (x y : Interval) : Interval :=
  { lo := x.lo - y.hi, hi := x.hi - y.lo }

/-- [a,b] * [c,d] = [min(ac,ad,bc,bd), max(ac,ad,bc,bd)] -/
def mul (x y : Interval) : Interval :=
  let p1 := x.lo * y.lo
  let p2 := x.lo * y.hi
  let p3 := x.hi * y.lo
  let p4 := x.hi * y.hi
  let lo := min (min p1 p2) (min p3 p4)
  let hi := max (max p1 p2) (max p3 p4)
  { lo, hi }

/-- [a,b] / [c,d] = [a,b] * [1/d, 1/c], requires 0 not in [c,d] -/
def div (x y : Interval) : Interval :=
  if y.containsZero then
    { lo := -(1.0/0.0), hi := (1.0/0.0) }
  else
    mul x { lo := 1.0 / y.hi, hi := 1.0 / y.lo }

end Interval
