/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Interval Arithmetic: conservative error propagation via closed intervals.
See docs/type-system.md Section 4.1.
-/
import Measure.Error.UncertaintyModel

namespace Measure.Error

/-- Closed interval [lo, hi] with lo <= hi invariant. -/
structure Interval where
  lo : Float
  hi : Float
  deriving Repr, Inhabited, BEq

namespace Interval

def mk' (lo hi : Float) : Interval :=
  if lo ≤ hi then { lo, hi } else { lo := hi, hi := lo }

def midpoint (i : Interval) : Float :=
  (i.lo + i.hi) / 2.0

def halfWidth (i : Interval) : Float :=
  (i.hi - i.lo) / 2.0

def contains (i : Interval) (v : Float) : Bool :=
  i.lo ≤ v && v ≤ i.hi

def containsZero (i : Interval) : Bool :=
  i.lo ≤ 0.0 && 0.0 ≤ i.hi

end Interval
