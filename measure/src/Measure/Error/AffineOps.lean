/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Affine Arithmetic operations.
See docs/type-system.md Section 4.3.
-/
import Measure.Error.Affine

namespace Measure.Error

namespace Affine

/-- Merge two noise-term maps with a combiner. -/
def mergeTerms (f : Float → Float → Float)
    (t1 t2 : Std.HashMap NoiseId Float) : Std.HashMap NoiseId Float :=
  let merged := t1.fold (init := t2) fun acc nid c1 =>
    match acc.get? nid with
    | some c2 =>
      let v := f c1 c2
      if Float.abs v < 1e-300 then acc.erase nid else acc.insert nid v
    | none => acc.insert nid (f c1 0.0)
  t2.fold (init := merged) fun acc nid c2 =>
    match t1.get? nid with
    | some _ => acc
    | none   => acc.insert nid (f 0.0 c2)

/-- z = x + y (exact, no new noise symbol). -/
def add (x y : Affine) : Affine :=
  { center := x.center + y.center
  , terms := mergeTerms (· + ·) x.terms y.terms
  , nextId := mergeNextId x y }

/-- z = x - y (exact). x - x => all terms cancel => radius = 0. -/
def sub (x y : Affine) : Affine :=
  { center := x.center - y.center
  , terms := mergeTerms (· - ·) x.terms y.terms
  , nextId := mergeNextId x y }

/-- Scalar multiply: z = c * x. -/
def scale (c : Float) (x : Affine) : Affine :=
  { center := c * x.center
  , terms := x.terms.fold (init := (∅ : Std.HashMap NoiseId Float)) fun acc nid coeff =>
      acc.insert nid (c * coeff)
  , nextId := x.nextId }

/-- Constant shift: z = x + c. -/
def shift (x : Affine) (c : Float) : Affine :=
  { x with center := x.center + c }

end Affine
end Measure.Error
