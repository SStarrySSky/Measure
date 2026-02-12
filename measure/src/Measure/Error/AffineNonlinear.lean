/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Affine non-linear operations (mul, div, transcendental functions).
See docs/type-system.md Section 4.3.3.
-/
import Measure.Error.AffineOps

namespace Measure.Error

namespace Affine

/-- Merge two noise-term maps with a combiner (local copy for non-linear ops). -/
private def mergeTermsNL (f : Float → Float → Float)
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

/-- Multiplication: linear part + new noise symbol for quadratic residual.
    z = x * y = x0*y0 + sum(x0*yi + y0*xi)*ei + delta*e_new -/
def mul (x y : Affine) : Affine :=
  let linearTerms := mergeTermsNL
    (fun cx cy => y.center * cx + x.center * cy)
    x.terms y.terms
  let delta := x.radius * y.radius
  let eid := NoiseId.fresh
  let allTerms := if delta > 1e-300
    then linearTerms.insert eid delta
    else linearTerms
  { center := x.center * y.center, terms := allTerms }

/-- Reciprocal via Chebyshev approximation on [a, b].
    Requires 0 not in [a, b]. -/
def reciprocal (y : Affine) : Affine :=
  let (a, b) := y.toInterval
  if a ≤ 0.0 && 0.0 ≤ b then
    { center := (1.0 / 0.0), terms := ∅ }
  else
    let alpha := -1.0 / (a * b)
    let mid := 0.5 * (1.0 / a + 1.0 / b)
    let zeta := mid - 0.5 * alpha * (a + b)
    -- Evaluate error at geometric mean (where Chebyshev error peaks)
    let geoMean := if a > 0.0 then Float.sqrt (a * b)
                   else -Float.sqrt (a * b)
    let delta := Float.abs (1.0 / geoMean - (alpha * geoMean + zeta))
    let linear := scale alpha y |>.shift zeta
    let eid := NoiseId.fresh
    { linear with terms := linear.terms.insert eid delta }

/-- Division: x / y = x * (1/y). -/
def div (x y : Affine) : Affine :=
  let yInv := reciprocal y
  mul x yInv

end Affine
end Measure.Error
