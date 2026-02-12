/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Gaussian error model: data structure and core operations.
See docs/type-system.md Section 4.2.
-/
import Std
import Measure.Error.GaussianBase

namespace Measure.Error

/-- Gaussian error model with derivative tag tracking. -/
structure Gaussian where
  mean   : Float
  sigma  : Float
  derivs : Derivatives
  deriving Repr, Inhabited

namespace Gaussian

/-- Create an independent measurement with a fresh tag.
    The derivative map stores df/dz_i * sigma_i so that
    sigma = sqrt(sum(d_i^2)) gives the correct propagated uncertainty. -/
def independent (val sigma : Float) : Gaussian :=
  let tag := Tag.fresh
  { mean := val
  , sigma := sigma
  , derivs := (∅ : Derivatives) |>.insert tag sigma }

/-- Merge two derivative maps using a combiner function. -/
def mergeDerivs (f : Float → Float → Float)
    (d1 d2 : Derivatives) : Derivatives :=
  let merged := d1.fold (init := d2) fun acc tag v1 =>
    match acc.get? tag with
    | some v2 => acc.insert tag (f v1 v2)
    | none    => acc.insert tag (f v1 0.0)
  d2.fold (init := merged) fun acc tag v2 =>
    match d1.get? tag with
    | some _ => acc
    | none   => acc.insert tag (f 0.0 v2)

/-- Compute sigma from derivatives (root-sum-of-squares). -/
def computeSigma (derivs : Derivatives) (sigmaMap : Tag → Float) : Float :=
  let sumSq := derivs.fold (init := 0.0) fun acc tag d =>
    let s := sigmaMap tag
    acc + d * d * s * s
  Float.sqrt sumSq

end Gaussian
