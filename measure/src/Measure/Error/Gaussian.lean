/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Gaussian error model: data structure and core operations.
See docs/type-system.md Section 4.2.
-/
import Std
import Measure.Error.GaussianBase

/-! # Gaussian Error Model

Implements first-order (linear) error propagation for quantities with Gaussian
uncertainty. Each `Gaussian` value tracks a mean, a 1-sigma standard uncertainty,
and a derivative map (`Derivatives`) that records how the value depends on each
independent noise source.

The derivative map stores `∂f/∂zᵢ · σᵢ` for every source `zᵢ`, so the propagated
uncertainty is simply `σ = √(Σ dᵢ²)` (root-sum-of-squares). This approach correctly
handles correlated intermediate quantities because shared tags combine through the
derivative algebra rather than being double-counted.
-/

namespace Measure.Error

/-- Gaussian error model with derivative tag tracking. -/
structure Gaussian where
  mean     : Float
  sigma    : Float
  derivs   : Derivatives
  warnings : List String := []
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

/-- Compute sigma from derivatives (root-sum-of-squares).
    Since each derivative entry already stores `∂f/∂z_i · σ_i`,
    the propagated uncertainty is simply `√(Σ d_i²)`. -/
def computeSigma (derivs : Derivatives) : Float :=
  let sumSq := derivs.fold (init := 0.0) fun acc _ d =>
    acc + d * d
  Float.sqrt sumSq

/-- Threshold for relative uncertainty warning (10%). -/
def largeUncertaintyThreshold : Float := 0.1

/-- Check if result has large relative uncertainty and append warning if so.
    First-order Taylor expansion is inaccurate when sigma/|mean| > 10%. -/
def checkLargeUncertainty (g : Gaussian) : Gaussian :=
  let absMean := Float.abs g.mean
  if absMean > 0.0 then
    let relUnc := g.sigma / absMean
    if relUnc > largeUncertaintyThreshold then
      let pct := Float.round (relUnc * 1000.0) / 10.0
      { g with warnings := g.warnings ++
          [s!"Large relative uncertainty ({pct}%): first-order propagation may be inaccurate"] }
    else g
  else g

end Gaussian
