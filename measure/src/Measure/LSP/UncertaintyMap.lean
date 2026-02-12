/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Uncertainty heatmap visualization for the Measure LSP server.
Custom LSP method: measure/uncertaintyMap.
See docs/syntax-and-integration.md Section 6.2.
-/
import Measure.LSP.DimHints

namespace Measure.LSP

/-- Which input variable contributes most to output uncertainty. -/
structure DominantContributor where
  varName              : String
  contributionFraction : Float  -- 0.0 to 1.0
  deriving Repr, Inhabited

/-- An entry in the uncertainty heatmap. -/
structure UncertaintyEntry where
  range                : Range
  varName              : String
  relativeUncertainty  : Float
  absoluteUncertainty  : Float
  unit                 : String := ""
  model                : String := "Gaussian"
  colorIntensity       : Float  -- 0.0 to 1.0
  dominantContributor  : Option DominantContributor := none
  deriving Repr, Inhabited

/-- Response for measure/uncertaintyMap request. -/
structure UncertaintyMap where
  entries : List UncertaintyEntry := []
  deriving Repr, Inhabited

namespace UncertaintyEntry

/-- Compute color intensity from relative uncertainty.
    Maps [0, 1] relative uncertainty to [0, 1] color intensity
    using a logarithmic scale for better visual discrimination. -/
def computeColorIntensity (relUncertainty : Float) : Float :=
  if relUncertainty <= 0.0 then 0.0
  else if relUncertainty >= 1.0 then 1.0
  else
    let logVal := Float.log10 (relUncertainty * 100.0 + 1.0)
    let maxLog := Float.log10 101.0
    logVal / maxLog

/-- Create an uncertainty entry with auto-computed color intensity. -/
def mk' (range : Range) (varName : String)
    (absUnc : Float) (value : Float)
    (unit : String := "") (model : String := "Gaussian")
    (dominant : Option DominantContributor := none) : UncertaintyEntry :=
  let relUnc := if value == 0.0 then 0.0 else Float.abs (absUnc / value)
  { range := range
    varName := varName
    relativeUncertainty := relUnc
    absoluteUncertainty := absUnc
    unit := unit
    model := model
    colorIntensity := computeColorIntensity relUnc
    dominantContributor := dominant }

end UncertaintyEntry

end Measure.LSP
