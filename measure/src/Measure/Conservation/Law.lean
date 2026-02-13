/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Theory.Module

/-! # Conservation Law Definitions

Core data structures for conservation law checking:
- `ConservationLaw`: a quantity that must remain constant
- `ConservationSource`: how the law was established
- `ConservationVerdict`: result of static analysis
-/

namespace Measure.Conservation

open Measure.Theory

/-- Source of a conservation law. -/
inductive ConservationSource where
  | declared
  | noether (sym : SymmetryDecl)
  | inherited (fromTheory : String)
  deriving Inhabited, Repr

/-- Exactness of conservation. -/
inductive ConservationExactness where
  | exact
  | approximate (errorOrder : String)
  | anomalouslyBroken (anomaly : String)
  deriving Inhabited, Repr

/-- A conservation law. -/
structure ConservationLaw where
  name : String
  quantityExpr : String
  source : ConservationSource := .declared
  exactness : ConservationExactness := .exact
  tolerance : Float := 1e-10
  deriving Inhabited, Repr

end Measure.Conservation
