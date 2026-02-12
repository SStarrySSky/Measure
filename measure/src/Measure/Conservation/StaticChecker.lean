/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Conservation.Law

/-! # Conservation Static Checker

Three-pass static analysis algorithm:
- Pass 1: Decompose update function into atomic mutations
- Pass 2: Compute symbolic delta for each conserved quantity
- Pass 3: Residual analysis for symbolic deltas
-/

namespace Measure.Conservation

/-- Result of static conservation analysis. -/
inductive ConservationVerdict where
  | verified (proof : String)
  | verifiedApprox (bound : String)
  | inconclusive (reason : String)
  | violation (delta : String) (hint : String)
  deriving Inhabited, Repr

/-- An atomic state mutation from Pass 1. -/
structure AtomicMutation where
  target : String
  oldVal : String
  newVal : String
  line : Nat := 0
  deriving Inhabited, Repr

/-- Delta classification from Pass 2. -/
inductive DeltaResult where
  | zero
  | nonzero (value : Float)
  | symbolic (expr : String)
  deriving Inhabited, Repr

namespace StaticChecker

/-- Pass 2: Compute symbolic delta for a conservation law
    given a list of atomic mutations. -/
def computeDelta (law : ConservationLaw)
    (mutations : List AtomicMutation) : DeltaResult :=
  let relevant := mutations.filter fun m =>
    (law.quantityExpr.splitOn m.target).length > 1
  if relevant.isEmpty then .zero
  else .symbolic s!"delta({law.quantityExpr})"

/-- Pass 3: Residual analysis for a symbolic delta. -/
def residualAnalysis (delta : DeltaResult)
    (law : ConservationLaw) : ConservationVerdict :=
  match delta with
  | .zero => .verified "delta = 0"
  | .nonzero v => .violation (toString v)
      s!"Conservation of {law.name} violated: delta = {v}"
  | .symbolic expr =>
      .inconclusive s!"Static analysis inconclusive for {law.name}: {expr}"

/-- Main entry: check a single law against mutations. -/
def checkLaw (law : ConservationLaw)
    (mutations : List AtomicMutation) : ConservationVerdict :=
  let delta := computeDelta law mutations
  residualAnalysis delta law

end StaticChecker
end Measure.Conservation
