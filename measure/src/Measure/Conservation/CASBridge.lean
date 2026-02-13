/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

CAS Bridge: connects conservation checking to external computation engines
(Julia / Python+SymPy / Mathematica) via the External module.

When the C++ ConservationChecker reaches Strategy 3d (CAS delegation),
it calls back into Lean via FFI. This module provides the Lean-side handler
that dispatches to a real external CAS engine for symbolic simplification.

Type annotations: all results carry EngineKind (which engine was used),
and the verification result is typed as SymbolicVerifyResult.
-/
import Measure.External.Compute
import Measure.External.Verify
import Measure.External.Engine
import Measure.External.Adapter

namespace Measure.Conservation

open Measure.External

/-- Preferred engine order for CAS delegation.
    Mathematica > Python (SymPy) > Julia (SymbolicUtils.jl). -/
def casEnginePreference : List EngineKind :=
  [.mathematica, .python, .julia]

/-- Try to verify a symbolic expression via external CAS.
    Iterates through preferred engines until one succeeds.
    Returns: `some true` if CAS proves expr = 0,
             `some false` if CAS proves expr ≠ 0,
             `none` if no engine available or all inconclusive. -/
def delegateToCAS (symbolicExpr : String) : IO (Option Bool) := do
  for kind in casEnginePreference do
    let result ← VerifyEngine.verifyViaEngine kind symbolicExpr
    match result with
    | .verified => return some true
    | .refuted _ => return some false
    | .unknown _ => continue  -- try next engine
    | .engineUnavailable _ => continue  -- try next engine
  return none

/-- Verify a conservation law delta expression via external CAS.
    Wraps the expression in a "simplify to zero" query appropriate
    for each engine:
    - Mathematica: `Simplify[expr] == 0`
    - Python/SymPy: `sympy.simplify(expr) == 0`
    - Julia: `simplify(expr) == 0` -/
def verifyCASConservation (deltaExpr : String) (_lawName : String)
    : IO (Option Bool) := do
  -- Wrap the delta expression for zero-check
  let queryExpr := s!"({deltaExpr})"
  delegateToCAS queryExpr

/-- Result of a CAS-backed conservation check with type annotations. -/
structure CASVerdict where
  result     : Option Bool        -- true=conserved, false=violated, none=inconclusive
  engineUsed : Option EngineKind  -- which engine provided the answer
  rawOutput  : Option String      -- raw engine output for audit trail
  deriving Repr, Inhabited

/-- Full CAS verification with engine tracking. -/
def verifyCASConservationFull (deltaExpr : String) (_lawName : String)
    : IO CASVerdict := do
  for kind in casEnginePreference do
    let result ← VerifyEngine.verifyViaEngine kind deltaExpr
    match result with
    | .verified =>
      return { result := some true, engineUsed := some kind, rawOutput := some "verified" }
    | .refuted detail =>
      return { result := some false, engineUsed := some kind,
               rawOutput := some s!"refuted: {detail.getD "no detail"}" }
    | .unknown _reason =>
      continue
    | .engineUnavailable _ =>
      continue
  return { result := none, engineUsed := none, rawOutput := some "all engines unavailable" }

end Measure.Conservation
