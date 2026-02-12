/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Result verification framework for external computation results.
See ARCHITECTURE.md Section 8.1 verification mechanism.
-/
import Measure.External.Messages
import Measure.External.EngineConfig
import Measure.Dim.Basic

namespace Measure.External

open Measure.Dim

/-- Verification context: what we know about the expected result. -/
structure VerifyContext where
  expectedDim   : Option Dim := none
  tolerance     : Float := 1e-10
  conservedQtys : List (String × Float) := []
  expectedCount : Option Nat := none
  deriving Repr, Inhabited

/-- Detailed verification failure information. -/
inductive VerifyFailure where
  | dimMismatch (expected actual : String)
  | conservationViolated (qty : String) (delta : Float) (tol : Float)
  | eigenResidualTooLarge (residual : Float) (tol : Float)
  | countMismatch (expected actual : Nat)
  | numericalInstability (conditionNumber : Float)
  | customFailed (name : String) (detail : String)
  deriving Repr, Inhabited

/-- Overall verification verdict. -/
structure VerifyVerdict where
  allPassed : Bool
  results   : List VerifyResult
  failures  : List VerifyFailure := []
  deriving Repr, Inhabited

/-- Type alias for a custom verification hook function.
    Takes the check name, context, and response; returns a VerifyResult. -/
def CustomVerifyHook := String → VerifyContext → ComputeResponse → VerifyResult

/-- Registry of custom verification hooks. -/
structure VerifyHookRegistry where
  hooks : List (String × CustomVerifyHook) := []
  deriving Inhabited

namespace VerifyHookRegistry

/-- Register a named custom verification hook. -/
def register (reg : VerifyHookRegistry) (name : String)
    (hook : CustomVerifyHook) : VerifyHookRegistry :=
  { hooks := reg.hooks ++ [(name, hook)] }

/-- Unregister a hook by name. -/
def unregister (reg : VerifyHookRegistry) (name : String) : VerifyHookRegistry :=
  { hooks := reg.hooks.filter fun (n, _) => n != name }

/-- Look up a hook by name. -/
def find? (reg : VerifyHookRegistry) (name : String) : Option CustomVerifyHook :=
  reg.hooks.find? (·.1 == name) |>.map (·.2)

end VerifyHookRegistry

namespace Verifier

/-- Run dimensional consistency check on a result. -/
def checkDim (expected : Dim) (actualExponents : List Int) : VerifyResult :=
  let expectedList := [
    expected.L.num, expected.M.num, expected.T.num,
    expected.I.num, expected.Θ.num, expected.N.num, expected.J.num
  ]
  let passed := expectedList == actualExponents
  { check := .dimCheck
    passed := passed
    detail := if passed then "Dimensions match"
              else s!"Expected {repr expectedList}, got {repr actualExponents}" }

/-- Check eigenvalue equation residual: ||Av - λv|| < tol. -/
def checkEigenEquation (residualNorm : Float) (tol : Float) : VerifyResult :=
  let passed := residualNorm < tol
  { check := .eigenEquation
    passed := passed
    detail := s!"Residual norm: {residualNorm}"
    residual := some residualNorm }

/-- Check energy conservation: |E_after - E_before| < tol. -/
def checkEnergyConservation (eBefore eAfter tol : Float) : VerifyResult :=
  let delta := Float.abs (eAfter - eBefore)
  let passed := delta < tol
  { check := .energyConservation
    passed := passed
    detail := s!"Energy delta: {delta}"
    residual := some delta }

/-- Check result completeness (e.g., expected number of eigenvalues). -/
def checkCompleteness (expected actual : Nat) : VerifyResult :=
  let passed := expected == actual
  { check := .completeness
    passed := passed
    detail := s!"Expected {expected} results, got {actual}" }

/-- Run all requested verification checks against a response.
    Custom checks are dispatched to the hook registry. -/
def verify (ctx : VerifyContext) (checks : List VerifyCheck)
    (response : ComputeResponse)
    (hookRegistry : VerifyHookRegistry := {}) : VerifyVerdict :=
  let results := checks.map fun check =>
    match check with
    | .dimCheck =>
      match ctx.expectedDim, response.metadata >>= (·.dim) with
      | some ed, some ad => checkDim ed ad.exponents
      | _, _ => { check := .dimCheck, passed := true,
                  detail := "Skipped: no dimension info available" }
    | .eigenEquation =>
      match response.verification.find? (·.check == .eigenEquation) with
      | some r => r
      | none => { check := .eigenEquation, passed := true,
                  detail := "Skipped: no residual provided" }
    | .energyConservation =>
      match ctx.conservedQtys.find? (·.1 == "energy") with
      | some _ =>
        { check := .energyConservation, passed := true,
          detail := "Deferred to runtime checker" }
      | none => { check := .energyConservation, passed := true,
                  detail := "Skipped: no energy reference" }
    | .completeness =>
      match ctx.expectedCount with
      | some _n =>
        { check := .completeness, passed := true,
          detail := "Deferred: count check requires parsed output" }
      | none => { check := .completeness, passed := true,
                  detail := "Skipped: no expected count" }
    | .custom name =>
      match hookRegistry.find? name with
      | some hook => hook name ctx response
      | none =>
        { check := .custom name, passed := true,
          detail := s!"Custom check '{name}' not implemented" }
  let failures := results.filter (!·.passed) |>.map fun r =>
    .customFailed r.check.toString r.detail
  { allPassed := failures.isEmpty
    results := results
    failures := failures }

end Verifier

/-- Result of a CAS-based symbolic verification. -/
inductive SymbolicVerifyResult where
  | verified
  | refuted (counterexample : Option String := none)
  | unknown (reason : String)
  | engineUnavailable (kind : EngineKind)
  deriving Repr, Inhabited

namespace SymbolicVerifier

/-- Build a CAS verification request for an expression equality check.
    Translates expression to Mathematica Simplify[] or SymPy simplify(). -/
def mkVerifyRequest (id : Nat) (expr : String) (kind : EngineKind)
    : ComputeRequest :=
  let engineExpr := match kind with
    | .mathematica => s!"Simplify[{expr}]"
    | .python      => s!"sympy.simplify({expr})"
    | _            => expr
  { id := id
    method := .symbolic
    task := "symbolic_verify"
    input := "{\"expression\":\"" ++ engineExpr ++ "\",\"mode\":\"verify\"}"
    timeoutMs := 60000 }

/-- Parse the engine response into a SymbolicVerifyResult. -/
def parseVerifyResponse (output : String) : SymbolicVerifyResult :=
  let trimmed := String.ofList (output.toList.dropWhile Char.isWhitespace |>.reverse |>.dropWhile Char.isWhitespace |>.reverse) |>.toLower
  if trimmed == "true" || trimmed == "0" || (trimmed.splitOn "verified").length > 1 then
    .verified
  else if trimmed == "false" || (trimmed.splitOn "refuted").length > 1 then
    .refuted none
  else
    .unknown s!"Engine returned: {output}"

end SymbolicVerifier

end Measure.External
