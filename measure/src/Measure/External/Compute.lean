/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Compute command implementation: `compute via engine: expr`.
Orchestrates expression serialization, engine dispatch, and result deserialization.
Uses Engine.lean process management, Adapter.lean registry, Json.lean serialization.
See ARCHITECTURE.md Section 8.1.
-/
import Lean.Data.Json
import Measure.External.Engine
import Measure.External.Adapter
import Measure.External.Verify
import Measure.External.Json
import Measure.Quantity.Basic

namespace Measure.External

open Lean (Json toJson)
open Measure.Dim
open Measure.Quantity

/-- Errors specific to the compute pipeline. -/
inductive ComputeError where
  | engineNotInstalled (kind : EngineKind)
  | engineStartFailed (reason : String)
  | serializationFailed (expr : String) (reason : String)
  | engineError (code : ErrorCode) (msg : String)
  | deserializationFailed (raw : String) (reason : String)
  | verificationFailed (failures : List VerifyFailure)
  | timeout (ms : Nat)
  | adapterNotFound (kind : EngineKind)
  deriving Repr, Inhabited

abbrev ComputeResult (α : Type) := Except ComputeError α

/-- Result of a successful computation, carrying value + metadata. -/
structure ComputeOutput where
  value       : Float
  uncertainty : Option Float := none
  dim         : Option Dim := none
  rawOutput   : String
  engineUsed  : String
  computeMs   : Nat
  provenance  : Provenance
  deriving Repr, Inhabited

namespace ExprSerializer

/-- Serialize a Measure expression string to engine-specific format. -/
def serialize (kind : EngineKind) (expr : String) : Except String String :=
  match kind with
  | .julia       => .ok (juliaTranslate expr)
  | .mathematica => .ok (mathematicaTranslate expr)
  | .python      => .ok (pythonTranslate expr)
  | .custom _    => .ok expr
where
  juliaTranslate (e : String) : String := e
  mathematicaTranslate (e : String) : String :=
    let s := e.replace "sqrt(" "Sqrt["
    let s := s.replace "sin(" "Sin["
    let s := s.replace "cos(" "Cos["
    let s := s.replace "exp(" "Exp["
    s.replace ")" "]"
  pythonTranslate (e : String) : String :=
    let s := e.replace "^" "**"
    let s := s.replace "sqrt(" "sympy.sqrt("
    let s := s.replace "sin(" "sympy.sin("
    let s := s.replace "cos(" "sympy.cos("
    s.replace "exp(" "sympy.exp("

end ExprSerializer

namespace ResultDeserializer

/-- Parse the engine's JSON output into a ComputeOutput.
    Uses Json.lean FromJson for structured parsing. -/
def deserialize (resp : ComputeResponse) (kind : EngineKind)
    : ComputeResult ComputeOutput := do
  let rawVal := extractValue resp.output
  let parsed := (String.ofList (rawVal.toList.dropWhile Char.isWhitespace |>.reverse |>.dropWhile Char.isWhitespace |>.reverse)).toNat?.map (fun n => Float.ofNat n)
  match parsed with
  | some v =>
    .ok {
      value := v
      uncertainty := extractUncertainty resp.metadata
      dim := none
      rawOutput := resp.output
      engineUsed := resp.engine
      computeMs := resp.computeTimeMs
      provenance := .calculation s!"compute_via_{kind.toString}" []
    }
  | none =>
    .error (.deserializationFailed resp.output
      s!"Cannot parse numeric value: {rawVal}")
where
  extractValue (output : String) : String :=
    let trimmed := String.ofList (output.toList.dropWhile Char.isWhitespace |>.reverse |>.dropWhile Char.isWhitespace |>.reverse)
    match Json.parse trimmed with
    | .ok json =>
      match json.getObjValAs? Float "value" with
      | .ok v => toString v
      | .error _ => trimmed
    | .error _ => trimmed
  extractUncertainty (resultMeta : Option ResultMetadata) : Option Float :=
    resultMeta >>= (·.uncertainty) >>= (·.sigma)

end ResultDeserializer

namespace ComputeEngine

/-- Check if an engine binary is available on the system PATH. -/
def checkEngineAvailable (cfg : EngineConfig) : IO Bool := do
  let (cmd, _) := EngineProcess.spawnArgs cfg
  let result ← IO.Process.output {
    cmd := cmd
    args := #["--version"]
  } |>.toBaseIO
  match result with
  | .ok out => return out.exitCode == 0
  | .error _ => return false

/-- Full pipeline: compute via engine.
    Resolves adapter from AdapterRegistry, starts engine via EngineConfig,
    serializes expression, sends request, verifies result. -/
def computeViaEngine (kind : EngineKind) (expr : String)
    (registry : AdapterRegistry := {})
    (checks : List VerifyCheck := [])
    (verifyCtx : VerifyContext := {})
    (timeoutMs : Nat := 30000)
    : IO (ComputeResult ComputeOutput) := do
  -- Step 1: Resolve adapter from registry
  let adapter ← match registry.findByKind kind with
    | some a => pure a
    | none => return .error (.adapterNotFound kind)
  let cfg := adapter.config
  -- Step 2: Check engine availability
  let available ← checkEngineAvailable cfg
  if !available then
    return .error (.engineNotInstalled kind)
  -- Step 3: Serialize expression
  let serialized ← match ExprSerializer.serialize kind expr with
    | .ok s => pure s
    | .error reason => return .error (.serializationFailed expr reason)
  -- Step 4: Start engine process
  let procResult ← EngineIO.startEngine cfg
  let proc ← match procResult with
    | .ok p => pure p
    | .error e => return .error (.engineStartFailed (repr e).pretty)
  -- Step 5: Build request using Adapter helpers + Json serialization
  let reqId ← EngineIO.nextRequestId proc
  let inputJson := toString (Json.mkObj [("expression", toJson serialized)])
  let req := EngineAdapter.mkComputeRequest reqId "evaluate" inputJson checks timeoutMs
  -- Step 6: Round-trip communication
  let respResult ← EngineIO.roundTrip proc req
  -- Step 7: Always stop engine
  let _ ← EngineIO.stopEngine proc
  -- Step 8: Process result
  match respResult with
  | .error e =>
    return .error (.engineStartFailed s!"Engine communication failed: {repr e}")
  | .ok resp =>
    match ResultDeserializer.deserialize resp kind with
    | .error e => return .error e
    | .ok output =>
      if checks.isEmpty then
        return .ok output
      else
        let verdict := Verifier.verify verifyCtx checks resp
        if verdict.allPassed then
          return .ok output
        else
          return .error (.verificationFailed verdict.failures)

end ComputeEngine

namespace VerifyEngine

/-- Verify an expression via external CAS engine (Mathematica/SymPy).
    Uses SymbolicVerifier from Verify.lean for request building and response parsing,
    and EngineIO from Engine.lean for actual process communication. -/
def verifyViaEngine (kind : EngineKind) (expr : String)
    (registry : AdapterRegistry := {})
    : IO SymbolicVerifyResult := do
  -- Resolve adapter config
  let adapter ← match registry.findByKind kind with
    | some a => pure a
    | none => return .engineUnavailable kind
  let cfg := adapter.config
  -- Start engine
  let procResult ← EngineIO.startEngine cfg
  let proc ← match procResult with
    | .ok p => pure p
    | .error _ => return .engineUnavailable kind
  -- Build verify request
  let reqId ← EngineIO.nextRequestId proc
  let req := SymbolicVerifier.mkVerifyRequest reqId expr kind
  -- Round-trip
  let respResult ← EngineIO.roundTrip proc req
  -- Always stop engine
  let _ ← EngineIO.stopEngine proc
  -- Parse result
  match respResult with
  | .error _ => return .engineUnavailable kind
  | .ok resp => return SymbolicVerifier.parseVerifyResponse resp.output

end VerifyEngine

end Measure.External
