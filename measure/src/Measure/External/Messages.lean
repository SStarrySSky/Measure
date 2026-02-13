/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

JSON-RPC request/response message types for engine communication.
See docs/syntax-and-integration.md Section 4.2-4.3.
-/
import Measure.External.Protocol

namespace Measure.External

/-- Dimension specification in JSON-RPC messages. -/
structure DimSpec where
  label : String
  exponents : List Int := []
  deriving Repr, Inhabited

/-- Uncertainty specification in JSON-RPC messages. -/
structure UncertaintySpec where
  model : String := "Gaussian"
  sigma : Option Float := none
  interval : Option (Float × Float) := none
  deriving Repr, Inhabited

/-- Expected output specification for verification. -/
structure ExpectedOutput where
  dim   : Option DimSpec := none
  count : Option Nat := none
  shape : Option (List Nat) := none
  deriving Repr, Inhabited

/-- A computation request to an external engine. -/
structure ComputeRequest where
  id         : Nat
  method     : EngineMethod
  engineHint : Option String := none
  timeoutMs  : Nat := 30000
  task       : String
  input      : String  -- JSON-encoded input data
  expected   : Option ExpectedOutput := none
  verify     : List VerifyCheck := []
  deriving Repr, Inhabited

/-- Metadata returned with computation results. -/
structure ResultMetadata where
  dim             : Option DimSpec := none
  uncertainty     : Option UncertaintySpec := none
  conditionNumber : Option Float := none
  deriving Repr, Inhabited

/-- A successful computation response. -/
structure ComputeResponse where
  id              : Nat
  engine          : String
  engineVersion   : String
  computeTimeMs   : Nat
  output          : String  -- JSON-encoded output data
  metadata        : Option ResultMetadata := none
  verification    : List VerifyResult := []
  deriving Repr, Inhabited

/-- An error response from the engine. -/
structure EngineError where
  code       : ErrorCode
  message    : String
  data       : Option String := none
  suggestion : Option String := none
  deriving Repr, Inhabited

/-- Engine initialization capabilities. -/
structure EngineCapabilities where
  engineName       : String
  engineVersion    : String
  adapterVersion   : String
  supportedMethods : List String := []
  supportedTypes   : List String := []
  deriving Repr, Inhabited

end Measure.External
