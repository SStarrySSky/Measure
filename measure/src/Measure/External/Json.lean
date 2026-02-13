/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

JSON ToJson/FromJson instances for Protocol, Messages, and EngineConfig types.
Enables JSON-RPC 2.0 serialization for engine communication.
See ARCHITECTURE.md Section 8.1.
-/
import Lean.Data.Json
import Measure.External.Protocol
import Measure.External.Messages
import Measure.External.EngineConfig

namespace Measure.External

open Lean (Json ToJson FromJson toJson)

-- ============================================================
-- Protocol types
-- ============================================================

instance : ToJson ErrorCode where
  toJson c := toJson c.toInt

instance : FromJson ErrorCode where
  fromJson?
    | .num n => match ErrorCode.fromInt n.mantissa with
                | some c => .ok c
                | none   => .error s!"Unknown error code: {n.mantissa}"
    | j      => .error s!"Expected number for ErrorCode, got {j}"

instance : ToJson Transport where
  toJson
    | .tcp host port   => .mkObj [("type", "tcp"), ("host", toJson host), ("port", toJson port)]
    | .stdio command   => .mkObj [("type", "stdio"), ("command", toJson command)]
    | .unixSocket path => .mkObj [("type", "unix"), ("path", toJson path)]

instance : FromJson Transport where
  fromJson? j := do
    let ty ← j.getObjValAs? String "type"
    match ty with
    | "tcp"   => return .tcp (← j.getObjValAs? String "host") (← j.getObjValAs? Nat "port")
    | "stdio" => return .stdio (← j.getObjValAs? String "command")
    | "unix"  => return .unixSocket (← j.getObjValAs? String "path")
    | _       => .error s!"Unknown transport type: {ty}"

instance : ToJson VerifyCheck where
  toJson c := toJson c.toString

instance : FromJson VerifyCheck where
  fromJson?
    | .str s => .ok (VerifyCheck.fromString s)
    | j      => .error s!"Expected string for VerifyCheck, got {j}"

instance : ToJson VerifyResult where
  toJson r := .mkObj <|
    [("check", toJson r.check), ("passed", toJson r.passed), ("detail", toJson r.detail)]
    ++ match r.residual with
       | some v => [("residual", toJson v)]
       | none   => []

instance : FromJson VerifyResult where
  fromJson? j := do
    return { check := ← j.getObjValAs? VerifyCheck "check"
             passed := ← j.getObjValAs? Bool "passed"
             detail := (j.getObjValAs? String "detail").toOption.getD ""
             residual := (j.getObjValAs? Float "residual").toOption }

instance : ToJson EngineMethod where
  toJson m := toJson m.toRpcMethod

instance : FromJson EngineMethod where
  fromJson?
    | .str s => match EngineMethod.fromRpcMethod s with
                | some m => .ok m
                | none   => .error s!"Unknown engine method: {s}"
    | j      => .error s!"Expected string for EngineMethod, got {j}"

-- ============================================================
-- Messages types
-- ============================================================

instance : ToJson DimSpec where
  toJson d := .mkObj [("label", toJson d.label), ("exponents", toJson d.exponents)]

instance : FromJson DimSpec where
  fromJson? j := do
    return { label := ← j.getObjValAs? String "label"
             exponents := (j.getObjValAs? (List Int) "exponents").toOption.getD [] }

instance : ToJson UncertaintySpec where
  toJson u := .mkObj <|
    [("model", toJson u.model)]
    ++ match u.sigma with | some s => [("sigma", toJson s)] | none => []
    ++ match u.interval with | some (lo, hi) => [("lo", toJson lo), ("hi", toJson hi)] | none => []

instance : FromJson UncertaintySpec where
  fromJson? j := do
    let model := (j.getObjValAs? String "model").toOption.getD "Gaussian"
    let sigma := (j.getObjValAs? Float "sigma").toOption
    let interval := do
      let lo ← (j.getObjValAs? Float "lo").toOption
      let hi ← (j.getObjValAs? Float "hi").toOption
      return (lo, hi)
    return { model, sigma, interval }

instance : ToJson ExpectedOutput where
  toJson e := .mkObj <|
    (match e.dim with | some d => [("dim", toJson d)] | none => [])
    ++ (match e.count with | some c => [("count", toJson c)] | none => [])
    ++ (match e.shape with | some s => [("shape", toJson s)] | none => [])

instance : FromJson ExpectedOutput where
  fromJson? j := do
    return { dim := (j.getObjValAs? DimSpec "dim").toOption
             count := (j.getObjValAs? Nat "count").toOption
             shape := (j.getObjValAs? (List Nat) "shape").toOption }

instance : ToJson ResultMetadata where
  toJson m := .mkObj <|
    (match m.dim with | some d => [("dim", toJson d)] | none => [])
    ++ (match m.uncertainty with | some u => [("uncertainty", toJson u)] | none => [])
    ++ (match m.conditionNumber with | some c => [("conditionNumber", toJson c)] | none => [])

instance : FromJson ResultMetadata where
  fromJson? j := do
    return { dim := (j.getObjValAs? DimSpec "dim").toOption
             uncertainty := (j.getObjValAs? UncertaintySpec "uncertainty").toOption
             conditionNumber := (j.getObjValAs? Float "conditionNumber").toOption }

instance : ToJson ComputeRequest where
  toJson r := .mkObj <|
    [ ("jsonrpc", toJson "2.0")
    , ("id", toJson r.id)
    , ("method", toJson r.method)
    , ("params", .mkObj <|
        [ ("task", toJson r.task)
        , ("input", toJson r.input)
        , ("timeout_ms", toJson r.timeoutMs) ]
        ++ match r.engineHint with | some h => [("engine_hint", toJson h)] | none => []
        ++ match r.expected with | some e => [("expected", toJson e)] | none => []
        ++ if r.verify.isEmpty then [] else [("verify", toJson r.verify)]
      )
    ]

instance : FromJson ComputeRequest where
  fromJson? j := do
    let params ← j.getObjVal? "params"
    return { id := ← j.getObjValAs? Nat "id"
             method := ← j.getObjValAs? EngineMethod "method"
             engineHint := (params.getObjValAs? String "engine_hint").toOption
             timeoutMs := (params.getObjValAs? Nat "timeout_ms").toOption.getD 30000
             task := ← params.getObjValAs? String "task"
             input := ← params.getObjValAs? String "input"
             expected := (params.getObjValAs? ExpectedOutput "expected").toOption
             verify := (params.getObjValAs? (List VerifyCheck) "verify").toOption.getD [] }

instance : ToJson ComputeResponse where
  toJson r := .mkObj
    [ ("jsonrpc", toJson "2.0")
    , ("id", toJson r.id)
    , ("result", .mkObj <|
        [ ("engine", toJson r.engine)
        , ("engine_version", toJson r.engineVersion)
        , ("compute_time_ms", toJson r.computeTimeMs)
        , ("output", toJson r.output) ]
        ++ match r.metadata with | some m => [("metadata", toJson m)] | none => []
        ++ if r.verification.isEmpty then [] else [("verification", toJson r.verification)]
      )
    ]

instance : FromJson ComputeResponse where
  fromJson? j := do
    let result ← j.getObjVal? "result"
    return { id := ← j.getObjValAs? Nat "id"
             engine := ← result.getObjValAs? String "engine"
             engineVersion := ← result.getObjValAs? String "engine_version"
             computeTimeMs := ← result.getObjValAs? Nat "compute_time_ms"
             output := ← result.getObjValAs? String "output"
             metadata := (result.getObjValAs? ResultMetadata "metadata").toOption
             verification := (result.getObjValAs? (List VerifyResult) "verification").toOption.getD [] }

instance : ToJson EngineError where
  toJson e := .mkObj <|
    [ ("code", toJson e.code)
    , ("message", toJson e.message) ]
    ++ match e.data with | some d => [("data", toJson d)] | none => []
    ++ match e.suggestion with | some s => [("suggestion", toJson s)] | none => []

instance : FromJson EngineError where
  fromJson? j := do
    return { code := ← j.getObjValAs? ErrorCode "code"
             message := ← j.getObjValAs? String "message"
             data := (j.getObjValAs? String "data").toOption
             suggestion := (j.getObjValAs? String "suggestion").toOption }

-- ============================================================
-- EngineConfig types
-- ============================================================

instance : ToJson EngineKind where
  toJson k := toJson k.toString

instance : FromJson EngineKind where
  fromJson?
    | .str s => .ok (EngineKind.fromString s)
    | j      => .error s!"Expected string for EngineKind, got {j}"

instance : ToJson TypeMapEntry where
  toJson e := .mkObj [("measure", toJson e.measureType), ("engine", toJson e.engineType)]

instance : FromJson TypeMapEntry where
  fromJson? j := do
    return { measureType := ← j.getObjValAs? String "measure"
             engineType := ← j.getObjValAs? String "engine" }

instance : ToJson EngineConfig where
  toJson c := .mkObj <|
    [ ("kind", toJson c.kind)
    , ("adapter", toJson c.adapter)
    , ("transport", toJson c.transport)
    , ("timeout_ms", toJson c.timeoutMs)
    , ("max_retries", toJson c.maxRetries) ]
    ++ match c.startupCommand with | some cmd => [("startup", toJson cmd)] | none => []
    ++ if c.typeMap.isEmpty then [] else [("type_map", toJson c.typeMap)]

instance : FromJson EngineConfig where
  fromJson? j := do
    return { kind := ← j.getObjValAs? EngineKind "kind"
             adapter := ← j.getObjValAs? String "adapter"
             transport := ← j.getObjValAs? Transport "transport"
             startupCommand := (j.getObjValAs? String "startup").toOption
             timeoutMs := (j.getObjValAs? Nat "timeout_ms").toOption.getD 30000
             maxRetries := (j.getObjValAs? Nat "max_retries").toOption.getD 3
             typeMap := (j.getObjValAs? (List TypeMapEntry) "type_map").toOption.getD [] }

instance : ToJson EngineCapabilities where
  toJson c := .mkObj
    [ ("engine_name", toJson c.engineName)
    , ("engine_version", toJson c.engineVersion)
    , ("adapter_version", toJson c.adapterVersion)
    , ("supported_methods", toJson c.supportedMethods)
    , ("supported_types", toJson c.supportedTypes) ]

instance : FromJson EngineCapabilities where
  fromJson? j := do
    return { engineName := ← j.getObjValAs? String "engine_name"
             engineVersion := ← j.getObjValAs? String "engine_version"
             adapterVersion := ← j.getObjValAs? String "adapter_version"
             supportedMethods := (j.getObjValAs? (List String) "supported_methods").toOption.getD []
             supportedTypes := (j.getObjValAs? (List String) "supported_types").toOption.getD [] }

end Measure.External
