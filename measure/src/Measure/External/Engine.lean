/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Engine process management: spawn, communicate, and stop external computation engines.
Provides real IO-based process management using IO.Process.spawn.
Uses Json.lean ToJson/FromJson instances for serialization.
See ARCHITECTURE.md Section 8.1.
-/
import Lean.Data.Json
import Measure.External.Protocol
import Measure.External.Messages
import Measure.External.EngineConfig
import Measure.External.Json
import Measure.External.Adapter

namespace Measure.External

open Lean (Json ToJson FromJson toJson)

/-- Errors that can occur during engine process operations. -/
inductive EngineProcessError where
  | spawnFailed (cmd : String) (reason : String)
  | notRunning
  | sendFailed (reason : String)
  | recvFailed (reason : String)
  | parseFailed (raw : String) (reason : String)
  | timeout (ms : Nat)
  | shutdownFailed (reason : String)
  deriving Repr, Inhabited

abbrev EngineResult (α : Type) := Except EngineProcessError α

/-- A running engine process with stdin/stdout handles. -/
structure EngineProcess where
  kind       : EngineKind
  config     : EngineConfig
  child      : IO.Process.Child ⟨.piped, .piped, .piped⟩
  nextId     : IO.Ref Nat
  isRunning  : IO.Ref Bool

namespace EngineProcess

/-- Build the command and arguments for a given EngineConfig.
    Prefers config.startupCommand if set, otherwise derives from EngineKind. -/
def spawnArgs (cfg : EngineConfig) : String × Array String :=
  match cfg.startupCommand with
  | some cmd =>
    -- Parse "cmd arg1 arg2 ..." into (cmd, #[arg1, arg2, ...])
    let parts := cmd.splitOn " "
    match parts with
    | []      => ("echo", #["no command"])
    | c :: as => (c, as.toArray)
  | none =>
    match cfg.kind with
    | .julia       => ("julia", #["--project=@measure-bridge", "-e",
                                   "using MeasureBridge; serve()"])
    | .python      => ("python", #["-m", "measure_bridge"])
    | .mathematica => ("wolframscript", #["-code", "MeasureBridge`Serve[]"])
    | .custom name => (name, #[])

end EngineProcess

namespace EngineIO

/-- Environment variable names for each engine kind. -/
private def envVarForKind : EngineKind → Option String
  | .julia       => some "MEASURE_JULIA_PATH"
  | .python      => some "MEASURE_PYTHON_PATH"
  | .mathematica => some "MEASURE_MATHEMATICA_PATH"
  | .custom _    => none

/-- Default executable name for each engine kind. -/
private def defaultExeForKind : EngineKind → String
  | .julia       => "julia"
  | .python      => "python3"
  | .mathematica => "wolframscript"
  | .custom name => name

/-- Adapter script name in scripts/ directory. -/
private def adapterScriptForKind : EngineKind → String
  | .julia       => "scripts/measure-julia-bridge.jl"
  | .python      => "scripts/measure-python-bridge.py"
  | .mathematica => "scripts/measure-mma-bridge.wls"
  | .custom name => s!"scripts/measure-{name}-bridge"

/-- Check if a file exists at the given path. -/
private def fileExists (path : String) : IO Bool := do
  let p : System.FilePath := ⟨path⟩
  p.pathExists

/-- Try to find the engine executable using a discovery chain:
    1. Environment variable (MEASURE_JULIA_PATH, etc.)
    2. Adapter script in scripts/ directory
    3. Fallback to PATH lookup (the OS will resolve it at spawn time) -/
def discoverEnginePath (kind : EngineKind) : IO (Option String) := do
  -- Step 1: Check environment variable
  match envVarForKind kind with
  | some varName =>
    let val ← IO.getEnv varName
    match val with
    | some path =>
      if ← fileExists path then return some path
      else IO.eprintln s!"[engine discovery] {varName}={path} but file not found, continuing search..."
    | none => pure ()
  | none => pure ()
  -- Step 2: Check scripts/ directory for adapter script
  let scriptPath := adapterScriptForKind kind
  if ← fileExists scriptPath then
    return some scriptPath
  -- Step 3: Fallback to default executable name (let OS PATH resolve it)
  return some (defaultExeForKind kind)

/-- Spawn an engine process from an EngineConfig.
    Uses path discovery when no explicit startupCommand is set:
    env var -> scripts/ adapter -> PATH fallback. -/
def startEngine (cfg : EngineConfig)
    : IO (EngineResult EngineProcess) := do
  -- If no explicit startupCommand, try path discovery to override the default cmd
  let (cmd, args) ← do
    match cfg.startupCommand with
    | some _ => pure (EngineProcess.spawnArgs cfg)
    | none =>
      match ← discoverEnginePath cfg.kind with
      | some discovered =>
        let (_, defaultArgs) := EngineProcess.spawnArgs cfg
        pure (discovered, defaultArgs)
      | none =>
        return .error (.spawnFailed (defaultExeForKind cfg.kind)
          s!"Engine '{cfg.kind.toString}' not found. Set {(envVarForKind cfg.kind).getD "the engine path"} or install it on PATH.")
  try
    let child ← IO.Process.spawn {
      cmd := cmd
      args := args
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    let nextId ← IO.mkRef (1 : Nat)
    let isRunning ← IO.mkRef true
    return .ok { kind := cfg.kind, config := cfg, child, nextId, isRunning }
  catch e =>
    return .error (.spawnFailed cmd (toString e))

/-- Serialize a ComputeRequest via Json.lean ToJson and write to engine stdin. -/
def sendRequest (proc : EngineProcess) (req : ComputeRequest)
    : IO (EngineResult Unit) := do
  let running ← proc.isRunning.get
  if !running then
    return .error .notRunning
  try
    let json := toString (toJson req)
    proc.child.stdin.putStrLn json
    proc.child.stdin.flush
    return .ok ()
  catch e =>
    return .error (.sendFailed (toString e))

/-- Read a JSON line from engine stdout and parse via Json.lean FromJson. -/
def recvResponse (proc : EngineProcess)
    : IO (EngineResult ComputeResponse) := do
  let running ← proc.isRunning.get
  if !running then
    return .error .notRunning
  try
    let line ← proc.child.stdout.getLine
    let trimmed := String.ofList (line.toList.dropWhile Char.isWhitespace |>.reverse |>.dropWhile Char.isWhitespace |>.reverse)
    if trimmed.isEmpty then
      return .error (.recvFailed "Empty response from engine")
    match Json.parse trimmed with
    | .error parseErr =>
      return .error (.parseFailed trimmed s!"JSON parse error: {parseErr}")
    | .ok jsonVal =>
      -- Check for JSON-RPC error response
      match jsonVal.getObjVal? "error" with
      | .ok errObj =>
        let msg := (errObj.getObjValAs? String "message").toOption.getD "Unknown engine error"
        return .error (.parseFailed trimmed s!"Engine error: {msg}")
      | .error _ =>
        match @FromJson.fromJson? ComputeResponse _ jsonVal with
        | .ok resp => return .ok resp
        | .error e => return .error (.parseFailed trimmed e)
  catch e =>
    return .error (.recvFailed (toString e))

/-- Send a request and wait for the response (synchronous round-trip). -/
def roundTrip (proc : EngineProcess) (req : ComputeRequest)
    : IO (EngineResult ComputeResponse) := do
  match ← sendRequest proc req with
  | .error e => return .error e
  | .ok () => recvResponse proc

/-- Allocate the next request ID. -/
def nextRequestId (proc : EngineProcess) : IO Nat := do
  let id ← proc.nextId.get
  proc.nextId.set (id + 1)
  return id

/-- Send a shutdown request and wait for the process to exit. -/
def stopEngine (proc : EngineProcess) : IO (EngineResult Unit) := do
  let running ← proc.isRunning.get
  if !running then
    return .ok ()
  try
    let shutdownReq := EngineAdapter.mkShutdownRequest
    let _ ← sendRequest proc shutdownReq
    proc.isRunning.set false
    let _ ← proc.child.wait
    return .ok ()
  catch e =>
    proc.isRunning.set false
    return .error (.shutdownFailed (toString e))

end EngineIO

end Measure.External
