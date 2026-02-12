/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Engine lifecycle management: startup, health check, shutdown.
See ARCHITECTURE.md Section 8.1.
-/
import Measure.External.Transport
import Measure.External.Adapter

namespace Measure.External

/-- Engine lifecycle phase. -/
inductive LifecyclePhase where
  | idle
  | starting
  | initializing
  | ready
  | busy (requestId : Nat)
  | shuttingDown
  | stopped
  | failed (reason : String)
  deriving Repr, Inhabited

/-- Managed engine: adapter + connection + lifecycle state. -/
structure ManagedEngine where
  adapter    : EngineAdapter
  connection : Option ConnectionHandle := none
  phase      : LifecyclePhase := .idle
  retryCount : Nat := 0
  deriving Repr, Inhabited

namespace ManagedEngine

/-- Check if the engine is in a usable state. -/
def isReady (e : ManagedEngine) : Bool :=
  match e.phase with
  | .ready => true
  | _ => false

/-- Check if the engine can accept a new request. -/
def canAccept (e : ManagedEngine) : Bool :=
  match e.phase with
  | .ready => true
  | _ => false

end ManagedEngine

namespace EngineLifecycle

/-- Start an engine: connect transport + send initialize request. -/
def start (engine : ManagedEngine) : IO ManagedEngine := do
  let starting := { engine with phase := .starting }
  match ← TransportIO.connect engine.adapter.config.transport with
  | .error e =>
    return { starting with
      phase := .failed s!"Connection failed: {repr e}"
      retryCount := engine.retryCount + 1 }
  | .ok conn =>
    let initializing := { starting with
      connection := some conn
      phase := .initializing }
    match ← TransportIO.roundTrip conn EngineAdapter.mkInitRequest with
    | .error _e =>
      return { initializing with phase := .failed "Initialize handshake failed" }
    | .ok resp =>
      let caps : EngineCapabilities :=
        { engineName := resp.engine
          engineVersion := resp.engineVersion
          adapterVersion := "0.1.0" }
      return { initializing with
        adapter := { engine.adapter with state := .ready caps }
        phase := .ready }

/-- Gracefully shut down an engine. -/
def shutdown (engine : ManagedEngine) : IO ManagedEngine := do
  let shuttingDown := { engine with phase := .shuttingDown }
  match engine.connection with
  | none => return { shuttingDown with phase := .stopped }
  | some conn =>
    let _ ← TransportIO.sendRequest conn EngineAdapter.mkShutdownRequest
    let closedConn ← TransportIO.close conn
    return { shuttingDown with
      connection := some closedConn
      phase := .stopped
      adapter := { engine.adapter with state := .disconnected } }

/-- Send a compute request to a ready engine. -/
def sendCompute (engine : ManagedEngine) (req : ComputeRequest)
    : IO (ManagedEngine × TransportResult ComputeResponse) := do
  match engine.connection, engine.phase with
  | some conn, .ready =>
    let busy := { engine with phase := .busy req.id }
    let result ← TransportIO.roundTrip conn req
    let done := { busy with phase := .ready }
    return (done, result)
  | _, _ =>
    return (engine, .error (.ioError "Engine not ready"))

/-- Attempt to restart a failed engine (respects maxRetries). -/
def restart (engine : ManagedEngine) : IO ManagedEngine := do
  if engine.retryCount >= engine.adapter.config.maxRetries then
    return { engine with phase := .failed "Max retries exceeded" }
  else
    start engine

end EngineLifecycle

end Measure.External
