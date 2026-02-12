/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Engine adapter interface and Julia/Mathematica adapter skeletons.
See docs/syntax-and-integration.md Section 4.5.
-/
import Measure.External.Messages
import Measure.External.EngineConfig
import Measure.External.Verify

namespace Measure.External

/-- Engine connection state. -/
inductive ConnectionState where
  | disconnected
  | connecting
  | ready (capabilities : EngineCapabilities)
  | error (msg : String)
  deriving Repr, Inhabited

/-- Abstract engine adapter interface. -/
structure EngineAdapter where
  config     : EngineConfig
  state      : ConnectionState := .disconnected
  deriving Repr, Inhabited

namespace EngineAdapter

/-- Build an initialization request. -/
def mkInitRequest : ComputeRequest :=
  { id := 0
    method := .initialize
    task := "initialize"
    input := "{}" }

/-- Build a shutdown notification (no response expected). -/
def mkShutdownRequest : ComputeRequest :=
  { id := 0
    method := .shutdown
    task := "shutdown"
    input := "{}" }

/-- Build a compute request with verification checks. -/
def mkComputeRequest (id : Nat) (task : String) (input : String)
    (checks : List VerifyCheck) (timeoutMs : Nat := 30000) : ComputeRequest :=
  { id := id
    method := .compute
    task := task
    input := input
    verify := checks
    timeoutMs := timeoutMs }

/-- Build a symbolic computation request. -/
def mkSymbolicRequest (id : Nat) (task : String) (input : String)
    (expected : Option ExpectedOutput := none) : ComputeRequest :=
  { id := id
    method := .symbolic
    task := task
    input := input
    expected := expected }

/-- Build an ODE solver request. -/
def mkOdeRequest (id : Nat) (input : String)
    (checks : List VerifyCheck) : ComputeRequest :=
  { id := id
    method := .solveOde
    task := "solve_ode"
    input := input
    verify := checks }

end EngineAdapter

/-- Julia adapter configuration. -/
def juliaAdapter : EngineAdapter :=
  { config := defaultJuliaConfig }

/-- Mathematica adapter configuration. -/
def mathematicaAdapter : EngineAdapter :=
  { config := defaultMathematicaConfig }

/-- Adapter registry: manages all active engine connections. -/
structure AdapterRegistry where
  adapters : List EngineAdapter := [juliaAdapter, mathematicaAdapter]
  deriving Repr, Inhabited

namespace AdapterRegistry

/-- Find an adapter by engine kind. -/
def findByKind (reg : AdapterRegistry) (kind : EngineKind) : Option EngineAdapter :=
  reg.adapters.find? fun a => a.config.kind == kind

/-- Check if any adapter is ready. -/
def hasReady (reg : AdapterRegistry) : Bool :=
  reg.adapters.any fun a =>
    match a.state with
    | .ready _ => true
    | _ => false

/-- Get all ready adapters. -/
def readyAdapters (reg : AdapterRegistry) : List EngineAdapter :=
  reg.adapters.filter fun a =>
    match a.state with
    | .ready _ => true
    | _ => false

/-- Dynamically register a new engine adapter. -/
def register (reg : AdapterRegistry) (adapter : EngineAdapter) : AdapterRegistry :=
  { adapters := reg.adapters ++ [adapter] }

/-- Unregister an adapter by engine kind. -/
def unregister (reg : AdapterRegistry) (kind : EngineKind) : AdapterRegistry :=
  { adapters := reg.adapters.filter fun a => a.config.kind != kind }

/-- Update the state of an adapter by engine kind. -/
def updateState (reg : AdapterRegistry) (kind : EngineKind)
    (state : ConnectionState) : AdapterRegistry :=
  { adapters := reg.adapters.map fun a =>
      if a.config.kind == kind then { a with state := state } else a }

/-- List all registered engine kinds. -/
def registeredKinds (reg : AdapterRegistry) : List EngineKind :=
  reg.adapters.map fun a => a.config.kind

end AdapterRegistry

end Measure.External
