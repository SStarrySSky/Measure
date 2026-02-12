/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Engine configuration types for measure-engines.toml parsing.
See docs/syntax-and-integration.md Section 4.5.
-/
import Measure.External.Protocol

namespace Measure.External

/-- Supported external engine types. -/
inductive EngineKind where
  | julia
  | mathematica
  | python
  | custom (name : String)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace EngineKind

def fromString : String → EngineKind
  | "julia"       => .julia
  | "mathematica" => .mathematica
  | "python"      => .python
  | s             => .custom s

def toString : EngineKind → String
  | .julia       => "julia"
  | .mathematica => "mathematica"
  | .python      => "python"
  | .custom s    => s

end EngineKind

/-- Type mapping entry between Measure and engine types. -/
structure TypeMapEntry where
  measureType : String
  engineType  : String
  deriving Repr, Inhabited

/-- Configuration for a single engine adapter. -/
structure EngineConfig where
  kind           : EngineKind
  adapter        : String
  transport      : Transport
  startupCommand : Option String := none
  timeoutMs      : Nat := 30000
  maxRetries     : Nat := 3
  typeMap        : List TypeMapEntry := []
  deriving Repr, Inhabited

/-- Default Julia engine configuration. -/
def defaultJuliaConfig : EngineConfig :=
  { kind := .julia
    adapter := "measure-julia"
    transport := .tcp "127.0.0.1" 9876
    startupCommand := some "julia --project=@measure-bridge -e 'using MeasureBridge; serve()'"
    timeoutMs := 30000
    maxRetries := 3
    typeMap := [
      { measureType := "Quantity",  engineType := "Unitful.Quantity" },
      { measureType := "Gaussian",  engineType := "Measurements.Measurement" },
      { measureType := "Matrix",    engineType := "Matrix{Float64}" },
      { measureType := "VectorField", engineType := "StaticArrays.SVector" }
    ] }

/-- Default Mathematica engine configuration. -/
def defaultMathematicaConfig : EngineConfig :=
  { kind := .mathematica
    adapter := "measure-mma"
    transport := .tcp "127.0.0.1" 9877
    timeoutMs := 60000
    maxRetries := 2
    typeMap := [
      { measureType := "Quantity",     engineType := "Quantity[value, unit]" },
      { measureType := "Gaussian",     engineType := "Around[value, sigma]" },
      { measureType := "Matrix",       engineType := "List[List[...]]" },
      { measureType := "SymbolicExpr", engineType := "Expression" }
    ] }

/-- Full engine registry from measure-engines.toml. -/
structure EngineRegistry where
  engines : List EngineConfig := [defaultJuliaConfig, defaultMathematicaConfig]
  deriving Repr, Inhabited

namespace EngineRegistry

/-- Find an engine config by kind. -/
def findByKind (reg : EngineRegistry) (kind : EngineKind) : Option EngineConfig :=
  reg.engines.find? fun e => e.kind == kind

/-- Find an engine config by adapter name. -/
def findByAdapter (reg : EngineRegistry) (adapter : String) : Option EngineConfig :=
  reg.engines.find? fun e => e.adapter == adapter

end EngineRegistry

end Measure.External
