/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

JSON-RPC 2.0 protocol types for external computation engines.
See ARCHITECTURE.md Section 8.1 and docs/syntax-and-integration.md Section 4.
-/
import Lean

namespace Measure.External

open Lean

/-- JSON-RPC 2.0 error codes: standard + Measure physics-specific. -/
inductive ErrorCode where
  | parseError           -- -32700
  | invalidRequest       -- -32600
  | methodNotFound       -- -32601
  | invalidParams        -- -32602
  | internalError        -- -32603
  | dimensionalMismatch  -- -32000
  | conservationViolation -- -32001
  | uncertaintyOverflow  -- -32002
  | numericalInstability -- -32003
  | engineTimeout        -- -32004
  | engineUnavailable    -- -32005
  | verificationFailed   -- -32006
  | incompatibleVersion  -- -32007
  | serializationError   -- -32008
  deriving DecidableEq, Repr, Inhabited, BEq

namespace ErrorCode

def toInt : ErrorCode → Int
  | .parseError           => -32700
  | .invalidRequest       => -32600
  | .methodNotFound       => -32601
  | .invalidParams        => -32602
  | .internalError        => -32603
  | .dimensionalMismatch  => -32000
  | .conservationViolation => -32001
  | .uncertaintyOverflow  => -32002
  | .numericalInstability => -32003
  | .engineTimeout        => -32004
  | .engineUnavailable    => -32005
  | .verificationFailed   => -32006
  | .incompatibleVersion  => -32007
  | .serializationError   => -32008

def fromInt : Int → Option ErrorCode
  | -32700 => some .parseError
  | -32600 => some .invalidRequest
  | -32601 => some .methodNotFound
  | -32602 => some .invalidParams
  | -32603 => some .internalError
  | -32000 => some .dimensionalMismatch
  | -32001 => some .conservationViolation
  | -32002 => some .uncertaintyOverflow
  | -32003 => some .numericalInstability
  | -32004 => some .engineTimeout
  | -32005 => some .engineUnavailable
  | -32006 => some .verificationFailed
  | -32007 => some .incompatibleVersion
  | -32008 => some .serializationError
  | _      => none

def isPhysicsError (c : ErrorCode) : Bool :=
  c.toInt >= -32006 && c.toInt <= -32000

end ErrorCode

/-- Transport mechanism for engine communication. -/
inductive Transport where
  | tcp (host : String) (port : Nat)
  | stdio (command : String)
  | unixSocket (path : String)
  deriving Repr, Inhabited

/-- Verification check types for external results. -/
inductive VerifyCheck where
  | dimCheck
  | eigenEquation
  | energyConservation
  | completeness
  | custom (name : String)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace VerifyCheck

def fromString : String → VerifyCheck
  | "dim_check"            => .dimCheck
  | "eigen_equation"       => .eigenEquation
  | "energy_conservation"  => .energyConservation
  | "completeness"         => .completeness
  | s                      => .custom s

def toString : VerifyCheck → String
  | .dimCheck           => "dim_check"
  | .eigenEquation      => "eigen_equation"
  | .energyConservation => "energy_conservation"
  | .completeness       => "completeness"
  | .custom s           => s

end VerifyCheck

/-- Result of a single verification check. -/
structure VerifyResult where
  check   : VerifyCheck
  passed  : Bool
  detail  : String := ""
  residual : Option Float := none
  deriving Repr, Inhabited

/-- Engine method namespace. -/
inductive EngineMethod where
  | compute
  | symbolic
  | solveOde
  | initialize
  | shutdown
  | progress
  | custom (name : String)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace EngineMethod

def toRpcMethod : EngineMethod → String
  | .compute    => "measure/compute"
  | .symbolic   => "measure/symbolic"
  | .solveOde   => "measure/solve_ode"
  | .initialize => "measure/initialize"
  | .shutdown   => "measure/shutdown"
  | .progress   => "measure/progress"
  | .custom name => s!"measure/{name}"

def fromRpcMethod : String → Option EngineMethod
  | "measure/compute"    => some .compute
  | "measure/symbolic"   => some .symbolic
  | "measure/solve_ode"  => some .solveOde
  | "measure/initialize" => some .initialize
  | "measure/shutdown"   => some .shutdown
  | "measure/progress"   => some .progress
  | s =>
    if s.startsWith "measure/" then
      some (.custom (s.drop 8).toString)
    else none

end EngineMethod

/-- Protocol version for compatibility checking. -/
structure ProtocolVersion where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

def protocolVersion : ProtocolVersion := { major := 0, minor := 1, patch := 0 }

end Measure.External
