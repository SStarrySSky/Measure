/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Physics-specific diagnostic codes for the Measure LSP server.
See ARCHITECTURE.md Section 8.3 and docs/syntax-and-integration.md Section 6.3.
-/
import Lean

namespace Measure.LSP

open Lean

/-- Diagnostic severity levels (matching LSP spec). -/
inductive Severity where
  | error
  | warning
  | info
  | hint
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Severity

def toNat : Severity → Nat
  | .error   => 1
  | .warning => 2
  | .info    => 3
  | .hint    => 4

end Severity

/-- Measure-specific diagnostic codes MSR001-MSR010. -/
inductive DiagnosticCode where
  | dimMismatch          -- MSR001
  | theoryConflict       -- MSR002
  | conservationViolation -- MSR003
  | rigorDowngrade       -- MSR004
  | uncertaintyOverflow  -- MSR005
  | staleDatabase        -- MSR006
  | approximationActive  -- MSR007
  | unitConversion       -- MSR008
  | simplification       -- MSR009
  | unverifiedExternal   -- MSR010
  | custom (code : String) -- User-defined diagnostic code
  deriving DecidableEq, Repr, Inhabited, BEq

namespace DiagnosticCode

def toCode : DiagnosticCode → String
  | .dimMismatch          => "MSR001"
  | .theoryConflict       => "MSR002"
  | .conservationViolation => "MSR003"
  | .rigorDowngrade       => "MSR004"
  | .uncertaintyOverflow  => "MSR005"
  | .staleDatabase        => "MSR006"
  | .approximationActive  => "MSR007"
  | .unitConversion       => "MSR008"
  | .simplification       => "MSR009"
  | .unverifiedExternal   => "MSR010"
  | .custom code          => code

def severity : DiagnosticCode → Severity
  | .dimMismatch          => .error
  | .theoryConflict       => .error
  | .conservationViolation => .error
  | .rigorDowngrade       => .warning
  | .uncertaintyOverflow  => .warning
  | .staleDatabase        => .warning
  | .approximationActive  => .info
  | .unitConversion       => .info
  | .simplification       => .hint
  | .unverifiedExternal   => .error
  | .custom _             => .warning

def source : DiagnosticCode → String
  | .dimMismatch          => "measure-dim"
  | .theoryConflict       => "measure-theory"
  | .conservationViolation => "measure-conservation"
  | .rigorDowngrade       => "measure-rigor"
  | .uncertaintyOverflow  => "measure-uncertainty"
  | .staleDatabase        => "measure-database"
  | .approximationActive  => "measure-approx"
  | .unitConversion       => "measure-unit"
  | .simplification       => "measure-simplify"
  | .unverifiedExternal   => "measure-external"
  | .custom _             => "measure-custom"

def description : DiagnosticCode → String
  | .dimMismatch          => "Dimensional mismatch"
  | .theoryConflict       => "Theory conflict"
  | .conservationViolation => "Conservation law violation"
  | .rigorDowngrade       => "Rigor level downgrade"
  | .uncertaintyOverflow  => "Uncertainty overflow"
  | .staleDatabase        => "Stale database cache"
  | .approximationActive  => "Approximation active"
  | .unitConversion       => "Implicit unit conversion"
  | .simplification       => "Expression simplifiable"
  | .unverifiedExternal   => "Unverified external computation"
  | .custom code          => s!"Custom diagnostic: {code}"

end DiagnosticCode

end Measure.LSP
