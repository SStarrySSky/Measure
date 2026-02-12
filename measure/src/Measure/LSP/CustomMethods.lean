/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Custom LSP methods in the measure/ namespace.
See docs/syntax-and-integration.md Section 6.5.
-/
import Measure.LSP.DimHints
import Measure.LSP.UncertaintyMap
import Measure.LSP.Diagnostics

namespace Measure.LSP

/-- All custom LSP methods in the measure/ namespace. -/
inductive CustomMethod where
  | uncertaintyMap
  | dimensionInfo
  | theoryGraph
  | conservationStatus
  | rigorTrace
  | engineStatus
  | databaseStatus
  | uncertaintyChanged
  | conservationViolation
  | engineConnected
  | custom (method : String)  -- User-defined custom LSP method
  deriving DecidableEq, Repr, Inhabited, BEq

namespace CustomMethod

def toMethodName : CustomMethod → String
  | .uncertaintyMap         => "measure/uncertaintyMap"
  | .dimensionInfo          => "measure/dimensionInfo"
  | .theoryGraph            => "measure/theoryGraph"
  | .conservationStatus     => "measure/conservationStatus"
  | .rigorTrace             => "measure/rigorTrace"
  | .engineStatus           => "measure/engineStatus"
  | .databaseStatus         => "measure/databaseStatus"
  | .uncertaintyChanged     => "measure/uncertaintyChanged"
  | .conservationViolation  => "measure/conservationViolation"
  | .engineConnected        => "measure/engineConnected"
  | .custom method          => s!"measure/{method}"

def fromMethodName : String → Option CustomMethod
  | "measure/uncertaintyMap"        => some .uncertaintyMap
  | "measure/dimensionInfo"         => some .dimensionInfo
  | "measure/theoryGraph"           => some .theoryGraph
  | "measure/conservationStatus"    => some .conservationStatus
  | "measure/rigorTrace"            => some .rigorTrace
  | "measure/engineStatus"          => some .engineStatus
  | "measure/databaseStatus"        => some .databaseStatus
  | "measure/uncertaintyChanged"    => some .uncertaintyChanged
  | "measure/conservationViolation" => some .conservationViolation
  | "measure/engineConnected"       => some .engineConnected
  | s                               =>
    if s.startsWith "measure/" then some (.custom (s.drop 8).toString)
    else none

/-- Whether this method is a client->server request. -/
def isRequest : CustomMethod → Bool
  | .uncertaintyMap     => true
  | .dimensionInfo      => true
  | .theoryGraph        => true
  | .conservationStatus => true
  | .rigorTrace         => true
  | .engineStatus       => true
  | .databaseStatus     => true
  | _                   => false

/-- Whether this method is a server->client notification. -/
def isNotification : CustomMethod → Bool
  | .uncertaintyChanged    => true
  | .conservationViolation => true
  | .engineConnected       => true
  | _                      => false

end CustomMethod

end Measure.LSP
