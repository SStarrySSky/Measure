/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Theory.RigorLevel
import Measure.Theory.Relation

/-! # Physics Axiom Definitions

Core axiom data structures: `PhysicsAxiom` with provenance metadata,
and `AxiomSet` with internal consistency tracking.
-/

namespace Measure.Theory

/-- Provenance of a physics axiom. -/
inductive AxiomProvenance where
  | postulate
  | empirical (source : String) (confidence : Float)
  | derived (fromTheory : String) (viaLimit : String)
  | mathematical
  deriving Inhabited, Repr

/-- A physics axiom with metadata. -/
structure PhysicsAxiom where
  name : String
  type : String
  validity : String := "universal"
  provenance : AxiomProvenance := .postulate
  deriving Inhabited, Repr

/-- Axiom set with internal consistency tracking. -/
structure AxiomSet where
  axioms : Array PhysicsAxiom := #[]
  internalConsistent : Bool := true
  contentHash : UInt64 := 0
  deriving Inhabited, Repr

end Measure.Theory
