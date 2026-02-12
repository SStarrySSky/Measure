/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Theory.RigorLevel

/-! # Theory Relation Types

Four relation types between theory modules:
- `approx`: A is an approximation of B under a limiting condition
- `conflict`: A and B have conflicting axioms
- `extension`: A extends B with new axioms without contradiction
- `compatible`: A and B are explicitly compatible (BFS-traversable)
-/

namespace Measure.Theory

/-- Direction of a limiting process on a parameter. -/
inductive LimitDirection where
  | toZero
  | toInfinity
  | toValue (v : Float)
  deriving Inhabited, BEq, Repr

/-- A limiting process: take parameter p to some value. -/
structure LimitProcess where
  parameter : String
  direction : LimitDirection
  order : Option Nat := none
  deriving Inhabited, BEq, Repr

/-- Coverage of an approximation bridge. -/
inductive ApproxCoverage where
  | full
  | partialObs (observables : List String)
  | conditional (description : String)
  deriving Inhabited, Repr

/-- Formal content of an approximation relation A ⊂≈ B. -/
structure ApproxBridge where
  source : String
  target : String
  limit : LimitProcess
  errorBound : String
  coverage : ApproxCoverage := .full
  rigorCap : RigorLevel := .approximate
  deriving Inhabited, Repr

/-- Classification of a conflict between theories. -/
inductive ConflictKind where
  | direct (prop : String)
  | structural (entity : String)
  | ontological (entity : String)
  | quantitative (observable : String)
  deriving Inhabited, Repr

/-- Severity of a conflict. -/
inductive ConflictSeverity where
  | fundamental
  | derived
  | regimeDependent (description : String)
  deriving Inhabited, Repr

/-- Evidence that two theories conflict. -/
structure ConflictWitness where
  proposition : String
  proofFromLeft : String
  proofFromRight : String
  kind : ConflictKind
  severity : ConflictSeverity
  deriving Inhabited, Repr

/-- A directed relation between two theory modules. -/
inductive TheoryRelation where
  | approx (source target : String) (bridge : ApproxBridge)
  | conflict (left right : String) (witness : ConflictWitness)
  | extension (child parent : String) (newAxioms : List String)
  | compatible (left right : String)
  deriving Inhabited, Repr

end Measure.Theory
