/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Theory.RigorLevel
import Measure.Theory.Relation
import Measure.Theory.Axiom
import Measure.Syntax.Theory

/-! # Theory Module Structure

The complete TheoryModule: axioms, parameters, symmetries,
relations, and metadata bundled into a single unit.
-/

namespace Measure.Theory

/-- Domain constraint bound type. -/
inductive ConstraintBound where
  | lt (val : Float)
  | gt (val : Float)
  | between (lo hi : Float)
  | eq (val : Float)
  deriving Inhabited, BEq, Repr

/-- Applicability domain of a theory. -/
structure ApplicabilityDomain where
  constraints : List (String × ConstraintBound) := []
  description : String := ""
  deriving Inhabited, Repr

/-- Symmetry group classification. -/
inductive SymmetryGroup where
  | translation (temporal : Bool)
  | rotation (dim : Nat)
  | gauge (group : String)
  | lorentz
  | poincare
  | custom (name : String)
  deriving Inhabited, BEq, Repr

/-- Symmetry exactness. -/
inductive SymmetryExactness where
  | exact
  | approximate (breakingScale : Float)
  | anomalous (anomaly : String)
  deriving Inhabited, Repr

/-- A continuous symmetry declaration. -/
structure SymmetryDecl where
  name : String
  group : SymmetryGroup
  transformation : String := ""
  conservedQtyName : String := ""
  exactness : SymmetryExactness := .exact
  deriving Inhabited, Repr

/-- Theory metadata. -/
structure TheoryMeta where
  description : String := ""
  references : List String := []
  version : String := "0.1.0"
  deriving Inhabited, Repr

/-- A physical theory module. -/
structure TheoryModule where
  name : String
  axioms : AxiomSet := {}
  rigorLevel : RigorLevel := .strict
  domain : ApplicabilityDomain := {}
  symmetries : List SymmetryDecl := []
  relations : List TheoryRelation := []
  imports : List String := []
  metadata : TheoryMeta := {}
  deriving Inhabited, Repr

namespace TheoryModule

/-- Convert a TheoryModule to a lightweight TheoryInfo summary.
    Used for environment extension registration. -/
def toTheoryInfo (tm : TheoryModule) : Measure.Syntax.TheoryInfo where
  name := .mkSimple tm.name
  rigorLevel := match tm.rigorLevel with
    | .strict      => .strict
    | .approximate => .approximate
    | .empirical   => .empirical
    | .numerical   => .numerical
  extends_ := tm.imports.map .mkSimple

/-- Create a TheoryModule from a TheoryInfo (minimal skeleton).
    Populates name, rigor, and imports; other fields default. -/
def fromTheoryInfo (info : Measure.Syntax.TheoryInfo) : TheoryModule where
  name := info.name.toString
  rigorLevel := match info.rigorLevel with
    | .strict      => .strict
    | .approximate => .approximate
    | .empirical   => .empirical
    | .numerical   => .numerical
  imports := info.extends_.map Lean.Name.toString

end TheoryModule

end Measure.Theory
