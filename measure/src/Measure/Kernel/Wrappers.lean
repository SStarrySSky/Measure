/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

High-level wrappers around the raw FFI bindings.
Provides a friendlier Lean API on top of Measure.Kernel.FFI.
-/
import Measure.Kernel.FFI

namespace Measure.Kernel

-- ============================================================
-- EpsilonVal helpers
-- ============================================================

namespace EpsilonVal

instance : ToString EpsilonVal where
  toString e := e.toString

instance : BEq EpsilonVal where
  beq a b := a.leq b && b.leq a

instance : LE EpsilonVal where
  le a b := a.leq b = true

instance : Inhabited EpsilonVal where
  default := EpsilonVal.zero ()

/-- Create an epsilon value from a rational numerator/denominator pair.
    Returns `inf` when `den = 0`. -/
def ofRat (num den : UInt64) : EpsilonVal :=
  EpsilonVal.make num den

/-- Check whether two epsilon values are equal (both directions of leq). -/
def beq (a b : EpsilonVal) : Bool :=
  a.leq b && b.leq a

end EpsilonVal

-- ============================================================
-- MeasureMetadata helpers
-- ============================================================

namespace MeasureMetadata

instance : Inhabited MeasureMetadata where
  default := MeasureMetadata.default ()

/-- Functional update: set theory while preserving other fields. -/
def withTheory (m : MeasureMetadata) (t : TheoryId) : MeasureMetadata :=
  m.setTheory t

/-- Get rigor level as a RigorLevel enum. -/
def getRigor (m : MeasureMetadata) : RigorLevel :=
  RigorLevel.ofUInt8 m.getRigorRaw

/-- Set rigor level from a RigorLevel enum. -/
def setRigor (m : MeasureMetadata) (r : RigorLevel) : MeasureMetadata :=
  m.setRigorRaw r.toUInt8

/-- Functional update: set rigor while preserving other fields. -/
def withRigor (m : MeasureMetadata) (r : RigorLevel) : MeasureMetadata :=
  m.setRigorRaw r.toUInt8

/-- Create metadata with specific theory, rigor, and optional epsilon bound. -/
def make (theory : TheoryId) (rigor : RigorLevel)
    (epsBound : EpsilonVal := EpsilonVal.zero ()) : MeasureMetadata :=
  let m := MeasureMetadata.default ()
  let m := m.setTheory theory
  let m := m.setRigorRaw rigor.toUInt8
  m.setEpsilonBound epsBound

/-- Functional update: set epsilon bound while preserving other fields. -/
def withEpsilonBound (m : MeasureMetadata) (e : EpsilonVal) : MeasureMetadata :=
  m.setEpsilonBound e

end MeasureMetadata

-- ============================================================
-- TheoryRegistry helpers
-- ============================================================

namespace TheoryRegistry

instance : Inhabited TheoryRegistry where
  default := TheoryRegistry.new ()

/-- Register a theory with no parents. -/
def registerRoot (reg : TheoryRegistry) (name : String)
    (rigor : RigorLevel) (maxEpsNum maxEpsDen : UInt64) : TheoryId :=
  reg.register name #[] rigor.toUInt8 maxEpsNum maxEpsDen

end TheoryRegistry

-- ============================================================
-- TheoryGraph helpers
-- ============================================================

namespace TheoryGraph

/-- Compatibility status result type. -/
inductive CompatStatus where
  | compatible
  | bridgeable
  | incompatible
  deriving Repr, BEq, Inhabited

/-- Check compatibility with typed result. -/
def checkCompat (g : TheoryGraph) (a b : TheoryId) : CompatStatus :=
  match g.checkCompatRaw a b with
  | 0 => .compatible
  | 1 => .bridgeable
  | _ => .incompatible

end TheoryGraph

-- ============================================================
-- ConservationChecker helpers
-- ============================================================

namespace ConservationChecker

/-- Check all conservation laws against a function body and return verdicts. -/
def checkAndReport (c : ConservationChecker) (fnBody : String) : Array String :=
  c.checkAll fnBody

end ConservationChecker

-- ============================================================
-- ApproxEqChecker helpers
-- ============================================================

namespace ApproxEqChecker

instance : Inhabited ApproxEqChecker where
  default := ApproxEqChecker.new ()

/-- Try numeric approximation and return a structured result. -/
structure NumericResult where
  isApproxEq : Bool
  epsNumerator : UInt64
  epsDenominator : UInt64

def tryNumericResult (c : ApproxEqChecker) (a b : Float) : NumericResult :=
  let (eq, num, den) := c.tryNumeric a b
  { isApproxEq := eq, epsNumerator := num, epsDenominator := den }

end ApproxEqChecker

-- ============================================================
-- Rigor propagation wrappers
-- ============================================================

/-- Propagate rigor level (weakest link rule). -/
def propagateRigor (a b : RigorLevel) : RigorLevel :=
  RigorLevel.ofUInt8 (Rigor.propagateRaw a.toUInt8 b.toUInt8)

/-- Check if actual rigor is compatible with declared. -/
def isRigorCompatible (declared actual : RigorLevel) : Bool :=
  Rigor.isCompatibleRaw declared.toUInt8 actual.toUInt8

/-- Convert rigor level to display string. -/
def rigorToString (r : RigorLevel) : String :=
  Rigor.toStringRaw r.toUInt8

instance : ToString RigorLevel where
  toString := rigorToString

-- ============================================================
-- EpsilonTracker helpers
-- ============================================================

namespace EpsilonTracker

instance : Inhabited EpsilonTracker where
  default := EpsilonTracker.new ()

/-- Node ID type alias for clarity. -/
abbrev NodeId := UInt64

/-- Record a literal epsilon (leaf node) with an optional source hint. -/
def recordLiteral (t : EpsilonTracker) (eps : EpsilonVal)
    (hint : String := "") : NodeId :=
  t.mkLiteral eps hint

/-- Record an addition: eps = left.eps + right.eps -/
def recordAdd (t : EpsilonTracker) (left right : NodeId)
    (hint : String := "") : NodeId :=
  t.mkAdd left right hint

/-- Record a multiplication with absolute value context. -/
def recordMul (t : EpsilonTracker) (left right : NodeId)
    (valAAbs valBAbs : EpsilonVal) (hint : String := "") : NodeId :=
  t.mkMul left right valAAbs valBAbs hint

/-- Record a max node: eps = max(left.eps, right.eps) -/
def recordMax (t : EpsilonTracker) (left right : NodeId)
    (hint : String := "") : NodeId :=
  t.mkMax left right hint

/-- Record a transitivity node: eps = left.eps + right.eps -/
def recordTrans (t : EpsilonTracker) (left right : NodeId)
    (hint : String := "") : NodeId :=
  t.mkTrans left right hint

/-- Record a substitution node with a scaling factor. -/
def recordSubst (t : EpsilonTracker) (child : NodeId)
    (scale : EpsilonVal) (hint : String := "") : NodeId :=
  t.mkSubst child scale hint

/-- Get the cumulative epsilon at a given proof node. -/
def getCumulativeEpsilon (t : EpsilonTracker) (id : NodeId) : EpsilonVal :=
  t.getEpsilon id

/-- Check whether the cumulative epsilon at a node exceeds a bound. -/
def checkBound (t : EpsilonTracker) (id : NodeId)
    (bound : EpsilonVal) : Bool :=
  (t.getEpsilon id).leq bound

/-- Get the proof tree rooted at a node as a human-readable string. -/
def getProofTree (t : EpsilonTracker) (id : NodeId) : String :=
  t.renderTree id

end EpsilonTracker

end Measure.Kernel