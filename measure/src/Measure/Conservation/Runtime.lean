/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Conservation.Law

/-! # Runtime Conservation Assertions

When static analysis is inconclusive, the compiler inserts
runtime checkpoints that monitor conserved quantities during
execution and halt early on violation.
-/

namespace Measure.Conservation

/-- Tolerance specification for runtime checks. -/
inductive CheckTolerance where
  | absolute (epsilon : Float)
  | relative (epsilon : Float)
  | adaptive (baseEpsilon : Float)
  deriving Inhabited, Repr

/-- What to do when a violation is detected at runtime. -/
inductive ViolationAction where
  | halt
  | warn
  | correct (correctorName : String)
  | haltAfter (count : Nat)
  deriving Inhabited, Repr

/-- How often to perform runtime checks. -/
inductive CheckFrequency where
  | everyN (n : Nat)
  | logarithmic
  | timed (intervalMs : Nat)
  | adaptive (initial : Nat) (growth : Nat) (max : Nat)
  | manual (breakpoints : List Nat)
  deriving Inhabited, Repr

/-- A runtime conservation checkpoint. -/
structure ConservationCheckpoint where
  laws : List ConservationLaw
  tolerances : List CheckTolerance
  onViolation : ViolationAction := .halt
  frequency : CheckFrequency := .adaptive 1 2 10000
  deriving Inhabited, Repr

/-- Runtime violation report. -/
structure ViolationReport where
  lawName : String
  iteration : Nat
  delta : Float
  tolerance : Float
  severityRatio : Float
  deriving Inhabited, Repr

namespace RuntimeChecker

/-- Determine if execution should halt based on violation and action. -/
def shouldHalt (action : ViolationAction)
    (consecutiveCount : Nat) : Bool :=
  match action with
  | .halt => true
  | .warn => false
  | .correct _ => false
  | .haltAfter n => consecutiveCount >= n

/-- Compute the next check interval for adaptive frequency. -/
def nextInterval (current : Nat) (growth : Nat)
    (maxInterval : Nat) (violated : Bool) (initial : Nat) : Nat :=
  if violated then initial
  else min (current * growth) maxInterval

/-- Check if a conservation law is violated at runtime. -/
def checkViolation (qBefore qAfter tolerance : Float) : Bool :=
  Float.abs (qAfter - qBefore) > tolerance

/-- Build a violation report from runtime measurements. -/
def mkReport (lawName : String) (iteration : Nat)
    (qBefore qAfter tolerance : Float) : ViolationReport :=
  let delta := Float.abs (qAfter - qBefore)
  { lawName := lawName
    iteration := iteration
    delta := delta
    tolerance := tolerance
    severityRatio := delta / tolerance }

end RuntimeChecker
end Measure.Conservation
