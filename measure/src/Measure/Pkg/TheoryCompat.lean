/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Theory compatibility auto-check for package imports.
Verifies that imported packages don't introduce theory conflicts.
See ARCHITECTURE.md Section 6.5 compatibility judgment.
-/
import Measure.Pkg.Manifest

namespace Measure.Pkg

open Lean

/-- Result of a theory compatibility check. -/
inductive CompatResult where
  | compatible
  | conflict (theoryA theoryB : Name) (reason : String)
  | unknown (msg : String)
  deriving Repr, Inhabited

/-- A conflict detected between package theories. -/
structure TheoryConflict where
  packageA : String
  theoryA  : Name
  packageB : String
  theoryB  : Name
  reason   : String
  deriving Repr, Inhabited

/-- Compatibility check report for a set of packages. -/
structure CompatReport where
  checked   : Nat := 0
  conflicts : List TheoryConflict := []
  warnings  : List String := []
  deriving Repr, Inhabited

namespace CompatReport

def isClean (r : CompatReport) : Bool :=
  r.conflicts.isEmpty

def summary (r : CompatReport) : String :=
  if r.isClean then
    s!"Checked {r.checked} theory pairs: all compatible."
  else
    let conflictLines := r.conflicts.map fun c =>
      s!"  CONFLICT: {c.packageA}/{c.theoryA} vs {c.packageB}/{c.theoryB}: {c.reason}"
    s!"Checked {r.checked} theory pairs: {r.conflicts.length} conflict(s) found.\n" ++
    String.join (conflictLines.intersperse "\n")

end CompatReport

namespace TheoryCompat

/-- Check if two theory declarations are compatible.
    Two theories conflict if either explicitly declares conflict
    with the other. -/
def checkPair (a b : TheoryDecl) : CompatResult :=
  if a.conflicts.contains b.name then
    .conflict a.name b.name s!"{a.name} declares conflict with {b.name}"
  else if b.conflicts.contains a.name then
    .conflict a.name b.name s!"{b.name} declares conflict with {a.name}"
  else
    .compatible

/-- Collect all theory declarations from a list of packages. -/
def collectTheories (packages : List PackageManifest)
    : List (String × TheoryDecl) :=
  packages.flatMap fun pkg =>
    pkg.theories.map fun t => (pkg.name, t)

/-- Check all theory pairs across packages for conflicts. -/
def checkAll (packages : List PackageManifest) : CompatReport :=
  let theories := collectTheories packages
  let indexed := theories.zipIdx
  let pairs : List (String × TheoryDecl × String × TheoryDecl) :=
    indexed.flatMap fun ((pkgA, tA), i) =>
      List.filterMap (fun ((pkgB, tB), j) =>
        if i < j then some (pkgA, tA, pkgB, tB) else none) indexed
  let results : List (Option TheoryConflict) := List.map (fun (pkgA, tA, pkgB, tB) =>
    match checkPair tA tB with
    | .conflict a b reason =>
      some { packageA := pkgA, theoryA := a,
             packageB := pkgB, theoryB := b,
             reason := reason : TheoryConflict }
    | _ => none) pairs
  { checked := List.length pairs
    conflicts := List.filterMap id results }

/-- Check if adding a new package would introduce conflicts
    with existing packages. -/
def checkNewPackage (existing : List PackageManifest)
    (newPkg : PackageManifest) : CompatReport :=
  checkAll (existing ++ [newPkg])

end TheoryCompat

end Measure.Pkg
