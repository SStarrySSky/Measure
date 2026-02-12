/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dependency resolution with theory constraint propagation.
See ARCHITECTURE.md Section 10.5 Phase 5.
-/
import Measure.Pkg.Manifest
import Measure.Pkg.TheoryCompat

namespace Measure.Pkg

open Lean

/-- Resolution status for a single dependency. -/
inductive ResolveStatus where
  | resolved (version : SemVer)
  | versionConflict (required : VersionConstraint) (available : List SemVer)
  | theoryConflict (conflicts : List TheoryConflict)
  | notFound
  deriving Repr, Inhabited

/-- A resolved dependency with its full manifest. -/
structure ResolvedDep where
  name     : String
  version  : SemVer
  manifest : PackageManifest
  deriving Repr, Inhabited

/-- Full resolution result for a package. -/
structure ResolveResult where
  resolved  : List ResolvedDep := []
  errors    : List (String × ResolveStatus) := []
  compatReport : CompatReport := {}
  deriving Repr, Inhabited

namespace ResolveResult

def isSuccess (r : ResolveResult) : Bool :=
  r.errors.isEmpty && r.compatReport.isClean

def summary (r : ResolveResult) : String :=
  if r.isSuccess then
    s!"Resolved {r.resolved.length} dependencies successfully."
  else
    let errLines := r.errors.map fun (name, status) =>
      s!"  {name}: {repr status}"
    s!"Resolution failed with {r.errors.length} error(s).\n" ++
    String.join (errLines.intersperse "\n") ++ "\n" ++
    r.compatReport.summary

end ResolveResult

/-- In-memory package registry for local resolution.
    Maps package names to lists of available manifests (by version). -/
structure PackageRegistry where
  packages : List (String × List PackageManifest) := []
  deriving Repr, Inhabited

namespace PackageRegistry

/-- Create an empty registry. -/
def empty : PackageRegistry := {}

/-- Register a package manifest in the registry. -/
def add (reg : PackageRegistry) (manifest : PackageManifest) : PackageRegistry :=
  let name := manifest.name
  let existing := reg.packages.find? (·.1 == name) |>.map (·.2) |>.getD []
  let updated := existing ++ [manifest]
  let filtered := reg.packages.filter (·.1 != name)
  { packages := filtered ++ [(name, updated)] }

/-- Look up a package by name and version constraint. -/
def lookup (reg : PackageRegistry) (name : String)
    (constraint : VersionConstraint) : Option PackageManifest :=
  match reg.packages.find? (·.1 == name) with
  | none => none
  | some (_, versions) =>
    let matching := versions.filter fun m => constraint.satisfiedBy m.version
    -- Pick the highest compatible version
    matching.foldl (fun best m =>
      match best with
      | none => some m
      | some b =>
        if m.version.major > b.version.major then some m
        else if m.version.major == b.version.major &&
                m.version.minor > b.version.minor then some m
        else if m.version.major == b.version.major &&
                m.version.minor == b.version.minor &&
                m.version.patch > b.version.patch then some m
        else best
    ) none

end PackageRegistry

namespace Resolver

/-- Look up a package from a registry, falling back to the in-memory store. -/
def lookupPackage (reg : PackageRegistry := {})
    (name : String) (constraint : VersionConstraint)
    : Option PackageManifest :=
  reg.lookup name constraint

/-- Resolve all dependencies for a package manifest.
    Performs version resolution then theory compatibility check. -/
def resolve (manifest : PackageManifest)
    (registry : String → VersionConstraint → Option PackageManifest
      := lookupPackage {})
    : ResolveResult :=
  let resolveResults := manifest.dependencies.map fun dep =>
    match registry dep.name dep.version with
    | some pkg =>
      let dep : ResolvedDep := { name := dep.name, version := pkg.version, manifest := pkg }
      Sum.inl dep
    | none => Sum.inr (dep.name, ResolveStatus.notFound)
  let resolved := resolveResults.filterMap fun
    | Sum.inl r => some r
    | Sum.inr _ => none
  let errors := resolveResults.filterMap fun
    | Sum.inl _ => none
    | Sum.inr e => some e
  let allManifests := manifest :: resolved.map (·.manifest)
  let compatReport := TheoryCompat.checkAll allManifests
  let theoryErrors := if compatReport.isClean then []
    else compatReport.conflicts.map fun c =>
      (s!"{c.packageA}/{c.theoryA}",
       ResolveStatus.theoryConflict [c])
  { resolved := resolved
    errors := errors ++ theoryErrors
    compatReport := compatReport }

end Resolver

end Measure.Pkg
