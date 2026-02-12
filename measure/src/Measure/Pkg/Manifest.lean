/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Package manifest types for measure-pkg (MeasurePkg.toml schema).
Extends Lake with theory compatibility metadata.
See ARCHITECTURE.md Section 10.5 Phase 5.
-/
import Lean
import Measure.Syntax.Attributes

namespace Measure.Pkg

open Lean Measure.Syntax

/-- Semantic version for package versioning. -/
structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

namespace SemVer

def toString (v : SemVer) : String :=
  s!"{v.major}.{v.minor}.{v.patch}"

def isCompatible (required actual : SemVer) : Bool :=
  actual.major == required.major && actual.minor >= required.minor

end SemVer

/-- Version constraint for dependencies. -/
inductive VersionConstraint where
  | exact (v : SemVer)
  | atLeast (v : SemVer)
  | range (lo hi : SemVer)
  | any
  deriving Repr, Inhabited

namespace VersionConstraint

def satisfiedBy (c : VersionConstraint) (v : SemVer) : Bool :=
  match c with
  | .exact req => req == v
  | .atLeast req => SemVer.isCompatible req v
  | .range lo hi =>
    SemVer.isCompatible lo v &&
    (v.major < hi.major ||
     (v.major == hi.major && v.minor <= hi.minor))
  | .any => true

end VersionConstraint

/-- Theory declaration within a package manifest. -/
structure TheoryDecl where
  name       : Name
  rigor      : RigorLevel := .strict
  conflicts  : List Name := []
  approximates : List Name := []
  extends_   : List Name := []
  deriving Repr, Inhabited

/-- Where to fetch a dependency from. -/
inductive DependencySource where
  | registry
  | git (url : String) (rev : Option String := none)
  | local_ (path : String)
  deriving Repr, Inhabited

/-- A package dependency. -/
structure Dependency where
  name       : String
  version    : VersionConstraint := .any
  source     : DependencySource := .registry
  theories   : List Name := []
  deriving Repr, Inhabited

/-- The full package manifest (MeasurePkg.toml). -/
structure PackageManifest where
  name         : String
  version      : SemVer
  authors      : List String := []
  license      : String := "Apache-2.0"
  leanVersion  : Option String := none
  theories     : List TheoryDecl := []
  dependencies : List Dependency := []
  deriving Repr, Inhabited

end Measure.Pkg
