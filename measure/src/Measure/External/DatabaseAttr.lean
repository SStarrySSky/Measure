/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

@[database] attribute macro with version locking.
Ensures reproducibility by pinning data source versions.
See ARCHITECTURE.md Section 8.2.
-/
import Lean
import Measure.External.DataSource

namespace Measure.External

open Lean

/-- Database version lock: records which data source and version a definition depends on. -/
structure DatabaseLock where
  source  : String
  version : DataVersion
  key     : Option String := none
  deriving Repr, Inhabited, BEq

/-- Environment extension for storing database locks per declaration. -/
initialize databaseExt : SimplePersistentEnvExtension (Name × DatabaseLock) (Std.HashMap Name (List DatabaseLock)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map (name, lock) =>
      let existing := map.getD name []
      map.insert name (lock :: existing)
    addImportedFn := fun arrays =>
      arrays.foldl (fun map arr =>
        arr.foldl (fun map (name, lock) =>
          let existing := map.getD name []
          map.insert name (lock :: existing)) map) {}
  }

/-- Get all database locks for a declaration. -/
def getDatabaseLocks (env : Environment) (name : Name) : List DatabaseLock :=
  (databaseExt.getState env).getD name []

/-- Check if a declaration has any database dependencies. -/
def hasDatabaseDeps (env : Environment) (name : Name) : Bool :=
  !(getDatabaseLocks env name).isEmpty

end Measure.External

namespace Measure.Syntax

open Lean Elab Meta

/-- @[database] attribute.
    Pins a definition to a specific data source version for reproducibility.
    Usage: @[database] on a definition that depends on external data. -/
initialize registerBuiltinAttribute {
  name := `database
  descr := "Pin a definition to a specific data source version"
  add := fun declName _stx _attrKind => do
    -- In a full implementation, parse source name and version from stx
    -- and register via databaseExt.addEntry
    let env ← getEnv
    let lock : External.DatabaseLock :=
      { source := "NIST"
        version := { name := "CODATA", year := 2022 } }
    setEnv (External.databaseExt.addEntry env (declName, lock))
  applicationTime := .afterTypeChecking
}

end Measure.Syntax
