/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Attribute handlers for @[rigor], @[uncertainty], @[conservation].
Registers Lean4 tag attributes and stores MeasureMetadata per declaration.
-/
import Lean
import Measure.Syntax.Attributes

namespace Measure.Syntax

open Lean

/-- Environment extension mapping declaration names to MeasureMetadata. -/
initialize metadataExt : SimplePersistentEnvExtension (Name × MeasureMetadata)
    (Std.HashMap Name MeasureMetadata) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map (name, metadata) =>
      match map.get? name with
      | some existing => map.insert name {
          rigor        := metadata.rigor.orElse (fun _ => existing.rigor)
          uncertainty  := metadata.uncertainty.orElse (fun _ => existing.uncertainty)
          conservation := existing.conservation ++ metadata.conservation
          tolerance    := metadata.tolerance.orElse (fun _ => existing.tolerance)
        }
      | none => map.insert name metadata
    addImportedFn := fun arrays =>
      arrays.foldl (init := {}) fun acc arr =>
        arr.foldl (init := acc) fun m (name, metadata) =>
          m.insert name metadata
  }

/-- Look up metadata for a declaration. -/
def findMetadata? (env : Environment) (name : Name) : Option MeasureMetadata :=
  (metadataExt.getState env).get? name

/-- Set metadata for a declaration. -/
def setMetadata (env : Environment) (name : Name) (metadata : MeasureMetadata)
    : Environment :=
  metadataExt.addEntry env (name, metadata)

end Measure.Syntax
