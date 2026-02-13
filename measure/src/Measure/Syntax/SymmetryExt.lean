/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Symmetry extension: stores raw symmetry declarations per theory namespace.
Used by the theory elaborator for Noether auto-derivation.
-/
import Lean

namespace Measure.Syntax

open Lean

/-- Raw symmetry declaration stored in the environment extension.
    Uses strings to avoid circular imports with Theory.Module. -/
structure RawSymmetryDecl where
  name      : String
  groupKind : String   -- e.g. "time_translation", "rotation", "gauge_U1", "lorentz"
  exactness : String   -- "exact", "approximate:<scale>", "anomalous:<name>"
  conserved : String   -- optional override for conserved quantity name
  deriving Inhabited, Repr, BEq

/-- Environment extension mapping declaration names to RawSymmetryDecl. -/
initialize symmetryExt : SimplePersistentEnvExtension (Name × RawSymmetryDecl)
    (Std.HashMap Name RawSymmetryDecl) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map (name, decl) => map.insert name decl
    addImportedFn := fun arrays =>
      arrays.foldl (init := {}) fun acc arr =>
        arr.foldl (init := acc) fun m (name, decl) =>
          m.insert name decl
  }

/-- Look up a symmetry declaration for a given declaration name. -/
def findSymmetry? (env : Environment) (name : Name) : Option RawSymmetryDecl :=
  (symmetryExt.getState env).get? name

/-- Register a symmetry declaration for a given declaration name. -/
def setSymmetry (env : Environment) (name : Name) (decl : RawSymmetryDecl)
    : Environment :=
  symmetryExt.addEntry env (name, decl)

/-- Collect all symmetry declarations whose name is prefixed by `ns`. -/
def collectSymmetries (env : Environment) (ns : Name) : List (Name × RawSymmetryDecl) :=
  (symmetryExt.getState env).toList.filter fun (n, _) => ns.isPrefixOf n

end Measure.Syntax
