/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

DataSource typeclass: unified interface for external physical data providers.
See ARCHITECTURE.md Section 8.2.
-/
import Measure.Dim.Basic
import Measure.Quantity.Basic
import Measure.Quantity.Provenance

namespace Measure.External

open Measure.Dim
open Measure.Quantity

/-- Version identifier for a data source snapshot. -/
structure DataVersion where
  name    : String
  year    : Nat
  edition : Option String := none
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Result of a data lookup: either a value or an error. -/
inductive DataResult (α : Type) where
  | ok (value : α) (version : DataVersion)
  | notFound (key : String)
  | versionMismatch (requested actual : DataVersion)
  | unavailable (reason : String)
  deriving Repr, Inhabited

/-- A single datum from a data source, carrying value + uncertainty + provenance. -/
structure Datum where
  value       : Float
  uncertainty : Float
  dim         : Dim
  isExact     : Bool := false
  source      : String
  version     : DataVersion
  deriving Repr, Inhabited

/-- Typeclass for external physical data providers.
    Implementations: NIST/CODATA, PDG, user-defined databases. -/
class DataSource (σ : Type) where
  /-- Human-readable name of this data source. -/
  name : σ → String
  /-- Current version of the bundled snapshot. -/
  bundledVersion : σ → DataVersion
  /-- Look up a constant by key (e.g., "speed_of_light"). -/
  get (src : σ) (key : String) : DataResult Datum
  /-- Look up with explicit version pinning. -/
  getVersioned (src : σ) (key : String) (ver : DataVersion) : DataResult Datum
  /-- List all available keys. -/
  keys (src : σ) : List String
  /-- Check if a key exists. -/
  hasKey (src : σ) (key : String) : Bool := (keys src).any (· == key)

namespace DataSource

/-- Convert a Datum to an ExactQ (discarding uncertainty info). -/
def datumToExactQ (dat : Datum) : ExactQ dat.dim :=
  { value := dat.value
    error := ()
    provenance := .database dat.source dat.version.name }

end DataSource

end Measure.External
