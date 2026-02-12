/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Core Quantity type: the central runtime type of Measure.
See docs/type-system.md Section 2.
-/
import Measure.Dim.Basic
import Measure.Quantity.Certainty
import Measure.Quantity.Provenance

namespace Measure.Quantity

open Measure.Dim

/-- Core Quantity type.
    `d` is a compile-time phantom parameter (erased at runtime).
    `c` determines whether error data is carried. -/
structure Quantity (d : Dim) (c : Certainty) where
  value      : Float
  error      : ErrorData c
  provenance : Provenance := .none

instance (d : Dim) (c : Certainty) [Inhabited (ErrorData c)] : Inhabited (Quantity d c) where
  default := { value := 0.0, error := default, provenance := .none }

/-- Exact quantity alias. -/
abbrev ExactQ (d : Dim) := Quantity d .exact

/-- Create an exact quantity from a float value. -/
def ExactQ.mk (d : Dim) (v : Float) : ExactQ d :=
  { value := v, error := () }

end Measure.Quantity
