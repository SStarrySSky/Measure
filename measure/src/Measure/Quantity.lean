/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Barrel file for Measure.Quantity module.
-/
import Measure.Quantity.Provenance
import Measure.Quantity.Certainty
import Measure.Quantity.Basic
import Measure.Quantity.Ops
import Measure.Quantity.MixedOps
import Measure.Quantity.Audit
import Measure.Quantity.Bridge

/-! # Quantity Module

Re-exports the full `Measure.Quantity` API: the core `Quantity` type, certainty
tags, provenance tracking, arithmetic operations (exact and uncertain), mixed-mode
promotion rules, auditing utilities, and the `Float ↔ ℝ` bridge for interoperation
with Mathlib-based physics proofs.
-/
