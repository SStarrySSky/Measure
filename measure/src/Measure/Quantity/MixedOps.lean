/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Mixed operations: exact + uncertain = uncertain.
Extends Quantity.Ops with cross-certainty arithmetic.
See ARCHITECTURE.md Section 5.2 and docs/type-system.md Section 2.2.
-/
import Measure.Quantity.Basic
import Measure.Quantity.Ops
import Measure.Error.UncertaintyModel

namespace Measure.Quantity

open Measure.Dim
open Measure.Error

/-- Uncertain quantity: a Quantity carrying an error model instance. -/
structure UncertainQ (d : Dim) (α : Type) [inst : UncertaintyModel α] where
  value      : Float
  error      : α
  provenance : Provenance := .none
  deriving Inhabited

namespace UncertainQ

/-- Create from independent measurement. -/
def fromMeasurement {α : Type} [UncertaintyModel α] (d : Dim) (val sigma : Float)
    (prov : Provenance := .none) : UncertainQ d α :=
  { value := val
    error := UncertaintyModel.fromIndependent val sigma
    provenance := prov }

/-- Create from exact value (zero uncertainty). -/
def fromExact {α : Type} [UncertaintyModel α] (d : Dim) (val : Float)
    (prov : Provenance := .none) : UncertainQ d α :=
  { value := val
    error := UncertaintyModel.fromExact val
    provenance := prov }

/-- Extract standard uncertainty. -/
def uncertainty {d : Dim} {α : Type} [UncertaintyModel α] (q : UncertainQ d α) : Float :=
  UncertaintyModel.uncertainty q.error

/-- Extract conservative interval. -/
def toInterval {d : Dim} {α : Type} [UncertaintyModel α] (q : UncertainQ d α) : Float × Float :=
  UncertaintyModel.toInterval q.error

end UncertainQ

-- ============================================================
-- uncertain + uncertain = uncertain
-- ============================================================

instance {α : Type} [UncertaintyModel α] {d : Dim} :
    HAdd (UncertainQ d α) (UncertainQ d α) (UncertainQ d α) where
  hAdd a b :=
    { value := a.value + b.value
      error := UncertaintyModel.add a.error b.error
      provenance := .combine "add" a.provenance b.provenance }

instance {α : Type} [UncertaintyModel α] {d : Dim} :
    HSub (UncertainQ d α) (UncertainQ d α) (UncertainQ d α) where
  hSub a b :=
    { value := a.value - b.value
      error := UncertaintyModel.sub a.error b.error
      provenance := .combine "sub" a.provenance b.provenance }

instance {α : Type} [UncertaintyModel α] {d1 d2 : Dim} :
    HMul (UncertainQ d1 α) (UncertainQ d2 α) (UncertainQ (Dim.mul d1 d2) α) where
  hMul a b :=
    { value := a.value * b.value
      error := UncertaintyModel.mul a.error b.error a.value b.value
      provenance := .combine "mul" a.provenance b.provenance }

instance {α : Type} [UncertaintyModel α] {d1 d2 : Dim} :
    HDiv (UncertainQ d1 α) (UncertainQ d2 α) (UncertainQ (Dim.div d1 d2) α) where
  hDiv a b :=
    { value := a.value / b.value
      error := UncertaintyModel.div a.error b.error a.value b.value
      provenance := .combine "div" a.provenance b.provenance }

instance {α : Type} [UncertaintyModel α] {d : Dim} : Neg (UncertainQ d α) where
  neg a :=
    { value := -a.value
      error := UncertaintyModel.neg a.error
      provenance := .applyOp "neg" a.provenance }

-- ============================================================
-- exact + uncertain = uncertain (promote exact to zero-uncertainty)
-- ============================================================

/-- Promote an ExactQ to UncertainQ with zero uncertainty. -/
def promoteExact {d : Dim} {α : Type} [UncertaintyModel α] (q : ExactQ d) : UncertainQ d α :=
  UncertainQ.fromExact d q.value q.provenance

instance {α : Type} [UncertaintyModel α] {d : Dim} :
    HAdd (ExactQ d) (UncertainQ d α) (UncertainQ d α) where
  hAdd a b := (promoteExact a : UncertainQ d α) + b

instance {α : Type} [UncertaintyModel α] {d : Dim} :
    HAdd (UncertainQ d α) (ExactQ d) (UncertainQ d α) where
  hAdd a b := a + (promoteExact b : UncertainQ d α)

instance {α : Type} [UncertaintyModel α] {d : Dim} :
    HSub (ExactQ d) (UncertainQ d α) (UncertainQ d α) where
  hSub a b := (promoteExact a : UncertainQ d α) - b

instance {α : Type} [UncertaintyModel α] {d : Dim} :
    HSub (UncertainQ d α) (ExactQ d) (UncertainQ d α) where
  hSub a b := a - (promoteExact b : UncertainQ d α)

instance {α : Type} [UncertaintyModel α] {d1 d2 : Dim} :
    HMul (ExactQ d1) (UncertainQ d2 α) (UncertainQ (Dim.mul d1 d2) α) where
  hMul a b := (promoteExact a : UncertainQ d1 α) * b

instance {α : Type} [UncertaintyModel α] {d1 d2 : Dim} :
    HMul (UncertainQ d1 α) (ExactQ d2) (UncertainQ (Dim.mul d1 d2) α) where
  hMul a b := a * (promoteExact b : UncertainQ d2 α)

instance {α : Type} [UncertaintyModel α] {d1 d2 : Dim} :
    HDiv (ExactQ d1) (UncertainQ d2 α) (UncertainQ (Dim.div d1 d2) α) where
  hDiv a b := (promoteExact a : UncertainQ d1 α) / b

instance {α : Type} [UncertaintyModel α] {d1 d2 : Dim} :
    HDiv (UncertainQ d1 α) (ExactQ d2) (UncertainQ (Dim.div d1 d2) α) where
  hDiv a b := a / (promoteExact b : UncertainQ d2 α)

-- ============================================================
-- Scalar * uncertain
-- ============================================================

instance {α : Type} [UncertaintyModel α] {d : Dim} :
    HMul Float (UncertainQ d α) (UncertainQ d α) where
  hMul s q :=
    { value := s * q.value
      error := UncertaintyModel.scale s q.error
      provenance := .applyOp "scale" q.provenance }

end Measure.Quantity
