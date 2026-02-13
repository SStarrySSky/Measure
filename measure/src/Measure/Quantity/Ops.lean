/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Mixed operation rules for Quantity types.
Defines how exact and uncertain quantities interact.
See docs/type-system.md Section 2.2.
-/
import Measure.Quantity.Basic
import Measure.Error.UncertaintyModel

/-! # Quantity Arithmetic Operations

Typeclass instances for `+`, `-`, `*`, `/`, and unary `-` on `Quantity`.

Two groups of instances are provided:

1. **Exact arithmetic** (`ExactQ`): operations carry no error data and produce
   exact results. Dimension parameters are checked at the type level -- addition
   and subtraction require matching dimensions, while multiplication and division
   combine dimensions algebraically.

2. **Uncertain arithmetic** (`Quantity d (.uncertain model)`): operations delegate
   error propagation to the `UncertaintyModel` typeclass, so the concrete error
   model (e.g., Gaussian) determines how uncertainties combine.

The module also defines approximate-equality (`≈[ε]`) and ordering relations
(`<<`, `>>`) on quantity values.
-/

namespace Measure.Quantity

open Measure.Dim
open Measure.Error

-- exact + exact = exact
instance {d : Dim} : HAdd (ExactQ d) (ExactQ d) (ExactQ d) where
  hAdd a b := {
    value := a.value + b.value
    error := ()
    provenance := .combine "add" a.provenance b.provenance
  }

-- exact - exact = exact
instance {d : Dim} : HSub (ExactQ d) (ExactQ d) (ExactQ d) where
  hSub a b := {
    value := a.value - b.value
    error := ()
    provenance := .combine "sub" a.provenance b.provenance
  }

-- exact * exact = exact (dimensions multiply)
instance {d1 d2 : Dim} :
    HMul (ExactQ d1) (ExactQ d2) (ExactQ (Dim.mul d1 d2)) where
  hMul a b := {
    value := a.value * b.value
    error := ()
    provenance := .combine "mul" a.provenance b.provenance
  }

-- exact / exact = exact (dimensions divide)
instance {d1 d2 : Dim} :
    HDiv (ExactQ d1) (ExactQ d2) (ExactQ (Dim.div d1 d2)) where
  hDiv a b := {
    value := a.value / b.value
    error := ()
    provenance := .combine "div" a.provenance b.provenance
  }

-- Negation of exact
instance {d : Dim} : Neg (ExactQ d) where
  neg a := {
    value := -a.value
    error := ()
    provenance := .applyOp "neg" a.provenance
  }

-- Scalar multiplication: Float * ExactQ
instance {d : Dim} : HMul Float (ExactQ d) (ExactQ d) where
  hMul s q := {
    value := s * q.value
    error := ()
    provenance := .applyOp "scale" q.provenance
  }

-- ============================================================
-- Uncertain Quantity arithmetic: Quantity d (.uncertain model)
-- ============================================================

-- uncertain + uncertain = uncertain (same dimension)
instance {d : Dim} {model : Type} [UncertaintyModel model] :
    HAdd (Quantity d (.uncertain model)) (Quantity d (.uncertain model))
         (Quantity d (.uncertain model)) where
  hAdd a b :=
    let ea : model := a.error
    let eb : model := b.error
    { value := a.value + b.value
      error := UncertaintyModel.add ea eb
      provenance := .combine "add" a.provenance b.provenance }

-- uncertain - uncertain = uncertain (same dimension)
instance {d : Dim} {model : Type} [UncertaintyModel model] :
    HSub (Quantity d (.uncertain model)) (Quantity d (.uncertain model))
         (Quantity d (.uncertain model)) where
  hSub a b :=
    let ea : model := a.error
    let eb : model := b.error
    { value := a.value - b.value
      error := UncertaintyModel.sub ea eb
      provenance := .combine "sub" a.provenance b.provenance }

-- uncertain * uncertain = uncertain (dimensions multiply)
instance {d1 d2 : Dim} {model : Type} [UncertaintyModel model] :
    HMul (Quantity d1 (.uncertain model)) (Quantity d2 (.uncertain model))
         (Quantity (Dim.mul d1 d2) (.uncertain model)) where
  hMul a b :=
    let ea : model := a.error
    let eb : model := b.error
    { value := a.value * b.value
      error := UncertaintyModel.mul ea eb a.value b.value
      provenance := .combine "mul" a.provenance b.provenance }

-- uncertain / uncertain = uncertain (dimensions divide)
instance {d1 d2 : Dim} {model : Type} [UncertaintyModel model] :
    HDiv (Quantity d1 (.uncertain model)) (Quantity d2 (.uncertain model))
         (Quantity (Dim.div d1 d2) (.uncertain model)) where
  hDiv a b :=
    let ea : model := a.error
    let eb : model := b.error
    { value := a.value / b.value
      error := UncertaintyModel.div ea eb a.value b.value
      provenance := .combine "div" a.provenance b.provenance }

-- Negation of uncertain
instance {d : Dim} {model : Type} [UncertaintyModel model] :
    Neg (Quantity d (.uncertain model)) where
  neg a :=
    let ea : model := a.error
    { value := -a.value
      error := UncertaintyModel.neg ea
      provenance := .applyOp "neg" a.provenance }

-- Scalar multiplication: Float * uncertain
instance {d : Dim} {model : Type} [UncertaintyModel model] :
    HMul Float (Quantity d (.uncertain model)) (Quantity d (.uncertain model)) where
  hMul s q :=
    let eq : model := q.error
    { value := s * q.value
      error := UncertaintyModel.scale s eq
      provenance := .applyOp "scale" q.provenance }

-- ============================================================
-- Comparison operators
-- ============================================================

/-- Less-than for exact quantities (same dimension). -/
instance {d : Dim} : LT (ExactQ d) where
  lt a b := a.value < b.value

/-- Less-or-equal for exact quantities (same dimension). -/
instance {d : Dim} : LE (ExactQ d) where
  le a b := a.value ≤ b.value

/-- Decidable LT for ExactQ (enables `if a < b then ...`). -/
instance {d : Dim} (a b : ExactQ d) : Decidable (a < b) :=
  Float.decLt a.value b.value

/-- Decidable LE for ExactQ (enables `if a ≤ b then ...`). -/
instance {d : Dim} (a b : ExactQ d) : Decidable (a ≤ b) :=
  Float.decLe a.value b.value

/-- Less-than for uncertain quantities (compares central values). -/
instance {d : Dim} {model : Type} [UncertaintyModel model] :
    LT (Quantity d (.uncertain model)) where
  lt a b := a.value < b.value

/-- Less-or-equal for uncertain quantities (compares central values). -/
instance {d : Dim} {model : Type} [UncertaintyModel model] :
    LE (Quantity d (.uncertain model)) where
  le a b := a.value ≤ b.value

/-- Decidable LT for uncertain quantities (enables `if a < b then ...`). -/
instance {d : Dim} {model : Type} [UncertaintyModel model]
    (a b : Quantity d (.uncertain model)) : Decidable (a < b) :=
  Float.decLt a.value b.value

/-- Decidable LE for uncertain quantities (enables `if a ≤ b then ...`). -/
instance {d : Dim} {model : Type} [UncertaintyModel model]
    (a b : Quantity d (.uncertain model)) : Decidable (a ≤ b) :=
  Float.decLe a.value b.value

/-- Approximate equality within tolerance ε.
    `approxEq a b ε` holds when `|a.value - b.value| < ε`. -/
def approxEq {d : Dim} {c₁ c₂ : Certainty}
    (a : Quantity d c₁) (b : Quantity d c₂) (ε : Float) : Prop :=
  Float.abs (a.value - b.value) < ε

/-- Much-less-than relation for quantities.
    `muchLessThan a b` holds when `|a.value| < 0.01 * |b.value|`. -/
def muchLessThan {d : Dim} {c₁ c₂ : Certainty}
    (a : Quantity d c₁) (b : Quantity d c₂) : Prop :=
  Float.abs a.value < 0.01 * Float.abs b.value

/-- Much-greater-than relation for quantities. -/
def muchGreaterThan {d : Dim} {c₁ c₂ : Certainty}
    (a : Quantity d c₁) (b : Quantity d c₂) : Prop :=
  muchLessThan b a

-- Notation: a ≈[ε] b  =>  approxEq a b ε
notation:50 a " ≈[" ε "] " b => approxEq a b ε

-- Notation: a << b  =>  muchLessThan a b
notation:50 a " << " b => muchLessThan a b

-- Notation: a >> b  =>  muchGreaterThan a b
notation:50 a " >> " b => muchGreaterThan a b

end Measure.Quantity
