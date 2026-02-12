/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Mixed operation rules for Quantity types.
Defines how exact and uncertain quantities interact.
See docs/type-system.md Section 2.2.
-/
import Measure.Quantity.Basic

namespace Measure.Quantity

open Measure.Dim

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
