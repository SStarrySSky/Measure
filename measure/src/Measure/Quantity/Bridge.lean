/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Bridge between Float-based Quantity and ℝ-based Physics modules.
Provides RealQuantity and conversion functions so the two worlds can interoperate.
-/
import Measure.Quantity.Basic
import Mathlib.Data.Real.Basic

/-! # Float-to-Real Bridge

This module bridges the gap between the runtime `Float`-based `Quantity` type and
the `ℝ`-valued `RealQuantity` used in Mathlib-backed physics proofs.

The conversion path is:

    Float  →  ℚ  →  ℝ      (exact, via IEEE 754 bit decoding)
    ℝ      →  Float         (approximate, via axiomatic `Real.approxFloat`)

`Float.toReal` is exact for every finite IEEE 754 double; NaN and ±∞ map to 0.
`Real.approxFloat` is declared as an axiom representing nearest-double rounding,
since `ℝ` is noncomputable in Lean 4.

`RealQuantity` mirrors `Quantity` but stores its value in `ℝ`, sharing the same
`Dim` and `Certainty` parameters so it plugs directly into the dimension-checking
infrastructure. Arithmetic instances for the exact case are provided.
-/

/-! ## IEEE 754 double-precision decoding

These helpers live outside any namespace so they extend `Float` directly. -/

/-- Extract the sign bit (bit 63) from a Float's IEEE 754 representation. -/
def Float.ieeeSign (x : Float) : Nat :=
  (x.toUInt64.shiftRight 63).toNat

/-- Extract the biased exponent field (bits 62..52). -/
def Float.ieeeExponent (x : Float) : Nat :=
  ((x.toUInt64.shiftRight 52).land 0x7FF).toNat

/-- Extract the mantissa/significand field (bits 51..0). -/
def Float.ieeeMantissa (x : Float) : Nat :=
  (x.toUInt64.land 0x000FFFFFFFFFFFFF).toNat

/-- Convert a Float to ℚ by decoding its IEEE 754 double-precision representation.

    IEEE 754 double layout (64 bits):
    - Bit 63: sign (0 = positive, 1 = negative)
    - Bits 62..52: biased exponent (11 bits, bias = 1023)
    - Bits 51..0: mantissa/significand (52 bits)

    Normal:    ±(2^52 + m) × 2^(e − 1075)
    Subnormal: ±m × 2^(−1074)
    Inf/NaN:   mapped to 0 -/
def Float.toRat (x : Float) : ℚ :=
  let s := x.ieeeSign
  let e := x.ieeeExponent
  let m := x.ieeeMantissa
  if e == 2047 then 0  -- Inf / NaN
  else
    let significand : Int := if e == 0 then Int.ofNat m else Int.ofNat (2^52 + m)
    let signed : Int := if s == 1 then -significand else significand
    let exp : Int := if e == 0 then -1074 else Int.ofNat e - 1075
    if exp ≥ 0 then
      -- result = signed * 2^exp, which is an integer
      (signed * Int.ofNat (2^exp.toNat) : ℤ)
    else
      -- result = signed / 2^|exp|
      (signed : ℚ) / (Int.ofNat (2^(-exp).toNat) : ℚ)

/-- Convert a Float to ℝ by decoding its IEEE 754 representation to ℚ, then embedding.
    Exact for all finite Float values. NaN and ±∞ map to 0. -/
noncomputable def Float.toReal (x : Float) : ℝ :=
  (x.toRat : ℝ)

/-- Convert ℝ to Float. Since ℝ is noncomputable in Lean 4, this is an axiom
    representing the nearest IEEE 754 double-precision approximation. -/
noncomputable axiom Real.approxFloat : ℝ → Float

namespace Measure.Quantity

open Measure.Dim

/-! ## RealQuantity: the ℝ-valued counterpart of Quantity -/

/-- A quantity whose value lives in ℝ rather than Float.
    Shares the same Dim and Certainty parameters so it plugs into the
    existing dimension-checking infrastructure. -/
structure RealQuantity (d : Dim) (c : Certainty) where
  value      : ℝ
  error      : ErrorData c
  provenance : Provenance := .none

/-- Exact real quantity alias, mirroring ExactQ. -/
abbrev ExactRQ (d : Dim) := RealQuantity d .exact

/-- Create an exact real quantity from a real value. -/
noncomputable def ExactRQ.mk (d : Dim) (v : ℝ) : ExactRQ d :=
  { value := v, error := () }

/-! ## Quantity ↔ RealQuantity conversion -/

/-- Lift a Float-based Quantity into ℝ. -/
noncomputable def toRealQuantity {d : Dim} {c : Certainty}
    (q : Quantity d c) : RealQuantity d c :=
  { value      := Float.toReal q.value
    error      := q.error
    provenance := q.provenance }

/-- Project a RealQuantity back to Float (approximate).
    Uses the axiomatic Real.approxFloat which represents nearest-double rounding. -/
noncomputable def RealQuantity.toFloat {d : Dim} {c : Certainty}
    (q : RealQuantity d c) : Quantity d c :=
  { value      := Real.approxFloat q.value
    error      := q.error
    provenance := q.provenance }

/-! ## Basic arithmetic on RealQuantity (exact case) -/

noncomputable instance {d : Dim} : HAdd (ExactRQ d) (ExactRQ d) (ExactRQ d) where
  hAdd a b := {
    value      := a.value + b.value
    error      := ()
    provenance := .combine "add" a.provenance b.provenance
  }

noncomputable instance {d : Dim} : HSub (ExactRQ d) (ExactRQ d) (ExactRQ d) where
  hSub a b := {
    value      := a.value - b.value
    error      := ()
    provenance := .combine "sub" a.provenance b.provenance
  }

noncomputable instance {d1 d2 : Dim} :
    HMul (ExactRQ d1) (ExactRQ d2) (ExactRQ (Dim.mul d1 d2)) where
  hMul a b := {
    value      := a.value * b.value
    error      := ()
    provenance := .combine "mul" a.provenance b.provenance
  }

noncomputable instance {d1 d2 : Dim} :
    HDiv (ExactRQ d1) (ExactRQ d2) (ExactRQ (Dim.div d1 d2)) where
  hDiv a b := {
    value      := a.value / b.value
    error      := ()
    provenance := .combine "div" a.provenance b.provenance
  }

noncomputable instance {d : Dim} : Neg (ExactRQ d) where
  neg a := {
    value      := -a.value
    error      := ()
    provenance := .applyOp "neg" a.provenance
  }

/-- Scalar multiplication: ℝ * ExactRQ. -/
noncomputable instance {d : Dim} : HMul ℝ (ExactRQ d) (ExactRQ d) where
  hMul s q := {
    value      := s * q.value
    error      := ()
    provenance := .applyOp "scale" q.provenance
  }

/-! ## Convenience: build RealQuantity directly from Physics ℝ values -/

/-- Wrap a bare ℝ as a dimensionless exact real quantity. -/
noncomputable def RealQuantity.dimensionless (v : ℝ) : ExactRQ Dim.dimensionless :=
  ExactRQ.mk Dim.dimensionless v

/-- Extract the bare ℝ value, discarding dimension and provenance. -/
def RealQuantity.val {d : Dim} {c : Certainty} (q : RealQuantity d c) : ℝ :=
  q.value

end Measure.Quantity
