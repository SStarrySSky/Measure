/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode lexer: Unicode helpers for superscripts and Greek letters.
-/

namespace Measure.Scratch.Unicode

/-- Map Unicode superscript digits to their numeric value. -/
def superscriptToDigit (c : Char) : Option Nat :=
  match c with
  | '\u00B2' => some 2  -- superscript 2
  | '\u00B3' => some 3  -- superscript 3
  | '\u2070' => some 0
  | '\u00B9' => some 1
  | '\u2074' => some 4
  | '\u2075' => some 5
  | '\u2076' => some 6
  | '\u2077' => some 7
  | '\u2078' => some 8
  | '\u2079' => some 9
  | _ => none

/-- Check if a character is a Unicode superscript digit. -/
def isSuperscriptDigit (c : Char) : Bool :=
  (superscriptToDigit c).isSome

/-- Check if a character is a Greek letter (U+0391-U+03C9). -/
def isGreekLetter (c : Char) : Bool :=
  let n := c.toNat
  (0x0391 ≤ n && n ≤ 0x03C9)

/-- Check if character is the plus-minus sign U+00B1. -/
def isPlusMinus (c : Char) : Bool :=
  c == '\u00B1'

/-- Check if character is the approximately-equal sign U+2248. -/
def isApproxEq (c : Char) : Bool :=
  c == '\u2248'

/-- Check if a character is a Unicode subscript digit (U+2080-U+2089). -/
def isSubscriptDigit (c : Char) : Bool :=
  let n := c.toNat
  (0x2080 ≤ n && n ≤ 0x2089)

/-- Map Unicode subscript digits to their numeric value. -/
def subscriptToDigit (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x2080 ≤ n && n ≤ 0x2089 then some (n - 0x2080)
  else none

/-- Check if a character is a much-less-than sign U+226A. -/
def isMuchLessThan (c : Char) : Bool :=
  c == '\u226A'

/-- Check if a character is a much-greater-than sign U+226B. -/
def isMuchGreaterThan (c : Char) : Bool :=
  c == '\u226B'

end Measure.Scratch.Unicode
