/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode lexer: String → List LocToken.
Handles space-multiply markers, ± uncertainty, Unicode superscripts,
scientific notation, Greek letters, and SI unit tokens.
See docs/syntax-and-integration.md Section 1.2.
-/
import Measure.Scratch.LocToken
import Measure.Scratch.LexerDefs
import Measure.Scratch.Unicode

namespace Measure.Scratch

/-- Lexer state threaded through tokenization. -/
structure LexerState where
  input  : String
  pos    : Nat
  line   : Nat := 1
  col    : Nat := 1
  deriving Repr, Inhabited

namespace Lexer

/-- Check if we've reached end of input. -/
def atEnd (s : LexerState) : Bool :=
  s.pos ≥ s.input.length

/-- Peek at the current character without consuming. -/
def peek (s : LexerState) : Option Char :=
  if s.pos < s.input.length then
    some (String.Pos.Raw.get s.input ⟨s.pos⟩)
  else
    none

/-- Peek at the character at offset `n` from current position. -/
def peekAt (s : LexerState) (n : Nat) : Option Char :=
  let idx := s.pos + n
  if idx < s.input.length then
    some (String.Pos.Raw.get s.input ⟨idx⟩)
  else
    none

/-- Advance the lexer by one character. -/
def advance (s : LexerState) : LexerState :=
  if s.pos < s.input.length then
    let c := String.Pos.Raw.get s.input ⟨s.pos⟩
    if c == '\n' then
      { s with pos := s.pos + 1, line := s.line + 1, col := 1 }
    else
      { s with pos := s.pos + 1, col := s.col + 1 }
  else s

/-- Get current source position. -/
def sourcePos (s : LexerState) : SourcePos :=
  { line := s.line, column := s.col, offset := s.pos }

/-- Extract substring from start to current position. -/
def slice (s : LexerState) (start : Nat) : String :=
  (String.Pos.Raw.extract s.input ⟨start⟩ ⟨s.pos⟩)

/-- Skip whitespace (spaces and tabs only, not newlines). -/
partial def skipSpaces (s : LexerState) : LexerState :=
  match peek s with
  | some ' '  => skipSpaces (advance s)
  | some '\t' => skipSpaces (advance s)
  | _ => s

/-- Check if a character can start an identifier. -/
def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || Unicode.isGreekLetter c

/-- Check if a character can continue an identifier. -/
def isIdentCont (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || Unicode.isGreekLetter c || Unicode.isSubscriptDigit c

/-- Read an identifier or keyword string. -/
partial def readIdentStr (s : LexerState) : LexerState × String :=
  let start := s.pos
  let s' := go s
  (s', slice s' start)
where
  go (s : LexerState) : LexerState :=
    match peek s with
    | some c => if isIdentCont c then go (advance s) else s
    | none => s

/-- Classify an identifier string into the appropriate TokenKind. -/
def classifyIdent (name : String) : TokenKind :=
  -- Check keywords first
  match keywords.find? (fun p => p.1 == name) with
  | some (_, tk) => tk
  | none =>
    -- Check known functions
    if knownFunctions.contains name then .knownFunc name
    -- Check known units
    else if knownUnits.contains name then .unitToken name
    -- Check if starts with Greek letter
    else if name.length > 0 && Unicode.isGreekLetter (String.Pos.Raw.get name ⟨0⟩) then
      .greekIdent name
    else .ident name

/-- Convert a digit Char to its numeric value. -/
private def digitVal (c : Char) : Nat :=
  Char.toNat c - Char.toNat '0'

/-- Parse a numeric string to Float. Handles integer, decimal, and scientific notation. -/
private def parseFloat (text : String) : Float :=
  let chars := text.toList
  let (intPart, rest) := chars.span (fun c => c.isDigit)
  let intVal := intPart.foldl (fun acc c => acc * 10 + digitVal c) 0
  let (fracVal, fracLen, rest) := match rest with
    | '.' :: ds =>
      let fracDigits := ds.takeWhile (fun c => c.isDigit)
      let fv := fracDigits.foldl (fun acc c => acc * 10 + digitVal c) 0
      (fv, fracDigits.length, ds.dropWhile (fun c => c.isDigit))
    | _ => (0, 0, rest)
  let (expNeg, expAbs) := match rest with
    | 'e' :: r | 'E' :: r =>
      let (neg, digits) := match r with
        | '-' :: ds => (true, ds)
        | '+' :: ds => (false, ds)
        | ds => (false, ds)
      (neg, digits.foldl (fun acc c => acc * 10 + digitVal c) 0)
    | _ => (false, 0)
  let mantissa := intVal * (10 ^ fracLen) + fracVal
  -- Compute effective exponent: expVal - fracLen (as signed)
  -- If expNeg: effective = -(expAbs) - fracLen, always negative => use true
  -- If !expNeg: effective = expAbs - fracLen, could be positive or negative
  if expNeg then
    Float.ofScientific mantissa true (expAbs + fracLen)
  else if expAbs >= fracLen then
    Float.ofScientific mantissa false (expAbs - fracLen)
  else
    Float.ofScientific mantissa true (fracLen - expAbs)

/-- Read a number literal (integer, float, or scientific notation). -/
partial def readNumber (s : LexerState) : LexerState × Float :=
  let start := s.pos
  -- Read integer part
  let s := readDigits s
  -- Check for decimal point
  let s := match peek s, peekAt s 1 with
    | some '.', some c =>
      if c == '.' then s  -- '..' is range operator, not decimal
      else if c.isDigit then readDigits (advance s)
      else s
    | _, _ => s
  -- Check for exponent
  let s := match peek s with
    | some 'e' | some 'E' =>
      let s1 := advance s
      let s2 := match peek s1 with
        | some '+' | some '-' => advance s1
        | _ => s1
      match peek s2 with
      | some c => if c.isDigit then readDigits s2 else s
      | none => s
    | _ => s
  let text := slice s start
  let val := parseFloat text
  (s, val)
where
  readDigits (s : LexerState) : LexerState :=
    match peek s with
    | some c => if c.isDigit then readDigits (advance s) else s
    | none => s

/-- Read a line comment (-- to end of line). -/
partial def readLineComment (s : LexerState) : LexerState × String :=
  let start := s.pos
  let s := go s
  (s, slice s start)
where
  go (s : LexerState) : LexerState :=
    match peek s with
    | some '\n' => s
    | some _ => go (advance s)
    | none => s

/-- Read a block comment (/- ... -/). -/
partial def readBlockComment (s : LexerState) : LexerState × String :=
  let start := s.pos
  let s := go s 1  -- depth starts at 1
  (s, slice s start)
where
  go (s : LexerState) (depth : Nat) : LexerState :=
    if depth == 0 then s
    else match peek s, peekAt s 1 with
    | some '/', some '-' => go (advance (advance s)) (depth + 1)
    | some '-', some '/' => go (advance (advance s)) (depth - 1)
    | some _, _ => go (advance s) depth
    | none, _ => s  -- unterminated, return what we have

/-- Read Unicode superscript digits and convert to integer. -/
partial def readSuperscript (s : LexerState) : LexerState × Option Nat :=
  go s 0 false
where
  go (s : LexerState) (acc : Nat) (found : Bool) : LexerState × Option Nat :=
    match peek s with
    | some c =>
      match Unicode.superscriptToDigit c with
      | some d => go (advance s) (acc * 10 + d) true
      | none => if found then (s, some acc) else (s, none)
    | none => if found then (s, some acc) else (s, none)

/-- Measure leading indentation at the start of a line. -/
partial def measureIndent (s : LexerState) : LexerState × Nat :=
  go s 0
where
  go (s : LexerState) (depth : Nat) : LexerState × Nat :=
    match peek s with
    | some ' '  => go (advance s) (depth + 1)
    | some '\t' => go (advance s) (depth + 4)
    | _ => (s, depth)

/-- Tokenize a single token from the current position. Returns none at EOF. -/
partial def nextToken (s : LexerState) (atLineStart : Bool)
    : Option (LexerState × LocToken × Bool) :=
  if atEnd s then
    some (s, { kind := .eof, pos := sourcePos s, text := "" }, false)
  else
    let c := (peek s).get!
    let pos := sourcePos s

    -- Newline
    if c == '\n' then
      let s := advance s
      some (s, { kind := .newline, pos, text := "\n" }, true)

    -- Line comment: --
    else if c == '-' && peekAt s 1 == some '-' then
      let s := advance (advance s)
      let (s, text) := readLineComment s
      some (s, { kind := .comment text, pos, text := "--" ++ text }, false)

    -- Block comment: /-
    else if c == '/' && peekAt s 1 == some '-' then
      let s := advance (advance s)
      let (s, text) := readBlockComment s
      some (s, { kind := .comment text, pos, text := "/-" ++ text }, false)

    -- Indentation at line start
    else if atLineStart && (c == ' ' || c == '\t') then
      let (s, depth) := measureIndent s
      some (s, { kind := .indent depth, pos, text := "" }, false)

    -- Skip non-line-start whitespace (but track it for juxtaposition)
    else if c == ' ' || c == '\t' then
      let s := skipSpaces s
      nextToken s false

    -- Number literal
    else if c.isDigit then
      let start := s.pos
      let (s, val) := readNumber s
      let text := slice s start
      -- Check for Unicode superscript immediately after number
      let (s, kind) := match peek s with
        | some sc =>
          if Unicode.isSuperscriptDigit sc then
            let (s2, sup) := readSuperscript s
            match sup with
            | some _ => (s2, TokenKind.number val)
            | none => (s, TokenKind.number val)
          else (s, TokenKind.number val)
        | none => (s, TokenKind.number val)
      some (s, { kind, pos, text }, false)

    -- Identifier, keyword, function, unit, or Greek letter
    else if isIdentStart c then
      let (s, name) := readIdentStr s
      let kind := classifyIdent name
      some (s, { kind, pos, text := name }, false)

    -- Plus-minus: +- or +/- or U+00B1
    else if Unicode.isPlusMinus c then
      some (advance s, { kind := .pmOp, pos, text := "±" }, false)

    else if c == '+' && peekAt s 1 == some '-' &&
            peekAt s 2 != some '-' then  -- avoid confusing with +-- (plus then comment)
      some (advance (advance s), { kind := .pmOp, pos, text := "+-" }, false)

    else if c == '+' && peekAt s 1 == some '/' && peekAt s 2 == some '-' then
      some (advance (advance (advance s)),
        { kind := .pmOp, pos, text := "+/-" }, false)

    -- Approx-equal U+2248, possibly followed by '[' for ≈[ε] notation
    else if Unicode.isApproxEq c then
      if peekAt s 1 == some '[' then
        some (advance (advance s), { kind := .approxEqBrack, pos, text := "≈[" }, false)
      else
        some (advance s, { kind := .approxEq, pos, text := "≈" }, false)

    -- Two-character operators
    else if c == '=' && peekAt s 1 == some '=' then
      some (advance (advance s), { kind := .eqEq, pos, text := "==" }, false)

    else if c == '!' && peekAt s 1 == some '=' then
      some (advance (advance s), { kind := .neq, pos, text := "!=" }, false)

    -- << (much less than) must come before single <
    else if c == '<' && peekAt s 1 == some '<' then
      some (advance (advance s), { kind := .muchLt, pos, text := "<<" }, false)

    else if c == '<' && peekAt s 1 == some '=' then
      some (advance (advance s), { kind := .leq, pos, text := "<=" }, false)

    -- >> (much greater than) must come before single >
    else if c == '>' && peekAt s 1 == some '>' then
      some (advance (advance s), { kind := .muchGt, pos, text := ">>" }, false)

    else if c == '>' && peekAt s 1 == some '=' then
      some (advance (advance s), { kind := .geq, pos, text := ">=" }, false)

    else if c == '-' && peekAt s 1 == some '>' then
      some (advance (advance s), { kind := .arrow, pos, text := "->" }, false)

    else if c == '=' && peekAt s 1 == some '>' then
      some (advance (advance s), { kind := .fatArrow, pos, text := "=>" }, false)

    else if c == '.' && peekAt s 1 == some '.' then
      some (advance (advance s), { kind := .dotDot, pos, text := ".." }, false)

    -- @[ attribute open
    else if c == '@' && peekAt s 1 == some '[' then
      some (advance (advance s), { kind := .attrOpen, pos, text := "@[" }, false)

    -- Single-character operators and punctuation
    else if c == '+' then
      some (advance s, { kind := .plus, pos, text := "+" }, false)
    else if c == '-' then
      some (advance s, { kind := .minus, pos, text := "-" }, false)
    else if c == '*' then
      some (advance s, { kind := .star, pos, text := "*" }, false)
    else if c == '/' then
      some (advance s, { kind := .slash, pos, text := "/" }, false)
    else if c == '^' then
      some (advance s, { kind := .caret, pos, text := "^" }, false)
    else if c == '(' then
      some (advance s, { kind := .lparen, pos, text := "(" }, false)
    else if c == ')' then
      some (advance s, { kind := .rparen, pos, text := ")" }, false)
    else if c == '[' then
      some (advance s, { kind := .lbracket, pos, text := "[" }, false)
    else if c == ']' then
      some (advance s, { kind := .rbracket, pos, text := "]" }, false)
    else if c == '{' then
      some (advance s, { kind := .lbrace, pos, text := "{" }, false)
    else if c == '}' then
      some (advance s, { kind := .rbrace, pos, text := "}" }, false)
    else if c == '=' then
      some (advance s, { kind := .assign, pos, text := "=" }, false)
    else if c == '<' then
      some (advance s, { kind := .lt, pos, text := "<" }, false)
    else if c == '>' then
      some (advance s, { kind := .gt, pos, text := ">" }, false)
    else if c == ':' then
      some (advance s, { kind := .colon, pos, text := ":" }, false)
    else if c == ',' then
      some (advance s, { kind := .comma, pos, text := "," }, false)
    else if c == '.' then
      some (advance s, { kind := .dot, pos, text := "." }, false)
    else if c == '\'' then
      some (advance s, { kind := .prime, pos, text := "'" }, false)
    else if c == '|' then
      some (advance s, { kind := .pipe, pos, text := "|" }, false)
    else if c == '_' then
      -- Could be start of identifier like _foo, or standalone underscore
      if peekAt s 1 |>.map isIdentCont |>.getD false then
        let (s, name) := readIdentStr s
        some (s, { kind := .ident name, pos, text := name }, false)
      else
        some (advance s, { kind := .underscore, pos, text := "_" }, false)

    -- Unicode superscript digits (standalone, e.g. after an expression)
    else if Unicode.isSuperscriptDigit c then
      let (s, sup) := readSuperscript s
      match sup with
      | some n =>
        let txt := String.Pos.Raw.extract s.input ⟨pos.offset⟩ ⟨s.pos⟩
        some (s, { kind := .number n.toFloat, pos := pos, text := txt }, false)
      | none => some (advance s, { kind := .ident (toString c), pos := pos, text := toString c }, false)

    -- Unknown character: skip
    else
      nextToken (advance s) false

/-- Tokenize an entire input string into a list of LocTokens.
    Filters out comments and adds EOF. -/
partial def tokenize (input : String) : List LocToken :=
  let s : LexerState := { input, pos := 0 }
  go s true []
where
  go (s : LexerState) (atLine : Bool) (acc : List LocToken) : List LocToken :=
    match nextToken s atLine with
    | none => acc.reverse
    | some (s', tok, atLine') =>
      if tok.kind == .eof then
        (tok :: acc).reverse
      else
        match tok.kind with
        | .comment _ => go s' atLine' acc  -- skip comments
        | _ => go s' atLine' (tok :: acc)

end Lexer

end Measure.Scratch
