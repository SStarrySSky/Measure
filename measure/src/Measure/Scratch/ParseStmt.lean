/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode parser: statement and declaration parsing.
Handles let, def, import, simulation, compute, verify, assert, emit.
See docs/syntax-and-integration.md Section 1.4-1.6.
-/
import Measure.Scratch.ParseParam

namespace Measure.Scratch.Parser

/-- Read a raw block delimited by braces, tracking nesting depth.
    Returns the raw text content between the outermost braces. -/
partial def readRawBlock (s : ParserState) (depth : Nat)
    : Except String (ParserState × String) :=
  go s depth ""
where
  go (s : ParserState) (depth : Nat) (acc : String)
      : Except String (ParserState × String) :=
    match peekKind s with
    | some .lbrace => go (advance s) (depth + 1) (acc ++ "{")
    | some .rbrace =>
      if depth <= 1 then .ok (advance s, acc)
      else go (advance s) (depth - 1) (acc ++ "}")
    | some .eof | none => .error "unterminated raw block"
    | _ =>
      let text := match peek s with
        | some tok => tok.text
        | none => ""
      go (advance s) depth (acc ++ text ++ " ")

mutual

/-- Parse a block of statements (indentation-delimited).
    Consumes newlines and collects statements until dedent or EOF. -/
partial def parseBlock (s : ParserState) : Except String (ParserState × List Stmt) :=
  let s := skipNewlines s
  go s []
where
  go (s : ParserState) (acc : List Stmt) : Except String (ParserState × List Stmt) :=
    let s := skipNewlines s
    match peekKind s with
    | some .eof | none => .ok (s, acc.reverse)
    | some (.indent _) =>
      let s := advance s
      match parseStmt s with
      | .ok (s, stmt) => go s (stmt :: acc)
      | .error _ => .ok (s, acc.reverse)
    | _ =>
      match parseStmt s with
      | .ok (s, stmt) => go s (stmt :: acc)
      | .error _ => .ok (s, acc.reverse)

/-- Parse a single statement. -/
partial def parseStmt (s : ParserState) : Except String (ParserState × Stmt) :=
  let s := skipNewlines s
  match peekKind s with
  | some .kwLet => parseLetStmt s
  | some .kwDef => parseDefStmt s
  | some .kwImport => parseImportStmt s
  | some .kwFrom => parseFromImportStmt s
  | some .kwSimulation => parseSimulationStmt s
  | some .kwAssert => parseAssertStmt s
  | some .kwEmit => parseEmitStmt s
  | some .kwCompute => parseComputeStmt s
  | some .kwVerify => parseVerifyStmt s
  | some .attrOpen => parseAttributedStmt s
  | some .kwIf => parseIfStmt s
  | some .kwFor => parseForStmt s
  | _ => parseExprStmt s

/-- Parse let statement: 'let' ident (':' type)? '=' rhs-expr -/
partial def parseLetStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'let'
  let (name, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected identifier after 'let'"
  -- Optional type annotation
  let (ty, s) ← match peekKind s with
    | some .colon =>
      let s := advance s
      match peekKind s with
      | some (.ident t) => .ok (some t, advance s)
      | _ => .error "expected type after ':'"
    | _ => .ok (none, s)
  -- '='
  let (s, _) ← expect s .assign "'='"
  -- RHS expression
  let (s, rhs) ← parseExpr s 0
  .ok (s, .letDecl name ty rhs)

/-- Parse def statement: 'def' ident param-list ('->' type)? ':' block -/
partial def parseDefStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'def'
  let (name, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected function name after 'def'"
  let (s, params) ← parseParamList s
  -- Optional return type
  let (retTy, s) ← match peekKind s with
    | some .arrow =>
      let s := advance s
      match peekKind s with
      | some (.ident t) => .ok (some t, advance s)
      | _ => .error "expected return type after '->'"
    | _ => .ok (none, s)
  -- ':' then block
  let (s, _) ← expect s .colon "':'"
  let (s, body) ← parseBlock s
  .ok (s, .defDecl name params retTy body)

/-- Parse import statement: 'import' module.path -/
partial def parseImportStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'import'
  let (s, path) ← parseModulePath s
  .ok (s, .importStmt path)

/-- Parse from-import: 'from' module.path 'import' ident-list -/
partial def parseFromImportStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'from'
  let (s, path) ← parseModulePath s
  let (s, _) ← expect s .kwImport "'import'"
  let (s, names) ← parseIdentList s
  .ok (s, .fromImport path names)

/-- Parse a dotted module path: ident ('.' ident)* -/
partial def parseModulePath (s : ParserState)
    : Except String (ParserState × List String) := do
  let (first, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected module name"
  go s [first]
where
  go (s : ParserState) (acc : List String)
      : Except String (ParserState × List String) :=
    match peekKind s with
    | some .dot =>
      let s := advance s
      match peekKind s with
      | some (.ident n) => go (advance s) (acc ++ [n])
      | _ => .ok (s, acc)
    | _ => .ok (s, acc)

/-- Parse comma-separated identifier list. -/
partial def parseIdentList (s : ParserState)
    : Except String (ParserState × List String) := do
  let (first, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected identifier"
  go s [first]
where
  go (s : ParserState) (acc : List String)
      : Except String (ParserState × List String) :=
    match peekKind s with
    | some .comma =>
      let s := advance s
      match peekKind s with
      | some (.ident n) => go (advance s) (acc ++ [n])
      | _ => .ok (s, acc)
    | _ => .ok (s, acc)

/-- Parse assert statement: 'assert' expr string? -/
partial def parseAssertStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'assert'
  let (s, cond) ← parseExpr s 0
  -- Optional message string (simplified: just check for string-like ident)
  .ok (s, .assertStmt cond none)

/-- Parse emit statement: 'emit' ident '=' expr -/
partial def parseEmitStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'emit'
  let (name, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected name after 'emit'"
  let (s, _) ← expect s .assign "'='"
  let (s, value) ← parseExpr s 0
  .ok (s, .emitStmt name value)

/-- Parse compute statement:
    'compute' name 'via' engine ':' body   (new syntax)
    'compute' engine ':' expr              (legacy syntax) -/
partial def parseComputeStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'compute'
  let (firstIdent, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected identifier after 'compute'"
  -- Check for 'via' keyword (new syntax: compute name via engine: body)
  match peekKind s with
  | some .kwVia =>
    let s := advance s  -- consume 'via'
    let (engine, s) ← match peekKind s with
      | some (.ident n) => .ok (n, advance s)
      | _ => .error "expected engine name after 'via'"
    let (s, _) ← expect s .colon "':'"
    -- Check for raw block (multi-line external code delimited by braces)
    match peekKind s with
    | some .lbrace =>
      let s := advance s  -- consume '{'
      let (s, raw) ← readRawBlock s 1
      .ok (s, .compute firstIdent engine (.ident "<raw>" { line := 0, column := 0, offset := 0 }) (some raw))
    | _ =>
      let (s, body) ← parseExpr s 0
      .ok (s, .compute firstIdent engine body)
  | _ =>
    -- Legacy syntax: compute engine: expr
    let (s, _) ← expect s .colon "':'"
    let (s, body) ← parseExpr s 0
    .ok (s, .compute "result" firstIdent body)

/-- Parse verify statement: 'verify' (ident)? ('where' | ':') clauses
    Supports both named and anonymous verify blocks. -/
partial def parseVerifyStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'verify'
  -- Optional name (anonymous if next token is 'where' or ':')
  let (name, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | some .kwWhere | some .colon => .ok ("_anon", s)
    | _ =>
      -- Try parsing as anonymous expression verify
      .ok ("_anon", s)
  -- 'where' or ':'
  let s := match peekKind s with
    | some .kwWhere => advance s
    | some .colon => advance s
    | _ => s
  let (s, clauses) ← parseVerifyClauses s
  .ok (s, .verify name clauses)

/-- Parse verify clauses: (ident ':=' expr)* or anonymous expressions. -/
partial def parseVerifyClauses (s : ParserState)
    : Except String (ParserState × List VerifyClause) :=
  let s := skipNewlines s
  go s [] 0
where
  go (s : ParserState) (acc : List VerifyClause) (idx : Nat)
      : Except String (ParserState × List VerifyClause) :=
    let s := skipNewlines s
    -- Skip indent tokens
    let s := match peekKind s with
      | some (.indent _) => advance s
      | _ => s
    match peekKind s with
    | some (.ident name) =>
      let s := advance s
      -- Check for ':=' (named clause)
      match peekKind s with
      | some .colon =>
        let s := advance s
        match peekKind s with
        | some .assign =>
          let s := advance s
          match parseExpr s 0 with
          | .ok (s, expr) =>
            go s (acc ++ [{ name, expr := some expr }]) (idx + 1)
          | .error e => .error e
        | _ => .ok (s, acc.reverse)
      | _ =>
        -- Anonymous expression clause: backtrack and parse as expression
        let s := { s with pos := s.pos - 1 }
        match parseExpr s 0 with
        | .ok (s, expr) =>
          go s (acc ++ [{ name := s!"_check{idx}", expr := some expr }]) (idx + 1)
        | .error _ => .ok (s, acc.reverse)
    | some .eof | none => .ok (s, acc.reverse)
    | _ =>
      -- Try parsing as anonymous expression
      match parseExpr s 0 with
      | .ok (s, expr) =>
        go s (acc ++ [{ name := s!"_check{idx}", expr := some expr }]) (idx + 1)
      | .error _ => .ok (s, acc.reverse)

/-- Parse @[attr] decorated statement. -/
partial def parseAttributedStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let (s, attrs) ← parseAttributes s
  let (s, inner) ← parseStmt s
  .ok (s, .attributed attrs inner)

/-- Parse attributes: @[entry, entry, ...] -/
partial def parseAttributes (s : ParserState)
    : Except String (ParserState × List AttrEntry) := do
  let (s, _) ← expect s .attrOpen "'@['"
  let (s, entries) ← parseAttrEntries s
  -- Expect ']'
  let (s, _) ← expect s .rbracket "']'"
  .ok (s, entries)

/-- Parse attribute entries: entry (',' entry)* -/
partial def parseAttrEntries (s : ParserState)
    : Except String (ParserState × List AttrEntry) := do
  let (s, first) ← parseAttrEntry s
  go s [first]
where
  go (s : ParserState) (acc : List AttrEntry)
      : Except String (ParserState × List AttrEntry) :=
    match peekKind s with
    | some .comma =>
      let s := advance s
      match parseAttrEntry s with
      | .ok (s, entry) => go s (acc ++ [entry])
      | .error e => .error e
    | _ => .ok (s, acc)

/-- Parse a single attribute entry: ident arg* -/
partial def parseAttrEntry (s : ParserState)
    : Except String (ParserState × AttrEntry) := do
  let (name, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected attribute name"
  let (s, args) ← parseAttrArgs s
  .ok (s, { name, args })

/-- Parse attribute arguments (identifiers and numbers until ',' or ']'). -/
partial def parseAttrArgs (s : ParserState)
    : Except String (ParserState × List String) :=
  go s []
where
  go (s : ParserState) (acc : List String)
      : Except String (ParserState × List String) :=
    match peekKind s with
    | some (.ident n) => go (advance s) (acc ++ [n])
    | some (.number v) => go (advance s) (acc ++ [toString v])
    | _ => .ok (s, acc)

/-- Parse if statement as expression statement. -/
partial def parseIfStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'if'
  let (s, cond) ← parseExpr s 0
  let (s, _) ← expect s .colon "':'"
  let (s, thenBody) ← parseBlock s
  let thenExprs := thenBody.map stmtToExpr
  -- DEFERRED: elif/else chains require grammar extension for chained conditionals
  let expr := Expr.ifExpr cond thenExprs [] none
  .ok (s, .exprStmt expr)

/-- Parse for statement as expression statement. -/
partial def parseForStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'for'
  let (varName, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected loop variable after 'for'"
  let (s, _) ← expect s .kwIn "'in'"
  let (s, start) ← parseExpr s 0
  let (s, _) ← expect s .dotDot "'..'"
  let (s, stop) ← parseExpr s 0
  -- Optional 'step' expr
  let (step, s) ← match peekKind s with
    | some .kwStep =>
      let s := advance s
      match parseExpr s 0 with
      | .ok (s, e) => .ok (some e, s)
      | .error e => .error e
    | _ => .ok (none, s)
  -- ':' or 'do'
  let s := match peekKind s with
    | some .colon => advance s
    | some .kwDo => advance s
    | _ => s
  let (s, body) ← parseBlock s
  let bodyExprs := body.map stmtToExpr
  .ok (s, .exprStmt (.forExpr varName start stop step bodyExprs))

/-- Parse simulation block. -/
partial def parseSimulationStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let s := advance s  -- consume 'simulation'
  let (name, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected simulation name"
  let (s, _) ← expect s .colon "':'"
  -- Parse init statements and loop
  let (s, initStmts, loopVar, loopRange, loopBody) ← parseSimBody s
  let sim : SimulationNode := {
    name, attrs := [], initStmts, loopVar, loopRange, loopBody
  }
  .ok (s, .simulation sim)

/-- Parse simulation body: init lets, then for loop. -/
partial def parseSimBody (s : ParserState)
    : Except String (ParserState × List (String × Expr) × String
        × RangeExpr × List SimStep) := do
  let s := skipNewlines s
  -- Skip indent
  let s := match peekKind s with
    | some (.indent _) => advance s
    | _ => s
  -- Collect init let statements until we hit 'for'
  let (s, inits) ← parseSimInits s
  -- Parse the for loop
  let s := skipNewlines s
  let s := match peekKind s with
    | some (.indent _) => advance s
    | _ => s
  let (s, loopVar, range, body) ← parseSimLoop s
  .ok (s, inits, loopVar, range, body)

/-- Parse simulation init statements (let bindings before the loop). -/
partial def parseSimInits (s : ParserState)
    : Except String (ParserState × List (String × Expr)) :=
  let s := skipNewlines s
  let s := match peekKind s with
    | some (.indent _) => advance s
    | _ => s
  match peekKind s with
  | some .kwLet =>
    let s := advance s
    match peekKind s with
    | some (.ident name) =>
      let s := advance s
      match expect s .assign "'='" with
      | .ok (s, _) =>
        match parseExpr s 0 with
        | .ok (s, rhs) =>
          match parseSimInits s with
          | .ok (s, rest) => .ok (s, (name, rhs) :: rest)
          | .error e => .error e
        | .error e => .error e
      | .error e => .error e
    | _ => .ok (s, [])
  | _ => .ok (s, [])

/-- Parse simulation for loop. -/
partial def parseSimLoop (s : ParserState)
    : Except String (ParserState × String × RangeExpr × List SimStep) := do
  let (s, _) ← expect s .kwFor "'for'"
  let (varName, s) ← match peekKind s with
    | some (.ident n) => .ok (n, advance s)
    | _ => .error "expected loop variable"
  let (s, _) ← expect s .kwIn "'in'"
  let (s, start) ← parseExpr s 0
  let (s, _) ← expect s .dotDot "'..'"
  let (s, stop) ← parseExpr s 0
  let (step, s) ← match peekKind s with
    | some .kwStep =>
      let s := advance s
      match parseExpr s 0 with
      | .ok (s, e) => .ok (some e, s)
      | .error e => .error e
    | _ => .ok (none, s)
  let s := match peekKind s with
    | some .colon => advance s
    | _ => s
  let range : RangeExpr := { start, stop, step }
  let (s, body) ← parseSimSteps s
  .ok (s, varName, range, body)

/-- Parse simulation steps inside the loop body. -/
partial def parseSimSteps (s : ParserState)
    : Except String (ParserState × List SimStep) :=
  go s []
where
  go (s : ParserState) (acc : List SimStep)
      : Except String (ParserState × List SimStep) :=
    let s := skipNewlines s
    let s := match peekKind s with
      | some (.indent _) => advance s
      | _ => s
    match peekKind s with
    | some .eof | none => .ok (s, acc.reverse)
    | some .kwAssert =>
      let s := advance s
      match parseExpr s 0 with
      | .ok (s, cond) => go s (.assertStep cond none :: acc)
      | .error e => .error e
    | some .kwEmit =>
      let s := advance s
      match peekKind s with
      | some (.ident name) =>
        let s := advance s
        match expect s .assign "'='" with
        | .ok (s, _) =>
          match parseExpr s 0 with
          | .ok (s, val) => go s (.emitStep name val :: acc)
          | .error e => .error e
        | .error e => .error e
      | _ => .ok (s, acc.reverse)
    | some .kwLet =>
      let s := advance s
      match peekKind s with
      | some (.ident name) =>
        let s := advance s
        match expect s .assign "'='" with
        | .ok (s, _) =>
          match parseExpr s 0 with
          | .ok (s, rhs) => go s (.letBinding name rhs :: acc)
          | .error e => .error e
        | .error e => .error e
      | _ => .ok (s, acc.reverse)
    | some (.ident name) =>
      -- Check for primed update: ident ' = expr
      let s1 := advance s
      match peekKind s1 with
      | some .prime =>
        let s1 := advance s1
        match expect s1 .assign "'='" with
        | .ok (s1, _) =>
          match parseExpr s1 0 with
          | .ok (s1, rhs) => go s1 (.primedUpdate name rhs :: acc)
          | .error e => .error e
        | .error e => .error e
      | _ =>
        -- Could be a function call or expression
        match parseExpr s 0 with
        | .ok (s, expr) =>
          match expr with
          | .call fn args => go s (.funcCall fn args :: acc)
          | _ => .ok (s, acc.reverse)  -- stop if not recognizable
        | .error _ => .ok (s, acc.reverse)
    | _ => .ok (s, acc.reverse)

/-- Convert a Stmt to an Expr (for embedding in if/for bodies). -/
partial def stmtToExpr : Stmt → Expr
  | .letDecl name ty rhs => .letExpr name ty rhs
  | .exprStmt e => e
  | _ => .ident "<unsupported-stmt>" { line := 0, column := 0, offset := 0 }

/-- Parse an expression as a statement. -/
partial def parseExprStmt (s : ParserState)
    : Except String (ParserState × Stmt) := do
  let (s, e) ← parseExpr s 0
  .ok (s, .exprStmt e)

end -- mutual

/-- Parse top-level statements until EOF. -/
partial def parseTopLevel (s : ParserState)
    : Except String (ParserState × List Stmt) :=
  go s []
where
  go (s : ParserState) (acc : List Stmt)
      : Except String (ParserState × List Stmt) :=
    let s := skipNewlines s
    match peekKind s with
    | some .eof | none => .ok (s, acc.reverse)
    | _ =>
      match parseStmt s with
      | .ok (s, stmt) => go s (stmt :: acc)
      | .error _ => .ok (s, acc.reverse)

/-- Parse a complete program: optional module decl, then statements. -/
partial def parseProgram (s : ParserState)
    : Except String (ParserState × Program) := do
  let s := skipNewlines s
  -- Optional module declaration
  let (modName, s) ← match peekKind s with
    | some .kwModule =>
      let s := advance s
      match peekKind s with
      | some (.ident n) => .ok (some n, advance s)
      | _ => .error "expected module name"
    | _ => .ok (none, s)
  -- Parse all top-level statements
  let (s, stmts) ← parseTopLevel s
  .ok (s, { moduleName := modName, stmts })

end Parser
end Measure.Scratch
