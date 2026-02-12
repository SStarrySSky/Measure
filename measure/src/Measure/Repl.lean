/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

REPL (Read-Eval-Print Loop) for Measure Scratch Mode.
-/
import Measure.Scratch.ScratchFrontend

namespace Measure.Repl

/-- REPL configuration. -/
structure ReplConfig where
  prompt : String := "measure> "
  continuePrompt : String := "  ...> "
  version : String := "0.1.0"
  deriving Inhabited

/-- Print welcome banner. -/
def printBanner (cfg : ReplConfig) : IO Unit := do
  IO.println s!"Measure Language v{cfg.version}"
  IO.println "Type :help for help, :quit to exit."
  IO.println ""

/-- Print help message. -/
def printHelp : IO Unit := do
  IO.println "Commands:"
  IO.println "  :help          Show this help message"
  IO.println "  :quit, :exit   Exit the REPL"
  IO.println "  :ast <expr>    Show the AST of an expression"
  IO.println "  :type <expr>   Show the type/dimension of an expression"
  IO.println "  <expr>         Parse and evaluate an expression"
  IO.println "  <stmt>         Parse and execute a statement"
  IO.println ""
  IO.println "Multi-line input: end a line with \\ to continue on the next line."

/-- Read a possibly multi-line input from stdin.
    Lines ending with '\\' are continued. -/
partial def readInput (cfg : ReplConfig) (first : Bool := true) : IO (Option String) := do
  if first then
    IO.print cfg.prompt
  else
    IO.print cfg.continuePrompt
  let stdout ← IO.getStdout
  stdout.flush
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then
    return none  -- EOF
  let line := String.ofList (line.toList.reverse.dropWhile Char.isWhitespace |>.reverse)
  if line.endsWith "\\" then
    let pfx := String.ofList (line.toList.reverse.drop 1 |>.reverse)
    match ← readInput cfg (first := false) with
    | none => return some pfx
    | some rest => return some (pfx ++ "\n" ++ rest)
  else
    return some line

/-- Handle :ast command. -/
def handleAst (input : String) : IO Unit := do
  let trimmed := String.ofList (input.toList.dropWhile Char.isWhitespace |>.reverse |>.dropWhile Char.isWhitespace |>.reverse)
  if trimmed.isEmpty then
    IO.println "Error: :ast requires an expression"
    return
  match Measure.Scratch.parseScratch trimmed with
  | .ok expr => IO.println (repr expr).pretty
  | .error e => IO.println s!"Parse error: {e}"

/-- Handle :type command — now shows dimension info from evaluation. -/
def handleType (env : Measure.Scratch.Env) (input : String) : IO Unit := do
  let trimmed := String.ofList (input.toList.dropWhile Char.isWhitespace |>.reverse |>.dropWhile Char.isWhitespace |>.reverse)
  if trimmed.isEmpty then
    IO.println "Error: :type requires an expression"
    return
  match Measure.Scratch.parseScratch trimmed with
  | .ok expr =>
    match Measure.Scratch.evalExpr env expr with
    | .ok v =>
      let dim := v.getDim
      IO.println s!"value: {v.format}"
      IO.println s!"dim:   {Measure.Scratch.Format.formatDim dim}"
    | .error e => IO.println s!"Eval error: {e}"
  | .error e => IO.println s!"Parse error: {e}"

/-- Process a single REPL input line. Returns (continue?, updated env). -/
def processInput (env : Measure.Scratch.Env) (input : String)
    : IO (Bool × Measure.Scratch.Env) := do
  let trimmed := String.ofList (input.toList.dropWhile Char.isWhitespace |>.reverse |>.dropWhile Char.isWhitespace |>.reverse)
  if trimmed.isEmpty then
    return (true, env)
  if trimmed == ":quit" || trimmed == ":exit" then
    IO.println "Goodbye."
    return (false, env)
  if trimmed == ":help" then
    printHelp
    return (true, env)
  if trimmed.startsWith ":ast " then
    handleAst (trimmed.drop 5).toString
    return (true, env)
  if trimmed.startsWith ":type " then
    handleType env (trimmed.drop 6).toString
    return (true, env)
  if trimmed.startsWith ":" then
    IO.println s!"Unknown command: {trimmed.takeWhile (· != ' ')}"
    IO.println "Type :help for available commands."
    return (true, env)
  -- Try evaluating as a program (statements); catch IO exceptions to keep REPL alive
  try
    let (newEnv, _) ← Measure.Scratch.evalScratchProgram env trimmed
    return (true, newEnv)
  catch e =>
    IO.println s!"error: {e}"
    return (true, env)

/-- Main REPL loop with persistent environment. -/
partial def replLoop (cfg : ReplConfig) (env : Measure.Scratch.Env) : IO Unit := do
  match ← readInput cfg with
  | none => IO.println "\nGoodbye."
  | some input =>
    let (continue_, newEnv) ← processInput env input
    if continue_ then
      replLoop cfg newEnv

/-- Entry point: run the REPL with default physics environment. -/
def runRepl : IO Unit := do
  let cfg : ReplConfig := {}
  printBanner cfg
  replLoop cfg Measure.Scratch.defaultEnv

end Measure.Repl
