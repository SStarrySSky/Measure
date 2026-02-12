/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Main entry point for the Measure CLI.
Usage: measure <file.msr> [--ast] [--check] [--repl]
       measure              (enters REPL)
-/
import Measure.Scratch.ScratchFrontend
import Measure.Repl

namespace MeasureCli

/-- Parsed command-line options. -/
structure CliOptions where
  file : Option String := none
  showAst : Bool := false
  check : Bool := false
  repl : Bool := false
  deriving Inhabited

/-- Parse command-line arguments into CliOptions. -/
def parseArgs (args : List String) : Except String CliOptions :=
  go args {}
where
  go : List String → CliOptions → Except String CliOptions
  | [], opts => .ok opts
  | "--ast" :: rest, opts => go rest { opts with showAst := true }
  | "--check" :: rest, opts => go rest { opts with check := true }
  | "--repl" :: rest, opts => go rest { opts with repl := true }
  | arg :: rest, opts =>
    if arg.startsWith "--" then
      .error s!"Unknown option: {arg}"
    else if opts.file.isSome then
      .error s!"Unexpected argument: {arg} (file already specified)"
    else
      go rest { opts with file := some arg }

/-- Format an error with file context. -/
def formatError (file : String) (msg : String) : String :=
  s!"{file}: error: {msg}"

/-- Run the CLI with parsed options. -/
def run (opts : CliOptions) : IO UInt32 := do
  -- No file and --repl, or no file and no flags → enter REPL
  if opts.file.isNone then
    Measure.Repl.runRepl
    return 0
  let file := opts.file.get!
  -- If --repl flag with a file, still enter REPL
  if opts.repl then
    Measure.Repl.runRepl
    return 0
  -- Read the source file
  let readResult ← IO.FS.readFile ⟨file⟩ |>.toBaseIO
  let contents ← match readResult with
    | .ok c => pure c
    | .error _ =>
      IO.eprintln (formatError file "could not read file")
      return 1
  if contents.trimAscii.toString.isEmpty then
    IO.eprintln (formatError file "file is empty")
    return 1
  -- Parse
  match Measure.Scratch.parseScratchProgram contents with
  | .error e =>
    IO.eprintln (formatError file e)
    return 1
  | .ok prog =>
    if opts.showAst then
      IO.println (repr prog).pretty
    if opts.check then
      -- Execute the program with the evaluator
      let env := Measure.Scratch.defaultEnv
      let (_, _) ← Measure.Scratch.evalScratchProgram env contents
      IO.println s!"{file}: OK ({prog.stmts.length} top-level statement(s))"
    -- If neither --ast nor --check, execute by default
    if !opts.showAst && !opts.check then
      let env := Measure.Scratch.defaultEnv
      let (_, _) ← Measure.Scratch.evalScratchProgram env contents
      pure ()
    return 0

end MeasureCli

/-- Main entry point. -/
def main (args : List String) : IO UInt32 := do
  match MeasureCli.parseArgs args with
  | .error e =>
    IO.eprintln s!"measure: {e}"
    IO.eprintln "Usage: measure [<file.msr>] [--ast] [--check] [--repl]"
    return 1
  | .ok opts =>
    MeasureCli.run opts
