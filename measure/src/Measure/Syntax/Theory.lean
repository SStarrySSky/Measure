/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Theory keyword: Lean4 macro for isolated axiom contexts.
See ARCHITECTURE.md Section 6 and docs/syntax-and-integration.md Section 2.1.

Provides:
- `theory Name (extends Parent₁, Parent₂, ...)? where body` syntax
- TheoryInfo registration in environment extension
- Conflict detection via checkTheoryCompat
- Rigor context propagation into the theory namespace
-/
import Lean
import Measure.Syntax.Attributes
import Measure.Kernel.Elab

namespace Measure.Syntax

open Lean Elab Command Meta
open Measure.Kernel (TheoryRegistry TheoryGraph TheoryId RigorLevel)
open Measure.Kernel.Elab (getRegistry registerTheoryFFI checkTheoryCompatFFI)

/-- Theory module data structure stored in the environment. -/
structure TheoryInfo where
  name         : Name
  rigorLevel   : RigorLevel := .strict
  uncertainty  : UncertaintyModelId := .gaussian
  conservation : List ConservedQty := []
  extends_     : List Name := []
  deriving Repr, Inhabited

/-- Environment extension for storing theory module info. -/
initialize theoryExt : SimplePersistentEnvExtension TheoryInfo (Array TheoryInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl Array.append #[]
  }

/-- Look up a theory by name. -/
def findTheory? (env : Environment) (name : Name) : Option TheoryInfo :=
  (theoryExt.getState env).find? fun t => t.name == name

/-- Get all registered theories. -/
def allTheories (env : Environment) : Array TheoryInfo :=
  theoryExt.getState env

/-- Check if a theory name is already registered. -/
def isTheoryRegistered (env : Environment) (name : Name) : Bool :=
  (findTheory? env name).isSome

/-- Compatibility check result for theory registration. -/
inductive TheoryCompatResult where
  | ok
  | conflict (a b : Name) (reason : String)
  deriving Repr, Inhabited

/-- Check that all parent theories exist. -/
private def checkParentsExist (env : Environment) (child : Name)
    : List Name → Option TheoryCompatResult
  | [] => none
  | p :: rest =>
    match findTheory? env p with
    | none => some (.conflict p child s!"Parent theory '{p}' is not registered")
    | some _ => checkParentsExist env child rest

/-- Check pairwise rigor compatibility among parent TheoryInfos. -/
private def checkPairwiseCompat : List TheoryInfo → Option TheoryCompatResult
  | [] => none
  | _ :: [] => none
  | a :: rest =>
    match rest.find? (fun b =>
      (a.rigorLevel == .strict && b.rigorLevel == .numerical) ||
      (a.rigorLevel == .numerical && b.rigorLevel == .strict)) with
    | some b => some (.conflict a.name b.name
        s!"Rigor mismatch between '{a.name}' and '{b.name}'")
    | none => checkPairwiseCompat rest

/-- Check compatibility of a new theory against its parents. -/
def checkTheoryCompat (env : Environment) (info : TheoryInfo)
    : TheoryCompatResult :=
  match checkParentsExist env info.name info.extends_ with
  | some err => err
  | none =>
    let parentInfos := info.extends_.filterMap (findTheory? env)
    match checkPairwiseCompat parentInfos with
    | some err => err
    | none => .ok

-- ============================================================
-- Syntax: theory Name (extends Parent₁, ...)? where body
-- ============================================================

/-- Syntax for the `theory` command.
    Supports: `theory Foo where ...` and `theory Foo extends Bar, Baz where ...` -/
syntax (name := theoryCmd)
  "theory " ident (" extends " ident,+)? " where" ppDedent(ppLine command*) : command

/-- Register a theory and elaborate its body inside a namespace.
    Performs both Lean-side and FFI-side compatibility checks. -/
@[command_elab theoryCmd]
def elabTheoryCmd : CommandElab := fun stx => do
  let nameStx    := stx[1]
  let extendsOpt := stx[2]
  let body       := stx[4].getArgs

  let theoryName := nameStx.getId

  -- Duplicate check
  let env ← getEnv
  if isTheoryRegistered env theoryName then
    throwError s!"Theory '{theoryName}' is already registered"

  -- Parse extends clause
  let parentNames : List Name :=
    if extendsOpt.isNone then []
    else
      let sepArray := extendsOpt[0][1]
      (sepArray.getSepArgs.toList.map Syntax.getId)

  -- Build TheoryInfo (default rigor=strict, uncertainty=gaussian)
  let info : TheoryInfo := {
    name     := theoryName
    extends_ := parentNames
  }

  -- Phase 1: Lean-side compatibility check (parent existence + rigor pairwise)
  match checkTheoryCompat env info with
  | .conflict a b reason =>
    throwError s!"Theory conflict: '{a}' vs '{b}': {reason}"
  | .ok => pure ()

  -- Phase 2: Register into C++ TheoryRegistry via FFI (if available)
  match registerTheoryFFI env theoryName.toString
      (parentNames.toArray.map fun pname =>
        match getRegistry env with
        | some reg => reg.findByName pname.toString
        | none => 0)
      (Kernel.RigorLevel.ofUInt8 (UInt8.ofNat info.rigorLevel.toNat)) (0 : UInt64) (1 : UInt64) with
  | some (newId, env') =>
    modifyEnv fun _ => env'
    -- Phase 3: FFI-based domain compatibility check against all loaded theories
    let env'' ← getEnv
    let existingTheories := allTheories env''
    let existingIds : Array TheoryId := existingTheories.filterMap fun t =>
      if t.name == theoryName then none
      else match getRegistry env'' with
        | some reg => some (reg.findByName t.name.toString)
        | none => none
    match checkTheoryCompatFFI env'' newId existingIds with
    | some (a, b, reason) =>
      throwError s!"Theory incompatibility (FFI): '{a}' vs '{b}': {reason}"
    | none => pure ()
  | none =>
    -- FFI not available; skip C++ registration (Lean-side only)
    pure ()

  -- Register in Lean environment extension
  modifyEnv fun env => theoryExt.addEntry env info
  logInfo m!"Registered theory '{theoryName}' (extends={parentNames})"

  -- Elaborate body inside a namespace
  elabCommand (← `(namespace $(mkIdent theoryName)))
  for cmd in body do
    elabCommand cmd
  elabCommand (← `(end $(mkIdent theoryName)))

end Measure.Syntax
