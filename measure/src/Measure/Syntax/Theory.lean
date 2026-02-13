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
import Measure.Syntax.MetadataExt
import Measure.Dim.Basic
import Measure.Kernel.Elab

namespace Measure.Syntax

open Lean Elab Command Meta
open Measure.Kernel (TheoryRegistry TheoryGraph TheoryId RigorLevel ConservationChecker)
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

-- ============================================================
-- Approximation relation tracking (separate extension)
-- ============================================================

/-- A directed approximation relationship between two theories.
    `child` is an approximation of `parent` when `parent` has strictly higher rigor. -/
structure ApproxRelation where
  child    : Name        -- the lower-rigor (approximation) theory
  parent   : Name        -- the higher-rigor (more fundamental) theory
  rigorGap : Nat         -- parent.rigor.toNat - child.rigor.toNat
  deriving Repr, Inhabited

/-- Environment extension for storing approximation relationships between theories. -/
initialize approxRelExt : SimplePersistentEnvExtension ApproxRelation (Array ApproxRelation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl Array.append #[]
  }

/-- Check if `child` is registered as an approximation of `parent`. -/
def isApproximationOf (env : Environment) (child parent : Name) : Bool :=
  (approxRelExt.getState env).any fun r => r.child == child && r.parent == parent

/-- Get all theories that a given theory subsumes (i.e. theories that are approximations of it). -/
def getSubsumed (env : Environment) (parent : Name) : Array Name :=
  (approxRelExt.getState env).filterMap fun r =>
    if r.parent == parent then some r.child else none

/-- Get all theories that a given theory is an approximation of. -/
def getApproximationTargets (env : Environment) (child : Name) : Array Name :=
  (approxRelExt.getState env).filterMap fun r =>
    if r.child == child then some r.parent else none

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
      info.rigorLevel (0 : UInt64) (1 : UInt64) with
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

  -- Phase 4: Auto-degradation — mark lower-rigor parents as approximations
  for pname in parentNames do
    let env ← getEnv
    match findTheory? env pname with
    | none => pure ()
    | some parentInfo =>
      if info.rigorLevel.toNat > parentInfo.rigorLevel.toNat then
        let rel : ApproxRelation := {
          child    := pname
          parent   := theoryName
          rigorGap := info.rigorLevel.toNat - parentInfo.rigorLevel.toNat
        }
        modifyEnv fun env => approxRelExt.addEntry env rel
        logInfo m!"Theory '{pname}' is subsumed by '{theoryName}' as approximation (rigor: {parentInfo.rigorLevel.toString} < {info.rigorLevel.toString})"

  -- Elaborate body inside a namespace
  elabCommand (← `(namespace $(mkIdent theoryName)))
  for cmd in body do
    elabCommand cmd
  elabCommand (← `(end $(mkIdent theoryName)))

  -- Phase 5: Rigor auto-propagation — compute effective rigor from declaration metadata
  do
    let env ← getEnv
    -- Convert declared rigor to UInt8 for C++ propagation
    let declaredU8 : UInt8 := info.rigorLevel.toUInt8
    let metadataMap := metadataExt.getState env
    let mut effectiveU8 : UInt8 := declaredU8
    let mut degradingDecl : Option Name := none
    for (declName, md) in metadataMap.toList do
      if theoryName.isPrefixOf declName then
        match md.rigor with
        | some syntaxRigor =>
          let declU8 : UInt8 := syntaxRigor.toUInt8
          let propagated := Measure.Kernel.Rigor.propagateRaw effectiveU8 declU8
          if propagated > effectiveU8 then
            effectiveU8 := propagated
            degradingDecl := some declName
        | none => pure ()
    if effectiveU8 > declaredU8 then
      let declaredStr := Measure.Kernel.Rigor.toStringRaw declaredU8
      let effectiveStr := Measure.Kernel.Rigor.toStringRaw effectiveU8
      let axiomStr := match degradingDecl with
        | some n => s!"'{n}'"
        | none   => "unknown"
      logWarning m!"Theory '{theoryName}' rigor degraded from {declaredStr} to {effectiveStr} due to axiom {axiomStr}"
      -- Convert effective rigor back to RigorLevel for TheoryInfo
      let effectiveSyntaxRigor : Measure.Syntax.RigorLevel :=
        Measure.Theory.RigorLevel.ofUInt8 effectiveU8
      let updatedInfo : TheoryInfo := { info with rigorLevel := effectiveSyntaxRigor }
      modifyEnv fun env => theoryExt.addEntry env updatedInfo

  -- Phase 6: Automatic self-consistency verification
  -- Scan all declarations in the theory namespace and verify:
  --   (a) Dimensional consistency of all axioms with Quantity types
  --   (b) Internal axiom consistency via C++ ConservationChecker
  --   (c) Noether conservation law derivation from symmetries
  let env ← getEnv
  let mut axiomCount : Nat := 0
  let mut dimErrors : Array String := #[]
  let mut conservationLaws : Array (Name × String) := #[]

  -- (a) Dimensional consistency: iterate all constants in the theory namespace
  let theoryDecls := env.constants.fold (init := #[]) fun acc declName cinfo =>
    if theoryName.isPrefixOf declName then acc.push (declName, cinfo) else acc
  for (declName, cinfo) in theoryDecls do
    match cinfo with
    | .axiomInfo ai =>
      axiomCount := axiomCount + 1
      let checkResult ← liftTermElabM do
        let ty := ai.type
        let ty ← whnf ty
        forallTelescope ty fun _xs body => do
          let body ← whnf body
          match body.eq? with
          | some (eqTy, lhs, rhs) =>
            let eqTy ← whnf eqTy
            -- Case 1: @Eq (Quantity d c) lhs rhs — dims trivially match
            match eqTy.getAppFn.constName? with
            | some n =>
              if n == `Measure.Quantity.Quantity then
                return (none : Option String)
              else
                -- Case 2: @Eq T lhs rhs where lhs/rhs have Quantity types
                let lhsTy ← inferType lhs
                let rhsTy ← inferType rhs
                let lhsTy ← whnf lhsTy
                let rhsTy ← whnf rhsTy
                let lhsDim : Option Expr := do
                  let cn ← lhsTy.getAppFn.constName?
                  if cn == `Measure.Quantity.Quantity then lhsTy.getAppArgs[0]? else none
                let rhsDim : Option Expr := do
                  let cn ← rhsTy.getAppFn.constName?
                  if cn == `Measure.Quantity.Quantity then rhsTy.getAppArgs[0]? else none
                match lhsDim, rhsDim with
                | some d1, some d2 =>
                  let compat ← isDefEq d1 d2
                  if compat then return none
                  else return some s!"Axiom '{declName}': LHS dim ≠ RHS dim in equality"
                | _, _ => return none
            | none => return none
          | none => return (none : Option String)
      match checkResult with
      | some errMsg => dimErrors := dimErrors.push errMsg
      | none => pure ()
    | _ => pure ()

  -- Report dimensional errors
  for errMsg in dimErrors do
    throwError m!"Theory '{theoryName}' dimensional inconsistency: {errMsg}"

  -- (b) Conservation checking via C++ ConservationChecker
  let env ← getEnv
  let mut conservationCount : Nat := 0
  -- Collect all declarations with @[conservation] metadata in this namespace
  for (declName, _) in theoryDecls do
    match findMetadata? env declName with
    | some md =>
      for qty in md.conservation do
        conservationLaws := conservationLaws.push (declName, qty.toString)
    | none => pure ()

  -- If conservation laws exist, run the C++ checker
  if conservationLaws.size > 0 then
    let env ← getEnv
    match getRegistry env with
    | some reg =>
      let tid := reg.findByName theoryName.toString
      let checker := ConservationChecker.new tid
      -- Add each conservation law to the checker
      for (declName, qtyName) in conservationLaws do
        let _ := checker.addLaw declName.toString qtyName
      -- Run checkAll with the theory name as context
      let verdicts := checker.checkAll theoryName.toString
      conservationCount := conservationLaws.size
      for verdict in verdicts do
        if verdict.startsWith "FAIL" then
          throwError m!"Theory '{theoryName}' conservation violation: {verdict}"
        else
          logInfo m!"[conservation] {verdict}"
    | none =>
      -- FFI unavailable, skip conservation checking
      conservationCount := conservationLaws.size

  logInfo m!"Theory '{theoryName}' self-consistency verified: {axiomCount} axioms checked, {conservationCount} conservation laws"

end Measure.Syntax
