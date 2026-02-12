/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Elaboration hooks that connect the Measure kernel FFI to the Lean elaborator.
Provides attributes, commands, and tactic extensions.
-/
import Measure.Kernel.Wrappers
import Lean.Elab.Command
import Lean.Elab.Tactic

namespace Measure.Kernel.Elab

open Lean Elab Command Tactic Meta

-- ============================================================
-- Environment extension: global TheoryRegistry
-- ============================================================

initialize measureRegistryExt : EnvExtension (Option TheoryRegistry) ←
  registerEnvExtension (pure none)

/-- Get the global theory registry from the environment, if it exists.
    Returns `none` if the FFI registry has not been initialized. -/
def getRegistry (env : Environment) : Option TheoryRegistry :=
  measureRegistryExt.getState env

-- ============================================================
-- TheoryGraph extension: cached graph for compat checks
-- ============================================================

initialize measureGraphExt : EnvExtension (Option TheoryGraph) ←
  registerEnvExtension (pure none)

/-- Get or create the theory graph from the registry.
    Returns `none` if the FFI registry has not been initialized. -/
def getOrCreateGraph (env : Environment) : Option TheoryGraph :=
  match measureGraphExt.getState env with
  | some g => some g
  | none   =>
    match getRegistry env with
    | some reg => some (TheoryGraph.new reg)
    | none => none

/-- FFI compatibility result codes from TheoryGraph.checkCompat:
    0 = compatible, 1 = bridge (compatible via bridge), 2 = incompatible -/
def compatResultIsIncompatible (code : UInt8) : Bool := code == 2

-- ============================================================
-- registerTheory: register to both Lean extension and C++ registry
-- ============================================================

/-- Register a theory into the C++ TheoryRegistry and return its TheoryId.
    Also refreshes the cached TheoryGraph.
    Returns `none` if the FFI registry is not available. -/
def registerTheoryFFI (env : Environment) (name : String)
    (parentIds : Array TheoryId) (rigor : RigorLevel)
    (maxEpsNum maxEpsDen : UInt64) : Option (TheoryId × Environment) :=
  match getRegistry env with
  | none => none
  | some reg =>
    let tid := reg.register name parentIds rigor.toUInt8 maxEpsNum maxEpsDen
    -- Refresh the graph cache after registration
    let graph := TheoryGraph.new reg
    let env := measureGraphExt.setState env (some graph)
    some (tid, env)

/-- Check compatibility of a new theory (by TheoryId) against a list of
    existing theory ids using the C++ TheoryGraph.
    Returns `none` if all compatible (or FFI unavailable),
    or `some (a, b, reason)` on conflict. -/
def checkTheoryCompatFFI (env : Environment) (newId : TheoryId)
    (existingIds : Array TheoryId) : Option (String × String × String) :=
  match getRegistry env, getOrCreateGraph env with
  | some reg, some graph =>
    existingIds.foldl (init := none) fun acc eid =>
      match acc with
      | some conflict => some conflict
      | none =>
        let code := graph.checkCompatRaw newId eid
        if compatResultIsIncompatible code then
          let newName := reg.getName newId
          let existName := reg.getName eid
          some (newName, existName,
            s!"Theory '{newName}' is incompatible with '{existName}' (FFI conflict detected)")
        else
          none
  | _, _ => none

-- ============================================================
-- Command: register_measure_theory
-- ============================================================

syntax (name := registerMeasureTheory)
  "register_measure_theory" str ("[" ident,* "]")? ("rigor" ":=" num)? : command

@[command_elab registerMeasureTheory]
def elabRegisterMeasureTheory : CommandElab := fun stx => do
  let name := stx[1].isStrLit?.getD ""
  let rigorLevel : RigorLevel := match stx[3].isNone with
    | true => .approximate
    | false =>
      let n := stx[3][1].isNatLit?.getD 1
      RigorLevel.ofUInt8 (UInt8.ofNat n)
  let env ← getEnv
  match getRegistry env with
  | some reg =>
    let _id := reg.registerRoot name rigorLevel 0 1
    logInfo m!"Registered measure theory: {name}"
  | none =>
    logInfo m!"Registered measure theory (Lean-only, FFI unavailable): {name}"

-- ============================================================
-- Tactic: check_rigor_compat
-- ============================================================

syntax (name := checkRigorCompat) "check_rigor_compat" num num : tactic

@[tactic checkRigorCompat]
def elabCheckRigorCompat : Tactic := fun stx => do
  let declared := RigorLevel.ofUInt8 (UInt8.ofNat (stx[1].isNatLit?.getD 0))
  let actual := RigorLevel.ofUInt8 (UInt8.ofNat (stx[2].isNatLit?.getD 0))
  if isRigorCompatible declared actual then
    logInfo m!"Rigor levels compatible: {rigorToString declared} >= {rigorToString actual}"
  else
    throwError "Rigor incompatible: declared {rigorToString declared} < actual {rigorToString actual}"

-- ============================================================
-- Tactic: measure_approx_eq
-- ============================================================

syntax (name := measureApproxEq) "measure_approx_eq" num num : tactic

@[tactic measureApproxEq]
def elabMeasureApproxEq : Tactic := fun stx => do
  let a := (stx[1].isNatLit?.getD 0).toFloat
  let b := (stx[2].isNatLit?.getD 0).toFloat
  let checker := ApproxEqChecker.new ()
  let result := checker.tryNumeric a b
  let (isEq, epsNum, epsDen) := result
  if isEq then
    logInfo m!"Values are approximately equal (eps = {epsNum}/{epsDen})"
  else
    throwError "Values are not approximately equal"

end Measure.Kernel.Elab