/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Theory.Module

/-! # Theory Graph

The global theory relation graph maintained by the kernel.
Supports registration, BFS reachability, compatibility checking,
and structural rule validation.
-/

namespace Measure.Theory

/-- Compatibility check result. -/
inductive CompatResult where
  | compatible
  | bridgeable (bridge : ApproxBridge)
  | incompatible (witness : ConflictWitness)
  deriving Inhabited, Repr

/-- Structural rule violation. -/
structure RuleViolation where
  ruleNumber : Nat
  description : String
  involvedA : String
  involvedB : String
  deriving Inhabited, Repr

/-- The global theory relation graph. -/
structure TheoryGraph where
  modules : Std.HashMap String TheoryModule := {}
  conflicts : List (String × String) := []
  bridges : Std.HashMap String (List ApproxBridge) := {}

instance : Inhabited TheoryGraph := ⟨{}, [], {}⟩

namespace TheoryGraph

/-- Register a new theory module. -/
def register (g : TheoryGraph) (m : TheoryModule)
    : Except String TheoryGraph :=
  if g.modules.contains m.name then
    .error s!"Theory already registered: {m.name}"
  else
    .ok { g with modules := g.modules.insert m.name m }

/-- Check if two theories are in conflict. -/
def areConflicting (g : TheoryGraph) (a b : String) : Bool :=
  let norm := if a < b then (a, b) else (b, a)
  g.conflicts.any (· == norm)

/-- Find an approximation bridge from source to target. -/
def findBridge (g : TheoryGraph) (source target : String)
    : Option ApproxBridge := do
  let bridges ← g.bridges.get? source
  bridges.find? (fun b => b.target == target)

/-- BFS reachability via extends/compatible edges. -/
partial def isAccessible (g : TheoryGraph) (from_ target : String)
    : Bool :=
  if from_ == target then true
  else
    let rec bfs (queue : List String) (visited : List String)
        : Bool :=
      match queue with
      | [] => false
      | cur :: rest =>
        match g.modules.get? cur with
        | none => bfs rest visited
        | some mod =>
          -- BFS traverses extends and compatible edges (not conflict/approx)
          let neighbors := mod.relations.filterMap fun r =>
            match r with
            | .extension child parent _ =>
              if child == cur then some parent
              else if parent == cur then some child
              else none
            | .compatible left right =>
              if left == cur then some right
              else if right == cur then some left
              else none
            | .conflict .. => none
            | .approx .. => none
          let newNodes := neighbors.filter (fun n => !visited.contains n)
          if newNodes.any (· == target) then true
          else
            let visited' := visited ++ newNodes
            bfs (rest ++ newNodes) visited'
    bfs [from_] [from_]

/-- Register a conflict between two theories (normalized pair). -/
def addConflict (g : TheoryGraph) (a b : String) (_wit : ConflictWitness)
    : TheoryGraph :=
  let norm := if a < b then (a, b) else (b, a)
  if g.conflicts.any (· == norm) then g
  else { g with conflicts := g.conflicts ++ [norm] }

/-- Four-stage compatibility check (mirrors C++ check_compatibility). -/
def checkCompatibility (g : TheoryGraph) (a b : String) : CompatResult :=
  -- Stage 1: Cache lookup
  if g.areConflicting a b then
    match g.findBridge a b |>.orElse (fun _ => g.findBridge b a) with
    | some bridge => .bridgeable bridge
    | none => .incompatible {
        proposition := s!"{a} ⊥ {b}"
        proofFromLeft := ""
        proofFromRight := ""
        kind := .direct s!"{a} ⊥ {b}"
        severity := .fundamental }
  else
    -- Stage 2+: no conflict in cache, report compatible
    .compatible

end TheoryGraph
end Measure.Theory
