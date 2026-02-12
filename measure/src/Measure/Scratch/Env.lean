/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode runtime: environment (variable bindings and scope).
-/
import Measure.Scratch.Value

namespace Measure.Scratch

/-- Runtime environment for the Scratch Mode interpreter. -/
structure Env where
  vars     : Std.HashMap String Value := {}
  parent   : Option Env := none
  imports  : List (List String) := []
  deriving Inhabited

namespace Env

/-- Create an empty top-level environment. -/
def empty : Env := {}

/-- Look up a variable, searching parent scopes. -/
partial def lookup (env : Env) (name : String) : Option Value :=
  match env.vars.get? name with
  | some v => some v
  | none =>
    match env.parent with
    | some p => p.lookup name
    | none => none

/-- Bind a variable in the current scope (immutable: returns new Env). -/
def bind (env : Env) (name : String) (val : Value) : Env :=
  { env with vars := env.vars.insert name val }

/-- Create a child scope (for let blocks, for loops, function bodies). -/
def pushScope (env : Env) : Env :=
  { vars := {}, parent := some env, imports := env.imports }

/-- Add an import path to the environment. -/
def addImport (env : Env) (path : List String) : Env :=
  { env with imports := path :: env.imports }

/-- Bind multiple variables at once. -/
def bindAll (env : Env) (bindings : List (String × Value)) : Env :=
  bindings.foldl (fun e (n, v) => e.bind n v) env

/-- Flatten the entire scope chain into a single HashMap (for closure capture).
    Inner scopes shadow outer scopes. -/
partial def flatten (env : Env) : Std.HashMap String Value :=
  match env.parent with
  | none => env.vars
  | some p =>
    let parentVars := p.flatten
    env.vars.fold (init := parentVars) fun acc k v => acc.insert k v

/-- Restore an Env from a captured closure snapshot. -/
def fromSnapshot (snap : Std.HashMap String Value) : Env :=
  { vars := snap, parent := none, imports := [] }

end Env

end Measure.Scratch
