/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Provenance audit API: query, validate, and report data lineage.
See ARCHITECTURE.md Section 5.2.
-/
import Measure.Quantity.Provenance
import Measure.External.DataSource

namespace Measure.Quantity

/-- Audit trail entry: a flattened record of one provenance node. -/
structure AuditEntry where
  depth     : Nat
  kind      : String
  label     : String
  children  : Nat := 0
  deriving Repr, Inhabited

namespace Provenance

/-- Collect all database sources referenced in a provenance tree. -/
def dataSources : Provenance → List (String × String)
  | .database source version => [(source, version)]
  | .combined _ children => children.flatMap dataSources
  | .calculation _ inputs => inputs.flatMap dataSources
  | _ => []

/-- Collect all measurement sources. -/
def measurements : Provenance → List (String × String)
  | .measurement lab instrument => [(lab, instrument)]
  | .combined _ children => children.flatMap measurements
  | .calculation _ inputs => inputs.flatMap measurements
  | _ => []

/-- Count the total number of nodes in the provenance tree. -/
def nodeCount : Provenance → Nat
  | .none => 0
  | .measurement _ _ => 1
  | .database _ _ => 1
  | .userDefined _ => 1
  | .calculation _ inputs => 1 + inputs.foldl (· + nodeCount ·) 0
  | .combined _ children => 1 + children.foldl (· + nodeCount ·) 0

/-- Maximum depth of the provenance tree. -/
def maxDepth : Provenance → Nat
  | .none => 0
  | .measurement _ _ => 1
  | .database _ _ => 1
  | .userDefined _ => 1
  | .calculation _ inputs =>
    1 + inputs.foldl (fun acc p => max acc (maxDepth p)) 0
  | .combined _ children =>
    1 + children.foldl (fun acc p => max acc (maxDepth p)) 0

/-- Flatten the provenance tree into an audit trail. -/
partial def toAuditTrail (p : Provenance) (depth : Nat := 0) : List AuditEntry :=
  match p with
  | .none => [{ depth, kind := "none", label := "(no provenance)" }]
  | .measurement lab inst =>
    [{ depth, kind := "measurement", label := s!"{lab}/{inst}" }]
  | .database source version =>
    [{ depth, kind := "database", label := s!"{source} v{version}" }]
  | .userDefined label =>
    [{ depth, kind := "user", label }]
  | .calculation op inputs =>
    { depth, kind := "calculation", label := op, children := inputs.length }
      :: inputs.flatMap (toAuditTrail · (depth + 1))
  | .combined op children =>
    { depth, kind := "combined", label := op, children := children.length }
      :: children.flatMap (toAuditTrail · (depth + 1))

/-- Render a human-readable audit report. -/
partial def auditReport (p : Provenance) : String :=
  let entries := toAuditTrail p
  let lines := entries.map fun e =>
    let indent := String.ofList (List.replicate (e.depth * 2) ' ')
    let suffix := if e.children > 0 then s!" ({e.children} inputs)" else ""
    s!"{indent}[{e.kind}] {e.label}{suffix}"
  "\n".intercalate lines

/-- Validate that all database references have matching versions. -/
def validateVersions (p : Provenance)
    (expected : List (String × String)) : List String :=
  let actual := dataSources p
  expected.filterMap fun (src, ver) =>
    match actual.find? (·.1 == src) with
    | some (_, actualVer) =>
      if actualVer == ver then Option.none
      else some s!"Version mismatch for {src}: expected {ver}, got {actualVer}"
    | Option.none => Option.none

end Provenance

end Measure.Quantity
