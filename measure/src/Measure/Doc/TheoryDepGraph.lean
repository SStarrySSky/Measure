/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Theory dependency graph visualization for documentation.
Exports DOT and JSON formats for rendering.
See ARCHITECTURE.md Section 10.5 Phase 5.
-/
import Lean

namespace Measure.Doc

open Lean

/-- Relation type between theories in the dependency graph. -/
inductive DepRelation where
  | approximation (limit : String)
  | conflict (reason : String)
  | extension
  | imports
  deriving Repr, Inhabited

/-- A node in the theory dependency graph. -/
structure DepNode where
  name      : Name
  rigor     : String := "strict"
  axiomCount : Nat := 0
  docstring : String := ""
  deriving Repr, Inhabited

/-- An edge in the theory dependency graph. -/
structure DepEdge where
  source   : Name
  target   : Name
  relation : DepRelation
  deriving Repr, Inhabited

/-- Full theory dependency graph. -/
structure TheoryDepGraph where
  nodes : List DepNode := []
  edges : List DepEdge := []
  deriving Repr, Inhabited

namespace TheoryDepGraph

/-- Add a theory node. -/
def addNode (g : TheoryDepGraph) (n : DepNode) : TheoryDepGraph :=
  { nodes := g.nodes ++ [n], edges := g.edges }

/-- Add a relation edge. -/
def addEdge (g : TheoryDepGraph) (e : DepEdge) : TheoryDepGraph :=
  { nodes := g.nodes, edges := g.edges ++ [e] }

/-- Export as DOT format for Graphviz rendering. -/
def toDot (g : TheoryDepGraph) : String :=
  let header := "digraph TheoryDependencies {\n"
  let config := "  rankdir=BT;\n  node [shape=box, style=\"rounded,filled\"];\n\n"
  let nodes := g.nodes.map fun n =>
    let color := match n.rigor with
      | "strict"      => "#e8f5e9"
      | "approximate" => "#fff3e0"
      | "empirical"   => "#fce4ec"
      | "numerical"   => "#e3f2fd"
      | _             => "#ffffff"
    s!"  \"{n.name}\" [label=\"{n.name}\\naxioms: {n.axiomCount}\\n[{n.rigor}]\", fillcolor=\"{color}\"];\n"
  let edges := g.edges.map fun e =>
    let (style, color, lbl) := match e.relation with
      | .approximation limit =>
        ("dashed", "blue", s!"via {limit}")
      | .conflict reason =>
        ("bold", "red", reason)
      | .extension =>
        ("solid", "green", "extends")
      | .imports =>
        ("dotted", "gray", "imports")
    s!"  \"{e.source}\" -> \"{e.target}\" [style={style}, color={color}, label=\"{lbl}\"];\n"
  let footer := "}\n"
  header ++ config ++ String.join nodes ++ "\n" ++ String.join edges ++ footer

/-- Export as JSON for web-based visualization. -/
def toJson (g : TheoryDepGraph) : String :=
  let lb := "{"
  let rb := "}"
  let nodeEntries := g.nodes.map fun n =>
    s!"    {lb}\"name\": \"{n.name}\", \"rigor\": \"{n.rigor}\", \"axioms\": {n.axiomCount}{rb}"
  let edgeEntries := g.edges.map fun e =>
    let relStr := match e.relation with
      | .approximation l => s!"approximation({l})"
      | .conflict r      => s!"conflict({r})"
      | .extension       => "extension"
      | .imports         => "imports"
    s!"    {lb}\"source\": \"{e.source}\", \"target\": \"{e.target}\", \"relation\": \"{relStr}\"{rb}"
  "{\n  \"nodes\": [\n" ++
  String.intercalate ",\n" nodeEntries ++
  "\n  ],\n  \"edges\": [\n" ++
  String.intercalate ",\n" edgeEntries ++
  "\n  ]\n}"

/-- Get all theories reachable from a given theory via imports/extensions. -/
def reachableFrom (g : TheoryDepGraph) (name : Name) : List Name :=
  let directDeps := g.edges.filter (fun e =>
    e.source == name &&
    match e.relation with
    | .extension | .imports => true
    | _ => false
  ) |>.map (·.target)
  directDeps

end TheoryDepGraph

end Measure.Doc
