/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Theory graph visualization for LSP: measure/theoryGraph method.
Provides theory boundary highlighting and relation graph export.
See docs/syntax-and-integration.md Section 6.5.
-/
import Measure.LSP.DimHints

namespace Measure.LSP

/-- Theory relation type for graph edges. -/
inductive TheoryRelationType where
  | approximation  -- A is approximation of B
  | conflict       -- A conflicts with B
  | extension      -- A extends B
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A node in the theory relation graph. -/
structure TheoryGraphNode where
  name   : String
  rigor  : String := "strict"
  range  : Option Range := none
  deriving Repr, Inhabited

/-- An edge in the theory relation graph. -/
structure TheoryGraphEdge where
  source   : String
  target   : String
  relation : TheoryRelationType
  label    : Option String := none
  deriving Repr, Inhabited

/-- Full theory graph for visualization. -/
structure TheoryGraph where
  nodes : List TheoryGraphNode := []
  edges : List TheoryGraphEdge := []
  deriving Repr, Inhabited

namespace TheoryGraph

/-- Export the theory graph as DOT format for Graphviz. -/
def toDot (g : TheoryGraph) : String :=
  let header := "digraph TheoryGraph {\n  rankdir=BT;\n  node [shape=box, style=rounded];\n"
  let nodes := g.nodes.map fun n =>
    s!"  \"{n.name}\" [label=\"{n.name}\\n[{n.rigor}]\"];\n"
  let edges := g.edges.map fun e =>
    let style := match e.relation with
      | .approximation => "style=dashed, color=blue"
      | .conflict      => "style=bold, color=red"
      | .extension     => "style=solid, color=green"
    let lbl := match e.label with
      | some l => s!", label=\"{l}\""
      | none   => ""
    s!"  \"{e.source}\" -> \"{e.target}\" [{style}{lbl}];\n"
  let footer := "}\n"
  header ++ String.join nodes ++ String.join edges ++ footer

/-- Find all theories that conflict with a given theory. -/
def conflictsWith (g : TheoryGraph) (name : String) : List String :=
  g.edges.filter (fun e =>
    e.relation == .conflict &&
    (e.source == name || e.target == name)
  ) |>.map fun e =>
    if e.source == name then e.target else e.source

/-- Find all theories that a given theory approximates. -/
def approximates (g : TheoryGraph) (name : String) : List String :=
  g.edges.filter (fun e =>
    e.relation == .approximation && e.source == name
  ) |>.map (·.target)

end TheoryGraph

end Measure.LSP
