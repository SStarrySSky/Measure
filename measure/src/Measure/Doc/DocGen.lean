/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Documentation generator: combines dimension index, theory graph,
conservation law docs, and module summaries.
See ARCHITECTURE.md Section 10.5 Phase 5.
-/
import Measure.Doc.DimIndex
import Measure.Doc.TheoryDepGraph

namespace Measure.Doc

open Measure.Syntax

/-- Conservation law documentation entry. -/
structure ConservationDocEntry where
  lawName    : String
  quantity   : String
  source     : String  -- "declared" | "noether" | "inherited"
  symmetry   : Option String := none
  modules    : List String := []
  deriving Repr, Inhabited

/-- Module-level documentation summary. -/
structure ModuleSummary where
  name           : String
  rigor          : RigorLevel
  theoryCount    : Nat := 0
  axiomCount     : Nat := 0
  theoremCount   : Nat := 0
  conservedQtys  : List String := []
  uncertaintyModel : String := "Gaussian"
  deriving Repr, Inhabited

/-- Full documentation bundle for a Measure project. -/
structure DocBundle where
  dimIndex         : DimIndex := DimIndex.defaultIndex
  theoryGraph      : TheoryDepGraph := {}
  conservationDocs : List ConservationDocEntry := []
  moduleSummaries  : List ModuleSummary := []
  deriving Repr, Inhabited

namespace DocBundle

/-- Generate the dimension index section. -/
def genDimSection (b : DocBundle) : String :=
  "## Physical Dimension Index\n\n" ++ b.dimIndex.toMarkdown

/-- Generate the theory graph section. -/
def genTheorySection (b : DocBundle) : String :=
  let header := "## Theory Dependency Graph\n\n"
  let dot := "```dot\n" ++ b.theoryGraph.toDot ++ "```\n"
  header ++ dot

/-- Generate the conservation law section. -/
def genConservationSection (b : DocBundle) : String :=
  let header := "## Conservation Laws\n\n"
  let tableHeader := "| Law | Quantity | Source | Symmetry | Modules |\n"
  let sep := "|-----|----------|--------|----------|--------|\n"
  let rows := b.conservationDocs.map fun e =>
    let sym := e.symmetry.getD "-"
    let mods := String.intercalate ", " e.modules
    s!"| {e.lawName} | {e.quantity} | {e.source} | {sym} | {mods} |\n"
  header ++ tableHeader ++ sep ++ String.join rows

/-- Generate module summaries section. -/
def genModuleSection (b : DocBundle) : String :=
  let header := "## Module Summaries\n\n"
  let tableHeader := "| Module | Rigor | Theories | Axioms | Theorems | Conserved | Uncertainty |\n"
  let sep := "|--------|-------|----------|--------|----------|-----------|-------------|\n"
  let rows := b.moduleSummaries.map fun m =>
    let conserved := String.intercalate ", " m.conservedQtys
    s!"| {m.name} | {RigorLevel.toString m.rigor} | {m.theoryCount} | {m.axiomCount} | {m.theoremCount} | {conserved} | {m.uncertaintyModel} |\n"
  header ++ tableHeader ++ sep ++ String.join rows

/-- Generate the complete documentation as markdown. -/
def generate (b : DocBundle) : String :=
  let title := "# Measure Project Documentation\n\n"
  title ++
  b.genDimSection ++ "\n" ++
  b.genTheorySection ++ "\n" ++
  b.genConservationSection ++ "\n" ++
  b.genModuleSection

end DocBundle

end Measure.Doc
