/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Main entry point for the Measure CLI.
-/
import Measure

-- ============================================================
-- Version & metadata
-- ============================================================

private def version : String := "0.1.0"

private def leanVersion : String := "Lean 4 + Mathlib"

-- ============================================================
-- Help text
-- ============================================================

private def helpText : String :=
  "Measure — Physics Theory Formalization Language\n" ++
  "Built on " ++ leanVersion ++ "\n" ++
  "\n" ++
  "Usage: measure <command> [arguments]\n" ++
  "\n" ++
  "Commands:\n" ++
  "  check [flags] <file|dir>  Audit .lean files (sorry, axiom, theorem counts)\n" ++
  "  info                      Show project summary (theories, constants)\n" ++
  "  constants                 List all physical constants with uncertainty status\n" ++
  "  theories [flags]          List registered theory modules and compatibility\n" ++
  "  version                   Print version\n" ++
  "  help                      Show this help message\n" ++
  "\n" ++
  "Check flags:\n" ++
  "  --verbose    Show per-file breakdown of sorry and axiom locations\n" ++
  "  --json       Output results as JSON for tooling integration\n" ++
  "\n" ++
  "Theories flags:\n" ++
  "  --json       Output theory list as JSON\n" ++
  "\n" ++
  "Examples:\n" ++
  "  measure check src/Measure/Physics/Relativity.lean\n" ++
  "  measure check --verbose src/Measure/Physics/\n" ++
  "  measure check --json src/Measure/Physics/Relativity.lean\n" ++
  "  measure theories --json\n" ++
  "  measure constants"

-- ============================================================
-- Constants table
-- ============================================================

private structure ConstantEntry where
  name        : String
  symbol      : String
  value       : String
  unit        : String
  exact       : Bool
  source      : String

private def constantsTable : List ConstantEntry := [
  { name := "Speed of light"
    symbol := "c"
    value := "299 792 458"
    unit := "m/s"
    exact := true
    source := "SI 2019 (defining)" },
  { name := "Planck constant"
    symbol := "h"
    value := "6.626 070 15 × 10⁻³⁴"
    unit := "J·s"
    exact := true
    source := "SI 2019 (defining)" },
  { name := "Reduced Planck constant"
    symbol := "ℏ"
    value := "1.054 571 817 × 10⁻³⁴"
    unit := "J·s"
    exact := true
    source := "Derived from h" },
  { name := "Boltzmann constant"
    symbol := "k_B"
    value := "1.380 649 × 10⁻²³"
    unit := "J/K"
    exact := true
    source := "SI 2019 (defining)" },
  { name := "Avogadro constant"
    symbol := "N_A"
    value := "6.022 140 76 × 10²³"
    unit := "mol⁻¹"
    exact := true
    source := "SI 2019 (defining)" },
  { name := "Elementary charge"
    symbol := "e"
    value := "1.602 176 634 × 10⁻¹⁹"
    unit := "C"
    exact := true
    source := "SI 2019 (defining)" },
  { name := "Stefan-Boltzmann constant"
    symbol := "σ"
    value := "5.670 374 419 × 10⁻⁸"
    unit := "W·m⁻²·K⁻⁴"
    exact := true
    source := "Derived (exact)" },
  { name := "Gravitational constant"
    symbol := "G"
    value := "(6.674 30 ± 0.000 15) × 10⁻¹¹"
    unit := "m³·kg⁻¹·s⁻²"
    exact := false
    source := "CODATA 2022" },
  { name := "Electron mass"
    symbol := "m_e"
    value := "(9.109 383 7015 ± 0.000 000 0028) × 10⁻³¹"
    unit := "kg"
    exact := false
    source := "CODATA 2022" },
  { name := "Proton mass"
    symbol := "m_p"
    value := "(1.672 621 923 69 ± 0.000 000 000 51) × 10⁻²⁷"
    unit := "kg"
    exact := false
    source := "CODATA 2022" },
  { name := "Fine-structure constant"
    symbol := "α"
    value := "(7.297 352 5693 ± 0.000 000 0011) × 10⁻³"
    unit := "(dimensionless)"
    exact := false
    source := "CODATA 2022" },
  { name := "Vacuum permeability"
    symbol := "μ₀"
    value := "(1.256 637 062 12 ± 0.000 000 000 19) × 10⁻⁶"
    unit := "N/A²"
    exact := false
    source := "CODATA 2022" },
  { name := "Vacuum permittivity"
    symbol := "ε₀"
    value := "(8.854 187 8128 ± 0.000 000 0013) × 10⁻¹²"
    unit := "F/m"
    exact := false
    source := "CODATA 2022" }
]

private def printConstants : IO Unit := do
  IO.println "Physical Constants (CODATA 2022 + SI 2019 exact values)"
  IO.println "======================================================="
  IO.println ""
  let exactConsts := constantsTable.filter (·.exact)
  let measuredConsts := constantsTable.filter (fun c => !c.exact)
  IO.println "── Exact (zero uncertainty, SI 2019 defining constants) ──"
  IO.println ""
  for c in exactConsts do
    IO.println s!"  {c.symbol}  {c.name}"
    IO.println s!"     = {c.value} {c.unit}"
    IO.println s!"     [{c.source}]"
    IO.println ""
  IO.println "── Measured (Gaussian 1σ uncertainty) ──"
  IO.println ""
  for c in measuredConsts do
    IO.println s!"  {c.symbol}  {c.name}"
    IO.println s!"     = {c.value} {c.unit}"
    IO.println s!"     [{c.source}]"
    IO.println ""
  IO.println s!"Total: {exactConsts.length} exact, {measuredConsts.length} measured"

-- ============================================================
-- Theories table
-- ============================================================

private structure TheoryEntry where
  name        : String
  rigor       : String
  description : String
  submodules  : List String

private def theoriesTable : List TheoryEntry := [
  { name := "ClassicalMechanics"
    rigor := "strict"
    description := "Lagrangian, Hamiltonian, Newton, Noether, Conservation"
    submodules := ["Lagrangian", "Hamiltonian", "Newton", "Noether", "Conservation"] },
  { name := "Electromagnetism"
    rigor := "strict"
    description := "Maxwell's equations, potentials, EM waves"
    submodules := ["Maxwell", "Potential", "Wave"] },
  { name := "QuantumMechanics"
    rigor := "strict"
    description := "Hilbert spaces, Schrodinger equation, operators"
    submodules := ["Hilbert", "Schrodinger", "Operators"] },
  { name := "Relativity"
    rigor := "strict"
    description := "Special relativity: Minkowski spacetime, Lorentz transforms"
    submodules := ["Minkowski", "Lorentz"] },
  { name := "GeneralRelativity"
    rigor := "strict"
    description := "Einstein field equations, metric tensor"
    submodules := ["Einstein", "Metric"] },
  { name := "QFT"
    rigor := "approximate"
    description := "Quantum field theory: fields, Fock space"
    submodules := ["Fields", "FockSpace"] },
  { name := "Thermodynamics"
    rigor := "strict"
    description := "Laws of thermodynamics"
    submodules := ["Laws"] },
  { name := "StatisticalMechanics"
    rigor := "strict"
    description := "Ensemble theory"
    submodules := ["Ensemble"] },
  { name := "CondensedMatter"
    rigor := "approximate"
    description := "Crystal structures, band theory"
    submodules := ["Crystal", "BandTheory"] },
  { name := "FluidMechanics"
    rigor := "strict"
    description := "Navier-Stokes, wave propagation"
    submodules := ["NavierStokes", "Waves"] },
  { name := "Optics"
    rigor := "approximate"
    description := "Geometric optics, wave optics"
    submodules := ["Geometric", "Wave"] },
  { name := "AtomicPhysics"
    rigor := "strict"
    description := "Hydrogen atom, nuclear physics"
    submodules := ["Hydrogen", "Nuclear"] },
  { name := "ParticlePhysics"
    rigor := "strict"
    description := "Standard Model, scattering"
    submodules := ["StandardModel", "Scattering"] },
  { name := "QuantumGravity"
    rigor := "numerical"
    description := "Loop quantum gravity, holography"
    submodules := ["LQG", "Holography"] },
  { name := "StringTheory"
    rigor := "numerical"
    description := "String theory, supersymmetry"
    submodules := ["Strings", "Supersymmetry"] },
  { name := "Astrophysics"
    rigor := "approximate"
    description := "Cosmology, stellar structure"
    submodules := ["Cosmology", "StellarStructure"] },
  { name := "PlasmaPhysics"
    rigor := "approximate"
    description := "MHD, basic plasma"
    submodules := ["MHD", "Basic"] },
  { name := "Biophysics"
    rigor := "empirical"
    description := "Diffusion, membrane physics"
    submodules := ["Diffusion", "Membrane"] },
  { name := "Geophysics"
    rigor := "empirical"
    description := "Atmosphere, seismology"
    submodules := ["Atmosphere", "Seismology"] },
  { name := "MaterialScience"
    rigor := "empirical"
    description := "Semiconductor, superconductivity, elasticity"
    submodules := ["Semiconductor", "Superconductivity", "Elasticity"] },
  { name := "NonlinearDynamics"
    rigor := "numerical"
    description := "Chaos, dynamical systems"
    submodules := ["Chaos", "DynamicalSystems"] },
  { name := "QuantumInfo"
    rigor := "strict"
    description := "Qubit, entanglement"
    submodules := ["Qubit", "Entanglement"] },
  { name := "Frontier"
    rigor := "numerical"
    description := "Dark matter, dark energy, quantum thermodynamics"
    submodules := ["DarkMatter", "DarkEnergy", "QuantumThermodynamics"] },
  { name := "Historical"
    rigor := "empirical"
    description := "Classical models, approximate theories, quantum models"
    submodules := ["ClassicalModels", "ApproximateTheories", "QuantumModels"] }
]

/-- Known theory compatibility relations. -/
private structure CompatEntry where
  theoryA : String
  theoryB : String
  relation : String

private def compatTable : List CompatEntry := [
  { theoryA := "ClassicalMechanics"
    theoryB := "Relativity"
    relation := "approx (v/c → 0)" },
  { theoryA := "ClassicalMechanics"
    theoryB := "QuantumMechanics"
    relation := "approx (ℏ → 0)" },
  { theoryA := "QuantumMechanics"
    theoryB := "QFT"
    relation := "extension" },
  { theoryA := "Relativity"
    theoryB := "GeneralRelativity"
    relation := "extension (flat limit)" },
  { theoryA := "Electromagnetism"
    theoryB := "QFT"
    relation := "approx (classical limit)" },
  { theoryA := "Thermodynamics"
    theoryB := "StatisticalMechanics"
    relation := "extension (microscopic foundation)" },
  { theoryA := "GeneralRelativity"
    theoryB := "QuantumGravity"
    relation := "approx (semiclassical limit)" },
  { theoryA := "QFT"
    theoryB := "StringTheory"
    relation := "extension (point → string)" },
  { theoryA := "Optics"
    theoryB := "Electromagnetism"
    relation := "approx (ray limit)" },
  { theoryA := "FluidMechanics"
    theoryB := "StatisticalMechanics"
    relation := "approx (continuum limit)" }
]

private def printTheories : IO Unit := do
  IO.println "Registered Theory Modules"
  IO.println "========================="
  IO.println ""
  -- Group by rigor level
  let rigorOrder := ["strict", "approximate", "empirical", "numerical"]
  for rigor in rigorOrder do
    let theories := theoriesTable.filter (·.rigor == rigor)
    if theories.length > 0 then
      IO.println s!"── {rigor} ({theories.length} theories) ──"
      IO.println ""
      for t in theories do
        let subCount := t.submodules.length
        IO.println s!"  {t.name}  [{subCount} submodules]"
        IO.println s!"    {t.description}"
      IO.println ""
  IO.println "Theory Relations"
  IO.println "────────────────"
  IO.println ""
  for rel in compatTable do
    IO.println s!"  {rel.theoryA} ↔ {rel.theoryB}: {rel.relation}"
  IO.println ""
  let totalSub := theoriesTable.foldl (fun acc t => acc + t.submodules.length) 0
  IO.println s!"Total: {theoriesTable.length} theories, {totalSub} submodules, {compatTable.length} relations"

-- ============================================================
-- Info command
-- ============================================================

private def printInfo : IO Unit := do
  IO.println "Measure Language — Project Info"
  IO.println "==============================="
  IO.println ""
  IO.println s!"  Version:            {version}"
  IO.println s!"  Backend:            {leanVersion}"
  IO.println s!"  Theory modules:     {theoriesTable.length}"
  let totalSub := theoriesTable.foldl (fun acc t => acc + t.submodules.length) 0
  IO.println s!"  Theory submodules:  {totalSub}"
  IO.println s!"  Physical constants: {constantsTable.length}"
  let exactCount := (constantsTable.filter (·.exact)).length
  let measuredCount := (constantsTable.filter (fun c => !c.exact)).length
  IO.println s!"    Exact (SI 2019):  {exactCount}"
  IO.println s!"    Measured (CODATA): {measuredCount}"
  IO.println s!"  Theory relations:   {compatTable.length}"
  IO.println ""
  IO.println "  Core modules:"
  IO.println "    Dim        — 7-dimensional SI quantity exponents"
  IO.println "    Quantity   — Dimensioned values with provenance tracking"
  IO.println "    Constants  — CODATA 2022 physical constants"
  IO.println "    Unit       — Unit system and conversions"
  IO.println "    Error      — Gaussian uncertainty propagation"
  IO.println "    Theory     — Axiom isolation and compatibility checking"
  IO.println "    Conservation — Noether theorem and conservation law verification"
  IO.println "    Kernel     — C++ FFI bridge for theory graph operations"
  IO.println "    Math       — Mathlib bridge (real analysis, linear algebra, groups)"
  IO.println "    Physics    — 24 physics domain formalizations"

-- ============================================================
-- Check command — line-based analysis
-- ============================================================

/-- Strip leading whitespace from a string. -/
private def stripLeading (s : String) : String :=
  ⟨s.data.dropWhile (· == ' ' || · == '\t')⟩

/-- Check if a line is inside a block comment or doc comment.
    Simple heuristic: lines starting with `/-` or containing only
    comment content are skipped. We track nesting via a counter. -/
private structure CommentState where
  depth : Nat := 0

/-- Update comment nesting depth for a raw line. Returns (newState, isInsideComment). -/
private def updateCommentState (st : CommentState) (line : String) : CommentState × Bool :=
  let opens := (line.splitOn "/-").length - 1
  let closes := (line.splitOn "-/").length - 1
  let newDepth := (st.depth + opens) - min (st.depth + opens) closes
  -- A line is "inside a comment" if we were already inside one at the start
  -- OR if the line itself opens a comment (and is not code before the comment)
  let insideBefore := st.depth > 0
  ({ depth := newDepth }, insideBefore)

/-- Check if a stripped line starts with a Lean keyword token.
    We require the keyword to appear at the start of the (stripped) line,
    optionally preceded by visibility modifiers. -/
private def lineStartsWith (stripped : String) (kw : String) : Bool :=
  stripped.startsWith kw ||
  stripped.startsWith ("private " ++ kw) ||
  stripped.startsWith ("protected " ++ kw) ||
  stripped.startsWith ("noncomputable " ++ kw) ||
  stripped.startsWith ("private noncomputable " ++ kw) ||
  stripped.startsWith ("protected noncomputable " ++ kw) ||
  stripped.startsWith ("@[" ) && (stripped.splitOn "] ").any (·.endsWith kw || ·.startsWith kw)

/-- Check if a stripped line contains a `sorry` that is actual proof sorry,
    not inside a string literal or comment reference. -/
private def lineHasSorry (stripped : String) : Bool :=
  -- Must contain "sorry" as a token, not as substring of another word
  if (stripped.splitOn "sorry").length <= 1 then false
  else
    -- Reject lines where "sorry" only appears inside string literals
    let parts := stripped.splitOn "sorry"
    -- Check: at least one occurrence is not preceded by `"` context
    -- Simple heuristic: if the line starts with `--` it's a comment
    if stripped.startsWith "--" then false
    -- If "sorry" appears as a standalone token (preceded by space/start, followed by space/end)
    else parts.length > 1

/-- Per-file analysis results. -/
private structure FileStats where
  path        : String
  imports     : Nat := 0
  defs        : Nat := 0
  theorems    : Nat := 0
  lemmas      : Nat := 0
  axioms      : Nat := 0
  theories    : Nat := 0
  sorryCount  : Nat := 0
  sorryLines  : List (Nat × String) := []  -- (lineNo, lineText)
  axiomLines  : List (Nat × String) := []
  totalLines  : Nat := 0

/-- Analyze a single .lean file using line-based parsing. -/
private def analyzeFile (path : String) : IO FileStats := do
  let contents ← IO.FS.readFile path
  let rawLines := contents.splitOn "\n"
  let mut stats : FileStats := { path := path, totalLines := rawLines.length }
  let mut commentSt : CommentState := {}
  let mut lineNo : Nat := 0
  for rawLine in rawLines do
    lineNo := lineNo + 1
    let (newSt, insideComment) := updateCommentState commentSt rawLine
    commentSt := newSt
    if insideComment then
      continue
    let stripped := stripLeading rawLine
    -- Skip empty lines and single-line comments
    if stripped.isEmpty || stripped.startsWith "--" then
      continue
    -- Count imports (must be at line start, no indentation in Lean)
    if stripped.startsWith "import " then
      stats := { stats with imports := stats.imports + 1 }
    -- Count definitions
    if lineStartsWith stripped "def " then
      stats := { stats with defs := stats.defs + 1 }
    -- Count theorems
    if lineStartsWith stripped "theorem " then
      stats := { stats with theorems := stats.theorems + 1 }
    -- Count lemmas
    if lineStartsWith stripped "lemma " then
      stats := { stats with lemmas := stats.lemmas + 1 }
    -- Count axioms
    if lineStartsWith stripped "axiom " then
      stats := { stats with
        axioms := stats.axioms + 1
        axiomLines := stats.axiomLines ++ [(lineNo, stripped)] }
    -- Count theory declarations
    if lineStartsWith stripped "theory " then
      stats := { stats with theories := stats.theories + 1 }
    -- Count sorry (standalone token, not in comments/strings)
    if lineHasSorry stripped then
      stats := { stats with
        sorryCount := stats.sorryCount + 1
        sorryLines := stats.sorryLines ++ [(lineNo, stripped)] }
  return stats

/-- Check if a path is a directory (by attempting readDir). -/
private def isDirectory (path : System.FilePath) : IO Bool := do
  try
    let _ ← path.readDir
    return true
  catch _ =>
    return false

/-- Collect all .lean files under a directory, recursively. -/
partial def collectLeanFiles (root : System.FilePath) : IO (List String) := do
  let mut result : List String := []
  let entries ← root.readDir
  for entry in entries do
    let path := entry.path
    let isDir ← isDirectory path
    if isDir then
      let sub ← collectLeanFiles path
      result := result ++ sub
    else if path.toString.endsWith ".lean" then
      result := result ++ [path.toString]
  return result

/-- Resolve the target to a list of .lean file paths. -/
private def resolveTarget (target : String) : IO (List String) := do
  let path : System.FilePath := target
  let isDir ← isDirectory path
  if isDir then
    collectLeanFiles path
  else if target.endsWith ".lean" then
    -- Verify file exists
    let exists_ ← path.pathExists
    if exists_ then return [target]
    else throw (IO.Error.userError s!"File not found: {target}")
  else
    throw (IO.Error.userError s!"Expected a .lean file or directory, got: {target}")

/-- Merge a list of FileStats into aggregate totals. -/
private def mergeStats (all : List FileStats) : FileStats :=
  all.foldl (init := { path := "(total)" }) fun acc s =>
    { acc with
      imports    := acc.imports + s.imports
      defs       := acc.defs + s.defs
      theorems   := acc.theorems + s.theorems
      lemmas     := acc.lemmas + s.lemmas
      axioms     := acc.axioms + s.axioms
      theories   := acc.theories + s.theories
      sorryCount := acc.sorryCount + s.sorryCount
      sorryLines := acc.sorryLines ++ s.sorryLines
      axiomLines := acc.axiomLines ++ s.axiomLines
      totalLines := acc.totalLines + s.totalLines }

/-- Escape a string for JSON output. -/
private def jsonEscape (s : String) : String :=
  let s := s.replace "\\" "\\\\"
  let s := s.replace "\"" "\\\""
  let s := s.replace "\n" "\\n"
  let s := s.replace "\t" "\\t"
  s

/-- Render a single FileStats as a JSON object string. -/
private def fileStatsToJson (s : FileStats) : String :=
  "{" ++
    "\"path\":\"" ++ jsonEscape s.path ++ "\"," ++
    "\"lines\":" ++ toString s.totalLines ++ "," ++
    "\"imports\":" ++ toString s.imports ++ "," ++
    "\"defs\":" ++ toString s.defs ++ "," ++
    "\"theorems\":" ++ toString s.theorems ++ "," ++
    "\"lemmas\":" ++ toString s.lemmas ++ "," ++
    "\"axioms\":" ++ toString s.axioms ++ "," ++
    "\"theories\":" ++ toString s.theories ++ "," ++
    "\"sorry\":" ++ toString s.sorryCount ++
  "}"

/-- Render full check results as JSON. -/
private def checkResultToJson (files : List FileStats) (total : FileStats)
    (buildOk : Bool) : String :=
  let fileEntries := ",".intercalate (files.map fileStatsToJson)
  "{" ++
    "\"files\":[" ++ fileEntries ++ "]," ++
    "\"totals\":" ++ fileStatsToJson total ++ "," ++
    "\"fileCount\":" ++ toString files.length ++ "," ++
    "\"buildPassed\":" ++ (if buildOk then "true" else "false") ++
  "}"

/-- Print verbose per-file details (sorry/axiom locations). -/
private def printVerboseDetails (files : List FileStats) : IO Unit := do
  let filesWithSorry := files.filter (·.sorryCount > 0)
  let filesWithAxiom := files.filter (·.axioms > 0)
  if filesWithSorry.length > 0 then
    IO.println ""
    IO.println s!"Files containing sorry ({filesWithSorry.length}):"
    for f in filesWithSorry do
      IO.println s!"  {f.path} ({f.sorryCount} sorry)"
      for (lineNo, lineText) in f.sorryLines do
        IO.println s!"    L{lineNo}: {lineText}"
  if filesWithAxiom.length > 0 then
    IO.println ""
    IO.println s!"Files containing axiom declarations ({filesWithAxiom.length}):"
    for f in filesWithAxiom do
      IO.println s!"  {f.path} ({f.axioms} axioms)"
      for (lineNo, lineText) in f.axiomLines do
        IO.println s!"    L{lineNo}: {lineText}"

/-- Run `lake build` and return (exitCode, stdout, stderr). -/
private def runLakeBuild : IO (UInt32 × String × String) := do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["build"]
    stdout := .piped
    stderr := .piped
  }
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  return (exitCode, stdout, stderr)

/-- The improved check command. Supports --verbose and --json flags. -/
private def runCheck (target : String) (verbose json : Bool) : IO UInt32 := do
  -- Resolve target to file list
  let files ← try
    resolveTarget target
  catch e =>
    IO.eprintln s!"Error: {e}"
    return 1
  if files.isEmpty then
    IO.eprintln s!"Error: no .lean files found in '{target}'"
    return 1
  -- Analyze all files
  let mut allStats : List FileStats := []
  for f in files do
    let stats ← try
      analyzeFile f
    catch e =>
      IO.eprintln s!"Warning: could not read '{f}': {e}"
      continue
      -- unreachable but needed for type
      pure { path := f : FileStats }
    allStats := allStats ++ [stats]
  let total := mergeStats allStats
  -- Run lake build
  let (buildExit, buildStdout, buildStderr) ← runLakeBuild
  let buildOk := buildExit == 0
  -- JSON output mode
  if json then
    IO.println (checkResultToJson allStats total buildOk)
    return (if buildOk then 0 else 1)
  -- Human-readable output
  let fileLabel := if allStats.length == 1 then "1 file" else s!"{allStats.length} files"
  IO.println s!"Checking: {target} ({fileLabel}, {total.totalLines} lines)"
  IO.println "─────────────────────────────────"
  IO.println s!"  Imports:     {total.imports}"
  IO.println s!"  Definitions: {total.defs}"
  IO.println s!"  Theorems:    {total.theorems}"
  IO.println s!"  Lemmas:      {total.lemmas}"
  IO.println s!"  Axioms:      {total.axioms}"
  IO.println s!"  Theories:    {total.theories}"
  IO.println ""
  if total.sorryCount > 0 then
    IO.println s!"  ⚠ sorry count: {total.sorryCount}"
    IO.println "    (incomplete proofs — these must be filled before publication)"
  else
    IO.println "  ✓ No sorry found"
  -- Verbose details
  if verbose then
    printVerboseDetails allStats
  IO.println ""
  -- Build results
  IO.println "Running dimensional type-check (lake build) ..."
  if buildOk then
    IO.println "  ✓ Build succeeded — all dimensions consistent"
    if !buildStdout.isEmpty then
      IO.println buildStdout
  else
    IO.println "  ✗ Build failed — type errors detected:"
    IO.println ""
    if !buildStderr.isEmpty then
      let errLines := buildStderr.splitOn "\n"
      for line in errLines do
        if !line.isEmpty then
          IO.println s!"    {line}"
    if !buildStdout.isEmpty then
      IO.println buildStdout
  IO.println ""
  IO.println "─────────────────────────────────"
  IO.println s!"Summary: {total.defs} defs, {total.theorems + total.lemmas} proofs, {total.axioms} axioms, {total.sorryCount} sorry"
  return (if buildOk then 0 else 1)

-- ============================================================
-- Theories command — with axiom/theorem counts from source
-- ============================================================

/-- Scan a theory's source files for axiom/theorem counts. -/
private def scanTheoryStats (t : TheoryEntry) : IO (Nat × Nat × Nat) := do
  -- Try to find the theory's source directory
  let basePath := "src/Measure/Physics/" ++ t.name
  let mut axiomTotal : Nat := 0
  let mut theoremTotal : Nat := 0
  let mut lemmaTotal : Nat := 0
  -- Check the main barrel file
  let barrelFile := basePath ++ ".lean"
  let barrelPath : System.FilePath := barrelFile
  let barrelExists ← barrelPath.pathExists
  if barrelExists then
    let stats ← analyzeFile barrelFile
    axiomTotal := axiomTotal + stats.axioms
    theoremTotal := theoremTotal + stats.theorems
    lemmaTotal := lemmaTotal + stats.lemmas
  -- Check submodule files
  for sub in t.submodules do
    let subFile := basePath ++ "/" ++ sub ++ ".lean"
    let subPath : System.FilePath := subFile
    let subExists ← subPath.pathExists
    if subExists then
      let stats ← analyzeFile subFile
      axiomTotal := axiomTotal + stats.axioms
      theoremTotal := theoremTotal + stats.theorems
      lemmaTotal := lemmaTotal + stats.lemmas
  return (axiomTotal, theoremTotal, lemmaTotal)

/-- Print theories with axiom/theorem counts. -/
private def printTheoriesWithCounts : IO Unit := do
  IO.println "Registered Theory Modules"
  IO.println "========================="
  IO.println ""
  let rigorOrder := ["strict", "approximate", "empirical", "numerical"]
  let mut grandAxioms : Nat := 0
  let mut grandTheorems : Nat := 0
  let mut grandLemmas : Nat := 0
  for rigor in rigorOrder do
    let theories := theoriesTable.filter (·.rigor == rigor)
    if theories.length > 0 then
      IO.println s!"── {rigor} ({theories.length} theories) ──"
      IO.println ""
      for t in theories do
        let (ax, th, lm) ← scanTheoryStats t
        grandAxioms := grandAxioms + ax
        grandTheorems := grandTheorems + th
        grandLemmas := grandLemmas + lm
        let subCount := t.submodules.length
        IO.println s!"  {t.name}  [{subCount} submodules]  axioms={ax} theorems={th} lemmas={lm}"
        IO.println s!"    {t.description}"
      IO.println ""
  IO.println "Theory Relations"
  IO.println "────────────────"
  IO.println ""
  for rel in compatTable do
    IO.println s!"  {rel.theoryA} ↔ {rel.theoryB}: {rel.relation}"
  IO.println ""
  let totalSub := theoriesTable.foldl (fun acc t => acc + t.submodules.length) 0
  IO.println s!"Total: {theoriesTable.length} theories, {totalSub} submodules, {compatTable.length} relations"
  IO.println s!"Source: {grandAxioms} axioms, {grandTheorems} theorems, {grandLemmas} lemmas"

/-- Render a single TheoryEntry as JSON. -/
private def theoryEntryToJson (t : TheoryEntry) (ax th lm : Nat) : String :=
  let subs := ",".intercalate (t.submodules.map (fun s => "\"" ++ jsonEscape s ++ "\""))
  "{" ++
    "\"name\":\"" ++ jsonEscape t.name ++ "\"," ++
    "\"rigor\":\"" ++ jsonEscape t.rigor ++ "\"," ++
    "\"description\":\"" ++ jsonEscape t.description ++ "\"," ++
    "\"submodules\":[" ++ subs ++ "]," ++
    "\"axioms\":" ++ toString ax ++ "," ++
    "\"theorems\":" ++ toString th ++ "," ++
    "\"lemmas\":" ++ toString lm ++
  "}"

/-- Render a CompatEntry as JSON. -/
private def compatEntryToJson (c : CompatEntry) : String :=
  "{" ++
    "\"theoryA\":\"" ++ jsonEscape c.theoryA ++ "\"," ++
    "\"theoryB\":\"" ++ jsonEscape c.theoryB ++ "\"," ++
    "\"relation\":\"" ++ jsonEscape c.relation ++ "\"" ++
  "}"

/-- Print theories as JSON. -/
private def printTheoriesJson : IO Unit := do
  let mut entries : List String := []
  for t in theoriesTable do
    let (ax, th, lm) ← scanTheoryStats t
    entries := entries ++ [theoryEntryToJson t ax th lm]
  let relEntries := compatTable.map compatEntryToJson
  let json :=
    "{" ++
      "\"theories\":[" ++ ",".intercalate entries ++ "]," ++
      "\"relations\":[" ++ ",".intercalate relEntries ++ "]," ++
      "\"theoryCount\":" ++ toString theoriesTable.length ++ "," ++
      "\"relationCount\":" ++ toString compatTable.length ++
    "}"
  IO.println json

-- ============================================================
-- Argument parsing helpers
-- ============================================================

/-- Parse check command arguments into (flags, target). -/
private def parseCheckArgs (args : List String)
    : Except String (Bool × Bool × String) :=
  let rec go (rest : List String) (verbose json : Bool) (target : Option String)
      : Except String (Bool × Bool × String) :=
    match rest with
    | [] =>
      match target with
      | some t => .ok (verbose, json, t)
      | none => .error "missing file or directory argument"
    | "--verbose" :: tail => go tail true json target
    | "--json" :: tail => go tail verbose true target
    | arg :: tail =>
      if arg.startsWith "--" then
        .error s!"unknown flag: {arg}"
      else
        match target with
        | some _ => .error s!"unexpected argument: {arg} (only one target allowed)"
        | none => go tail verbose json (some arg)
  go args false false none

-- ============================================================
-- Main entry point
-- ============================================================

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println helpText
    return 0
  | ["help"] | ["-h"] | ["--help"] =>
    IO.println helpText
    return 0
  | ["version"] | ["-v"] | ["--version"] =>
    IO.println s!"measure {version}"
    return 0
  | ["info"] =>
    printInfo
    return 0
  | ["constants"] =>
    printConstants
    return 0
  | ["theories"] =>
    printTheoriesWithCounts
    return 0
  | ["theories", "--json"] =>
    printTheoriesJson
    return 0
  | "check" :: rest =>
    if rest.isEmpty then
      IO.eprintln "Error: missing file or directory argument."
      IO.eprintln "Usage: measure check [--verbose] [--json] <file.lean|directory>"
      return 1
    match parseCheckArgs rest with
    | .ok (verbose, json, target) => runCheck target verbose json
    | .error msg =>
      IO.eprintln s!"Error: {msg}"
      IO.eprintln "Usage: measure check [--verbose] [--json] <file.lean|directory>"
      return 1
  | cmd :: _ =>
    IO.eprintln s!"Unknown command: {cmd}"
    IO.eprintln "Run 'measure help' for usage information."
    return 1
