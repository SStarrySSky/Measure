/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Physics-aware code actions for the Measure LSP server.
See docs/syntax-and-integration.md Section 6.4.
-/
import Measure.LSP.Diagnostics
import Measure.LSP.DimHints

namespace Measure.LSP

/-- A text edit to apply as part of a code action. -/
structure TextEdit where
  range   : Range
  newText : String
  deriving Repr, Inhabited

/-- A code action suggested by the Measure LSP server. -/
structure MeasureCodeAction where
  title       : String
  diagnostic  : DiagnosticCode
  edits       : List TextEdit := []
  isPreferred : Bool := false
  deriving Repr, Inhabited

/-- Type alias for a code action provider function.
    Given a diagnostic code and range, returns a list of code actions. -/
def CodeActionProvider := DiagnosticCode → Range → List MeasureCodeAction

/-- Mutable registry of code action providers.
    Plugins register providers via `CodeActionRegistry.register`. -/
structure CodeActionRegistry where
  providers : List (String × CodeActionProvider) := []
  deriving Inhabited

namespace CodeActionRegistry

/-- Register a named code action provider. -/
def register (reg : CodeActionRegistry) (name : String)
    (provider : CodeActionProvider) : CodeActionRegistry :=
  { providers := reg.providers ++ [(name, provider)] }

/-- Remove a registered provider by name. -/
def unregister (reg : CodeActionRegistry) (name : String) : CodeActionRegistry :=
  { providers := reg.providers.filter fun (n, _) => n != name }

/-- Query all registered providers for a given diagnostic. -/
def query (reg : CodeActionRegistry) (code : DiagnosticCode)
    (range : Range) : List MeasureCodeAction :=
  reg.providers.foldl (fun acc (_, provider) =>
    acc ++ provider code range) []

end CodeActionRegistry

namespace CodeActions

/-- Generate code action for MSR001: dimensional mismatch.
    Suggests multiplying by the missing dimensional factor. -/
def fixDimMismatch (range : Range) (missingDim : String) : MeasureCodeAction :=
  { title := s!"Multiply by missing factor ({missingDim})"
    diagnostic := .dimMismatch
    edits := [{ range := range, newText := s!" * {missingDim}" }] }

/-- Generate code action for MSR002: theory conflict.
    Suggests inserting an approximate bridge. -/
def bridgeTheoryConflict (range : Range)
    (theoryA theoryB param bound : String) : MeasureCodeAction :=
  { title := s!"Bridge via approximation ({theoryA} -> {theoryB})"
    diagnostic := .theoryConflict
    edits := [{
      range := range
      newText := s!"approximate {theoryA} where ({param} < {bound})\n"
    }] }

/-- Generate code action for MSR003: conservation violation.
    Suggests adding the missing term. -/
def fixConservationViolation (range : Range)
    (missingTerm : String) : MeasureCodeAction :=
  { title := s!"Add missing term: {missingTerm}"
    diagnostic := .conservationViolation
    edits := [{ range := range, newText := s!" + {missingTerm}" }] }

/-- Generate code action for MSR004: rigor downgrade.
    Suggests changing rigor attribute. -/
def downgradeRigor (range : Range) : MeasureCodeAction :=
  { title := "Downgrade to @[rigor approximate]"
    diagnostic := .rigorDowngrade
    edits := [{ range := range, newText := "@[rigor approximate]" }] }

/-- Generate code action for MSR005: uncertainty overflow.
    Suggests switching to Affine model. -/
def switchToAffine (range : Range) : MeasureCodeAction :=
  { title := "Switch to Affine uncertainty model"
    diagnostic := .uncertaintyOverflow
    edits := [{ range := range, newText := "@[uncertainty Affine]" }] }

/-- Generate code action for MSR008: implicit unit conversion.
    Suggests inserting an explicit unit conversion call. -/
def insertUnitConversion (range : Range)
    (fromUnit toUnit : String) : MeasureCodeAction :=
  { title := s!"Insert explicit conversion ({fromUnit} -> {toUnit})"
    diagnostic := .unitConversion
    edits := [{
      range := range
      newText := s!"convert({fromUnit}, {toUnit})"
    }] }

/-- Generate code action for MSR009: simplifiable expression.
    Suggests replacing with the simplified form. -/
def simplifyExpression (range : Range)
    (simplified : String) : MeasureCodeAction :=
  { title := s!"Simplify to: {simplified}"
    diagnostic := .simplification
    edits := [{ range := range, newText := simplified }]
    isPreferred := true }

/-- Generate code action for MSR010: unverified external.
    Generates a verify block template.
    INTENTIONAL: TODO in the template is a user-facing placeholder, not a code TODO. -/
def addVerifyBlock (range : Range) (varName : String) : MeasureCodeAction :=
  { title := s!"Add verify block for '{varName}'"
    diagnostic := .unverifiedExternal
    edits := [{
      range := range
      newText := s!"\nverify {varName} where\n  dim_check := {varName}.dim == TODO\n  bounds    := |{varName}| < TODO\n"
    }] }

/-- Select appropriate code actions for a given diagnostic.
    Also queries the plugin registry for additional actions. -/
def forDiagnostic (code : DiagnosticCode) (range : Range)
    (registry : CodeActionRegistry := {}) : List MeasureCodeAction :=
  let builtIn := match code with
  | .dimMismatch          => [fixDimMismatch range "L"]
  | .theoryConflict       => [bridgeTheoryConflict range "Theory" "Target" "v/c" "0.01"]
  | .conservationViolation => [fixConservationViolation range "Q_dissipated"]
  | .rigorDowngrade       => [downgradeRigor range]
  | .uncertaintyOverflow  => [switchToAffine range]
  | .unitConversion       => [insertUnitConversion range "SI" "CGS"]
  | .simplification       => [simplifyExpression range "simplified_expr"]
  | .unverifiedExternal   => [addVerifyBlock range "result"]
  | _                     => []
  builtIn ++ registry.query code range

end CodeActions

end Measure.LSP
