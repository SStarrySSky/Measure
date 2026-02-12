/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Measure.Conservation.Law
import Measure.Theory.Module

/-! # Noether's Theorem: Symmetry → Conservation

Automatic derivation of conservation laws from symmetry declarations.
Each continuous symmetry generates a conserved quantity.
-/

namespace Measure.Conservation

open Measure.Theory

/-- Derive a conservation law from a symmetry declaration via Noether's theorem. -/
def deriveFromNoether (sym : SymmetryDecl) : ConservationLaw :=
  let (name, expr) := match sym.group with
    | .translation true  => ("energy", "total_energy")
    | .translation false => ("momentum", "total_momentum")
    | .rotation _        => ("angularMomentum", "total_angular_momentum")
    | .gauge groupName   => (s!"{groupName}_charge", s!"total_{groupName}_charge")
    | .lorentz           => ("lorentzInvariant", "lorentz_invariant")
    | .poincare          => ("poincareInvariant", "poincare_invariant")
    | .custom n          => (sym.conservedQtyName, s!"{n}_conserved")
  let exactness := match sym.exactness with
    | .exact => ConservationExactness.exact
    | .approximate scale =>
        .approximate s!"O({scale})"
    | .anomalous anomaly =>
        .anomalouslyBroken anomaly
  { name := name
    quantityExpr := expr
    source := .noether sym
    exactness := exactness }

/-- Derive all conservation laws from a theory's symmetry declarations. -/
def deriveAllFromNoether (mod : TheoryModule) : List ConservationLaw :=
  mod.symmetries.map deriveFromNoether

end Measure.Conservation
