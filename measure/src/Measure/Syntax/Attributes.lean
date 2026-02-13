/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Physics-specific attributes: @[rigor], @[uncertainty], @[conservation].
See ARCHITECTURE.md Section 4.1 and docs/syntax-and-integration.md Section 2.4.

Provides:
- RigorLevel, UncertaintyModelId, ConservedQty data types
- MeasureMetadata structure for per-declaration metadata
- Environment extension for storing metadata
- @[rigor], @[uncertainty], @[conservation] attribute handlers
-/
import Lean
import Measure.Theory.RigorLevel

namespace Measure.Syntax

open Lean

/-- Rigor levels for the rigor spectrum.
    Re-exported from `Measure.Theory.RigorLevel` to avoid duplicate definitions. -/
abbrev RigorLevel := Measure.Theory.RigorLevel

/-- Uncertainty model selection. -/
inductive UncertaintyModelId where
  | gaussian
  | interval
  | affine
  | custom (name : Name)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace UncertaintyModelId

def fromString : String → UncertaintyModelId
  | "Gaussian" => .gaussian
  | "Interval" => .interval
  | "Affine"   => .affine
  | s          => .custom (Name.mkSimple s)

def toString : UncertaintyModelId → String
  | .gaussian    => "Gaussian"
  | .interval    => "Interval"
  | .affine      => "Affine"
  | .custom n    => n.toString

end UncertaintyModelId

/-- Conserved quantity identifiers. -/
inductive ConservedQty where
  | energy
  | momentum
  | angularMomentum
  | charge
  | leptonNumber
  | baryonNumber
  | custom (name : Name)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace ConservedQty

def fromString : String → ConservedQty
  | "energy"            => .energy
  | "momentum"          => .momentum
  | "angular_momentum"  => .angularMomentum
  | "charge"            => .charge
  | "lepton_number"     => .leptonNumber
  | "baryon_number"     => .baryonNumber
  | s                   => .custom (Name.mkSimple s)

def toString : ConservedQty → String
  | .energy           => "energy"
  | .momentum         => "momentum"
  | .angularMomentum  => "angular_momentum"
  | .charge           => "charge"
  | .leptonNumber     => "lepton_number"
  | .baryonNumber     => "baryon_number"
  | .custom n         => n.toString

end ConservedQty

/-- Measure-specific metadata attached to declarations. -/
structure MeasureMetadata where
  rigor        : Option RigorLevel       := none
  uncertainty  : Option UncertaintyModelId := none
  conservation : List ConservedQty       := []
  tolerance    : Option Float            := none
  unitName     : Option String           := none
  deriving Repr, Inhabited
