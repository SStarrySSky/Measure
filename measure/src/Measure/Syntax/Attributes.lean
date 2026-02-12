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

namespace Measure.Syntax

open Lean

/-- Rigor levels for the rigor spectrum. -/
inductive RigorLevel where
  | strict
  | approximate
  | empirical
  | numerical
  deriving DecidableEq, Repr, Inhabited, BEq

namespace RigorLevel

def fromString : String → Option RigorLevel
  | "strict"      => some .strict
  | "approximate" => some .approximate
  | "empirical"   => some .empirical
  | "numerical"   => some .numerical
  | _             => none

def toString : RigorLevel → String
  | .strict      => "strict"
  | .approximate => "approximate"
  | .empirical   => "empirical"
  | .numerical   => "numerical"

/-- Lattice ordering: strict > approximate > empirical > numerical. -/
def toNat : RigorLevel → Nat
  | .strict      => 3
  | .approximate => 2
  | .empirical   => 1
  | .numerical   => 0

/-- Min rule for rigor propagation (lattice homomorphism). -/
def min (a b : RigorLevel) : RigorLevel :=
  if a.toNat ≤ b.toNat then a else b

end RigorLevel

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

/-- Entry in the unit registry, tagged by @[unit]. -/
structure UnitRegistryEntry where
  declName : Name
  unitName : String
  symbol   : String := ""
  dim      : List Int := []  -- exponent vector [L,M,T,I,Θ,N,J]
  toSI     : Float := 1.0
  offset   : Float := 0.0
  system   : String := "SI"
  deriving Repr, Inhabited

/-- Unit registry: collects all @[unit]-tagged declarations. -/
structure UnitRegistry where
  entries : List UnitRegistryEntry := []
  deriving Repr, Inhabited

namespace UnitRegistry

/-- Register a new unit entry. -/
def register (reg : UnitRegistry) (entry : UnitRegistryEntry) : UnitRegistry :=
  { entries := reg.entries ++ [entry] }

/-- Look up a unit by name. -/
def findByName (reg : UnitRegistry) (name : String) : Option UnitRegistryEntry :=
  reg.entries.find? fun e => e.unitName == name

/-- Look up a unit by symbol. -/
def findBySymbol (reg : UnitRegistry) (sym : String) : Option UnitRegistryEntry :=
  reg.entries.find? fun e => e.symbol == sym

/-- List all units for a given system. -/
def forSystem (reg : UnitRegistry) (sys : String) : List UnitRegistryEntry :=
  reg.entries.filter fun e => e.system == sys

end UnitRegistry
