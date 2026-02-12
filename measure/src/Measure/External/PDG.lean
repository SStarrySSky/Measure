/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

PDG (Particle Data Group) connector skeleton.
Provides particle properties: masses, widths, branching ratios, coupling constants.
See ARCHITECTURE.md Section 8.2.
-/
import Measure.External.DataSource

namespace Measure.External

open Measure.Dim
open Measure.Quantity

/-- PDG 2024 bundled snapshot version. -/
def pdgVersion : DataVersion :=
  { name := "PDG", year := 2024, edition := some "RPP" }

/-- A single PDG particle property entry. -/
private structure PDGEntry where
  particle : String
  property : String
  value    : Float
  uncertainty : Float
  dim      : Dim
  deriving Repr, Inhabited

/-- Energy dimension for mass in natural units (MeV/c^2 stored as Energy). -/
private def massDim : Dim := Energy

/-- Bundled PDG 2024 particle data (representative subset). -/
private def pdgEntries : List PDGEntry := [
  -- Leptons
  { particle := "electron", property := "mass"
    value := 0.51099895, uncertainty := 0.00000015, dim := massDim },
  { particle := "muon", property := "mass"
    value := 105.6583755, uncertainty := 0.0000023, dim := massDim },
  { particle := "tau", property := "mass"
    value := 1776.86, uncertainty := 0.12, dim := massDim },
  -- Quarks
  { particle := "up_quark", property := "mass"
    value := 2.16, uncertainty := 0.49, dim := massDim },
  { particle := "down_quark", property := "mass"
    value := 4.67, uncertainty := 0.48, dim := massDim },
  { particle := "strange_quark", property := "mass"
    value := 93.4, uncertainty := 8.6, dim := massDim },
  { particle := "charm_quark", property := "mass"
    value := 1270.0, uncertainty := 20.0, dim := massDim },
  { particle := "bottom_quark", property := "mass"
    value := 4180.0, uncertainty := 30.0, dim := massDim },
  { particle := "top_quark", property := "mass"
    value := 172760.0, uncertainty := 300.0, dim := massDim },
  -- Gauge bosons
  { particle := "W_boson", property := "mass"
    value := 80369.0, uncertainty := 13.0, dim := massDim },
  { particle := "W_boson", property := "total_width"
    value := 2085.0, uncertainty := 42.0, dim := massDim },
  { particle := "Z_boson", property := "mass"
    value := 91187.6, uncertainty := 2.1, dim := massDim },
  { particle := "Z_boson", property := "total_width"
    value := 2495.2, uncertainty := 2.3, dim := massDim },
  -- Higgs
  { particle := "higgs", property := "mass"
    value := 125250.0, uncertainty := 170.0, dim := massDim },
  -- Hadrons
  { particle := "proton", property := "mass"
    value := 938.27208816, uncertainty := 0.00000029, dim := massDim },
  { particle := "neutron", property := "mass"
    value := 939.56542052, uncertainty := 0.00000054, dim := massDim },
  { particle := "pion_charged", property := "mass"
    value := 139.57039, uncertainty := 0.00018, dim := massDim },
  { particle := "pion_neutral", property := "mass"
    value := 134.9768, uncertainty := 0.0005, dim := massDim }
]

/-- PDG data source state. -/
structure PDGSource where
  version : DataVersion := pdgVersion
  deriving Repr, Inhabited

private def lookupPDGEntry (particle property : String) : Option PDGEntry :=
  pdgEntries.find? fun e => e.particle == particle && e.property == property

private def pdgEntryToDatum (e : PDGEntry) (ver : DataVersion) : Datum :=
  { value := e.value
    uncertainty := e.uncertainty
    dim := e.dim
    isExact := false
    source := "PDG"
    version := ver }

/-- Compound key: "particle.property" -/
private def parseCompoundKey (key : String) : Option (String × String) :=
  match key.splitOn "." with
  | [p, prop] => some (p, prop)
  | _ => none

instance : DataSource PDGSource where
  name _ := "PDG (Particle Data Group)"
  bundledVersion s := s.version
  get src key :=
    match parseCompoundKey key with
    | some (particle, property) =>
      match lookupPDGEntry particle property with
      | some e => .ok (pdgEntryToDatum e src.version) src.version
      | none   => .notFound key
    | none => .notFound key
  getVersioned src key ver :=
    if ver == src.version then
      match parseCompoundKey key with
      | some (particle, property) =>
        match lookupPDGEntry particle property with
        | some e => .ok (pdgEntryToDatum e src.version) src.version
        | none   => .notFound key
      | none => .notFound key
    else
      .versionMismatch ver src.version
  keys _ := pdgEntries.map fun e => s!"{e.particle}.{e.property}"

/-- Default PDG source instance. -/
def PDG : PDGSource := {}

namespace PDG

/-- Look up a particle property: PDG.get "electron" "mass" -/
def get (particle property : String) : DataResult Datum :=
  DataSource.get (σ := PDGSource) PDG s!"{particle}.{property}"

end PDG

end Measure.External
