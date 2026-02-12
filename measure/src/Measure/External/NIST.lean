/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

NIST/CODATA connector: bundled snapshot of fundamental physical constants.
CODATA 2022 recommended values.
See ARCHITECTURE.md Section 8.2.
-/
import Measure.External.DataSource

namespace Measure.External

open Measure.Dim
open Measure.Quantity

/-- A single CODATA constant entry. -/
private structure CODATAEntry where
  key         : String
  value       : Float
  uncertainty : Float
  dim         : Dim
  isExact     : Bool
  description : String
  deriving Repr, Inhabited

/-- CODATA 2022 bundled snapshot version. -/
def codataVersion : DataVersion :=
  { name := "CODATA", year := 2022, edition := some "recommended" }

/-- Bundled CODATA 2022 constants.
    After 2019 SI redefinition, c, h, e, k_B, N_A are exact by definition. -/
private def codataEntries : List CODATAEntry := [
  -- Exact constants (2019 SI redefinition)
  { key := "speed_of_light"
    value := 299792458.0
    uncertainty := 0.0
    dim := Velocity
    isExact := true
    description := "Speed of light in vacuum" },
  { key := "planck_constant"
    value := 6.62607015e-34
    uncertainty := 0.0
    dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-1) 1 }
    isExact := true
    description := "Planck constant" },
  { key := "elementary_charge"
    value := 1.602176634e-19
    uncertainty := 0.0
    dim := Charge
    isExact := true
    description := "Elementary charge" },
  { key := "boltzmann_constant"
    value := 1.380649e-23
    uncertainty := 0.0
    dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1, Θ := QExp.mk' (-1) 1 }
    isExact := true
    description := "Boltzmann constant" },
  { key := "avogadro_constant"
    value := 6.02214076e23
    uncertainty := 0.0
    dim := { N := QExp.mk' (-1) 1 }
    isExact := true
    description := "Avogadro constant" },
  -- Measured constants (CODATA 2022)
  { key := "gravitational_constant"
    value := 6.67430e-11
    uncertainty := 1.5e-15
    dim := { L := QExp.mk' 3 1, M := QExp.mk' (-1) 1, T := QExp.mk' (-2) 1 }
    isExact := false
    description := "Newtonian constant of gravitation" },
  { key := "fine_structure_constant"
    value := 7.2973525693e-3
    uncertainty := 1.1e-12
    dim := Dim.dimensionless
    isExact := false
    description := "Fine-structure constant" },
  { key := "electron_mass"
    value := 9.1093837015e-31
    uncertainty := 2.8e-40
    dim := { M := QExp.one }
    isExact := false
    description := "Electron mass" },
  { key := "proton_mass"
    value := 1.67262192369e-27
    uncertainty := 5.1e-37
    dim := { M := QExp.one }
    isExact := false
    description := "Proton mass" },
  { key := "vacuum_permittivity"
    value := 8.8541878128e-12
    uncertainty := 1.3e-21
    dim := { L := QExp.mk' (-3) 1, M := QExp.mk' (-1) 1, T := QExp.mk' 4 1, I := QExp.mk' 2 1 }
    isExact := false
    description := "Vacuum electric permittivity" },
  { key := "vacuum_permeability"
    value := 1.25663706212e-6
    uncertainty := 1.9e-16
    dim := { L := QExp.one, M := QExp.one, T := QExp.mk' (-2) 1, I := QExp.mk' (-2) 1 }
    isExact := false
    description := "Vacuum magnetic permeability" },
  { key := "gravity"
    value := 9.80665
    uncertainty := 0.00001
    dim := Acceleration
    isExact := false
    description := "Standard acceleration of gravity" },
  { key := "reduced_planck_constant"
    value := 1.054571817e-34
    uncertainty := 0.0
    dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-1) 1 }
    isExact := true
    description := "Reduced Planck constant (h-bar)" }
]

/-- NIST data source state (stateless for bundled snapshot). -/
structure NISTSource where
  version : DataVersion := codataVersion
  deriving Repr, Inhabited

private def lookupEntry (key : String) : Option CODATAEntry :=
  codataEntries.find? (·.key == key)

private def entryToDatum (e : CODATAEntry) (ver : DataVersion) : Datum :=
  { value := e.value
    uncertainty := e.uncertainty
    dim := e.dim
    isExact := e.isExact
    source := "NIST/CODATA"
    version := ver }

instance : DataSource NISTSource where
  name _ := "NIST/CODATA"
  bundledVersion s := s.version
  get src key :=
    match lookupEntry key with
    | some e => .ok (entryToDatum e src.version) src.version
    | none   => .notFound key
  getVersioned src key ver :=
    if ver == src.version then
      match lookupEntry key with
      | some e => .ok (entryToDatum e ver) ver
      | none   => .notFound key
    else
      .versionMismatch ver src.version
  keys _ := codataEntries.map (·.key)

/-- Default NIST source instance. -/
def NIST : NISTSource := {}

namespace NIST

/-- Convenience: look up a NIST constant by key. -/
def get (key : String) : DataResult Datum :=
  DataSource.get (σ := NISTSource) NIST key

end NIST

end Measure.External
