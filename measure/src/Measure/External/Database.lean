/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Live database query layer: NIST CODATA and PDG with HTTP fetch.
Integrates with Cache.lean four-tier caching (memory -> local -> bundled -> miss).
Falls back to hardcoded data (NIST.lean / PDG.lean) when network is unavailable.
See ARCHITECTURE.md Section 8.2.
-/
import Lean.Data.Json
import Measure.External.DataSource
import Measure.External.Cache
import Measure.External.NIST
import Measure.External.PDG

namespace Measure.External

open Lean (Json)
open Measure.Dim
open Measure.Quantity

-- HTTP fetch via curl subprocess.
namespace HttpFetch

def httpGet (url : String) (timeoutSec : Nat := 10)
    : IO (Except String String) := do
  try
    let result ← IO.Process.output {
      cmd := "curl"
      args := #["-s", "-f", "--max-time", toString timeoutSec, url]
    }
    if result.exitCode == 0 then
      return .ok result.stdout
    else
      return .error s!"HTTP error (exit {result.exitCode}): {result.stderr}"
  catch e =>
    return .error (toString e)

end HttpFetch

namespace LiveQuery

/-- NIST CODATA API base URL. -/
private def nistApiUrl : String :=
  "https://physics.nist.gov/cgi-bin/cuu/Value"

/-- PDG API base URL. -/
private def pdgApiUrl : String :=
  "https://pdg.lbl.gov/2024/api"

/-- Extract numeric characters from a string. -/
private def extractNumeric (s : String) : String :=
  String.ofList (s.toList.filter fun c =>
    c.isDigit || c == '.' || c == '-' || c == 'e' || c == 'E' || c == '+')

/-- Parse a NIST plain-text response into a Datum. -/
private def parseNistResponse (raw : String) (_key : String)
    : Option Datum :=
  let lines := raw.splitOn "\n"
  let valueLine := lines.find? fun l => (l.splitOn "Value").length > 1
  match valueLine with
  | none => none
  | some vl =>
    let numStr := extractNumeric (vl.replace " " "")
    match numStr.toNat? with
    | some n => some {
        value := Float.ofNat n
        uncertainty := 0.0
        dim := Dim.dimensionless
        isExact := (raw.splitOn "(exact)").length > 1
        source := "NIST/CODATA-live"
        version := { name := "CODATA", year := 2022, edition := some "live" }
      }
    | none => none

/-- Parse a PDG JSON response into a Datum. -/
private def parsePdgResponse (raw : String) : Option Datum :=
  match Json.parse raw with
  | .error _ => none
  | .ok json =>
    match json.getObjValAs? Float "value" with
    | .error _ => none
    | .ok v =>
      let unc := (json.getObjValAs? Float "uncertainty").toOption.getD 0.0
      some {
        value := v
        uncertainty := unc
        dim := Dim.dimensionless
        isExact := false
        source := "PDG-live"
        version := { name := "PDG", year := 2024, edition := some "live" }
      }

end LiveQuery

namespace DatabaseQuery

/-- Query NIST CODATA using four-tier cache strategy:
    Tier 1 (memory) + Tier 3 (bundled) handled by DataCache.lookup.
    Tier 2 (local/network) handled here via HTTP fetch.
    Tier 4 = miss. -/
def queryNIST (key : String) (cache : DataCache NISTSource)
    : IO (DataResult Datum × DataCache NISTSource) := do
  -- Tier 1 + Tier 3: try DataCache (memory -> bundled)
  let (result, tier, newCache) ← cache.lookup key
  match result, tier with
  | .ok datum ver, .memory =>
    return (.ok datum ver, newCache)
  | .ok datum ver, .bundled =>
    return (.ok datum ver, newCache)
  | _, .miss =>
    -- Tier 2: try live HTTP fetch before giving up
    let url := s!"{LiveQuery.nistApiUrl}?{key.replace "_" ""}|search_for=universal"
    let httpResult ← HttpFetch.httpGet url
    match httpResult with
    | .ok body =>
      match LiveQuery.parseNistResponse body key with
      | some datum =>
        let entry : CachedEntry := { datum, tier := .local_ }
        let updatedCache := { newCache with
          memory := newCache.memory.insert key entry
          stats := newCache.stats.recordHit .local_ }
        return (.ok datum datum.version, updatedCache)
      | none =>
        return (.unavailable s!"NIST parse failed for: {key}", newCache)
    | .error _ =>
      return (.unavailable s!"Network unavailable, key not in bundled: {key}", newCache)
  | other, _ =>
    return (other, newCache)

/-- Query PDG using four-tier cache strategy. -/
def queryPDG (particle property : String) (cache : DataCache PDGSource)
    : IO (DataResult Datum × DataCache PDGSource) := do
  let compoundKey := s!"{particle}.{property}"
  -- Tier 1 + Tier 3: try DataCache (memory -> bundled)
  let (result, tier, newCache) ← cache.lookup compoundKey
  match result, tier with
  | .ok datum ver, .memory =>
    return (.ok datum ver, newCache)
  | .ok datum ver, .bundled =>
    return (.ok datum ver, newCache)
  | _, .miss =>
    -- Tier 2: try live HTTP fetch
    let url := s!"{LiveQuery.pdgApiUrl}/particle/{particle}/{property}"
    let httpResult ← HttpFetch.httpGet url
    match httpResult with
    | .ok body =>
      match LiveQuery.parsePdgResponse body with
      | some datum =>
        let entry : CachedEntry := { datum, tier := .local_ }
        let updatedCache := { newCache with
          memory := newCache.memory.insert compoundKey entry
          stats := newCache.stats.recordHit .local_ }
        return (.ok datum datum.version, updatedCache)
      | none =>
        return (.unavailable s!"PDG parse failed for: {compoundKey}", newCache)
    | .error _ =>
      return (.unavailable s!"Network unavailable, key not in bundled: {compoundKey}", newCache)
  | other, _ =>
    return (other, newCache)

/-- Combined database state holding both NIST and PDG caches. -/
structure DatabaseState where
  nistCache : DataCache NISTSource := { source := NIST }
  pdgCache  : DataCache PDGSource  := { source := PDG }
  deriving Repr, Inhabited

/-- Unified query: routes by key format.
    "electron.mass" -> PDG, "speed_of_light" -> NIST. -/
def query (key : String) (state : DatabaseState)
    : IO (DataResult Datum × DatabaseState) := do
  match key.splitOn "." with
  | [particle, property] =>
    let (result, newPdg) ← queryPDG particle property state.pdgCache
    return (result, { state with pdgCache := newPdg })
  | _ =>
    let (result, newNist) ← queryNIST key state.nistCache
    return (result, { state with nistCache := newNist })

end DatabaseQuery

end Measure.External
