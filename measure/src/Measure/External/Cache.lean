/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Four-tier caching strategy for external data sources.
Tier 1: In-memory LRU (session), Tier 2: Local file cache (persistent),
Tier 3: Bundled snapshot, Tier 4: Compile error.
See ARCHITECTURE.md Section 8.2.
-/
import Measure.External.DataSource

namespace Measure.External

/-- Cache tier identifier. -/
inductive CacheTier where
  | memory    -- Tier 1: in-memory LRU
  | local_    -- Tier 2: local file cache
  | bundled   -- Tier 3: bundled snapshot
  | miss      -- Tier 4: all tiers exhausted
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A cached entry with metadata about where it came from. -/
structure CachedEntry where
  datum     : Datum
  tier      : CacheTier
  hitCount  : Nat := 1
  deriving Repr, Inhabited

/-- Cache statistics for diagnostics. -/
structure CacheStats where
  memoryHits  : Nat := 0
  localHits   : Nat := 0
  bundledHits : Nat := 0
  misses      : Nat := 0
  deriving Repr, Inhabited

namespace CacheStats

def totalQueries (s : CacheStats) : Nat :=
  s.memoryHits + s.localHits + s.bundledHits + s.misses

def hitRate (s : CacheStats) : Float :=
  let total := s.totalQueries
  if total == 0 then 0.0
  else (s.memoryHits + s.localHits + s.bundledHits).toFloat / total.toFloat

def recordHit (s : CacheStats) (tier : CacheTier) : CacheStats :=
  match tier with
  | .memory  => { s with memoryHits := s.memoryHits + 1 }
  | .local_  => { s with localHits  := s.localHits + 1 }
  | .bundled => { s with bundledHits := s.bundledHits + 1 }
  | .miss    => { s with misses := s.misses + 1 }

end CacheStats

/-- In-memory LRU cache (simplified: bounded list, most recent first). -/
structure MemoryCache where
  entries  : List (String × CachedEntry) := []
  capacity : Nat := 256
  deriving Repr, Inhabited

namespace MemoryCache

def lookup (cache : MemoryCache) (key : String) : Option CachedEntry :=
  match cache.entries.find? (·.1 == key) with
  | some (_, entry) => some { entry with hitCount := entry.hitCount + 1 }
  | none => none

def insert (cache : MemoryCache) (key : String) (entry : CachedEntry) : MemoryCache :=
  let filtered := cache.entries.filter (·.1 != key)
  let newEntries := (key, entry) :: filtered
  let trimmed := if newEntries.length > cache.capacity
                 then newEntries.take cache.capacity
                 else newEntries
  { cache with entries := trimmed }

def invalidate (cache : MemoryCache) (key : String) : MemoryCache :=
  { cache with entries := cache.entries.filter (·.1 != key) }

def clear (cache : MemoryCache) : MemoryCache :=
  { cache with entries := [] }

def size (cache : MemoryCache) : Nat := cache.entries.length

end MemoryCache

/-- DJB2 hash of a string, returned as a hex string. -/
private partial def djb2Hex (s : String) : String :=
  let hash := s.foldl (fun acc c => acc * 33 + c.toNat) 5381
  let n := hash % 0xFFFFFFFF
  hexOfNat n 8
where
  hexDigit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
  hexOfNat (n : Nat) (width : Nat) : String :=
    let rec go (n : Nat) (acc : List Char) (rem : Nat) : List Char :=
      if rem == 0 then acc
      else go (n / 16) (hexDigit (n % 16) :: acc) (rem - 1)
    String.ofList (go n [] width)

/-- Find a substring and return its character position.
    Returns the character index where `needle` first appears in `s`. -/
private def findSubstr? (s : String) (needle : String) : Option Nat :=
  if needle.isEmpty then some 0
  else
    let parts := s.splitOn needle
    match parts with
    | [] => none
    | [_] => none  -- needle not found
    | first :: _ => some first.length

/-- Find the index of the first character satisfying a predicate. -/
private def findCharIdx? (s : String) (p : Char → Bool) : Option Nat :=
  let chars := s.toList
  go 0 chars
where
  go (i : Nat) : List Char → Option Nat
    | [] => none
    | c :: cs => if p c then some i else go (i + 1) cs

/-- Parse digit characters into a Float. -/
private def parseDigitChars (digits : List Char) (neg : Bool) : Option Float :=
  let restStr := String.ofList digits
  let parts := restStr.splitOn "."
  match parts with
  | [intPart] =>
    match intPart.toNat? with
    | some n => some (if neg then -(Float.ofNat n) else Float.ofNat n)
    | none => none
  | [intPart, fracPart] =>
    let intN := intPart.toNat?.getD 0
    let fracN := fracPart.toNat?.getD 0
    let fracLen := fracPart.length
    let flt := Float.ofScientific (intN * (10 ^ fracLen) + fracN) true fracLen
    some (if neg then -flt else flt)
  | _ => none

/-- Parse a string as a Float, returning none on failure.
    Handles simple decimal numbers like "3.14", "-2.5", "100". -/
private def parseFloat? (s : String) : Option Float :=
  let chars := s.toList.dropWhile Char.isWhitespace
  let trimmed := chars.reverse.dropWhile Char.isWhitespace |>.reverse
  match trimmed with
  | [] => none
  | '-' :: ds => parseDigitChars ds true
  | ds => parseDigitChars ds false

-- Tier 2: File-system cache for persistent local storage.
-- Cache directory: MEASURE_CACHE_DIR env var or ~/.measure/cache/
-- File naming: djb2(key ++ "@" ++ version) as hex + ".json"
-- Format: simple JSON with value, uncertainty, dim fields.
namespace FileCache

/-- Resolve the cache directory path. -/
def cacheDir : IO System.FilePath := do
  match (← IO.getEnv "MEASURE_CACHE_DIR") with
  | some dir => pure ⟨dir⟩
  | none =>
    let home ← match (← IO.getEnv "HOME") with
      | some h => pure h
      | none => match (← IO.getEnv "USERPROFILE") with
        | some h => pure h
        | none => pure "."
    pure ⟨home ++ "/.measure/cache"⟩

/-- Build the cache file path for a given key and version. -/
def cacheFilePath (key : String) (ver : DataVersion) : IO System.FilePath := do
  let dir ← cacheDir
  let composite := key ++ "@" ++ ver.name ++ "." ++ toString ver.year
  let hash := djb2Hex composite
  pure (dir / (hash ++ ".json"))

/-- Ensure the cache directory exists. -/
def ensureCacheDir : IO Bool := do
  try
    let dir ← cacheDir
    IO.FS.createDirAll dir
    pure true
  catch _ => pure false

/-- Serialize a Datum to a simple JSON string. -/
def datumToJson (d : Datum) : String :=
  let exact := if d.isExact then "true" else "false"
  let edStr := match d.version.edition with
    | some e => s!"\"{e}\""
    | none => "null"
  "{\"value\":" ++ toString d.value ++ ",\"uncertainty\":" ++ toString d.uncertainty ++ "," ++
  "\"isExact\":" ++ exact ++ ",\"source\":\"" ++ d.source ++ "\"," ++
  "\"version\":{\"name\":\"" ++ d.version.name ++ "\",\"year\":" ++ toString d.version.year ++ "," ++
  "\"edition\":" ++ edStr ++ "}}"

/-- Parse a Float from a JSON substring. -/
private def parseJsonFloat (s : String) : Float :=
  match parseFloat? s with
  | some f => f
  | none => 0.0

/-- Extract a JSON string value for a given key from a flat JSON object. -/
private def extractJsonString (json : String) (key : String) : Option String :=
  let needle := "\"" ++ key ++ "\":\""
  match findSubstr? json needle with
  | none => none
  | some idx =>
    let start := idx + needle.length
    let rest := (json.drop start).toString
    match findCharIdx? rest (· == '"') with
    | some endIdx => some (rest.take endIdx).toString
    | none => none

/-- Extract a JSON numeric value for a given key. -/
private def extractJsonNumber (json : String) (key : String) : Option Float :=
  let needle := "\"" ++ key ++ "\":"
  match findSubstr? json needle with
  | none => none
  | some idx =>
    let start := idx + needle.length
    let rest := (json.drop start).toString
    let numStr := (rest.takeWhile (fun c => c.isDigit || c == '.' || c == '-' || c == 'e' || c == 'E' || c == '+')).toString
    parseFloat? numStr

/-- Extract a JSON bool value for a given key. -/
private def extractJsonBool (json : String) (key : String) : Option Bool :=
  let needle := "\"" ++ key ++ "\":"
  match findSubstr? json needle with
  | none => none
  | some idx =>
    let start := idx + needle.length
    let rest := (json.drop start).toString
    let restTrimmed := String.ofList (rest.toList.dropWhile Char.isWhitespace)
    if restTrimmed.startsWith "true" then some true
    else if restTrimmed.startsWith "false" then some false
    else none

/-- Deserialize a Datum from a JSON string. -/
def datumFromJson (json : String) : Option Datum := do
  let value ← extractJsonNumber json "value"
  let uncertainty ← extractJsonNumber json "uncertainty"
  let isExact := (extractJsonBool json "isExact").getD false
  let source ← extractJsonString json "source"
  let vName ← extractJsonString json "name"
  let vYear ← extractJsonNumber json "year"
  some {
    value := value
    uncertainty := uncertainty
    dim := Measure.Dim.Dim.dimensionless
    isExact := isExact
    source := source
    version := { name := vName, year := vYear.toUInt64.toNat }
  }

/-- Look up a datum in the file cache. Returns none on any failure. -/
def lookup (key : String) (ver : DataVersion) : IO (Option Datum) := do
  try
    let path ← cacheFilePath key ver
    let contents ← IO.FS.readFile path
    pure (datumFromJson contents)
  catch _ => pure none

/-- Store a datum in the file cache. Silently fails on error. -/
def store (key : String) (datum : Datum) : IO Unit := do
  try
    let _ ← ensureCacheDir
    let path ← cacheFilePath key datum.version
    IO.FS.writeFile path (datumToJson datum)
  catch _ => pure ()

end FileCache

/-- Four-tier cache state. -/
structure DataCache (σ : Type) where
  source  : σ
  memory  : MemoryCache := {}
  stats   : CacheStats := {}
  deriving Repr, Inhabited

namespace DataCache

variable {σ : Type}

/-- Pure lookup through tiers 1, 3, 4 (skips file cache). -/
def lookupPure [DataSource σ] (cache : DataCache σ) (key : String)
    : DataResult Datum × CacheTier × DataCache σ :=
  -- Tier 1: memory
  match cache.memory.lookup key with
  | some entry =>
    let newCache := { cache with
      memory := cache.memory.insert key entry
      stats := cache.stats.recordHit .memory }
    (.ok entry.datum entry.datum.version, .memory, newCache)
  | none =>
    -- Tier 3: bundled snapshot
    match DataSource.get cache.source key with
    | .ok datum ver =>
      let entry : CachedEntry := { datum := datum, tier := .bundled }
      let newCache := { cache with
        memory := cache.memory.insert key entry
        stats := cache.stats.recordHit .bundled }
      (.ok datum ver, .bundled, newCache)
    | other =>
      -- Tier 4: miss
      let newCache := { cache with stats := cache.stats.recordHit .miss }
      (other, .miss, newCache)

/-- Look up through all four tiers in order (IO for file cache access). -/
def lookup [DataSource σ] (cache : DataCache σ) (key : String)
    : IO (DataResult Datum × CacheTier × DataCache σ) := do
  -- Tier 1: memory
  match cache.memory.lookup key with
  | some entry =>
    let newCache := { cache with
      memory := cache.memory.insert key entry
      stats := cache.stats.recordHit .memory }
    return (.ok entry.datum entry.datum.version, .memory, newCache)
  | none =>
    -- Tier 2: local file cache
    let bundledVer := DataSource.bundledVersion cache.source
    match (← FileCache.lookup key bundledVer) with
    | some datum =>
      let entry : CachedEntry := { datum := datum, tier := .local_ }
      let newCache := { cache with
        memory := cache.memory.insert key entry
        stats := cache.stats.recordHit .local_ }
      return (.ok datum datum.version, .local_, newCache)
    | none =>
      -- Tier 3: bundled snapshot
      match DataSource.get cache.source key with
      | .ok datum ver =>
        let entry : CachedEntry := { datum := datum, tier := .bundled }
        let newCache := { cache with
          memory := cache.memory.insert key entry
          stats := cache.stats.recordHit .bundled }
        -- Store in file cache for next session
        FileCache.store key datum
        return (.ok datum ver, .bundled, newCache)
      | other =>
        -- Tier 4: miss
        let newCache := { cache with stats := cache.stats.recordHit .miss }
        return (other, .miss, newCache)

/-- Pure versioned lookup through tiers 1, 3, 4 (skips file cache). -/
def lookupVersionedPure [DataSource σ] (cache : DataCache σ) (key : String)
    (ver : DataVersion) : DataResult Datum × CacheTier × DataCache σ :=
  match cache.memory.lookup key with
  | some entry =>
    if entry.datum.version == ver then
      let newCache := { cache with
        memory := cache.memory.insert key entry
        stats := cache.stats.recordHit .memory }
      (.ok entry.datum ver, .memory, newCache)
    else
      match DataSource.getVersioned cache.source key ver with
      | .ok datum v =>
        let entry : CachedEntry := { datum := datum, tier := .bundled }
        let newCache := { cache with
          memory := cache.memory.insert key entry
          stats := cache.stats.recordHit .bundled }
        (.ok datum v, .bundled, newCache)
      | other =>
        let newCache := { cache with stats := cache.stats.recordHit .miss }
        (other, .miss, newCache)
  | none =>
    match DataSource.getVersioned cache.source key ver with
    | .ok datum v =>
      let entry : CachedEntry := { datum := datum, tier := .bundled }
      let newCache := { cache with
        memory := cache.memory.insert key entry
        stats := cache.stats.recordHit .bundled }
      (.ok datum v, .bundled, newCache)
    | other =>
      let newCache := { cache with stats := cache.stats.recordHit .miss }
      (other, .miss, newCache)

/-- Versioned lookup through all four tiers (IO for file cache access). -/
def lookupVersioned [DataSource σ] (cache : DataCache σ) (key : String)
    (ver : DataVersion) : IO (DataResult Datum × CacheTier × DataCache σ) := do
  -- Tier 1: memory
  match cache.memory.lookup key with
  | some entry =>
    if entry.datum.version == ver then
      let newCache := { cache with
        memory := cache.memory.insert key entry
        stats := cache.stats.recordHit .memory }
      return (.ok entry.datum ver, .memory, newCache)
  | none => pure ()
  -- Tier 2: file cache
  match (← FileCache.lookup key ver) with
  | some datum =>
    let entry : CachedEntry := { datum := datum, tier := .local_ }
    let newCache := { cache with
      memory := cache.memory.insert key entry
      stats := cache.stats.recordHit .local_ }
    return (.ok datum datum.version, .local_, newCache)
  | none => pure ()
  -- Tier 3: bundled snapshot
  match DataSource.getVersioned cache.source key ver with
  | .ok datum v =>
    let entry : CachedEntry := { datum := datum, tier := .bundled }
    let newCache := { cache with
      memory := cache.memory.insert key entry
      stats := cache.stats.recordHit .bundled }
    FileCache.store key datum
    return (.ok datum v, .bundled, newCache)
  | other =>
    -- Tier 4: miss
    let newCache := { cache with stats := cache.stats.recordHit .miss }
    return (other, .miss, newCache)

end DataCache

end Measure.External
