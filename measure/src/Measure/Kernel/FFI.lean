/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

FFI declarations for the Measure kernel extension.
Each @[extern] binding corresponds to a C function in ffi_bridge.cpp.
-/
namespace Measure.Kernel

-- ============================================================
-- Opaque types wrapping C++ external classes
-- ============================================================

opaque EpsilonValPointed : NonemptyType.{0}
def EpsilonVal := EpsilonValPointed.type
instance : Nonempty EpsilonVal := EpsilonValPointed.property

opaque MeasureMetadataPointed : NonemptyType.{0}
def MeasureMetadata := MeasureMetadataPointed.type
instance : Nonempty MeasureMetadata := MeasureMetadataPointed.property

opaque TheoryRegistryPointed : NonemptyType.{0}
def TheoryRegistry := TheoryRegistryPointed.type
instance : Nonempty TheoryRegistry := TheoryRegistryPointed.property

opaque TheoryGraphPointed : NonemptyType.{0}
def TheoryGraph := TheoryGraphPointed.type
instance : Nonempty TheoryGraph := TheoryGraphPointed.property

opaque ConservationCheckerPointed : NonemptyType.{0}
def ConservationChecker := ConservationCheckerPointed.type
instance : Nonempty ConservationChecker := ConservationCheckerPointed.property

opaque ApproxEqCheckerPointed : NonemptyType.{0}
def ApproxEqChecker := ApproxEqCheckerPointed.type
instance : Nonempty ApproxEqChecker := ApproxEqCheckerPointed.property

opaque EpsilonTrackerPointed : NonemptyType.{0}
def EpsilonTracker := EpsilonTrackerPointed.type
instance : Nonempty EpsilonTracker := EpsilonTrackerPointed.property

/-- Theory identifier (maps to C++ `theory_id` = `uint32_t`). -/
abbrev TheoryId := UInt32

/-- Rigor level spectrum (maps to C++ `rigor_level` enum). -/
inductive RigorLevel where
  | strict      -- 0: full formal proof
  | approximate -- 1: controlled approximation
  | empirical   -- 2: empirical formula
  | numerical   -- 3: pure numerical
  deriving Inhabited, BEq, Repr

def RigorLevel.toUInt8 : RigorLevel → UInt8
  | .strict => 0 | .approximate => 1 | .empirical => 2 | .numerical => 3

def RigorLevel.ofUInt8 : UInt8 → RigorLevel
  | 0 => .strict | 1 => .approximate | 2 => .empirical | _ => .numerical

-- ============================================================
-- EpsilonVal FFI (13 functions)
-- ============================================================

@[extern "lean_measure_epsilon_zero"]
opaque EpsilonVal.zero : Unit → EpsilonVal

@[extern "lean_measure_epsilon_one"]
opaque EpsilonVal.one : Unit → EpsilonVal

@[extern "lean_measure_epsilon_inf"]
opaque EpsilonVal.inf : Unit → EpsilonVal

@[extern "lean_measure_epsilon_make"]
opaque EpsilonVal.make : UInt64 → UInt64 → EpsilonVal

@[extern "lean_measure_epsilon_is_zero"]
opaque EpsilonVal.isZero : @& EpsilonVal → Bool

@[extern "lean_measure_epsilon_is_inf"]
opaque EpsilonVal.isInf : @& EpsilonVal → Bool

@[extern "lean_measure_epsilon_leq"]
opaque EpsilonVal.leq : @& EpsilonVal → @& EpsilonVal → Bool

@[extern "lean_measure_epsilon_add"]
opaque EpsilonVal.add : @& EpsilonVal → @& EpsilonVal → EpsilonVal

@[extern "lean_measure_epsilon_mul"]
opaque EpsilonVal.mul : @& EpsilonVal → @& EpsilonVal → EpsilonVal

@[extern "lean_measure_epsilon_max"]
opaque EpsilonVal.max : @& EpsilonVal → @& EpsilonVal → EpsilonVal

@[extern "lean_measure_epsilon_to_string"]
opaque EpsilonVal.toString : @& EpsilonVal → String

@[extern "lean_measure_epsilon_numerator"]
opaque EpsilonVal.numerator : @& EpsilonVal → UInt64

@[extern "lean_measure_epsilon_denominator"]
opaque EpsilonVal.denominator : @& EpsilonVal → UInt64

-- ============================================================
-- MeasureMetadata FFI (8 functions)
-- ============================================================

@[extern "lean_measure_metadata_default"]
opaque MeasureMetadata.default : Unit → MeasureMetadata

@[extern "lean_measure_metadata_get_theory"]
opaque MeasureMetadata.getTheory : @& MeasureMetadata → TheoryId

@[extern "lean_measure_metadata_get_rigor"]
opaque MeasureMetadata.getRigorRaw : @& MeasureMetadata → UInt8

@[extern "lean_measure_metadata_get_epsilon_bound"]
opaque MeasureMetadata.getEpsilonBound : @& MeasureMetadata → EpsilonVal

@[extern "lean_measure_metadata_is_default"]
opaque MeasureMetadata.isDefault : @& MeasureMetadata → Bool

@[extern "lean_measure_metadata_set_theory"]
opaque MeasureMetadata.setTheory : @& MeasureMetadata → TheoryId → MeasureMetadata

@[extern "lean_measure_metadata_set_rigor"]
opaque MeasureMetadata.setRigorRaw : @& MeasureMetadata → UInt8 → MeasureMetadata

@[extern "lean_measure_metadata_set_epsilon_bound"]
opaque MeasureMetadata.setEpsilonBound : @& MeasureMetadata → @& EpsilonVal → MeasureMetadata

-- ============================================================
-- TheoryRegistry FFI (6 functions)
-- ============================================================

@[extern "lean_measure_theory_registry_new"]
opaque TheoryRegistry.new : Unit → TheoryRegistry

@[extern "lean_measure_theory_registry_register"]
opaque TheoryRegistry.register :
  @& TheoryRegistry → @& String → @& Array TheoryId →
  UInt8 → UInt64 → UInt64 → TheoryId

@[extern "lean_measure_theory_registry_find_by_name"]
opaque TheoryRegistry.findByName : @& TheoryRegistry → @& String → TheoryId

@[extern "lean_measure_theory_registry_is_accessible"]
opaque TheoryRegistry.isAccessible : @& TheoryRegistry → TheoryId → TheoryId → Bool

@[extern "lean_measure_theory_registry_get_name"]
opaque TheoryRegistry.getName : @& TheoryRegistry → TheoryId → String

@[extern "lean_measure_theory_registry_set_relation"]
opaque TheoryRegistry.setRelation : @& TheoryRegistry → TheoryId → TheoryId → UInt8 → Bool

-- ============================================================
-- TheoryGraph FFI (5 functions)
-- ============================================================

@[extern "lean_measure_theory_graph_new"]
opaque TheoryGraph.new : @& TheoryRegistry → TheoryGraph

@[extern "lean_measure_theory_graph_are_conflicting"]
opaque TheoryGraph.areConflicting : @& TheoryGraph → TheoryId → TheoryId → Bool

@[extern "lean_measure_theory_graph_check_compat"]
opaque TheoryGraph.checkCompatRaw : @& TheoryGraph → TheoryId → TheoryId → UInt8

@[extern "lean_measure_theory_graph_conflict_count"]
opaque TheoryGraph.conflictCount : @& TheoryGraph → UInt64

@[extern "lean_measure_theory_graph_bridge_count"]
opaque TheoryGraph.bridgeCount : @& TheoryGraph → UInt64

-- ============================================================
-- ConservationChecker FFI (4 functions)
-- ============================================================

@[extern "lean_measure_conservation_checker_new"]
opaque ConservationChecker.new : TheoryId → ConservationChecker

@[extern "lean_measure_conservation_add_law"]
opaque ConservationChecker.addLaw : @& ConservationChecker → @& String → @& String → Bool

@[extern "lean_measure_conservation_check_all"]
opaque ConservationChecker.checkAll : @& ConservationChecker → @& String → Array String

@[extern "lean_measure_conservation_law_count"]
opaque ConservationChecker.lawCount : @& ConservationChecker → UInt32

-- ============================================================
-- ApproxEqChecker FFI (4 functions)
-- ============================================================

@[extern "lean_measure_approx_eq_checker_new"]
opaque ApproxEqChecker.new : Unit → ApproxEqChecker

@[extern "lean_measure_approx_eq_try_numeric"]
opaque ApproxEqChecker.tryNumeric : @& ApproxEqChecker → Float → Float → Bool × UInt64 × UInt64

@[extern "lean_measure_approx_eq_has_overflow"]
opaque ApproxEqChecker.hasOverflow : @& ApproxEqChecker → Bool

@[extern "lean_measure_approx_eq_reset"]
opaque ApproxEqChecker.reset : @& ApproxEqChecker → Unit

-- ============================================================
-- EpsilonTracker FFI (15 functions)
-- ============================================================

@[extern "lean_measure_epsilon_tracker_new"]
opaque EpsilonTracker.new : Unit → EpsilonTracker

@[extern "lean_measure_epsilon_tracker_reset"]
opaque EpsilonTracker.reset : @& EpsilonTracker → Unit

@[extern "lean_measure_epsilon_tracker_set_overflow_threshold"]
opaque EpsilonTracker.setOverflowThreshold : @& EpsilonTracker → @& EpsilonVal → Unit

@[extern "lean_measure_epsilon_tracker_mk_literal"]
opaque EpsilonTracker.mkLiteral : @& EpsilonTracker → @& EpsilonVal → @& String → UInt64

@[extern "lean_measure_epsilon_tracker_mk_add"]
opaque EpsilonTracker.mkAdd : @& EpsilonTracker → UInt64 → UInt64 → @& String → UInt64

@[extern "lean_measure_epsilon_tracker_mk_mul"]
opaque EpsilonTracker.mkMul :
  @& EpsilonTracker → UInt64 → UInt64 →
  @& EpsilonVal → @& EpsilonVal → @& String → UInt64

@[extern "lean_measure_epsilon_tracker_mk_max"]
opaque EpsilonTracker.mkMax : @& EpsilonTracker → UInt64 → UInt64 → @& String → UInt64

@[extern "lean_measure_epsilon_tracker_mk_trans"]
opaque EpsilonTracker.mkTrans : @& EpsilonTracker → UInt64 → UInt64 → @& String → UInt64

@[extern "lean_measure_epsilon_tracker_mk_subst"]
opaque EpsilonTracker.mkSubst : @& EpsilonTracker → UInt64 → @& EpsilonVal → @& String → UInt64

@[extern "lean_measure_epsilon_tracker_get_epsilon"]
opaque EpsilonTracker.getEpsilon : @& EpsilonTracker → UInt64 → EpsilonVal

@[extern "lean_measure_epsilon_tracker_has_overflow"]
opaque EpsilonTracker.hasOverflow : @& EpsilonTracker → Bool

@[extern "lean_measure_epsilon_tracker_overflow_count"]
opaque EpsilonTracker.overflowCount : @& EpsilonTracker → UInt64

@[extern "lean_measure_epsilon_tracker_render_tree"]
opaque EpsilonTracker.renderTree : @& EpsilonTracker → UInt64 → String

@[extern "lean_measure_epsilon_tracker_render_overflow_report"]
opaque EpsilonTracker.renderOverflowReport : @& EpsilonTracker → String

@[extern "lean_measure_epsilon_tracker_size"]
opaque EpsilonTracker.size : @& EpsilonTracker → UInt64

-- ============================================================
-- Rigor propagation FFI (3 functions)
-- ============================================================

@[extern "lean_measure_rigor_propagate"]
opaque Rigor.propagateRaw : UInt8 → UInt8 → UInt8

@[extern "lean_measure_rigor_is_compatible"]
opaque Rigor.isCompatibleRaw : UInt8 → UInt8 → Bool

@[extern "lean_measure_rigor_to_string"]
opaque Rigor.toStringRaw : UInt8 → String

end Measure.Kernel
