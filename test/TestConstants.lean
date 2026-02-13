/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Tests for physical constants: exact values, uncertain values,
dimension correctness, and CODATA 2022 compliance.
-/
import Measure.Constants

namespace TestConstants

open Measure.Dim
open Measure.Quantity
open Measure.Constants
open Measure.Error

-- ============================================================
-- Exact constants: value checks
-- ============================================================

-- Speed of light = 299792458 m/s
#eval show IO Unit from do
  if c.value != 299792458.0 then throw (IO.userError "c value mismatch")

-- Planck constant ≈ 6.626e-34
#eval show IO Unit from do
  if Float.abs (h.value - 6.62607015e-34) >= 1e-48 then
    throw (IO.userError "h value mismatch")

-- Boltzmann constant ≈ 1.381e-23
#eval show IO Unit from do
  if Float.abs (k_B.value - 1.380649e-23) >= 1e-37 then
    throw (IO.userError "k_B value mismatch")

-- Avogadro constant ≈ 6.022e23
#eval show IO Unit from do
  if Float.abs (N_A.value - 6.02214076e23) >= 1e9 then
    throw (IO.userError "N_A value mismatch")

-- Elementary charge ≈ 1.602e-19
#eval show IO Unit from do
  if Float.abs (e.value - 1.602176634e-19) >= 1e-33 then
    throw (IO.userError "e value mismatch")

-- Reduced Planck constant ℏ = h/(2π)
#eval show IO Unit from do
  let expected := 6.62607015e-34 / (2.0 * 3.14159265358979323846)
  if Float.abs (ℏ.value - expected) >= 1e-48 then
    throw (IO.userError "ℏ value mismatch")

-- Stefan-Boltzmann constant ≈ 5.670e-8
#eval show IO Unit from do
  if Float.abs (σ.value - 5.670374419e-8) >= 1e-22 then
    throw (IO.userError "σ value mismatch")

-- ============================================================
-- Exact constants: zero uncertainty
-- ============================================================

-- Exact constants have Unit error (no uncertainty data)
example : c.error = () := rfl
example : h.error = () := rfl
example : k_B.error = () := rfl
example : N_A.error = () := rfl
example : e.error = () := rfl
example : ℏ.error = () := rfl
example : σ.error = () := rfl

-- ============================================================
-- Exact constants: dimension checks
-- ============================================================

-- c has dimension Velocity = L T⁻¹
example : @ExactQ.mk Velocity 299792458.0 = c := rfl

-- e has dimension Charge = T I
example : @ExactQ.mk Charge 1.602176634e-19 = e := rfl

-- ============================================================
-- Measured constants: non-zero uncertainty
-- ============================================================

-- G has non-zero uncertainty
#eval show IO Unit from do
  if G.uncertainty <= 0.0 then throw (IO.userError "G uncertainty should be > 0")

-- m_e has non-zero uncertainty
#eval show IO Unit from do
  if m_e.uncertainty <= 0.0 then throw (IO.userError "m_e uncertainty should be > 0")

-- m_p has non-zero uncertainty
#eval show IO Unit from do
  if m_p.uncertainty <= 0.0 then throw (IO.userError "m_p uncertainty should be > 0")

-- Fine-structure constant α has non-zero uncertainty
#eval show IO Unit from do
  if α.uncertainty <= 0.0 then throw (IO.userError "α uncertainty should be > 0")

-- μ₀ has non-zero uncertainty
#eval show IO Unit from do
  if μ₀.uncertainty <= 0.0 then throw (IO.userError "μ₀ uncertainty should be > 0")

-- ε₀ has non-zero uncertainty
#eval show IO Unit from do
  if ε₀.uncertainty <= 0.0 then throw (IO.userError "ε₀ uncertainty should be > 0")

-- ============================================================
-- Measured constants: value checks
-- ============================================================

-- G ≈ 6.674e-11
#eval show IO Unit from do
  if Float.abs (G.value - 6.67430e-11) >= 1e-15 then
    throw (IO.userError "G value mismatch")

-- m_e ≈ 9.109e-31
#eval show IO Unit from do
  if Float.abs (m_e.value - 9.1093837015e-31) >= 1e-40 then
    throw (IO.userError "m_e value mismatch")

-- m_p ≈ 1.673e-27
#eval show IO Unit from do
  if Float.abs (m_p.value - 1.67262192369e-27) >= 1e-37 then
    throw (IO.userError "m_p value mismatch")

-- α ≈ 7.297e-3
#eval show IO Unit from do
  if Float.abs (α.value - 7.2973525693e-3) >= 1e-13 then
    throw (IO.userError "α value mismatch")

-- ============================================================
-- Measured constants: uncertainty magnitude sanity
-- ============================================================

-- G uncertainty is much smaller than G value
#eval show IO Unit from do
  if G.uncertainty >= Float.abs G.value * 0.001 then
    throw (IO.userError "G uncertainty too large relative to value")

-- m_e uncertainty is much smaller than m_e value
#eval show IO Unit from do
  if m_e.uncertainty >= Float.abs m_e.value * 1e-6 then
    throw (IO.userError "m_e uncertainty too large relative to value")

-- ============================================================
-- Measured constants: interval sanity
-- ============================================================

-- G interval contains the central value
#eval show IO Unit from do
  let (lo, hi) := G.toInterval
  if lo >= G.value then throw (IO.userError "G interval lo >= value")
  if hi <= G.value then throw (IO.userError "G interval hi <= value")

-- m_e interval contains the central value
#eval show IO Unit from do
  let (lo, hi) := m_e.toInterval
  if lo >= m_e.value then throw (IO.userError "m_e interval lo >= value")
  if hi <= m_e.value then throw (IO.userError "m_e interval hi <= value")

-- ============================================================
-- Provenance tracking on constants
-- ============================================================

-- G has database provenance from CODATA
#eval show IO Unit from do
  match G.provenance with
  | .database "CODATA" "2022" => pure ()
  | _ => throw (IO.userError "Expected CODATA 2022 provenance for G")

-- m_e has database provenance from CODATA
#eval show IO Unit from do
  match m_e.provenance with
  | .database "CODATA" "2022" => pure ()
  | _ => throw (IO.userError "Expected CODATA 2022 provenance for m_e")

-- ============================================================
-- Arithmetic with constants
-- ============================================================

-- c * c gives a quantity with dimension L² T⁻²
#eval show IO Unit from do
  let c2 := c * c
  if c2.value != 299792458.0 * 299792458.0 then
    throw (IO.userError "c² value mismatch")

-- Scalar * constant works
#eval show IO Unit from do
  let two_c := (2.0 : Float) * c
  if two_c.value != 2.0 * 299792458.0 then
    throw (IO.userError "2c value mismatch")

end TestConstants
