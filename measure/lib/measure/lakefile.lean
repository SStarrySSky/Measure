import Lake
open Lake DSL

-- In unified fork mode, the C++ kernel extensions are compiled
-- directly into the lean4 binary via CMake (MEASURE_EXTENSIONS=ON).
-- No separate static library linking is needed here.
--
-- The ffi_bridge.cpp is compiled into the lean4 kernel itself via CMake,
-- so Lake does not need to compile it separately. Include paths for the
-- kernel headers are handled by the CMake build.

package measure where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  -- In fork mode, kernel extensions (including ffi_bridge.o) are already
  -- linked into the lean/leanc binary. No extra moreLinkArgs needed.
  moreLinkArgs := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib Measure where
  srcDir := "../../src"
  roots := #[`Measure]

lean_exe «measure-cli» where
  srcDir := "../../src"
  root := `Main
  supportInterpreter := true

lean_lib MeasureTest where
  srcDir := "../../../test"
  roots := #[`TestDim, `TestQuantity, `TestConstants, `TestBridge, `TestPhysics, `TestProperties, `TestIntegration, `TestStress]
