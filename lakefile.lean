import Lake
open Lake DSL

package measure where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  moreLinkArgs := #["-lstdc++"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

/-- Compile the C++ kernel sources into a static FFI library. -/
extern_lib «measure-ffi» pkg := do
  let srcDir := pkg.dir / ".." / ".." / "src"
  let kernelDir := srcDir / "kernel"
  let buildDir := pkg.dir / "build" / "ir"
  let includeFlag := s!"-I{srcDir}"
  let leanIncDir ← getLeanIncludeDir
  let leanIncFlag := s!"-I{leanIncDir}"
  let weakFlags := #[includeFlag, leanIncFlag]
  let traceFlags := #["-std=c++17", "-fPIC", "-O2"]
  let cppFiles := #[
    "approx_eq",
    "rigor_propagation",
    "measure_metadata",
    "theory_module",
    "epsilon_tracker",
    "is_approx_eq",
    "theory_graph",
    "conservation",
    "ffi_bridge"
  ]
  let oFiles ← cppFiles.mapM fun name => do
    let srcJob ← inputTextFile (kernelDir / s!"{name}.cpp")
    buildO (buildDir / s!"{name}.o") srcJob weakFlags traceFlags "c++"
  let libFile := pkg.dir / "build" / "lib" / nameToStaticLib "measure-ffi"
  buildStaticLib libFile oFiles

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
