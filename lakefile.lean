import Lake
open Lake DSL

package pnp2

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

@[default_target]
lean_lib Pnp2 where
  -- The main library now lives entirely under `Pnp2`.
  srcDir := "."
  roots := #[`Pnp2]

lean_exe tests where
  root := `Main
  srcDir := "test"
  supportInterpreter := true

@[test_driver]
lean_lib Tests where

  -- Only build the modules that compile successfully. Some of the legacy
  -- tests relied on the old `Pnp` namespace and no longer work after the
  -- migration, so we exclude them from the test library.
  globs := #[
    `CoverExtra,
    `Cover2Test,
    `Pnp2Tests,
    `SatCoverTest,
    `CoverComputeTest,
    `CoverResBaseTest,
    `SunflowerTest
  ]
  srcDir := "test"
