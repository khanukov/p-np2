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

  globs := #[`Basic, `CoverExtra, `Migrated, `Pnp2Tests, `SatCoverTest,
    `CoverComputeTest]
  srcDir := "test"
