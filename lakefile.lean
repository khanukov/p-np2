import Lake
open Lake DSL

package pnp

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

@[default_target]
lean_lib Pnp where
  srcDir := "pnp"

/-- Legacy Pnp2 code base preserved for reference.  We build it as a separate
    library so that historical proofs continue to compile. -/
lean_lib Pnp2 where
  srcDir := "."
  roots := #[`Pnp2]

lean_exe tests where
  root := `Main
  srcDir := "test"
  supportInterpreter := true

@[test_driver]
lean_lib Tests where

  globs := #[`Basic, `CoverExtra, `Migrated, `Pnp2Legacy]
  srcDir := "test"
