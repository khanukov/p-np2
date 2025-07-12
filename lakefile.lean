import Lake
open Lake DSL

package pnp2

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

@[default_target]
lean_lib Pnp2 where
  -- Source files live at the repository root.
  srcDir := "."

lean_lib Pnp where
  srcDir := "."

@[test_driver]
lean_exe tests where
  root := `Main
  srcDir := "test"
  supportInterpreter := true

lean_lib Tests where
  globs := #[`SunflowerStep]
  srcDir := "test"
