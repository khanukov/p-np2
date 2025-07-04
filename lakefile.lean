import Lake
open Lake DSL

package pnp2

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

@[default_target]
lean_lib Pnp2 where
  -- Source files live at the repository root.
  srcDir := "."
