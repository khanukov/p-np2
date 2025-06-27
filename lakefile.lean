import Lake
open Lake DSL

package pnp2

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "6e08340fe7c928dd55c20625ccf419477f5dd106"

@[default_target]
lean_lib Pnp2 where
  -- Source files live at the repository root.
  srcDir := "."
