import Lake
open Lake DSL

package «p-subset-ppoly» where
  version := v!"1.0.0"
  keywords := #["complexity theory", "P vs NP", "circuit complexity"]
  -- Specify root module
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.22.0-rc2"

@[default_target]
lean_lib «PSubsetPpoly» where
  -- src directory is at the root, so modules are PSubsetPpoly.*

lean_lib «Utils» where
  -- Utils library for helper functions
  roots := #[`Utils]
