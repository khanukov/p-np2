import Lake
open Lake DSL

package mistral_test

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

lean_lib MistralTestLib where
  srcDir := "."
  moreLinkArgs := #["-L", "../.lake/build/lib"]
  moreLeanArgs := #["-Dpp.unsafe=true"]
