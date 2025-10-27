import Lake
open Lake DSL

package fact_sunflower

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

/--
Lightweight wrapper around the classical sunflower lemma.  The build only
needs the `FactSunflower` library and its submodules, so we restrict the
compilation globs accordingly.
-/
lean_lib FactSunflower where
  srcDir := "."
  globs := #[Glob.submodules `FactSunflower]
