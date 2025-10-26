import Lake
open Lake DSL

package fact_psubset_ppoly

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

/--
Minimal wrapper around the external `P ⊆ P/poly` fact.  The library only
needs to expose the simplified complexity interfaces and the named
theorem, so we restrict the build to those modules. -/
lean_lib FactPsubsetPpoly where
  srcDir := "."
  globs := #[
    Glob.one `Proof.Complexity.Interfaces,
    Glob.one `FactPsubsetPpoly
  ]
