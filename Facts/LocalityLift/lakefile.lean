import Lake
open Lake DSL

package fact_locality_lift

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

/--
Minimal skeleton for the locality-lift fact.  At the moment the library only
contains interface declarations and extensive documentation stubs, so we limit
the build to those modules.  The actual proof will be added in follow-up work.
-/
lean_lib FactLocalityLift where
  srcDir := "."
  globs := #[
    Glob.submodules `Facts.LocalityLift.Interface,
    Glob.submodules `Facts.LocalityLift.Proof,
    Glob.submodules `Facts.LocalityLift.ProofSketch,
    Glob.one `Facts.LocalityLift.Exports,
    Glob.one `Facts.LocalityLift
  ]
