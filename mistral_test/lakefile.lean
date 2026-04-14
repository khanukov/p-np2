import Lake
open Lake DSL

package mistral_test

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

lean_lib MistralTestLib where
  srcDir := "."
  globs := #[
    Glob.one `MistralTestLib,
    Glob.one `MistralTestLib.SourceTheorems.CircuitBound,
    Glob.one `MistralTestLib.SourceTheorems.CircuitEncoding,
    Glob.one `MistralTestLib.SourceTheorems.ConcreteFamily,
    Glob.one `MistralTestLib.SourceTheorems.ConcreteGlobalNP,
    Glob.one `MistralTestLib.SourceTheorems.ConcreteGlobalNP_FINAL,
    Glob.one `MistralTestLib.SourceTheorems.ConcreteGlobalNP_New,
    Glob.one `MistralTestLib.SourceTheorems.FinalProof,
    Glob.one `MistralTestLib.SourceTheorems.ForcingProperty,
    Glob.one `MistralTestLib.SourceTheorems.IsoStrongMain,
    Glob.one `MistralTestLib.SourceTheorems.Frontier.UnifiedFrontier
  ]
  moreLinkArgs := #["-L", "../.lake/build/lib"]
  moreLeanArgs := #["-Dpp.unsafe=true"]
