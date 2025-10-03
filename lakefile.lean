import Lake
open Lake DSL

package pnp2

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

@[default_target]
lean_lib PnP3 where
  srcDir := "pnp3"
  globs := #[
    `Core.BooleanBasics,
    `Core.PDT,
    `Core.Atlas,
    `Core.SAL_Core,
    `Counting.BinomialBounds,
    `Counting.Count_EasyFuncs,
    `Counting.Atlas_to_LB_Core,
    `Models.Model_GapMCSP,
    `LowerBounds.LB_Formulas,
    `LowerBounds.LB_LocalCircuits,
    `Magnification.Facts_Magnification,
    `Magnification.Bridge_to_Magnification,
    `ThirdPartyFacts.Facts_Switching
  ]

@[test_driver]
lean_lib PnP3Tests where
  srcDir := "pnp3/Tests"
  globs := #[
    `Atlas_Count_Sanity,
    `Atlas_Counterexample_Search
  ]
