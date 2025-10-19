import Lake
open Lake DSL

package pnp2

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

lean_lib Pnp2 where
  srcDir := "Pnp2"
  globs := #[
    `ComplexityClasses,
    `NP_separation
  ]

@[default_target]
lean_lib PnP3 where
  srcDir := "pnp3"
  globs := #[
    `Core.BooleanBasics,
    `Core.PDTPartial,
    `Core.PDT,
    `Core.Atlas,
    `Core.SAL_Core,
    `Core.ShrinkageWitness,
    `Core.ShrinkageAC0,
    `Counting.BinomialBounds,
    `Counting.Count_EasyFuncs,
    `Counting.Atlas_to_LB_Core,
    `AC0.Formulas,
    `Complexity.Interfaces,
    `Models.Model_GapMCSP,
    `Models.Model_SparseNP,
    `LowerBounds.LB_Formulas,
    `LowerBounds.AntiChecker,
    `LowerBounds.LB_Formulas_Core,
    `LowerBounds.LB_LocalCircuits,
    `LowerBounds.LB_GeneralFromLocal,
    `Magnification.Facts_Magnification,
    `Magnification.PipelineStatements,
    `Magnification.LocalityLift,
    `Magnification.Bridge_to_Magnification,
    `Magnification.FinalResult,
    `ThirdPartyFacts.AC0Witness,
    `ThirdPartyFacts.BaseSwitching,
    `ThirdPartyFacts.Facts_Switching,
    `ThirdPartyFacts.HastadMSL,
    `ThirdPartyFacts.LeafBudget
  ]

@[test_driver]
lean_lib PnP3Tests where
  srcDir := "pnp3/Tests"
  globs := #[
    `Atlas_Count_Sanity,
    `Atlas_Counterexample_Search,
    `LB_Smoke_Scenario,
    `LB_Core_Contradiction,
    `Magnification_Core_Contradiction,
    `Switching_Basics
  ]
