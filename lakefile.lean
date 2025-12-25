import Lake
open Lake DSL

package pnp3

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"
require fact_psubset_ppoly from "./Facts/PsubsetPpoly"
require fact_locality_lift from "./Facts/LocalityLift"
require fact_sunflower from "./Facts/Sunflower"

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
    `Counting.BinomialBounds,
    `Counting.CapacityGap,
    `Counting.Count_EasyFuncs,
    `Counting.Atlas_to_LB_Core,
    `AC0.Formulas,
    `Complexity.Promise,
    `Complexity.Interfaces,
    `Models.Model_GapMCSP,
    `Models.Model_SparseNP,
    `LowerBounds.LB_Formulas,
    `LowerBounds.AntiChecker,
    `LowerBounds.LB_Formulas_Core,
    `LowerBounds.LB_LocalCircuits,
    `LowerBounds.LB_GeneralFromLocal,
    `Magnification.LocalityInterfaces,
    `Magnification.Facts_Magnification,
    `Magnification.PipelineStatements,
    `Magnification.LocalityLift,
    `Magnification.Bridge_to_Magnification,
    `Magnification.FinalResult,
    `ThirdPartyFacts.Facts_Switching,
    `ThirdPartyFacts.LocalityLift,
    `ThirdPartyFacts.PsubsetPpoly,
    `ThirdPartyFacts.LeafBudget,
    `Tests.SmokeTests,
    `Tests.UnitTests
  ]

@[test_driver]
lean_exe test where
  root := `Tests.TestDriver
  srcDir := "pnp3"
