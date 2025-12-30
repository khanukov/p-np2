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
    Glob.one `Core.BooleanBasics,
    Glob.one `Core.PDTPartial,
    Glob.one `Core.PDT,
    Glob.one `Core.Atlas,
    Glob.one `Core.SAL_Core,
    Glob.one `Core.ShrinkageWitness,
    Glob.one `Counting.BinomialBounds,
    Glob.one `Counting.CapacityGap,
    Glob.one `Counting.Count_EasyFuncs,
    Glob.one `Counting.Atlas_to_LB_Core,
    Glob.one `AC0.Formulas,
    Glob.one `AC0.MultiSwitching.Definitions,
    Glob.one `AC0.MultiSwitching.Counting,
    Glob.one `AC0.MultiSwitching.Encoding,
    Glob.one `Complexity.Promise,
    Glob.one `Complexity.Interfaces,
    Glob.one `Complexity.Reductions,
    Glob.one `Models.Model_GapMCSP,
    Glob.one `Models.Model_SparseNP,
    Glob.one `LowerBounds.LB_Formulas,
    Glob.one `LowerBounds.AntiChecker,
    Glob.one `LowerBounds.LB_Formulas_Core,
    Glob.one `LowerBounds.LB_LocalCircuits,
    Glob.one `LowerBounds.LB_GeneralFromLocal,
    Glob.one `Magnification.LocalityInterfaces,
    Glob.one `Magnification.Facts_Magnification,
    Glob.one `Magnification.PipelineStatements,
    Glob.one `Magnification.LocalityLift,
    Glob.one `Magnification.Bridge_to_Magnification,
    Glob.one `Magnification.FinalResult,
    Glob.one `ThirdPartyFacts.Facts_Switching,
    Glob.one `ThirdPartyFacts.LocalityLift,
    Glob.one `ThirdPartyFacts.PsubsetPpoly,
    Glob.one `ThirdPartyFacts.LeafBudget,
    Glob.one `Tests.AxiomsAudit,
    Glob.one `Tests.SmokeTests,
    Glob.one `Tests.UnitTests
  ]

@[test_driver]
lean_exe test where
  root := `Tests.TestDriver
  srcDir := "pnp3"
