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

lean_lib FactPsubsetPpoly where
  srcDir := "Facts/PsubsetPpoly"
  globs := #[
    Glob.one `Utils.Nat,
    Glob.one `Proof.Bitstring,
    Glob.one `Proof.Circuit.Tree,
    Glob.one `Proof.Circuit.StraightLine,
    Glob.one `Proof.Circuit.Family,
    Glob.one `Proof.Turing.Encoding,
    Glob.one `Proof.Complexity.Interfaces,
    Glob.one `Proof.Complexity.PsubsetPpoly,
    Glob.submodules `Proof.Simulation,
    Glob.submodules `ExampleProofs,
    Glob.one `FactPsubsetPpoly
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
    `ThirdPartyFacts.Facts_Switching,
    `ThirdPartyFacts.LeafBudget,
    `Tests.SmokeTests,
    `Tests.UnitTests
  ]

@[test_driver]
lean_exe test where
  root := `Tests.TestDriver
  srcDir := "pnp3"
