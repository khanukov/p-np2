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
    Glob.one `Counting.CircuitCounting,
    Glob.one `Counting.ShannonCounting,
    Glob.one `Counting.Atlas_to_LB_Core,
    Glob.one `AC0.AC0Formula,
    Glob.one `AC0.AC0FormulaFamily,
    Glob.one `AC0.AC0FormulaWitness,
    Glob.one `AC0.AC0FormulaRestrict,
    Glob.one `AC0.Formulas,
    -- Multi-switching core: include the shared restriction model plus
    -- the canonical trace helper so downstream modules can import it
    -- without missing `.olean` artifacts.
    Glob.one `AC0.MultiSwitching.Restrictions,
    Glob.one `AC0.MultiSwitching.Duality,
    Glob.one `AC0.MultiSwitching.Definitions,
    Glob.one `AC0.MultiSwitching.BadEvents,
    Glob.one `AC0.MultiSwitching.CanonicalTrace,
    Glob.one `AC0.MultiSwitching.CanonicalDT,
    -- Parameter block for Step 3.2 numerics/encodings.
    Glob.one `AC0.MultiSwitching.Params,
    Glob.one `AC0.MultiSwitching.Numerics,
    Glob.one `AC0.MultiSwitching.Trace,
    Glob.one `AC0.MultiSwitching.TraceBridge,
    Glob.one `AC0.MultiSwitching.CommonBad,
    Glob.one `AC0.MultiSwitching.EncodingCommon,
    Glob.one `AC0.MultiSwitching.CommonBad_Func,
    Glob.one `AC0.MultiSwitching.EncodingCommon_Func,
    Glob.one `AC0.MultiSwitching.Decides,
    Glob.one `AC0.MultiSwitching.Atoms,
    Glob.one `AC0.MultiSwitching.IHInterface,
    Glob.one `AC0.MultiSwitching.FuncCNF,
    Glob.one `AC0.MultiSwitching.DecidesAtoms,
    Glob.one `AC0.MultiSwitching.AC0FormulaAtom,
    Glob.one `AC0.MultiSwitching.CommonCCDT_Func,
    Glob.one `AC0.MultiSwitching.CommonCCDT,
    Glob.one `AC0.MultiSwitching.Counting,
    Glob.one `AC0.MultiSwitching.Encoding,
    Glob.one `AC0.MultiSwitching.ShrinkageFromGood,
    Glob.one `AC0.MultiSwitching.Main,
    Glob.one `AC0.MultiSwitching.FullSwitching,
    Glob.one `Complexity.Promise,
    Glob.one `Complexity.Interfaces,
    Glob.one `Complexity.Reductions,
    Glob.one `Models.PartialTruthTable,
    Glob.one `Models.Model_PartialMCSP,
    Glob.one `LowerBounds.LB_Formulas,
    Glob.one `LowerBounds.SolverLocality,
    Glob.one `LowerBounds.MCSPGapLocality,
    Glob.one `LowerBounds.AntiChecker_Partial,
    Glob.one `LowerBounds.LB_Formulas_Core_Partial,
    Glob.one `LowerBounds.LB_LocalCircuits_Partial,
    Glob.one `LowerBounds.LB_GeneralFromLocal_Partial,
    Glob.one `Magnification.LocalityInterfaces_Partial,
    Glob.one `Magnification.Facts_Magnification_Partial,
    Glob.one `Magnification.PipelineStatements_Partial,
    Glob.one `Magnification.LocalityProvider_Partial,
    Glob.one `Magnification.LocalityLift_Partial,
    Glob.one `Magnification.Bridge_to_Magnification_Partial,
    Glob.one `Magnification.FinalResult,
    Glob.one `ThirdPartyFacts.Facts_Switching,
    -- Partial-track bibliography/lemmas used by final magnification result.
    Glob.one `ThirdPartyFacts.PartialTransport,
    Glob.one `ThirdPartyFacts.PartialLocalityLift,
    Glob.one `ThirdPartyFacts.PpolyFormula,
    Glob.one `ThirdPartyFacts.PsubsetPpoly,
    Glob.one `ThirdPartyFacts.LeafBudget,
    Glob.one `Tests.AxiomsAudit,
    Glob.one `Tests.SmokeTests,
    Glob.one `Tests.StructuredLocalityDemo,
    Glob.one `Tests.UnitTests
  ]

@[test_driver]
lean_exe test where
  root := `Tests.TestDriver
  srcDir := "pnp3"
