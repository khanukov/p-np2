import Lake
open Lake DSL

package fact_psubset_ppoly

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

/--
Standalone library packaging all modules required for the `P ⊆ P/poly`
proof copied from the original `Pnp2` development.
-/
lean_lib FactPsubsetPpoly where
  srcDir := "."
  globs := #[
    Glob.one `Pnp2.Agreement,
    Glob.one `Pnp2.Algorithms.SatCover,
    Glob.one `Pnp2.BoolFunc,
    Glob.one `Pnp2.BoolFunc.Sensitivity,
    Glob.one `Pnp2.BoolFunc.Support,
    Glob.one `Pnp2.Boolcube,
    Glob.one `Pnp2.Circuit.EntropyCover,
    Glob.one `Pnp2.Circuit.Family,
    Glob.one `Pnp2.Circuit.Numeric,
    Glob.one `Pnp2.Circuit.StraightLine,
    Glob.one `Pnp2.CollentropyBasic,
    Glob.one `Pnp2.ComplexityClasses,
    Glob.one `Pnp2.ComplexityClasses.PsubsetPpoly,
    Glob.one `Pnp2.Cover.Bounds,
    Glob.one `Pnp2.Cover.BuildCover,
    Glob.one `Pnp2.Cover.Canonical,
    Glob.one `Pnp2.Cover.CoarseBound,
    Glob.one `Pnp2.Cover.Compute,
    Glob.one `Pnp2.Cover.Lifting,
    Glob.one `Pnp2.Cover.Measure,
    Glob.one `Pnp2.Cover.SubcubeAdapters,
    Glob.one `Pnp2.Cover.Uncovered,
    Glob.one `Pnp2.DecisionTree,
    Glob.one `Pnp2.NP_separation,
    Glob.one `Pnp2.Pnp2,
    Glob.one `Pnp2.PsubsetPpoly,
    Glob.one `Pnp2.Sunflower.Aux,
    Glob.one `Pnp2.Sunflower.RSpread,
    Glob.one `Pnp2.Sunflower.Sunflower,
    Glob.one `Pnp2.TM.Encoding,
    Glob.one `Pnp2.acc_mcsp_sat,
    Glob.one `Pnp2.bound,
    Glob.one `Pnp2.canonical_circuit,
    Glob.one `Pnp2.collentropy,
    Glob.one `Pnp2.cover2,
    Glob.one `Pnp2.cover_numeric,
    Glob.one `Pnp2.cover_size,
    Glob.one `Pnp2.entropy,
    Glob.one `Pnp2.examples,
    Glob.one `Pnp2.family_entropy_cover,
    Glob.one `Pnp2.low_sensitivity,
    Glob.one `Pnp2.low_sensitivity_cover,
    Glob.one `Pnp2.merge_low_sens,
    Glob.one `Pnp2.sat_cover,
    Glob.one `Pnp2.sunflower,
    Glob.one `Pnp2.table_locality,
    Glob.one `FactPsubsetPpoly
  ]
