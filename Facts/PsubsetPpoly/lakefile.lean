import Lake
open Lake DSL

package fact_psubset_ppoly

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

/--
Standalone library packaging just the modules required for the `P ⊆ P/poly`
proof copied from the original `Pnp2` development.
-/
lean_lib FactPsubsetPpoly where
  srcDir := "."
  globs := #[
    Glob.one `Pnp2.BoolFunc,
    Glob.one `Pnp2.Boolcube,
    Glob.one `Pnp2.canonical_circuit,
    Glob.one `Pnp2.Circuit.StraightLine,
    Glob.one `Pnp2.Circuit.Family,
    Glob.one `Pnp2.ComplexityClasses,
    Glob.one `Pnp2.ComplexityClasses.PsubsetPpoly,
    Glob.one `Pnp2.PsubsetPpoly,
    Glob.one `Pnp2.TM.Encoding,
    Glob.one `FactPsubsetPpoly
  ]
