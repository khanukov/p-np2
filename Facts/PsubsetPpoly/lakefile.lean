import Lake
open Lake DSL

package fact_psubset_ppoly

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"

/--
Standalone library packaging just the modules required for the `P ⊆ P/poly`
proof.
-/
lean_lib FactPsubsetPpoly where
  srcDir := "."
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

/--
Auxiliary library that builds the example witnesses and proofs used for
regression testing the `P ⊆ P/poly` development.  Compiling this library allows
the Lean interpreter to load the modules without relying on generated C code.
-/
lean_lib FactPsubsetPpolyExamples where
  srcDir := "."
  globs := #[Glob.submodules `ExampleProofs]

