# Fact: `P ⊆ P/poly`

This directory is a standalone Lake package exposing only the definitions and
lemmas necessary to formalise the classical inclusion of polynomial-time
languages into non-uniform polynomial size.  The development is self-contained
and designed to be imported directly into other projects without any historical
baggage.

## Layout

- `Proof/Bitstring.lean` — minimal terminology for Boolean cubes.
- `Proof/Circuit/` — inductive and straight-line circuit interfaces together with the combinators used in the simulation.
- `Proof/Turing/Encoding.lean` — the single-tape deterministic machine model.
- `Proof/Simulation/Configuration.lean` — tape/head/state indicators and their circuit encodings.
- `Proof/Simulation/Core.lean` — straight-line builders and snapshot machinery for simulating machine steps.
- `Proof/Simulation/Bounds.lean` — polynomial gate bounds and the bundled `InPpoly` witness.
- `Proof/Simulation.lean` — convenience shim re-exporting the layered simulation.
- `Proof/Complexity/` — the class interface and the final bridging theorem.
- `Utils/Nat.lean` — small arithmetic lemmas supporting the size analysis.
- `ExampleProofs/Examples.lean` — executable proofs that instantiate the simulation on concrete machines.

## Using the fact in other projects

Importing `Proof.Complexity.Interfaces` gives direct access to the theorem
`complexity_P_subset_Ppoly`.  All of its dependencies live inside this package,
so downstream developments can rely on the result without pulling in unrelated
infrastructure.  For convenience the module `FactPsubsetPpoly` re-exports both
the core class interface and the final bridge theorem for one-line imports.

## Building the package locally

This directory ships with its own `lean-toolchain`, so running `lake build`
here automatically pins Lean (and the bundled Lake binary) to
`leanprover/lean4:v4.22.0-rc2`.  A typical build session therefore looks like

```bash
cd Facts/PsubsetPpoly
lake build
```

On the very first invocation Lake will clone the Mathlib ecosystem
dependencies declared in `manifest.json` — notably `mathlib4`, `aesop`,
`ProofWidgets4`, and their helper libraries.  The download is sizeable (several
hundred megabytes) and Lake currently prints only a few status lines while the
underlying `git clone` runs, so allow a few minutes for the initial setup.  All
subsequent builds reuse the cached copies stored under `.lake/` and finish
quickly.

After the dependencies are available the usual compilation traces appear.  You
should see Lake unpacking the Mathlib cache and eventually reporting
“`Build completed successfully.`”.

## Testing

The package ships with illustrative tests under `ExampleProofs/Examples.lean`.  They
construct explicit polynomial-time machines (an always-accepting decider and
a one-step first-bit checker) and verify that both languages lie in `P/poly`
via `inPpoly_of_polyBound` as well as the global theorem
`complexity_P_subset_Ppoly`.  Running `lake build` from this directory builds the
library and executes the embedded `#eval` regression checks in
`ExampleProofs/Main.lean`, printing a short report that the simulation machinery
and the final `P ⊆ P/poly` bridge behave as expected on concrete machines.
