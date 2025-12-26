# Integrating the standalone `P ⊆ P/poly` proof

This note documents how the standalone proof in `Facts/PsubsetPpoly` is now
imported into `pnp3` after resolving the namespace collisions described in the
previous revision of this file.

## Updated integration workflow

1. Build the isolated package to make sure its own copy of the proof compiles:

   ```bash
   cd Facts/PsubsetPpoly
   lake build
   ```

   This succeeds and produces `.olean` files under `Facts/PsubsetPpoly/.lake/`.

2. Return to the repository root and build `PnP3`.  The project now depends on
   the namespaced modules, so a normal build suffices:

   ```bash
   cd /workspace/p-np2
   lake build PnP3
   ```

   The build now succeeds; see the lint warnings emitted by the unrelated
   modules for the usual maintenance backlog, but the `ThirdPartyFacts`
   component successfully links against the namespaced proof.

## What changed

Every declaration in the standalone proof is wrapped in the umbrella namespace
`Facts.PsubsetPpoly`.  This prevents duplicate names such as
`Boolcube.StraightLineCircuit` or `TM` from colliding with their legacy
counterparts from earlier development efforts.  The wrapper module
`pnp3/ThirdPartyFacts/PsubsetPpoly.lean` now imports
`Facts.PsubsetPpoly.FactPsubsetPpoly` directly and re-exports the final theorem
to the rest of the project, keeping the interface aligned with the namespaced
proof.
