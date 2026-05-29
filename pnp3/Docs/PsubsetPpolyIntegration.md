# `P ⊆ P/poly` status in `pnp3`

Scope note:
for unconditional `P ≠ NP` blockers see
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

Update note (2026-04-03):
this file is inclusion-only and should not be read as the current global status
of the DAG-separation or final-theorem layers.

## Current state

`pnp3` no longer depends on the external package `Facts/PsubsetPpoly`.
The constructive inclusion `P ⊆ P/poly` used by the main pipeline is now
internalized.  The pieces are:

Model and classes (definitions only):
- `pnp3/Complexity/PsubsetPpolyInternal/Bitstring.lean` — bitstrings;
- `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` — the TM model;
- `pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean` — `P`
  (`polyTimeDecider`);
- `pnp3/Complexity/Interfaces.lean` — the canonical non-uniform class
  `PpolyDAG` and `P_subset_PpolyDAG`.

The constructive inclusion proof itself:
- `pnp3/Complexity/PsubsetPpolyInternal/{StraightLine,StraightLineSemantics,
  StraightLineBuilder,CircuitTree,TreeToStraight,Simulation}.lean`;
- `pnp3/Complexity/{PpolyDAG_StraightLineCore,PpolyDAG_from_StraightLine,
  PsubsetPpolyDAG_Internal}.lean`;
- `pnp3/Complexity/Simulation/{TM_Encoding,Circuit_Compiler}.lean`.

No-arg endpoint:
- `Complexity.Simulation.proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.

(The `PsubsetPpolyInternal/GapMCSPVerifier.lean` file and the
`PsubsetPpolyInternal/TuringToolkit/` directory are **not** part of this
inclusion proof; they are separate NP-verifier scaffolding.)

## Build workflow

Use the standard repository build (from the repository root):

```bash
lake build PnP3 Pnp4
```

No separate build of `Facts/PsubsetPpoly` is required.
