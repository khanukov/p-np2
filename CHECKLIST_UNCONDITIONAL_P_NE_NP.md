# Checklist: Unconditional Constructive `P ≠ NP`

Updated: 2026-04-03

This is the canonical checklist for what still blocks an unconditional
in-repo theorem `P ≠ NP`.

For the current interim release posture, see `RELEASE_RC.md`.
For the current DAG route plan, see
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.

## Current final API (actual code)

Files:
- compatibility import path: `pnp3/Magnification/FinalResult.lean`
- active implementation surface: `pnp3/Magnification/FinalResultCore.lean`

Current public default theorem:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

Additional honest DAG-facing surfaces already present:

- asymptotic fixed-slice collapse wrappers;
- stable-restriction / source-closure / blocker `_TM` wrappers;
- support-half accepted-family fallback wrappers.

## What is already closed

1. Active `pnp3/` tree is axiom-clean (`axiom = 0`, `sorry/admit = 0`).
2. `./scripts/check.sh` passes on the current tree.
3. Inclusion is internalized via
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
4. The DAG endpoint surface is no longer blocked on plumbing.

## Remaining unconditional blockers

### Blocker A. Internal DAG separation theorem

The repository still lacks an internal theorem

```text
ComplexityInterfaces.NP_not_subset_PpolyDAG
```

This is the real logical blocker behind the current external argument
`hNPDag`.

### Blocker B. Public final API cleanup

Even after Blocker A is solved, the public theorem is not yet fully
assumption-free while it still exposes

```text
hMag : MagnificationAssumptions
```

The current implementation does not consume `hMag`, but the public theorem
still syntactically takes it.

Therefore full unconditionality requires:

1. internal DAG separation, and
2. a zero-argument public final theorem.

## Practical closure routes

### Fastest path to remove `hNPDag`

1. Pick a fixed slice
   `p* := hMag.antiChecker.asymptotic.pAt n hn`.
2. Prove one fixed-slice DAG source theorem, preferably
   `gapPartialMCSP_supportHalfObligation p*`,
   or equivalently `dagRouteBSourceBlocker p*`,
   or otherwise `dag_stableRestriction_producer p*`.
3. Feed that theorem into the already compiled asymptotic fixed-slice wrappers.

### Fastest path to a zero-argument final theorem

1. Choose a concrete fixed slice `p*`.
2. Provide a concrete `GapPartialMCSP_TMWitness p*`.
3. Prove a fixed-slice blocker on `p*`.
4. Route that data through the existing `_TM` final wrappers.

Alternative:

- internalize the magnification-assumption package instead of bypassing it.

## Proof-quality safety checks

Before declaring any blocker closed, confirm:

1. `./scripts/check.sh` passes.
2. Current audit/regression tests pass:
   `pnp3/Tests/AxiomsAudit.lean`,
   `pnp3/Tests/BarrierAudit.lean`,
   `pnp3/Tests/BarrierBypassAudit.lean`,
   `pnp3/Tests/BridgeLocalityRegression.lean`,
   `pnp3/Tests/WeakRouteSurfaceTests.lean`.
3. Final endpoints in `pnp3/Magnification/FinalResultCore.lean`
   (and compatibility import path `FinalResult.lean`) still compile.
4. No document claims unconditional `P ≠ NP` prematurely.

## Definition of done

All of the following must hold at once:

1. The repository proves `ComplexityInterfaces.NP_not_subset_PpolyDAG`
   internally.
2. The public final theorem no longer requires external `hNPDag`.
3. The public final theorem no longer exposes compatibility-only `hMag`.
4. A zero-argument theorem `P_ne_NP` is derivable in the active tree.
5. `README.md`, `STATUS.md`, `TODO.md`, and `AXIOMS_FINAL_LIST.md` are updated
   to state unconditional status explicitly and consistently.
