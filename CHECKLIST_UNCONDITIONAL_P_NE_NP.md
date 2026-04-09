# Checklist: Unconditional Constructive `P ≠ NP`

Updated: 2026-04-04

This is the canonical checklist for what still blocks an unconditional
in-repo theorem `P ≠ NP`.

For current release posture, see `RELEASE_RC.md`.
For current DAG route plan, see
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.
For hard route policy lock, see
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

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

## What is already closed

1. Active `pnp3/` tree is axiom-clean (`axiom = 0`, `sorry/admit = 0`).
2. `./scripts/check.sh` passes on current tree.
3. Inclusion is internalized via
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
4. DAG endpoint wiring is closed (wrappers/source-closure plumbing in place).
5. Historical fixed-slice support-half branch is explicitly archived as no-go
   route modules:
   - `FailedRoute_FixedSliceSupportHalfCore.lean`
   - `FailedRoute_FixedSliceSupportHalfImpossible.lean`.

## Remaining unconditional blockers

### Blocker A. Internal DAG separation theorem

Still missing internal theorem:

```text
ComplexityInterfaces.NP_not_subset_PpolyDAG
```

without an external DAG-separation assumption.

### Blocker B. Public final API cleanup

Even after Blocker A, public theorem is not assumption-free while it still
exposes:

```text
hMag : MagnificationAssumptions
```

Therefore full unconditionality requires both:

1. internal DAG separation,
2. zero-argument public final theorem.

## Single active practical route (policy)

Use only asymptotic/eventual theorem route:

1. prove eventual weak-route source theorem (`acceptedFamily` or `promiseYes`),
2. prove/instantiate required length-local bridge,
3. derive class-level contradiction payload,
4. instantiate existing wrappers to get internal
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`,
5. remove external `hNPDag`,
6. remove residual `hMag`.

Do **not** treat literal fixed-slice blocker hunt as active closure route.

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
   (and compatibility path `FinalResult.lean`) still compile.
4. No document claims unconditional `P ≠ NP` prematurely.

## Definition of done

All of the following must hold at once:

1. Repository proves `ComplexityInterfaces.NP_not_subset_PpolyDAG` internally.
2. Public final theorem no longer requires external `hNPDag`.
3. Public final theorem no longer exposes compatibility-only `hMag`.
4. Zero-argument theorem `P_ne_NP` is derivable in active tree.
5. `README.md`, `STATUS.md`, `TODO.md`, and `AXIOMS_FINAL_LIST.md` are updated
   consistently to unconditional wording.
