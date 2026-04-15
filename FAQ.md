# Frequently Asked Questions

Updated: 2026-04-15

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current milestone release checklist:
`RELEASE_RC.md`.

## What is currently proved in code?

Active final surface is implemented in
`pnp3/Magnification/FinalResultCore.lean`
(with compatibility import path `pnp3/Magnification/FinalResult.lean`) and
includes:

- `NP_not_subset_PpolyFormula_final*`
- `NP_not_subset_PpolyReal_final*`
- `P_ne_NP_final*`
- asymptotic fixed-slice DAG wrappers
- concrete `_TM` DAG wrappers from source-closure / blocker routes

These compile on the current tree.

## Is unconditional `P ≠ NP` proved here?

No. The repository still does not contain an unconditional in-repo theorem
`P ≠ NP`.

## Conditional on what exactly?

The current public default theorem is:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
```

Interpretation:

1. DAG separation is already internalized on the default path via
   `NP_not_subset_PpolyDAG_final hMag`.
2. `hMag` is the real remaining public blocker.

## Are we currently using GapMCSP or Partial MCSP in active code?

Active code (`pnp3/`) uses **Partial MCSP** (`GapPartialMCSP*` objects).
Legacy GapMCSP material is preserved under `archive/` for provenance only.

## Is the active tree axiom-free in the strictest sense?

No in the absolute metatheoretic sense. Active `pnp3/` has no project-local
`axiom` and no `sorry/admit`, but the audited theorem surface still uses the
standard Lean assumptions:
`propext`, `Classical.choice`, `Quot.sound`.

## Is `hNPDag` still a blocker?

That step is already done on the default final surface.

`P_ne_NP_final` no longer takes external DAG separation.

## What is the current fastest path to a zero-argument theorem?

Internalize the formula-side package currently exposed by

```text
NP_not_subset_PpolyFormula_final
  (hMag : MagnificationAssumptions)
```

and then remove residual `hMag` from `P_ne_NP_final`.

## Is axiom/sorry hygiene clean?

Yes for active `pnp3/`:

- active global `axiom`: 0
- active `sorry/admit`: 0

Use:

```bash
./scripts/check.sh
```

## How to quickly verify current audit surface?

```bash
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean; do
  lake env lean "$f"
done
```

## Where is the longer route map?

See `PROOF_OVERVIEW.md`.
