# Frequently Asked Questions

Updated: 2026-04-03

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
  (hNPDag : NP_not_subset_PpolyDAG)
```

Interpretation:

1. `hNPDag` is the real DAG-separation blocker.
2. `hMag` is still exposed in the public signature, even though the current
   implementation does not consume it.

## Are we currently using GapMCSP or Partial MCSP in active code?

Active code (`pnp3/`) uses **Partial MCSP** (`GapPartialMCSP*` objects).
Legacy GapMCSP material is preserved under `archive/` for provenance only.

## Is the active tree axiom-free in the strictest sense?

No in the absolute metatheoretic sense. Active `pnp3/` has no project-local
`axiom` and no `sorry/admit`, but the audited theorem surface still uses the
standard Lean assumptions:
`propext`, `Classical.choice`, `Quot.sound`.

## What is the current fastest path to remove `hNPDag`?

Prove one fixed-slice DAG source theorem on
`p* := hMag.antiChecker.asymptotic.pAt n hn`,
preferably `gapPartialMCSP_supportHalfObligation p*`,
and then use the already compiled asymptotic fixed-slice wrappers.

## What is the current fastest path to a zero-argument theorem?

Bypass `hMag` entirely:

1. choose a concrete fixed slice `p*`,
2. provide a concrete `GapPartialMCSP_TMWitness p*`,
3. prove a blocker on that slice,
4. use the existing `_TM` final wrappers.

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
