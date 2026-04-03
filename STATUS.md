# Project Status (current)

Updated: 2026-04-03

Authoritative checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.
Current DAG-route plan:
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.

## Verified State

- Active `axiom` declarations in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes on the current tree.
- Current audit/regression tests pass on the current tree:
  `AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
  `BridgeLocalityRegression`, `WeakRouteSurfaceTests`.

## What Is Closed

### Inclusion side

- Default inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- Default final wrappers no longer need external inclusion-contract bundles.

### DAG plumbing and endpoint surface

- Route-B source packaging is explicit:
  `dagRouteBSourceBlocker`,
  `DAGRouteBSourceClosure`,
  direct `_TM` final wrappers from stable restriction / source closure /
  blocker.
- Asymptotic fixed-slice collapse wrappers are present:
  `NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse`,
  `..._of_asymptotic_dag_stableRestriction`,
  `..._of_asymptotic_sourceClosure`,
  `..._of_asymptotic_blocker`,
  together with companion `P_ne_NP_final_of_*` wrappers.
- Canonical witness-density hardwire coverage is closed, including
  `canonicalEasyFamilyRealizesAllPatternsUpTo_of_hardwireCircuitBound`.
- Canonical all-slices builders now exist from extraction/support budgets into
  witness-easy-density / witness-uniform-lower / witness-transfer-quarter
  debts.
- Support-half fallback closure is compiled through accepted-family surfaces:
  `noSmallDAG_of_supportHalfBoundFamily` and
  `NP_not_subset_PpolyDAG_surface_of_supportHalfBoundFamily`.

## What Is Still Open

### DAG-side theorem debt

There is still no internal theorem

```text
ComplexityInterfaces.NP_not_subset_PpolyDAG
```

derived without an external DAG hypothesis.

### Final public API debt

The current default final wrapper is still

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

The important reality split is:

1. `hNPDag` is the real remaining DAG-separation blocker.
2. `hMag` remains in the signature only as compatibility context; the current
   implementation does not consume it.

So the repo is not yet unconditional either in the DAG theorem layer or in the
default public final API.

## Best Current Closure Order

### 1. Fastest path to remove `hNPDag` from the `hMag`-based final route

Use one fixed slice
`p* := hMag.antiChecker.asymptotic.pAt n hn`
and prove a fixed-slice source theorem, preferably:

- `gapPartialMCSP_supportHalfObligation p*`,
- or equivalently `dagRouteBSourceBlocker p*`,
- or otherwise `dag_stableRestriction_producer p*`.

This is now the shortest honest route because the asymptotic collapse wrappers
are already compiled.

### 2. Path to full unconditionality

Removing `hNPDag` from the current compatibility theorem is not the same as
producing a zero-argument theorem.

For full unconditionality, one of the following must still happen:

- bypass `hMag` with a concrete fixed slice `p*`, a concrete
  `GapPartialMCSP_TMWitness p*`, and a fixed-slice blocker fed into the `_TM`
  wrappers; or
- internalize the magnification-assumption package itself.

## Research Tracks

### Track A: fixed-slice integration route

This is the practical near-term route for current public API cleanup.
It uses the already existing asymptotic fixed-slice collapse wrappers and needs
only one fixed-slice DAG theorem.

### Track B: canonical all-slices witness route

The codebase already contains:

- `canonical_smallDAG_witnessEasyDensity_source_on_slices`,
- `canonical_smallDAG_witnessUniformLower_source_on_slices`,
- `canonical_smallDAG_witnessTransferQuarter_source_on_slices`,
- and compilers from support/extraction budgets into those debts.

This remains a legitimate theorem program for a standalone internal
`NP_not_subset_PpolyDAG`, but it is not the shortest current path to cleaning
up the existing final API.

### Track C: restricted-model fallback

Support-half and related restricted-model closures are now useful because they
already terminate at class-level non-inclusion surfaces. They are no longer
mere diagnostics.

## Repository-Wide Honesty Policy

Any file claiming unconditional `P ≠ NP` before the DAG theorem and the final
public API are both internalized is inaccurate.
