# Project Status (current)

Updated: 2026-04-04

Authoritative checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.
Current DAG-route plan:
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

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
- Canonical all-slices builders exist from extraction/support budgets into
  witness-easy-density / witness-uniform-lower / witness-transfer-quarter
  debts.
- Support-half accepted-family fallback closure is compiled through
  `noSmallDAG_of_supportHalfBoundFamily` and
  `NP_not_subset_PpolyDAG_surface_of_supportHalfBoundFamily`.

### Fixed-slice no-go status (closed historical branch)

The repository already formalizes that the historical fixed-slice support-half
route is closed as a no-go branch under fixed-slice `PpolyDAG` membership:

- `no_fixedSlice_stableRestriction_of_inPpolyDAG`
- `no_fixedSlice_blocker_of_inPpolyDAG`
- `not_gapPartialMCSP_supportHalfObligation_of_inPpolyDAG`

Interpretation: literal fixed-slice blocker proving is **not** the active path
for unconditional closure.

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
```

Reality split:

1. External class-level DAG separation is no longer an argument of the default
   final theorem.
2. Internal DAG separation is now derived by `NP_not_subset_PpolyDAG_final`.
3. `hMag` remains in the signature as compatibility context.

## Single remaining closure route

Only one route is still active for true unconditionality:

1. keep DAG separation internalized in `NP_not_subset_PpolyDAG_final`,
2. internalize the formula-side / magnification package exposed by
   `NP_not_subset_PpolyFormula_final (hMag : MagnificationAssumptions)`,
3. then remove residual `hMag` to reach zero-argument `P_ne_NP`.

## Repository-Wide Honesty Policy

Any file claiming unconditional `P ≠ NP` before both of the following are
internalized is inaccurate:

1. formula-side / magnification package theorem source;
2. zero-argument public final API.
