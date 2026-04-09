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
  (hNPDag : NP_not_subset_PpolyDAG)
```

Reality split:

1. `hNPDag` is the real remaining DAG-separation blocker.
2. `hMag` remains in the signature only as compatibility context.

## Single active closure route (current policy)

Only one route is considered active for internal DAG separation:

1. prove one **asymptotic/eventual** source theorem on a non-vacuous surface
   (eventual quantification + length-local bridge assumptions),
2. discharge one weak-route class-level theorem payload
   (`...acceptedFamily...` or `...promiseYes...`),
3. feed that payload through existing endpoint wrappers to internalize
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`,
4. then remove external `hNPDag` from the public final theorem,
5. then remove residual `hMag` to reach zero-argument `P_ne_NP`.

## Repository-Wide Honesty Policy

Any file claiming unconditional `P ≠ NP` before both of the following are
internalized is inaccurate:

1. internal DAG separation theorem;
2. zero-argument public final API.
