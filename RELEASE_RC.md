# Release Plan (RC): 2026-04-03

This document defines the recommended release posture for the current state.

## Release type

`RC / milestone`, not final unconditional claim.

## What is included in this RC

1. Default inclusion side is internalized through
   `Simulation.proved_P_subset_PpolyDAG_internal`.
2. Active tree remains axiom-clean (`axiom = 0`, `sorry/admit = 0` in
   `pnp3/`).
3. Additional DAG-native `_TM` wrappers are exposed from
   stable-restriction / source-closure / blocker surfaces.
4. Additional asymptotic fixed-slice DAG wrappers are exposed:
   `NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse`,
   `..._of_asymptotic_dag_stableRestriction`,
   `..._of_asymptotic_sourceClosure`,
   `..._of_asymptotic_blocker`,
   plus companion `P_ne_NP_final_of_*` wrappers.
5. Support-half fallback now closes downstream to a class-level separation
   surface via `NP_not_subset_PpolyDAG_surface_of_supportHalfBoundFamily`.
6. Canonical witness-density hardwire coverage and all-slices compiler glue are
   present in code.

## What is not included

1. Unconditional in-repo theorem `P ≠ NP`.
2. Internalized default source for `NP_not_subset_PpolyDAG`.
3. A zero-argument public final theorem.

The public default theorem is still:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

Interpretation:

1. `hNPDag` is still the logical blocker.
2. `hMag` remains a compatibility context argument until the public final API
   is cleaned up.

## Mandatory public wording for this RC

Use wording equivalent to:

1. "This release internalizes the inclusion side (`P ⊆ PpolyDAG`) for default
   final wrappers."
2. "The repository now exposes additional honest fixed-slice/asymptotic DAG
   wrappers and fallback DAG surfaces."
3. "Final `P ≠ NP` remains conditional; no unconditional claim is made in this
   release."

## Release checklist

Run and archive outputs for:

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean; do
  lake env lean "$f"
done
```

Confirm signatures in:

- `pnp3/Magnification/FinalResultCore.lean`
- compatibility import path `pnp3/Magnification/FinalResult.lean`
- `pnp3/Tests/WeakRouteSurfaceTests.lean`

Confirm docs are aligned:

- `README.md`
- `README_PUBLICATION.md`
- `STATUS.md`
- `TODO.md`
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`

## Post-RC closure plan

1. Internalize `NP_not_subset_PpolyDAG`.
2. Remove remaining external DAG-separation input from the public final route.
3. Then remove the residual compatibility `hMag` argument from the default
   public theorem surface.
4. Only after that switch repository-wide wording to unconditional status.
