# Release Plan (RC): 2026-03-25

This document defines the recommended release posture for the current state.

## Release type

`RC / milestone`, not final unconditional claim.

## What is included in this RC

1. Default final wrappers `P_ne_NP_final*` no longer require external
   inclusion contracts (`hPpolyContracts` removed from default signatures).
2. Default inclusion side is internalized through
   `Simulation.proved_P_subset_PpolyDAG_internal`.
3. Compatibility wrappers with explicit contract bundles are preserved.
4. Active tree remains axiom-clean (`axiom = 0`, `sorry/admit = 0` in `pnp3/`).
5. Additional DAG wrappers via support-bounds + `DAG → Formula` are exposed,
   but remain conditional bridge endpoints.
6. Additional DAG-native Route-B wrappers are exposed for
   `certificateProvider` / `invariantProvider` source contracts; they remain
   conditional until the strict DAG semantics generator is internalized.

## What is not included

1. Unconditional in-repo theorem `P ≠ NP`.
2. Internalized default source for `NP_not_subset_PpolyDAG`.

Default `P_ne_NP_final` is still conditional on:

1. `hNPDag : NP_not_subset_PpolyDAG`.

## Mandatory public wording for this RC

Use wording equivalent to:

1. "This release internalizes the inclusion side (`P ⊆ PpolyDAG`) for default
   final wrappers."
2. "Final `P ≠ NP` endpoint remains conditional on explicit DAG-separation
   assumption `NP_not_subset_PpolyDAG`."
3. "No unconditional `P ≠ NP` claim is made in this release."

## Release checklist

Run and archive outputs for:

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean; do
  lake env lean "$f"
done
```

Confirm signatures in:

- `pnp3/Magnification/FinalResult.lean`
- `pnp3/Tests/BridgeLocalityRegression.lean`

Confirm docs are aligned:

- `README.md`
- `README_PUBLICATION.md`
- `STATUS.md`
- `TODO.md`
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`

## Post-release full-path plan

1. Internalize `NP_not_subset_PpolyDAG` default route.
2. Remove remaining default external assumptions from final `P ≠ NP` route.
3. Only then switch repository-wide wording to unconditional status.
