# Checklist: Unconditional Constructive `P ≠ NP`

Updated: 2026-03-14

This is the canonical checklist for what blocks an unconditional in-repo
constructive theorem `P ≠ NP`.

For the current interim release posture (what can be shipped now without
overclaiming), see `RELEASE_RC.md`.

## Current final API (actual code)

File: `pnp3/Magnification/FinalResult.lean`

- `NP_not_subset_PpolyFormula_final*`
- `NP_not_subset_PpolyReal_final*`
- `P_ne_NP_final*`
- asymptotic NP bridge helpers:
  `AsymptoticNPPullback`,
  `asymptoticNPPullback_of_tmWitness`

## Unconditional blockers (must be internalized)

Active DAG endpoint `P_ne_NP_final` currently requires:

1. `NP_not_subset_PpolyDAG` (`hNPDag`)

Default contradiction step to `P ≠ NP` still depends on (1) above.

Until this DAG blocker set is fully discharged internally, the repository does
not contain an unconditional theorem `P ≠ NP`.

## Inclusion-side sub-checklist (default route)

Current code has closed:

1. `stepCompiledLinearCandidateStepSpecProvider_internal`
2. `compiledRuntimeCircuitSizeBoundLinear_internal`
3. `compiledRuntimeAcceptCorrectnessLinear_internal`
4. `compiledAcceptOutputWireAgreementLinear_internal`
5. no-arg inclusion theorem
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`

Inclusion-side integration status:

1. Default `P_ne_NP_final*` wrappers are already switched to
   `proved_P_subset_PpolyDAG_internal`.
2. Compatibility wrappers with explicit contract bundles are intentionally kept.

## Proof-quality safety checks

Before deleting routes/assumptions, confirm:

1. `./scripts/check.sh` passes.
2. `pnp3/Tests/AxiomsAudit.lean` remains in expected shape.
3. Current audit/regression tests pass:
   `pnp3/Tests/AxiomsAudit.lean`,
   `pnp3/Tests/BarrierAudit.lean`,
   `pnp3/Tests/BarrierBypassAudit.lean`,
   `pnp3/Tests/BridgeLocalityRegression.lean`.
4. Final endpoints above still compile and are reachable.
5. No document claims unconditional `P ≠ NP` prematurely.

## Definition of done (in-repo unconditional status)

All of the following must hold at once:

1. A theorem `P_ne_NP` is derivable without external bridge/provider hypotheses.
2. `P_ne_NP_final*` wrappers no longer require external
   `PsubsetPpolyInternalContracts*` inputs. (closed)
3. `P_ne_NP_final*` wrappers no longer require external
   `NP_not_subset_PpolyDAG` input.
4. Remaining final-route compatibility assumptions are either proved in-repo
   or removed from default endpoints.
5. `README.md`, `STATUS.md`, `TODO.md`, `AXIOMS_FINAL_LIST.md` are updated to
   state unconditional status explicitly and consistently.
