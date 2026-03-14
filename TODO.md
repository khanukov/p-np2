# TODO / Roadmap (current)

Updated: 2026-03-13

Canonical blocker checklist lives in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release checklist/w wording guardrail: `RELEASE_RC.md`.

## Snapshot

- Active `axiom` in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- Baseline checks: `./scripts/check.sh` and `pnp3/Tests/Step10*.lean` pass
- Final API remains conditional (`pnp3/Magnification/FinalResult.lean`)

## What is already closed

1. AC0/formula separation wiring is present and compiles.
2. Internal linear step-spec provider is closed:
   `stepCompiledLinearCandidateStepSpecProvider_internal`.
3. Linear route has closed internal size and correctness witnesses:
   `compiledRuntimeCircuitSizeBoundLinear_internal`,
   `compiledRuntimeAcceptCorrectnessLinear_internal`.
4. Axiom/sorry hygiene is clean in active `pnp3/`.

## What still blocks unconditional `P ≠ NP`

1. Internalize `hNPDag`: `NP_not_subset_PpolyDAG`.

Inclusion-side status:

1. Closed no-arg evaluator/output-wire agreement:
   `compiledAcceptOutputWireAgreementLinear_internal`.
2. Closed no-arg inclusion endpoint:
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
3. Default `P_ne_NP_final*` wiring already consumes this no-arg
   inclusion endpoint.

## Execution order

1. Keep docs honest: no unconditional claim while DAG blockers remain.
2. Close `NP_not_subset_PpolyDAG` internalization on the final route.
3. Only after (2), switch global wording to unconditional.

## Done criteria

1. Final route no longer needs external DAG separation input.
2. `./scripts/check.sh` and Step10 route tests pass unchanged.
3. Top-level docs report unconditional status consistently.
