# Project Status (current)

Updated: 2026-03-14

Authoritative checklist: `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release positioning for current tree: `RELEASE_RC.md`.

## Current verified state

- Active `axiom` declarations in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- `./scripts/check.sh` passes (rechecked on 2026-03-14)
- Current audit/regression tests pass (rechecked on 2026-03-14):
  `AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
  `BridgeLocalityRegression`

## Active final theorem surface

File: `pnp3/Magnification/FinalResult.lean`

- `NP_not_subset_PpolyFormula_final*`
- `NP_not_subset_PpolyReal_final*`
- `P_ne_NP_final*`
- asymptotic NP bridge helpers:
  `AsymptoticNPPullback`,
  `asymptoticNPPullback_of_tmWitness`

## Interpretation

- The repository currently formalizes a constructive, axiom-clean,
  AC0/formula pipeline plus conditional DAG final wrappers.
- Final `P ≠ NP` wrappers are conditional.
- The project does not currently contain an unconditional in-repo theorem
  `P ≠ NP`.

## Remaining blockers to unconditional status

Active DAG final wrapper `P_ne_NP_final` requires one external input:

1. `NP_not_subset_PpolyDAG` (`hNPDag`)

Current inclusion-side status:

- No-arg linear output-wire witness is closed:
  `compiledAcceptOutputWireAgreementLinear_internal`.
- No-arg inclusion endpoint is closed:
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- `RuntimeConfigEqStepCompiled` remains open only for legacy bridge routes
  (`runtimeConfig` path with `step = id`), not for the active no-arg linear
  closure.

## Documentation policy

Any file claiming unconditional `P ≠ NP` before these blockers are discharged
is incorrect and must be treated as outdated.
