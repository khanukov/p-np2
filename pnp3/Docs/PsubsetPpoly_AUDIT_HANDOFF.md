# P⊆P/poly internal route — Audit handoff

Last refresh: 2026-04-03.
Status: current for inclusion-side only.

Scope note: this is an inclusion-side handoff.  It does not record the
overall status of DAG separation or of the final `P ≠ NP`.

## 1) Current inclusion-side bottom line

`P ⊆ PpolyDAG` is closed at the active no-arg endpoint:
- `Complexity.Simulation.proved_P_subset_PpolyDAG_internal`

Machine check:
- `lake build` passes;
- `./scripts/check.sh` passes.

## 2) Active proof chain

1. `proved_P_subset_PpolyDAG_internal`
2. `proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts`
3. internal trio:
   `compiledAcceptOutputWireAgreementLinear_internal`,
   `compiledRuntimeCircuitSizeBoundLinear_internal`,
   `compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider (...)`

In the default final wiring:
- `pnp3/Magnification/FinalResultMainline.lean` uses
  `proved_P_subset_PpolyDAG_internal` (inside `P_ne_NP_final_dag_only`);
  `FinalResultCore.lean` aggregates it by import.

In the explicit-wrapper wiring:
- `with_provider` / `with_barriers` use the linear contract bundle
  `PsubsetPpolyCompiledRuntimeLinearOutputContracts`.

## 3) What was removed from the active surface

1. The legacy `step = id` runtime branch
   (`step/runConfig/runtimeConfig/runtimeConfig_eq_initial`).
2. The legacy bridge bus `runtimeConfig ↔ stepCompiled` in the default
   closure path.
3. The legacy / iterated compatibility chain from the active wrapper
   routes.
4. Legacy aliases in `PsubsetPpolyDAG_Internal.lean`.
5. Direct legacy naming in the active conversion route: the active
   entry point is `Complexity.PpolyDAG_from_StraightLine` plus
   `StraightLineAdapter`.

## 4) What remains but does not block inclusion

After closing the inclusion side, a separate external input remains:
- `NP_not_subset_PpolyDAG` (the DAG-separation layer).

This is not a blocker for the fact that
`proved_P_subset_PpolyDAG_internal` is unconditional.

## 5) Audit checks

Operational checklist:
- `pnp3/Docs/PsubsetPpoly_AUDITOR_CHECKLIST.md`

Key extra check on the conversion layer:
- `#print axioms` for
  `StraightLineAdapter.ppolyDAG_of_straightLine_family`,
  `ppolyDAG_of_ppolyStraightLine`,
  `P_subset_PpolyDAG_of_P_subset_PpolyStraightLine`.
