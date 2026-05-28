# PsubsetPpoly internal closure TODO (current inclusion-side status)

Last refresh: 2026-04-03.

Scope note: this file covers only the inclusion side (`P ⊆ PpolyDAG`)
and is not the source of the overall DAG / final-blocker status.

For the global status use:
- `/root/p-np2/STATUS.md`
- `/root/p-np2/TODO.md`
- `/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`

## Current route (machine-checked)

Canonical no-arg endpoint:
- `Complexity.Simulation.proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`

The active closure chain:
1. `proved_P_subset_PpolyDAG_internal`
2. `proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts`
3. internal trio:
   `compiledAcceptOutputWireAgreementLinear_internal`,
   `compiledRuntimeCircuitSizeBoundLinear_internal`,
   `compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider (...)`

This endpoint is what the final layer uses:
- `pnp3/Magnification/FinalResultCore.lean` (default route;
  `FinalResult.lean` remains a compatibility import path);
- the explicit-contract wrappers (`with_provider`, `with_barriers`)
  use the linear contract bundle
  `PsubsetPpolyCompiledRuntimeLinearOutputContracts`
  (no iterated canonical compatibility chain).

## Legacy cleanup status

Removed from the code (no longer the active runtime model):
- the `step = id` branch
  (`step`, `runConfig`, `runtimeConfig`, `runtimeConfig_eq_initial`);
- the legacy bridge contracts between `runtimeConfig` and
  `stepCompiled` in the closure path.

In `Circuit_Compiler.lean` there is no longer a separate
compatibility layer `InternalCompiler/*` or `EvalAgreement` branch:
the active surface is reduced to the linear route.

## Residual blocker (outside the P ⊆ PpolyDAG closure)

After closing the inclusion side, one tail remains open:
- internalisation of the DAG-separation input `NP_not_subset_PpolyDAG`.

This is a separate layer; it does not block the fact that
`proved_P_subset_PpolyDAG_internal` is unconditional.

## Audit pointers

Step-by-step machine checks are collected in:
- `pnp3/Docs/PsubsetPpoly_AUDITOR_CHECKLIST.md`
