# PsubsetPpoly Internal Closure TODO (current inclusion-side status)

Дата актуализации: 2026-04-03.

Scope note:
этот файл описывает только inclusion-side (`P ⊆ PpolyDAG`) и не является
источником общего DAG/final-blocker статуса проекта.
Для глобального статуса используйте:
- `/root/p-np2/STATUS.md`
- `/root/p-np2/TODO.md`
- `/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`

## Current route (machine-checked)

Канонический no-arg endpoint:
- `Complexity.Simulation.proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`

Фактическая активная цепочка закрытия:
1. `proved_P_subset_PpolyDAG_internal`
2. `proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts`
3. internal trio:
   `compiledAcceptOutputWireAgreementLinear_internal`,
   `compiledRuntimeCircuitSizeBoundLinear_internal`,
   `compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider (...)`

Именно этот endpoint используется финальным слоем:
- `pnp3/Magnification/FinalResultCore.lean` (default route;
  `FinalResult.lean` остаётся compatibility import path)
- explicit-contract wrappers (`with_provider`, `with_barriers`) используют
  linear contract bundle
  `PsubsetPpolyCompiledRuntimeLinearOutputContracts`
  (без iterated canonical compatibility chain).

## Legacy cleanup status

Удалено из кода (больше не active runtime модель):
- `step = id` ветка (`step`, `runConfig`, `runtimeConfig`, `runtimeConfig_eq_initial`)
- legacy bridge-контракты между `runtimeConfig` и `stepCompiled` в closure path

В `Circuit_Compiler.lean` больше нет отдельного compatibility-слоя
`InternalCompiler/*` и `EvalAgreement`-ветки: active surface сведён к linear-route.

## Residual blocker (outside P ⊆ PpolyDAG closure)

Открытый хвост после закрытия inclusion-side:
- internalization DAG-separation входа `NP_not_subset_PpolyDAG`

Это отдельный слой, не блокирует факт наличия безусловного
`proved_P_subset_PpolyDAG_internal`.

## Audit pointers

Пошаговые машинные проверки собраны в:
- `pnp3/Docs/PsubsetPpoly_AUDITOR_CHECKLIST.md`
