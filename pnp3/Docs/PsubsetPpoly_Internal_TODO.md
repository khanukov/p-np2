# PsubsetPpoly Internal Closure TODO (current status)

Дата актуализации: 2026-03-14.

## Current route (machine-checked)

Канонический no-arg endpoint:
- `Complexity.Simulation.proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`

Фактическая активная цепочка закрытия:
1. `proved_P_subset_PpolyDAG_internal`
2. `proved_P_subset_PpolyDAG_of_linearOutputAgreementAndLinearStepProvider`
3. `P_subset_PpolyDAG_of_compiledRuntimeLinearContracts`

Именно этот endpoint используется финальным слоем:
- `pnp3/Magnification/FinalResult.lean` (default route)
- explicit-contract wrappers (`with_provider`, `with_barriers`) используют
  linear contract bundle
  `PsubsetPpolyCompiledRuntimeLinearOutputContracts`
  (без iterated canonical compatibility chain).

## Legacy cleanup status

Удалено из кода (больше не active runtime модель):
- `step = id` ветка (`step`, `runConfig`, `runtimeConfig`, `runtimeConfig_eq_initial`)
- legacy bridge-контракты между `runtimeConfig` и `stepCompiled` в closure path

Оставшийся truth-table маршрут в `Circuit_Compiler.lean`:
- сохранён только как compatibility API для explicit-contract wiring
- не используется no-arg endpoint'ом `proved_P_subset_PpolyDAG_internal`

## Residual blocker (outside P ⊆ PpolyDAG closure)

Открытый хвост после закрытия inclusion-side:
- internalization DAG-separation входа `NP_not_subset_PpolyDAG`

Это отдельный слой, не блокирует факт наличия безусловного
`proved_P_subset_PpolyDAG_internal`.

## Audit pointers

Пошаговые машинные проверки собраны в:
- `pnp3/Docs/PsubsetPpoly_AUDITOR_CHECKLIST.md`
