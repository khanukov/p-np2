# P⊆P/poly Internal Route — Audit Handoff

Дата актуализации: 2026-04-03.
Статус: current for inclusion-side only.

Scope note:
это inclusion-side handoff. Он не фиксирует общий статус DAG-separation или
финального `P ≠ NP`.

## 1) Текущий итог по inclusion-side

`P ⊆ PpolyDAG` закрыт на active no-arg endpoint:
- `Complexity.Simulation.proved_P_subset_PpolyDAG_internal`

Machine-check:
- `lake build` проходит;
- `./scripts/check.sh` проходит.

## 2) Активная цепочка доказательства

1. `proved_P_subset_PpolyDAG_internal`
2. `proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts`
3. internal trio:
   `compiledAcceptOutputWireAgreementLinear_internal`,
   `compiledRuntimeCircuitSizeBoundLinear_internal`,
   `compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider (...)`

В финальном default wiring:
- `pnp3/Magnification/FinalResultCore.lean` использует
  `proved_P_subset_PpolyDAG_internal`.

В explicit-wrapper wiring:
- `with_provider` / `with_barriers` используют linear contract bundle
  `PsubsetPpolyCompiledRuntimeLinearOutputContracts`.

## 3) Что удалено из active surface

1. legacy `step = id` runtime-ветка (`step/runConfig/runtimeConfig/runtimeConfig_eq_initial`).
2. legacy bridge-шина `runtimeConfig ↔ stepCompiled` в default closure path.
3. legacy/iterated compatibility chain из активных wrapper-маршрутов.
4. legacy aliases в `PsubsetPpolyDAG_Internal.lean`.
5. direct legacy naming в active conversion route:
   активный вход — `Complexity.PpolyDAG_from_StraightLine` +
   `StraightLineAdapter`.

## 4) Остаток, который не блокирует inclusion

После закрытия inclusion-side остаётся отдельный внешний вход:
- `NP_not_subset_PpolyDAG` (DAG-separation слой).

Это не является блокером факта наличия безусловного
`proved_P_subset_PpolyDAG_internal`.

## 5) Аудиторские проверки

Операционный чеклист:
- `pnp3/Docs/PsubsetPpoly_AUDITOR_CHECKLIST.md`

Ключевая дополнительная проверка conversion-слоя:
- `#print axioms` для
  `StraightLineAdapter.ppolyDAG_of_straightLine_family`,
  `ppolyDAG_of_ppolyStraightLine`,
  `P_subset_PpolyDAG_of_P_subset_PpolyStraightLine`.
