# PsubsetPpoly Internal Closure TODO (single-pass runbook)

Цель: довести внутреннее доказательство `P ⊆ P/poly` в `pnp3` до состояния,
где финальный DAG-трек опирается только на внутренние доказанные узлы,
а не на временные контрактные гипотезы.

Рабочий deep-dive runbook по закрытию legacy bridge-узлов:
`pnp3/Docs/PsubsetPpolyDAG_Closure_Strategy.md`.

Runbook по закрытию compiled-runtime size блока:
`pnp3/Docs/CompiledRuntime_SizeClosure_Runbook.md`.

## Update (2026-03-03): external-audit freeze (proof paused)

Этот документ обновлён как freeze-point перед внешним аудитом.
Дальнейшее продвижение доказательства в этом проходе остановлено намеренно.

### Что зафиксировано новым кодом (последние коммиты)

- `21dfd13` — `feat: add linear-runtime DAG closure contract track`
  - добавлены linear-контракты:
    - `CompiledAcceptCircuitEvalAgreementLinear`
    - `CompiledRuntimeAcceptCorrectnessLinear`
    - `PsubsetPpolyCompiledRuntimeLinearContracts`
  - добавлен linear DAG-route:
    - `P_subset_PpolyDAG_of_compiledRuntimeLinearContracts`
    - `proved_P_subset_PpolyDAG_of_compiledRuntimeLinearContracts`

- `a6313f1` — `feat: bridge eval agreement for linear compiled-runtime route`
  - добавлен мост:
    - `compiledAcceptEvalAgreementLinear_of_evalAgreement`
    - `proved_P_subset_PpolyDAG_of_evalAgreementAndCompiledRuntimeLinear`

- `f3df23b` — `feat: add linear-semantics to DAG inclusion bridge`
  - добавлен мост от one-step linear semantics:
    - `compiledRuntimeAcceptCorrectnessLinear_of_linearSemantics`
    - `proved_P_subset_PpolyDAG_of_evalAgreementAndLinearSemantics`

### Что это значит по блокерам

- `CompiledRuntimeCircuitSizeBoundLinear_internal` закрыт и используется.
- Архитектурно route теперь сводится к содержательной семантической точке:
  - доказать `StepCompiledLinearCandidateSemantics` (или эквивалентный
    one-step `Spec` для linear switch-point).
- После этого линейный DAG-route замыкается почти механически через уже
  добавленные мосты.

### Текущее решение: не продолжать proof до внешнего аудита

- В этом проходе сознательно **не** продолжали закрывать
  `StepCompiledLinearCandidateSemantics`.
- Цель: отдать аудиторам точный срез и получить независимую верификацию
  выбранной стратегии дожатия.

## Update (2026-03-02): verified current blocker

- Default DAG-route уже переведён на runtime-only контракт:
  `PsubsetPpolyInternalContracts = RuntimeSpecProvider`.
- Global `EvalAgreement` и `RuntimeConfigEqStepCompiled` больше не блокируют
  default-route; они остались только в legacy/bridged ветках.
- Главный оставшийся блокер для fully no-arg closure:
  нет закрытого `RuntimeSpecProvider` в текущей `runtimeConfig`-форме.
  Формально это видно по тому, что `runtimeConfig` сейчас сводится к
  `initialStraightConfig` (через `step = id`), тогда как целевая спецификация
  требует соответствие `TM.run`.
- Для полного закрытия без внешних входов нужен runtime-layer refactor:
  canonical runtime через iterated `stepCompiled` + совместимый polynomial
  size-bound route для acceptance circuit.
- В код уже добавлен промежуточный compiled-runtime маршрут:
  `P_subset_PpolyDAG_of_compiledRuntimeContracts`, который сводит остаток к
  двум контрактам минимальной поверхности:
  `CompiledAcceptCircuitEvalAgreement` и `CompiledAcceptCircuitSizeBound`.
- Добавлен публичный bundle-слой для этого маршрута:
  `PsubsetPpolyCompiledRuntimeContracts` +
  `proved_P_subset_PpolyDAG_of_compiledRuntimeContracts`,
  а также интерфейсный endpoint
  `P_subset_PpolyDAG_internal_source_compiledRuntime`.
- Обновлён iterated runtime-only маршрут: `RuntimeConfigEqStepCompiled` убран
  из активного contract surface. Теперь
  `PsubsetPpolyInternalContractsIteratedRuntimeOnly`
  сводится к `(CompiledAcceptOutputWireAgreement ∧ CompiledRuntimeCircuitSizeBound)`.
  Мост `RuntimeConfigEqStepCompiled` остался только в legacy/bridged API.
- Критический size-аудит: текущая форма `stepCompiled` (через
  `toTreeWire -> compileTree/packFin`) с `ConfigCircuits.stepCircuits`
  на базе `truthTableCircuit` не даёт замкнуть внутренний polynomial witness
  для `CompiledRuntimeCircuitSizeBound` без рефактора шага.

## Краткий статус: что уже закрыли и что по плану осталось

Чтобы не терять нить, фиксируем состояние в самом коротком формате.

### Закрыли в этой ветке
- ✅ Финальный слой (`Magnification/FinalResult.lean`, `Barrier/Bypass.lean`) переключён
  на bundle-контракт `hPpolyContracts`, без прямого `hCompiler`/`hEvalAgree`.
- ✅ Добавлен и используется пакет внутренних контрактов
  (`PsubsetPpolyInternalContracts`) и мостики до `P_subset_PpolyDAG`.
- ✅ Разбита append-right обязанность на более управляемый уровень:
  введён gate-level контракт `AppendGateRightSemantics` и сборщик
  `appendWireSemantics_of_gateContracts`.
- ✅ Добавлены вспомогательные transport/index-леммы для стабилизации доказательств
  по `Fin`/cast в `StraightLine` и `TreeToStraight`.

### Осталось по плану (критический минимум)
- ⏳ Полностью закрыть `appendWireSemantics.right` (не только через контрактную
  декомпозицию, но и финальным безусловным доказательством).
- ⏳ Довести до конца `compileTreeWireSemantics`.
- ⏳ Собрать безусловный witness `StepCompiledContracts`.
- ⏳ Провести size-архитектурный рефактор compiled-runtime шага
  (`stepCompiledLinear`, DAG-preserving append-only assembly) и закрыть
  `CompiledRuntimeCircuitSizeBound` внутренним witness.
- ⏳ Получить закрытый `runtimeSpecProvider_internal` и затем
  безпараметрический `polyTMToStraightLineCompiler_internal`.
- ⏳ Финально переключить интерфейсный default-route на internal source как
  основной канал (без legacy/fallback как главного пути).

---

## 1) Что уже сделано (перепроверено по коду)

### ✅ Финальный слой уже переведён на bundle-контракт (без `hCompiler`)
- В `Magnification/FinalResult.lean` финальные DAG-wrapper’ы используют
  `hPpolyContracts : PsubsetPpolyInternalContracts`, а включение `P ⊆ PpolyDAG`
  берётся через `proved_P_subset_PpolyDAG_of_contracts`.
- В `Barrier/Bypass.lean` `P_ne_NP_final_with_barriers` тоже принимает
  `hPpolyContracts` и не принимает `hCompiler`.

### ✅ В `StraightLine` добавлены анти-`Fin` helper’ы
- Есть `toCircuitWireOf`, `evalWireOf`, `wireOf_eq` — это уже правильный паттерн
  для локализации зависимых разветвлений по `Fin (n + g)`.

### ✅ Pre-assembly для внутреннего `P ⊆ PpolyDAG` уже есть
- В `Simulation/Circuit_Compiler.lean` есть:
  - `polyTMToStraightLineCompiler_of_runtimeSpec`
  - `polyTMToStraightLineCompiler_internal` (пока с параметром `hRuntime`)
  - `P_subset_PpolyDAG_of_runtimeSpec`
  - `P_subset_PpolyDAG_of_stepSpec`
  - `PsubsetPpolyInternalContracts`
  - `proved_P_subset_PpolyDAG_of_contracts`

---

## 2) Что ещё НЕ закрыто (реальные блокеры)

### 🔴 Блокер A: нет внутреннего безусловного witness для `StepCompiledContracts`
Сейчас `StepCompiledContracts` определён, но в TODO-цепочке всё ещё требуется
внутреннее (без внешних гипотез) построение:
- `AppendWireSemantics` (особенно `right` ветка),
- `CompileTreeWireSemantics`,
- затем их упаковка в `StepCompiledContracts`.

### 🔴 Блокер B: `polyTMToStraightLineCompiler_internal` всё ещё параметризован
Сейчас это:
- `polyTMToStraightLineCompiler_internal (hRuntime : RuntimeSpecProvider) : ...`

Нужна финальная константа **без параметров** (или эквивалентный закрытый theorem),
чтобы шаг 10 считался полностью закрытым.

### 🟡 Блокер C: интерфейсный switch на «внутренний источник по умолчанию»
Даже при наличии контрактного closure нужно окончательно переключить интеграционные
точки (интерфейсы/статус-документацию), чтобы маршрут не зависел от legacy/fallback
как от основного источника.

---

## 3) Чёткий пошаговый план «в один проход»

Ниже — последовательность, которую можно запускать линейно, без развилок.

### Шаг 0. Базовая валидация перед изменениями
1. `lake build`
2. Зафиксировать, что текущее состояние зелёное по build (warnings допустимы).

### Шаг 1. Закрыть `AppendWireSemantics.right` в `TreeToStraight.lean`
1. Добавить локальные леммы для `liftWireIntoAppend` на уровне `evalWireAux`/`evalGateAux`.
2. Доказать правую ветку append-семантики.
3. Собрать финальный theorem:
   - `appendWireSemantics : AppendWireSemantics := ⟨left, right⟩`
4. Проверка:
   - `lake build pnp3/Complexity/PsubsetPpolyInternal/TreeToStraight.lean`

### Шаг 2. Закрыть `CompileTreeWireSemantics`
1. Довести структурную индукцию по `Boolcube.Circuit`.
2. Использовать уже существующие helper’ы:
   - `toCircuitWireOf`, `evalWireOf`, `wireOf_eq`,
   - sematics-леммы для `snoc`/append.
3. Получить theorem:
   - `compileTreeWireSemantics : CompileTreeWireSemantics`
4. Проверка:
   - `lake build pnp3/Complexity/PsubsetPpolyInternal/StraightLineSemantics.lean`
   - `lake build pnp3/Complexity/PsubsetPpolyInternal/TreeToStraight.lean`

### Шаг 3. Закрыть внутренний witness `StepCompiledContracts`
1. В `Simulation/Circuit_Compiler.lean` (или ближайшем internal-модуле)
   собрать безусловный witness:
   - `stepCompiledContracts_internal : StepCompiledContracts`
   из `compileTreeWireSemantics` + `appendWireSemantics`.
2. Проверка:
   - `lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean`

### Шаг 4. Закрыть `RuntimeSpecProvider` из внутренних контрактов
1. Использовать уже готовые:
   - `stepCompiledSemanticsProvider_of_contracts`,
   - `runtimeSpec_of_stepCompiledSemantics` / `runtimeSpec_of_stepCompiledContracts`.
2. Получить безусловный:
   - `runtimeSpecProvider_internal : RuntimeSpecProvider`
3. Проверка:
   - `lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean`

### Шаг 5. Сделать безпараметрический компилятор
1. Ввести финальный символ:
   - `polyTMToStraightLineCompiler_internal : PolyTMToStraightLineCompiler`
   без входного `hRuntime`.
2. Реализовать его через
   `polyTMToStraightLineCompiler_of_runtimeSpec runtimeSpecProvider_internal`.
3. Проверка:
   - `lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean`

### Шаг 6. Закрыть внутреннее `P_subset_PpolyDAG` без контрактных аргументов
1. Добавить theorem:
   - `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`
2. Реализация: через
   `P_subset_PpolyDAG_of_compiler polyTMToStraightLineCompiler_internal` + `EvalAgreement`.
3. Если `EvalAgreement` ещё параметризован — аналогично закрыть его внутренним witness’ом
   (или отдельным подшагом 6.a перед 6).
4. Проверка:
   - `lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean`

### Шаг 7. Переключить финальные wrapper’ы на внутренний theorem (опционально в том же PR)
1. В `FinalResult.lean` и `Barrier/Bypass.lean` заменить контрактный вход
   там, где политика проекта уже разрешает, на внутренний theorem из шага 6.
2. Если проект пока хочет держать контрактный API для обратной совместимости:
   - оставить публичный API,
   - добавить внутренние overload/theorem без параметров.
3. Проверка:
   - `lake build Magnification.FinalResult Barrier.Bypass`

### Шаг 8. Финальный аудит «одним запуском»
1. `lake build`
2. `./scripts/check.sh` (если скрипт присутствует и исполняем)
3. Проверить аксиомный аудит модулей (`Tests/AxiomsAudit.lean`, `Tests/BarrierAudit.lean`)
   через общий `lake build`.
4. Зафиксировать итог в этом файле (обновить статусы).

---

## 4) Definition of Done (чёткие критерии закрытия)

Считаем задачу закрытой, когда одновременно выполнено:

1. Существует **безпараметрический**
   `polyTMToStraightLineCompiler_internal : PolyTMToStraightLineCompiler`.
2. Существует **безпараметрический**
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG` (или эквивалентный theorem).
3. `lake build` полностью проходит.
4. Финальный DAG-layer не требует `hCompiler` (уже выполнено) и,
   по принятой политике, либо:
   - продолжает поддерживать совместимый контрактный API,
   - либо полностью переключён на внутренний theorem.

---

## 5) Короткий операционный чек-лист (copy/paste)

- [ ] `lake build`
- [x] Закрыт `AppendWireSemantics.right`
- [x] Закрыт `CompileTreeWireSemantics`
- [x] Получен `stepCompiledContracts_internal`
- [ ] Получен `runtimeSpecProvider_internal`
- [ ] Получен безпараметрический `polyTMToStraightLineCompiler_internal`
- [ ] Получен `proved_P_subset_PpolyDAG_internal`
- [ ] `lake build Magnification.FinalResult Barrier.Bypass`
- [ ] `lake build`
- [ ] (опц.) `./scripts/check.sh`
- [ ] Статусы в этом файле обновлены до фактических


---

## 6) Execution status (latest pass)

Run date: 2026-03-01 (agent pass)

Audit handoff snapshot: `pnp3/Docs/PsubsetPpoly_AUDIT_HANDOFF.md`.

Checklist from active task:
- [x] **A1** `appendWireSemantics_right + appendWireSemantics`
- [x] **A1.1** декомпозиция правой ветки на gate-level контракт (`AppendGateRightSemantics`) + сборка (`appendWireSemantics_of_gateContracts`)
- [x] **A1.2** закрыт transport-heavy узел правой gate-ветки:
      `evalGateAux_append_right` через нормальные формы + `HEq/cast`-леммы
- [x] **A2** `compileTreeWireSemantics` закрыт (безусловная теорема)
- [x] **A3** закрыт: собран `stepCompiledContracts_internal`
      (без входных контрактов)
- [ ] **B1** `runtimeSpecProvider_internal` (not closed)
- [x] **B1.iterated** `runtimeSpecProvider_internal_iterated` (closed)
- [x] **B1.1** runtime-spec сборка из split-контрактов:
      `runtimeSpec_of_splitContracts`
- [x] **B1.2.partial** добавлен публичный bridge
      `stepCompiledSemanticsProvider_of_appendGateRight`
- [x] **B1.3** добавлен формальный мост
      `runtimeSpecProvider_of_iterated_eq` + internal iterator witness
      `runtimeSpecProviderIterated_internal`
- [ ] **B2** `polyTMToStraightLineCompiler_internal` без аргументов + `proved_P_subset_PpolyDAG`
- [x] **B2.iterated-bridged** добавлен closure-route:
      `proved_P_subset_PpolyDAG_of_iteratedContractsBridged`
- [x] **C1** internal-source интерфейсный слой закрыт через
      `Complexity/Interfaces_InternalSource.lean` (без циклов импортов)
- [x] **C1.partial** добавлены iterated-bridged финальные wrapper’ы
      в `Magnification.FinalResult` и `Barrier.Bypass`
- [x] **C1.1** добавлены explicit internal-source endpoints:
      `P_ne_NP_final_internal_source`,
      `P_ne_NP_final_with_barriers_internal_source`
- [x] **D1** `lake build + scripts/check.sh + targeted builds`
- [x] TODO обновлён по факту

### Короткий отчёт по пунктам (текущий проход)
Сделано:
1. В `TreeToStraight.lean` добавлены транспортные леммы для зависимых cast:
   `Circuit.gate_heq`, `cast_liftOp_eq`, `append_gate_right_eq_lift`.
2. Закрыт узел `evalGateAux_append_right` (локальные переписывания вместо
   глобального `simp` в проблемных местах с `Fin`-индексами).
3. Закрыт контракт `appendGateRightSemantics`.
4. Подтверждена сборка:
   `lake build pnp3/Complexity/PsubsetPpolyInternal/TreeToStraight.lean`.

Осталось:
1. Закрыть B1/B2 в безусловной форме: получить `RuntimeSpecProvider` и
   `polyTMToStraightLineCompiler_internal` без входных гипотез.
2. (опц.) унифицировать naming/exports между `Complexity.Interfaces` и
   `Complexity.Interfaces_InternalSource` (технический polish, не блокер).

### Что реально подтверждено в этом проходе
1. Полный CI-скрипт прошёл: `./scripts/check.sh` (включая full build, smoke, hygiene, audits).
2. Targeted build прошёл: `lake build Magnification.FinalResult Barrier.Bypass`.
3. Репозиторий остаётся в зелёном состоянии без новых дыр (`sorry/admit`) и без `native_decide`.
4. Вынесен отдельный gate-level контракт `AppendGateRightSemantics` и сборщик
   `appendWireSemantics_of_gateContracts`, что закрывает декомпозицию шага A1
   (подшаг «локальные леммы/интерфейсы для правой ветки append»).
5. Закрыт assembly-подшаг B1.1: добавлен theorem
   `runtimeSpec_of_splitContracts`, который поднимает split-контракты
   (`CompileTreeWireSemantics ∧ AppendGateRightSemantics`) до runtime-spec
   итерации `stepCompiled`.


### Диагностика и статус блокера по right-ветке

Блокер на уровне `evalGateAux_append_right` закрыт в этом проходе:

- устранён разрыв между
  `C₂.gate ⟨C₁.gates + j - C₁.gates, _⟩` и `C₂.gate ⟨j, hj⟩`
  через `HEq`-транспорт (`Circuit.gate_heq`) и cast-элиминацию (`cast_liftOp_eq`);
- нормализация правой gate-ветки зафиксирована в `append_gate_right_eq_lift`;
- после этого `evalGateAux_append_right` и `appendGateRightSemantics` собираются без `sorry`.

Оставшийся blocker сместился на assembly B1/B2:
- A1 и A2 закрыты безусловными теоремами в `TreeToStraight.lean`;
- A3 закрыт: добавлен `stepCompiledContracts_internal` в `Circuit_Compiler.lean`;
- следующий линейный шаг: мост от `runtimeSpec_iterated_internal` к форме
  `RuntimeSpecProvider` (т.е. к `StraightConfig.runtimeConfig`) через лемму
  равенства конфигураций
  `runtimeConfig M n = Nat.iterate (stepCompiled M) (M.runTime n) (initialStraightConfig M n)`,
  затем безпараметрический компилятор.

Практический статус:
- конструктивно закрыт рабочий runtime-контракт в iterated-форме
  (`RuntimeSpecProviderIterated`);
- legacy-форма `RuntimeSpecProvider` остаётся открытой только из-за
  bridge-леммы равенства конфигураций.
- добавлен bundled iterated-bridged DAG closure:
  `PsubsetPpolyInternalContractsIteratedBridged ->
   proved_P_subset_PpolyDAG_of_iteratedContractsBridged`.
- финальные слои уже имеют internal-source wrapper’ы; оставшийся кусок C1 —
  закрыт отдельным интерфейсным модулем без нарушения import-графа.



### Attempt log: focused A1 transport refactor (resolved for gate-level)

Что сделано в `TreeToStraight.lean`:
- добавлен слой transport/cast-лемм для зависимых индексов;
- через этот слой закрыт `evalGateAux_append_right`;
- закрыт `appendGateRightSemantics`;
- добавлены безусловные сборки:
  `appendWireSemantics` и `compileTreeWireSemantics`;
- файл собирается локально без `sorry`.

Что дополнительно сделано в `Circuit_Compiler.lean`:
- добавлен `stepCompiledContracts_internal : StepCompiledContracts`;
- добавлен `stepCompiledSemanticsProvider_internal : StepCompiledSemanticsProvider`;
- добавлен `runtimeSpec_iterated_internal` (закрытая iterated-формулировка runtime-spec).

Решение для следующего прохода:
1. Сформировать `stepCompiledContracts_internal` из уже закрытых
   `compileTreeWireSemantics` и `appendWireSemantics`.
2. Поднять его до `runtimeSpecProvider_internal`.
3. Закрыть безпараметрический `polyTMToStraightLineCompiler_internal`.


### Следующий технический под-план (точечно)
1. Собрать closed witness `StepCompiledContracts` (без входных контрактов).
2. Поднять до closed `runtimeSpecProvider_internal`.
3. Перейти к закрытию B2 и C1.

### Commit refs
- Gate-right closure commit: `4f3b6ec`
- Earlier prep commits: `a0708cf`, `2de8a37`, `59b02af`, `2a5a942`
