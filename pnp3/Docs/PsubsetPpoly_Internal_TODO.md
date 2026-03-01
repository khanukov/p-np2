# PsubsetPpoly Internal Closure TODO (single-pass runbook)

Цель: довести внутреннее доказательство `P ⊆ P/poly` в `pnp3` до состояния,
где финальный DAG-трек опирается только на внутренние доказанные узлы,
а не на временные контрактные гипотезы.

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
- [ ] Закрыт `AppendWireSemantics.right`
- [ ] Закрыт `CompileTreeWireSemantics`
- [ ] Получен `stepCompiledContracts_internal`
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
- [ ] **A1** `appendWireSemantics_right + appendWireSemantics`
- [x] **A1.1** декомпозиция правой ветки на gate-level контракт (`AppendGateRightSemantics`) + сборка (`appendWireSemantics_of_gateContracts`)
- [x] **A2.partial** собран bridge `compileTreeWireSemantics_of_append` и
      `compileTreeWireSemantics_of_gateContracts` (через gate-контракт)
- [x] **A3.partial** добавлен bridge `stepCompiledContracts_of_appendGateRight`
      (сборка full `StepCompiledContracts` из gate-контракта)
- [ ] **B1** `runtimeSpecProvider_internal` (closed)
- [x] **B1.1** runtime-spec сборка из split-контрактов:
      `runtimeSpec_of_splitContracts`
- [x] **B1.2.partial** добавлен публичный bridge
      `stepCompiledSemanticsProvider_of_appendGateRight`
- [ ] **B2** `polyTMToStraightLineCompiler_internal` без аргументов + `proved_P_subset_PpolyDAG`
- [ ] **C1** `Interfaces.P_subset_Ppoly_proof -> internal source`
- [x] **D1** `lake build + scripts/check.sh + targeted builds`
- [x] TODO обновлён по факту

### Короткий отчёт по пунктам (текущий проход)
Сделано:
1. Добавлен публичный мост
   `stepCompiledSemanticsProvider_of_appendGateRight` в
   `Complexity/Simulation/Circuit_Compiler.lean`.
2. Добавлен публичный re-export
   `runtimeSpec_iterated_of_splitContracts` для итерационной runtime-spec
   формулировки из split-контрактов.
3. Подтверждена сборка `lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean`.

Осталось:
1. Полностью закрыть A1 (без контрактной подпорки) — прямое доказательство
   `appendWireSemantics.right`.
2. Закрыть B1/B2 в безусловной форме: получить `RuntimeSpecProvider` и
   `polyTMToStraightLineCompiler_internal` без входных гипотез.
3. Довести C1: переключение интерфейсов на internal source как default-route.

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


### Диагностика последней попытки «закрыть right-ветку полностью»

Ниже фиксируем, почему попытка прямого закрытия `appendWireSemantics.right`
в одном проходе не прошла (по факту вывода Lean), чтобы не терять контекст:

- Не закрылась база индукции для нового `evalWireAux_append_right`:
  цель сводится к равенству входного чтения `x ⟨↑(liftWireIntoAppend i), _⟩ = x i`,
  где нужны дополнительные transport-леммы по `Fin.ext` для `g = 0`.
- При раскрытии `evalWireAux` в succ-шаге `simp` зацикливается
  (`Possibly looping simp theorem: evalWireAux.eq_1`).
- В gate-части возникает типовой разрыв между
  `C₂.gate ⟨C₁.gates + j - C₁.gates, _⟩` и `C₂.gate ⟨j, hj⟩`:
  арифметика по Nat закрывается, но зависимый cast по `Fin` остаётся
  в форме, неудобной для автоматического `simpa`.
- Для `const/not/and/or`-веток после `cases hOp` нужны отдельные
  специализированные леммы развёртки `evalGateAux` через `cast`-перенос
  (иначе остаётся mismatch между «сырой» формой `match` и ожидаемой формой
  `evalGateAux ... = ...`).

Вывод: для полного закрытия right-ветки нужен отдельный небольшой слой
transport-лемм (gate-index + wire-index), а затем доказательство через
точечные `rw`/`conv` вместо глобального `simp`.

### Почему A1/A2/B1/B2/C1 пока не закрыты
Серьёзный технический блокер в зависимых индексах (`Fin (n + g)`) для правой ветки append:
- при попытке прямого закрытия `appendWireSemantics_right` возникают недоопределённые cast-цели
  в `TreeToStraight.lean` на уровне равенства gate-индексов после арифметической нормализации;
- это тянет за собой незакрытость `compileTreeWireSemantics`, затем `StepCompiledContracts`,
  а значит нельзя корректно объявить закрытые `runtimeSpecProvider_internal`/безпараметрический
  `polyTMToStraightLineCompiler_internal` без временных гипотез.

Практическая трактовка: шаг D1 закрыт полностью, но для A/B/C нужен отдельный
proof-refactor раунд в `TreeToStraight.lean` (с дополнительными transport/cast-леммами).



### Attempt log: focused A1/A2 transport refactor (latest)

Что пробовали в `TreeToStraight.lean`:
- добавляли transport/cast-леммы для правой ветки `liftWireIntoAppend`;
- пытались закрыть `evalGateAux_append_right` через эти cast-леммы;
- на базе этого пытались закрыть `appendWireSemantics_right` и затем `compileTreeWireSemantics`.

Точный блокер (воспроизводимо):
- при раскрытии `appendCircuit.gate` во второй ветке (`g \ge C₁.gates`) возникают
  transport-цели по зависимым индексам `Fin` вида
  `cast ... (liftOpIntoAppend (... ⟨C₁.gates + g - C₁.gates, ...⟩)) = ... ⟨g, hg⟩`;
- `simp`/`omega` закрывают арифметику по Nat, но не закрывают зависимые `cast`/`HEq`
  между индексированными `Fin`-термами в нужной форме;
- из-за этого прямой proof-path `evalGateAux_append_right -> appendWireSemantics_right`
  остаётся незакрытым без дополнительного слоя специализированных transport-лемм
  (отдельно для gate-индекса и для wire-индексов внутри `liftOpIntoAppend`).

Решение для следующего прохода:
1. Явно ввести леммы семейства `cast_gateIdx_append_right_*` и
   `cast_wireIdx_liftWireIntoAppend_*` (в терминах `Fin.ext` + `Nat.add_sub_cancel_left`).
2. Переписать `evalGateAux_append_right` без глобального `simp`, а через локальные
   `have`-шаги с точечным `rw` по этим cast-леммам.
3. После закрытия right-ветки собрать `appendWireSemantics` и повторить индукцию
   для `compileTreeWireSemantics`.


### Следующий технический под-план (точечно)
1. Вынести отдельные леммы вида `cast_gateIndex_append_right` для устранения transport-шумов.
2. После этого закрыть `evalGateAux_append_right`, затем `appendWireSemantics_right`.
3. На базе `appendWireSemantics` закрыть `compileTreeWireSemantics`.
4. Сразу собрать closed witness `StepCompiledContracts` и только затем продвигаться в B1/B2.

### Commit refs
- Current documentation sync commit: `TBD (filled in commit message/PR)`
- Baseline feature commit under review: `eac3110`
