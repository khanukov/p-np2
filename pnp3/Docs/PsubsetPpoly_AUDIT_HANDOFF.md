# P⊆P/poly Internal Route — Audit Handoff Snapshot

Статусный срез подготовлен для передачи аудитору/следующему инженеру.
Цель: зафиксировать, что уже собрано, что является реальным блокером,
и какие минимальные действия нужны, чтобы продолжить без потери контекста.

---

## 1) Snapshot (заморозка текущей стадии)

- Repo: `pnp3`
- Branch (на момент подготовки): `work`
- Baseline commit under review: `4d787d2`
- Текущее состояние: сборка целевых модулей зелёная; остаются только
  существующие non-fatal linter warnings (`simp/simpa`, unused simp args).

### Быстрый смысл текущей архитектуры

1. Финальные DAG-обёртки уже живут на bundle-контракте
   `PsubsetPpolyInternalContracts`.
2. Тяжёлый append-right участок декомпозирован в gate-level контракт
   `AppendGateRightSemantics` + сборочные мосты.
3. Добавлены assembly-мосты, позволяющие идти от split-контрактной поверхности
   к `StepCompiledContracts`/`StepCompiledSemanticsProvider`.

---

## 2) Что уже закрыто (проверяемые узлы)

### 2.1 Split/append assembly

- `appendWireSemantics_of_gateContracts`
- `compileTreeWireSemantics_of_append`
- `compileTreeWireSemantics_of_gateContracts`

Эти теоремы дают рабочую сборку по ветке tree→straight из gate-level
поверхности (без ручной склейки в каждом downstream месте).

### 2.2 Compiler-side assembly bridges

В `Complexity/Simulation/Circuit_Compiler.lean` доступны:

- `stepCompiledContracts_of_appendGateRight`
- `stepCompiledSemanticsProvider_of_appendGateRight`
- `runtimeSpec_of_splitContracts`
- `runtimeSpec_iterated_of_splitContracts`
- `PsubsetPpolyInternalContracts`
- `proved_P_subset_PpolyDAG_of_contracts`

Это уже достаточная «платформа склейки» для аудита связности маршрута,
даже при том, что финальный безусловный right-proof ещё не закрыт.

---

## 3) Что НЕ закрыто (главные блокеры)

### B0 (математический ядро-блокер)

Не закрыто полностью внутреннее безусловное доказательство
`appendWireSemantics.right` без внешней контрактной подпорки.

Это главный remaining blocker: пока он не закрыт, нельзя честно считать,
что internal route завершён в «безусловной» форме.

### B1 (assembly closure blocker)

Нет закрытого (без входных гипотез) `RuntimeSpecProvider` в форме,
которую можно напрямую подать в
`polyTMToStraightLineCompiler_internal` без параметров.

### B2 (endpoint closure blocker)

Соответственно, нет финальной безпараметрической точки
`polyTMToStraightLineCompiler_internal` + полного замыкания маршрута
как «конечной константы».

### B3 (interface default-route)

Интерфейсы ещё не полностью переключены на internal source как дефолтный
канал (без implicit reliance на legacy/fallback как основной путь).

---

## 4) Что проверять аудитору в первую очередь

1. **Логическая непротиворечивость сборочных мостов**
   (нет ли circularity между split→contracts→semantics→runtime).
2. **Границы контрактов**:
   где именно остаётся `AppendGateRightSemantics` как внешняя предпосылка.
3. **Статус финальных API**:
   что они действительно зависят от bundle-контракта,
   а не от старых параметров (`hCompiler`/`hEvalAgree`) напрямую.
4. **Отсутствие `sorry/admit`** в изменённом proof-surface.

---

## 5) Минимальный план продолжения (для следующего инженера)

### Шаг P1 — закрыть right-ветку напрямую

В `TreeToStraight.lean`:

- довести прямой proof-path для `appendWireSemantics.right`;
- избегать глобального `simp` в transport-heavy местах;
- использовать локальные `rw`/`simpa` после явных index-normalization шагов.

### Шаг P2 — собрать безусловный StepCompiled/runtime provider

После P1:

- собрать closed witness, который убирает последнюю внешнюю контрактную подпорку;
- получить `RuntimeSpecProvider` без входных гипотез.

### Шаг P3 — финализировать endpoint

- закрыть безпараметрический `polyTMToStraightLineCompiler_internal`;
- зафиксировать финальное `proved_P_subset_PpolyDAG` как route endpoint;
- обновить интерфейсный default-route.

---

## 6) Repro commands (handoff verification)

Минимальный набор проверок для «поднятия контекста» после переключения
инженера:

```bash
git log --oneline -n 5
lake build pnp3/Complexity/PsubsetPpolyInternal/TreeToStraight.lean
lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean
lake build pnp3/Magnification/FinalResult.lean pnp3/Barrier/Bypass.lean
```

Опционально полный прогон:

```bash
./scripts/check.sh
```

---

## 7) Риски и замечания

- Основной риск — «ложное ощущение закрытия»: assembly-мосты уже есть,
  но ядровой right-proof ещё контрактный.
- Второй риск — расползание статуса в документах.
  При каждом proof-pass синхронизировать этот файл и
  `PsubsetPpoly_Internal_TODO.md`.

---

## 8) Передача ответственности

Если следующий инженер начинает с нуля контекста:
1. Сначала читает **этот файл**.
2. Потом читает `PsubsetPpoly_Internal_TODO.md` (раздел Execution status).
3. Только после этого идёт в `TreeToStraight.lean` на direct closure B0.

