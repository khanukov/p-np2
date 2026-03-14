# Compiled Runtime Linear-Step Audit Pack

Дата: 2026-03-02  
Статус: ready-for-audit (engineering checkpoint)

## Update (2026-03-13): checkpoint superseded

После повторной проверки на текущем дереве:

- `./scripts/check.sh` проходит,
- `pnp3/Tests/Step10*.lean` проходят.

Состояние относительно checkpoint-а ниже:

1. Закрыт internal one-step provider:
   `stepCompiledLinearCandidateStepSpecProvider_internal`.
2. Закрыт internal linear correctness:
   `compiledRuntimeAcceptCorrectnessLinear_internal`.
3. Линейный route по размеру остаётся закрытым
   (`CompiledRuntimeCircuitSizeBoundLinear_internal`).

Актуальный остаток до no-arg `P ⊆ PpolyDAG` сместился на внутренний
evaluator/output-wire agreement witness
(`CompiledAcceptOutputWireAgreementLinear` / `InternalCompiler.EvalAgreement`).

Остальной текст файла ниже — исторический инженерный checkpoint.

## 1. Что именно уже сделано конструктивно

В `Simulation.lean` собран append-only каркас линейного one-step без
truth-table внутри самих новых builder-блоков:

1. Базовые блоки:
   - `buildSymbolFromCarry`
   - `buildBranchFromCarry`
   - `buildWriteTermFromCarry`
2. Вычисление записи:
   - `buildWriteBitAux`, `buildWriteBit`
3. Вычисление следующего состояния:
   - `buildStateTermFromCarry`, `buildNextStateAux`, `buildNextState`
4. Вычисление следующей позиции головы:
   - `moveIndex`
   - `buildHeadTermFromCarry`, `buildNextHeadAux`, `buildNextHead`
5. Вычисление следующего содержимого ленты:
   - `buildNextTapeFromCarry`, `buildNextTape`
6. Формализованный staging-контракт:
   - `LinearStepBlueprint`
   - `linearStepBlueprint`
   - `linearStepBlueprint_ready`
   - `linearStepBlueprint_base_le`

Смысл checkpoint'а: весь набор компонент `writeBit/nextTape/nextHead/nextState`
существует как append-only builders над `sc.circuit`.

## 2. Критическая оценка выбранного пути

Почему это правильный путь:

1. Старый маршрут (`stepCompiledTruthTable`) разворачивает шаг через
   tree/truth-table слой и не даёт реалистично закрыть внутренний size bound
   на runtime-итерации.
2. Новый маршрут строит шаги добавлением gates к существующему DAG, что
   структурно совместимо с доказательством вида:
   - one-step increment,
   - итерация по `runTime`,
   - `CompiledRuntimeCircuitGateBound`,
   - `CompiledRuntimeCircuitSizeBound`.

Почему это ещё не финиш:

1. `stepCompiledLinear` пока не переключён на новый blueprint.
2. Нет закрытой леммы per-step gate increment для новой сборки.
3. Нет финального моста от increment к runtime-итерации именно для linear-step.

## 3. Текущее состояние рисков

Низкий риск:

1. Локальные builder-блоки существуют и компилируются.
2. Непротиворечивость carry-транспорта в fold'ах (после фикса дефекта)
   подтверждена сборкой и структурой определений.

Средний риск:

1. Сборка единого shared-circuit для всех selectors (`tape/head/state`) ещё
   не зафиксирована в одном конструкторе.

Высокий риск (главный оставшийся):

1. Нужна формальная оценка gate-growth для новой one-step сборки, иначе
   `CompiledRuntimeCircuitGateBound` не закрывается.

## 4. Что аудиторы могут проверить прямо сейчас

Быстрые команды:

```bash
lake build pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean
lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean
lake env lean pnp3/Tests/StepCompiledLinearBlueprint.lean
```

Проверка ключевых определений:

```bash
rg -n "buildWriteBit|buildNextState|buildNextHead|buildNextTape|LinearStepBlueprint|linearStepBlueprint_ready" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean
rg -n "linearStepBlueprint_base_le|stepCompiledLinearBlueprint_ready_check|stepCompiledLinearBlueprint_base_le_check" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean pnp3/Tests/StepCompiledLinearBlueprint.lean
rg -n "sorry|admit" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean \
  pnp3/Tests/StepCompiledLinearBlueprint.lean \
  pnp3/Docs/CompiledRuntime_LinearStep_AuditPack.md
```

## 5. Следующий обязательный технический шаг

1. Сконструировать единый `stepCompiledLinear` из `LinearStepBlueprint` на
   одном shared circuit.
2. Доказать one-step increment bound для gates.
3. Поднять его по итерации и закрыть:
   - `CompiledRuntimeCircuitGateBound`
   - `CompiledRuntimeCircuitSizeBound`.
