# Compiled Runtime Size Closure Runbook (`P ⊆ PpolyDAG`)

Дата: 2026-03-02  
Статус: active

## 1. Executive decision

Текущий маршрут закрытия `CompiledRuntimeCircuitSizeBound` через существующий
`stepCompiled` **не является замыкаемым** в текущем виде.

Причина не в одной недостающей лемме, а в архитектуре шага:

1. `ConfigCircuits.stepCircuits` сейчас использует `truthTableCircuit` для
   `nextTapeCircuit/nextHeadCircuit/nextStateCircuit`.
2. `stepCompiled` строится через
   `toConfigCircuits` -> `toTreeWire` -> `packFin (compileTree ...)`.
3. Это регулярно разворачивает DAG-представление в деревья и компилирует заново.

Итог: нет реалистичного пути получить внутренний полиномиальный bound вида
`n^(c+5) + (c+5)` для `runtimeConfigCompiled` без рефактора шага.

## 2. Что это значит для стратегии

Лучший путь к финальной цели (`P ⊆ PpolyDAG` без внешних контрактов):

1. Убрать truth-table шаг как основу симуляции.
2. Сделать DAG-preserving шаг на уровне `StraightConfig` (append-only builder).
3. Доказывать размер через one-step gate increment и итерацию по `runTime`.

Именно этот путь одновременно:

- конструктивный,
- совместим с уже закрытой семантической частью (`stepCompiled`-ветка),
- даёт прямую траекторию к закрытию `CompiledRuntimeCircuitSizeBound`.

## 3. Priority plan (реально исполнимый)

### P0 (критический, высокая сложность)
Ввести новый шаг `stepCompiledLinear` (рабочее имя), который:

1. стартует из `sc.circuit` (`EvalBuildCtx`/builder primitives),
2. добавляет только новые gates (без `toTreeWire`/`compileTree` на всей формуле),
3. возвращает новые wire selectors для tape/head/state.

Ожидаемый результат:

- лемма one-step вида  
  `gates(stepCompiledLinear sc) ≤ gates(sc) + K(M,n)`.

### P1 (высокий)
Семантика нового шага:

1. one-step spec:
   `Spec sc f -> Spec (stepCompiledLinear sc) (TM.stepConfig ∘ f)`,
2. итерация:
   runtime-spec для `Nat.iterate stepCompiledLinear`.

### P2 (средне-высокий)
Size-chain:

1. из P0 вывести bound на `Nat.iterate`,
2. подставить `hRun : runTime ≤ n^c + c`,
3. получить `CompiledRuntimeCircuitGateBound`,
4. закрыть `CompiledRuntimeCircuitSizeBound` через уже существующий мост
   `compiledRuntimeCircuitSizeBound_of_gateBound`.

### P3 (средний)
Route closure:

1. закрыть runtime-only bundle полностью (без входных контрактов),
2. довести internal-source endpoint до no-arg theorem,
3. синхронизировать `FinalResult` / `Barrier.Bypass`.

## 4. Non-goals (чтобы не терять время)

1. Не пытаться «дожать» текущий `CompiledRuntimeCircuitSizeBound` только
   арифметическими леммами поверх старого `stepCompiled`.
2. Не наращивать дополнительные slack-версии bound (`+6`, `+7`, ...), пока шаг
   остаётся truth-table/tree-recompile.

## 5. Immediate next coding steps

1. Вынести в `Simulation.lean` новый namespace/блок для linear-step assembly.
2. Сначала закрыть только gate growth skeleton:
   - размер после append,
   - суммарный per-step прирост.
3. Затем подключить семантические obligations (используя уже существующие
   шаблоны `Spec` и `runtime_spec_of_next`).

## 6. Definition of Done for this runbook

Считаем блок закрытым, когда одновременно:

1. есть внутренний witness `CompiledRuntimeCircuitSizeBound`,
2. он не опирается на внешние contract inputs,
3. маршрут `proved_P_subset_PpolyDAG_of_iteratedRuntimeOnlyContracts` можно
   свернуть до no-arg internal theorem,
4. `lake build` проходит на ключевых и полном таргете.

## 7. Execution status (2026-03-02, current pass)

Сделано:

1. В `Simulation.lean` выделены switch-points:
   - `stepCircuitsTruthTable` + alias `stepCircuits`,
   - `stepCompiledTruthTable` + alias `stepCompiled`.
   - добавлены явные linear switch-points:
     `stepCircuitsLinear`, `stepCompiledLinear`.
2. В `StraightLineBuilder.lean` добавлены append-only helper'ы для
   `EvalBuildCtx`:
   - `appendOp`, `appendConst`, `appendNot`, `appendAnd`, `appendOr`.
3. В `Simulation.lean` добавлен append-only scaffolding:
   - `StraightConfig.BuiltWire` + базовые операции над текущими/base wire,
   - `BuiltWire.buildSymbolAux/buildSymbol` для
     `OR_i (head_i ∧ tape_i)` без tree-recompile.
   - `BuiltWire.buildGuardSymbol`, `BuiltWire.buildBranchIndicator`,
     `BuiltWire.buildWriteTerm`.
   - `BuiltWire.BuiltCarry` + append-carry transport helpers.
   - `BuiltWire.buildSymbolFromCarry`, `buildBranchFromCarry`,
     `buildWriteTermFromCarry`, `buildWriteBitAux/buildWriteBit`.
   - `linearWriteBitWire` как явный linear-step building block.
4. Исправлен critical carry-transport defect в append-only fold:
   - `buildSymbolFromCarry` теперь не теряет внешний accumulator-carry,
   - `buildBranchFromCarry`/`buildWriteTermFromCarry` сохраняют carry,
   - `buildWriteBitAux` теперь действительно делает `acc := acc OR term`.
5. Добавлены новые append-only blocks для продолжения linear-step:
   - `moveIndex`,
   - `headStateSymbolPairs`,
   - `buildStateTermFromCarry`, `buildNextStateAux`, `buildNextState`,
   - `buildHeadTermFromCarry`, `buildNextHeadAux`, `buildNextHead`,
   - `buildNextTapeFromCarry`, `buildNextTape`,
   - публичные switch wires:
     `linearNextStateWire`, `linearNextHeadWire`, `linearNextTapeWire`.
4. Сборка проходит:
   - `lake build pnp3/Complexity/PsubsetPpolyInternal/StraightLineBuilder.lean`
   - `lake build pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean`
   - `lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean`

Следующий шаг:

1. Собрать единый `stepCompiledLinear` (один shared circuit, selectors для tape/head/state)
   поверх уже готовых блоков `writeBit/nextState/nextHead/nextTape`.
2. Изолировать и зафиксировать per-step gate increment в явной лемме.
3. Поднять increment через итерацию по `runTime` и закрыть `CompiledRuntimeCircuitGateBound`.
