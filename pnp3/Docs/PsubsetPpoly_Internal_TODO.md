# PsubsetPpoly Internal Closure TODO

Цель: полностью внутреннее (в `pnp3`) конструктивное закрытие блока `P ⊆ P/poly`
в совместимом DAG-треке без внешних аксиом и без внешних параметров в финальном конусе.

Статусы:
- `done`
- `in_progress`
- `pending`

## План (фиксированный, v3, 14 шагов)

1. Зафиксировать инварианты и цель в коде (`Simulation.lean`, `Circuit_Compiler.lean`) и довести до критерия: финальные сигнатуры больше не принимают `hCompiler`.  
Status: `in_progress`

2. Доперенести минимальные индексационные утилиты (`stateCard`, `stateEquiv`, `stateIndex`) и использовать их в формулах состояния.  
Status: `done`

3. Портировать tree-шаг симуляции `ConfigCircuits.stepCircuits` (ядро: next tape/head/state).  
Status: `done`

4. Доказать корректность одного шага tree-симуляции:  
`ConfigCircuits.Spec cc f -> Spec (stepCircuits cc) (fun x => TM.stepConfig (f x))`.  
Status: `done`

5. Портировать итерацию и runtime tree-симуляции:  
`runtimeCircuits := Nat.iterate stepCircuits (M.runTime n) (initial M n)` + `runtimeCircuits_spec`.  
Status: `done`

6. Портировать `acceptCircuit` и его корректность на tree-уровне.  
Status: `done`

7. Портировать straight-line слой (`StraightConfig.step`, `straightRunConfig`, `straightRuntimeConfig`, `straightAcceptCircuit`).  
Status: `done`

8. Доказать корректность straight-line acceptance (`straightAcceptCircuit_spec`).  
Status: `done`

9. Портировать полиномиальную оценку размера до `straightAcceptCircuit_le_gatePolyBound` (+ `gatePolyBound`, `gatePolyBound_poly`).  
Status: `done`

10. Собрать внутренний компилятор в `Circuit_Compiler.lean`:  
`polyTMToStraightLineCompiler_internal : PolyTMToStraightLineCompiler`.  
Status: `in_progress`

11. Вывести внутреннее включение:  
`proved_P_subset_PpolyDAG : P_subset_PpolyDAG := P_subset_PpolyDAG_of_compiler ...`.  
Status: `pending`

12. Убрать `hCompiler` из финальных обёрток (`FinalResult.lean`, `Barrier/Bypass.lean`).  
Status: `pending`

13. Убрать из финального слоя технические/временные имена (`legacy/archive/old_attempt`) и привести API/файлы к нормальным production-названиям.  
Status: `pending`

14. Прогнать финальный аудит конуса (`lake build`, `scripts/check.sh`, аксиомный аудит) и зафиксировать release-ready промежуточную версию.  
Status: `pending`

## Текущий фокус

- Активный шаг: **10**.
- Блокер шага 10: базовые семантические контракты для compiled-ветки
  (`CompileTreeWireSemantics` + `AppendWireSemantics`).
- `EvalAgreement` остаётся отдельным блокером шага 11 (упаковка в `PpolyStraightLine`/`PpolyDAG`).
- Промежуточно выполнено для снятия блокеров: добавлен базовый builder-слой wire-токенов (`PsubsetPpolyInternal/StraightLineBuilder.lean`), который нужен для порта реального `StraightConfig.step`.
- Следом: **11/12**, затем **13/14**.

### Подшаги шага 10 (runtime-spec closure)

10.a `done` — Порт straight snapshot/builder слоя для одного шага:
- `branchSnapshot`, `writeSnapshot`, `tapeSnapshot`, `headSnapshot`.
- Локальные леммы сохранения семантики и роста числа вентилей.

10.b `in_progress` — Закрыть one-step spec через `stepCompiled`:
  - Добавлены: `stepCompiled`, `stepCompiled_spec_of_semantics`,
    `iterate_spec_of_next`, `runtime_spec_of_next`.
  - Добавлено сужение блокера: `packFinWireSemantics_of_contracts`, поэтому
    `PackFinWireSemantics` больше не отдельный первичный блокер.
  - Прогресс на текущем чекпоинте: в `TreeToStraight.lean` доказаны
    `evalWireAux_append_left`, `evalGateAux_append_left`,
    `appendWireSemantics_left`.
  - Оставшаяся цель: закрыть правую половину `AppendWireSemantics`
    (ветка `liftWireIntoAppend`) и затем `CompileTreeWireSemantics`
    без параметров.

10.c `done` — Доказаны generic-итерация/runtime-леммы:
`iterate_spec_of_next`, `runtime_spec_of_next`, `runtime_spec_of_stepCompiledSpec`.

10.d `in_progress` — Закрыть
`polyTMToStraightLineCompiler_internal : PolyTMToStraightLineCompiler`
без внешних параметров.
