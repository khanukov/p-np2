# Проект PNP3: активный Lean-код

Обновлено: 2026-04-03

Канонический чеклист до безусловного `P ≠ NP`:
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Текущий релизный режим:
`/root/p-np2/RELEASE_RC.md`.
Текущий DAG-план:
`/root/p-np2/pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.

## Что здесь

Каталог `pnp3/` содержит активный конвейер:

`SAL -> Covering-Power -> anti-checker -> magnification -> DAG-final wrappers`

## Граница вариантов MCSP

В активном `pnp3/` используется **только Partial MCSP**:

- модель: `Models/Model_PartialMCSP.lean`;
- язык/обещание: `gapPartialMCSP_Language`, `GapPartialMCSPPromise`.

Legacy-модель GapMCSP и другие старые ветки в `archive/` являются
историческим контекстом, а не источником текущего статуса.

## Текущая DAG-граница

Сейчас активная DAG-картина такая:

1. `LowerBounds/AsymptoticDAGBarrier.lean` содержит asymptotic/barrier-поверхность.
2. `LowerBounds/DAGStableRestrictionProducer.lean` содержит canonical
   witness-density / witness-transfer компиляторы и fixed-slice source-side
   математику.
3. `LowerBounds/DAGUnconditionalBlocker.lean` нормализует Route-B gate через
   `dagRouteBSourceBlocker` и `DAGRouteBSourceClosure`.
4. `Magnification/FinalResult.lean` содержит публичные DAG wrappers, включая
   asymptotic fixed-slice routes и concrete `_TM` routes.

## Что открыто

Текущий публичный default theorem всё ещё имеет вид:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

То есть:

1. внутреннего theorem `NP_not_subset_PpolyDAG` в дереве пока нет;
2. публичная zero-arg финальная формулировка пока тоже не закрыта.

## Источник статуса

Глобальный статус и блокеры проверяются только по:

- `/root/p-np2/STATUS.md`
- `/root/p-np2/TODO.md`
- `/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`

Локальные исторические заметки и старые roadmap-файлы нужно считать
неавторитетными, если они расходятся с этими документами.
