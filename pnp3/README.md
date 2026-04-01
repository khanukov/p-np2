# Проект PNP3: активный Lean-код

Обновлено: 2026-03-26

Канонический чеклист до безусловного `P ≠ NP`:
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Текущий релизный режим (RC) и правила формулировок:
`/root/p-np2/RELEASE_RC.md`.
Конкретный план по оставшемуся DAG-блокеру:
`/root/p-np2/pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.

## Что здесь

Каталог `pnp3/` содержит активный конвейер:

`SAL -> Covering-Power -> anti-checker -> magnification -> DAG-final wrappers`

## Граница вариантов MCSP (важно для аудита)

В активном `pnp3/` используется **только Partial MCSP**:

- модель: `Models/Model_PartialMCSP.lean`;
- язык/обещание: `gapPartialMCSP_Language`, `GapPartialMCSPPromise`.

Legacy-модель **GapMCSP (total truth table)** хранится в `archive/` и не
является источником текущего активного статуса.

Текущая DAG-граница формализована через
`pnp3/LowerBounds/AsymptoticDAGBarrier.lean`:

- `GapSliceFamily` (единый пакет `paramsOf/Tof/Mof` + coherence-поля);
- Layer A: `GapAntiLocalityAt/Statement`;
- Layer B: `SmallDAGImpliesCoordinateLocalityAt/Statement` с явным
  `SizeBound` и параметром `ε`;
- endpoint: `MagnificationStyleNoSmallDAG`.

## Источник статуса

Глобальный статус и блокеры проверяются только по:

- `/root/p-np2/STATUS.md`
- `/root/p-np2/TODO.md`
- `/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`

Локальные исторические заметки в подпапках не являются финальным статусом.
