# Проект PNP3: активный Lean-код

Обновлено: 2026-04-22

Канонический чеклист до безусловного `P != NP`:
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Текущий релизный режим:
`/root/p-np2/RELEASE_RC.md`.

## Что здесь

Каталог `pnp3/` содержит активный конвейер:

`SAL -> Covering-Power -> anti-checker -> magnification -> DAG-final wrappers`

## Граница вариантов MCSP

В активном `pnp3/` используется **только Partial MCSP**:

- модель: `Models/Model_PartialMCSP.lean`;
- язык/обещание: `gapPartialMCSP_Language`, `GapPartialMCSPPromise`.

Legacy-модель GapMCSP и другие старые ветки в `archive/` являются
историческим контекстом, а не источником текущего статуса.

## Текущая граница доказательства

Репозиторий компилирует большой DAG/magnification каркас:

1. inclusion side уже internalized через `proved_P_subset_PpolyDAG_internal`;
2. есть fixed-slice bridge `PpolyDAG -> PpolyFormula`;
3. есть asymptotic, Route-B, `_TM` и support-half wrappers;
4. есть falsifiability audit для support-bounds предпосылок.

Но безусловного `P != NP` в репозитории нет.

## Главная проблема

Старый источник support-bounds оказался формально ложным:

```text
FormulaSupportRestrictionBoundsPartial -> False
FormulaSupportBoundsFromMultiSwitchingContract -> False
MagnificationAssumptions -> False
FormulaSupportBoundsPartial_fromPipeline -> False
```

Поэтому теоремы, проходящие через эти предпосылки, являются vacuous: они
компилируются, но математически используют "из ложного следует что угодно".

Причина: truth-table hardwired формула для fixed slice является
`PpolyFormula`, но имеет носитель по всем переменным. Старые predicates
требовали полилогарифмический/малый support для слишком широкого класса
формул.

## FixedParams

Текущий честный кандидат:

```text
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

Он фиксирует AC0-параметры снаружи и поэтому блокирует известную singleton
provider атаку. Но это пока только форма будущего контракта, а не доказанная
математика.

Важно: `fixedParams + uniformProvenance` снова сводится к старому ложному
predicate и поэтому противоречиво в текущей формализации.

## Один файл для оставшегося гэпа

Оставшаяся research-граница вынесена в:

```text
Magnification/UnconditionalResearchGap.lean
```

Там определён `ResearchGapWitness` и доказан условный мост
`P_ne_NP_of_researchGap`.  Будущий безусловный прорыв должен доказать witness
в этом файле и затем открыть zero-argument theorem из него.

## Источник статуса

Глобальный статус и блокеры проверяются только по:

- `/root/p-np2/STATUS.md`
- `/root/p-np2/TODO.md`
- `/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`

Локальные исторические заметки и старые roadmap-файлы нужно считать
неавторитетными, если они расходятся с этими документами.
