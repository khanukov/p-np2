# Можно ли сейчас снять одну из гипотез `hMS / hAsym / hNPbridge`? (feasibility audit)

Дата: 2026-04-16.

## Короткий ответ

**Прямо сейчас, без добавления новых внешних предпосылок, полностью снять одну из трёх гипотез не получается.**

Но есть важная развилка по реализуемости:

1. `hMS` — наиболее реалистичный кандидат на внутреннее закрытие в следующем шаге;
2. `hAsym` — существенно тяжелее (нужен внутренний construction asymptotic track);
3. `hNPbridge` — самый тяжёлый (нужен внутренний NP-strict witness для global asymptotic language).

## Почему формально не снимается «прямо сейчас»

## 1) `hMS`

Текущий код действительно умеет строить `hMS` **из** `hBounds`:

- `multiswitching_contract_internalized_of_support_bounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  : FormulaSupportBoundsFromMultiSwitchingContract`.

Значит `hMS` не фундаментальный, но пока зависит от внешнего `hBounds`.

**Итог:** снять `hMS` безусловно нельзя, пока не внутренне закрыт источник
`FormulaSupportRestrictionBoundsPartial`.

## 2) `hAsym`

`AsymptoticFormulaTrackHypothesis` — это package с параметризованными slices,
равенствами индексов и slice-agreement. В репозитории нет no-arg builder,
который генерирует этот пакет полностью автоматически.

**Итог:** без новой содержательной математики/конструкции `hAsym` не снимается.

## 3) `hNPbridge`

`AsymptoticNPPullback hAsym` требует NP-strict witness для
`gapPartialMCSP_AsymptoticLanguage hAsym.spec`.

В текущем дереве нет внутреннего theorem-конструктора, который строит этот
witness из уже имеющихся безусловных фактов.

**Итог:** сейчас это самый «жёсткий» внешний payload.

## Что реально можно сделать следующим коммитом (практический прогресс)

## Шаг A (наиболее продуктивный): частично internalize `hMS`

Сделать (и уже сделать в текущей ветке) новый endpoint-слой:

- `NP_not_subset_PpolyDAG_final_of_supportBounds`
- `P_ne_NP_final_of_supportBounds`

который принимает `hBounds` вместо `hMS` и внутри строит `hMS` через
`multiswitching_contract_internalized_of_support_bounds`.

Это **не** делает theorem безусловной, но убирает один API-уровень
и сужает внешний долг до более «чистой» гипотезы.

## Шаг B: пытаться закрыть `FormulaSupportRestrictionBoundsPartial` внутренне

Если получится internal theorem source для `hBounds`, тогда `hMS` исчезает
полностью с дефолтного API без добавления новых внешних предпосылок.

## Шаг C: отдельно атаковать `hAsym/hNPbridge`

Это уже не «инженерная упаковка», а предметная математика:

- construction asymptotic track;
- NP-strict bridge для global asymptotic language.

## Оценка сложности

- Снять `hMS` через `hBounds`-маршрут: **средняя**.
- Полностью закрыть `hMS` без внешнего `hBounds`: **высокая**.
- Снять `hAsym`: **очень высокая**.
- Снять `hNPbridge`: **очень высокая / research-critical**.

## Bottom line

На вопрос «можем ли прямо сейчас честно закрыть одну гипотезу полностью внутри
репозитория без новых внешних допущений?» — **скорее нет**.

На вопрос «можем ли сделать шаг, который реально приближает к этому?» — **да**:
следующий рациональный удар — маршрутизировать API через `hBounds` и затем
дожимать internal source для `hBounds`.

## Попытка «математически закрыть `hMS` прямо сейчас» и точная причина провала

Проверенная попытка была такой:

1. взять гипотетическое `hFormula : PpolyFormula (gapPartialMCSP_Language p)`,
2. построить solver через `generalSolverOfFormula hFormula`,
3. применить internalized contradiction
   `LB_Formulas_core_partial_closed_internalized`.

На шаге (3) это **не типчекается**, потому что:

- `generalSolverOfFormula hFormula : SmallGeneralCircuitSolver_Partial p`,
- а `LB_Formulas_core_partial_closed_internalized` требует
  `SmallAC0Solver_Partial p`.

То есть в активном дереве сейчас нет готового внутреннего моста
`SmallGeneralCircuitSolver_Partial -> SmallAC0Solver_Partial` для этого хода.

Это и есть точная техническая причина, почему «снять `hMS` полностью без
новых предпосылок» в один шаг сейчас не получилось.

## Что уже сделано как «математический удар» в коде

В активном коде добавлен стартовый bridge-слой:

- `FormulaToAC0BridgeData` (точный пакет оставшихся AC0-обязательств),
- `formula_to_ac0_solver_bridge`,
- `false_of_formula_via_ac0_bridge`.

Смысл: мы не меняем API-упаковку, а явно фиксируем theorem-level мост
`PpolyFormula -> SmallAC0Solver_Partial` при предоставлении ровно тех
синтаксических AC0-данных, которых не хватает у голого `PpolyFormula`.
