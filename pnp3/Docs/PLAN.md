# План реализации SAL → Hardness Magnification

Документ фиксирует артефакты, внешние факты и чек-листы из пользовательского плана. Он служит ориентиром для постепенного заполнения Lean-файлов в каталоге `pnp3/`.

## Часть A. Базовые определения и ядро SAL

- **Цель**: реализовать определения подкубов, ошибок аппроксимации, частичных решающих деревьев (PDT) и атласов. Доказать леммы `shrinkage_to_common_PDT` и `PDT_to_atlas`, их композицию `SAL_Core`.
- **Файлы**: `Core/BooleanBasics.lean`, `Core/PDT.lean`, `Core/Atlas.lean`, `Core/SAL_Core.lean`.
- **Тесты**: `Tests/Parity_Counterexample.lean`, `Tests/SAL_Smoke_AC0.lean`.

## Часть B. Счёт и ёмкость

- **Цель**: формализовать оценку числа «лёгких функций» и количество покрытий словарём.
- **Файлы**: `Counting/Count_EasyFuncs.lean`, `Counting/Atlas_to_LB_Core.lean`.
- **Тесты**: `Tests/Atlas_Count_Sanity.lean`.

## Часть C. Модель GapMCSP и нижние оценки

- **Цель**: определить язык GapMCSP, параметры YES/NO и вывести нижние оценки для формул и локальных схем на основе SAL.
- **Файлы**: `Models/Model_GapMCSP.lean`, `LowerBounds/LB_Formulas.lean`, `LowerBounds/LB_LocalCircuits.lean`.

## Часть D. Магнификация

- **Цель**: записать внешние триггеры OPS/JACM и связать их с полученными нижними оценками.
- **Файлы**: `Magnification/Facts_Magnification.lean`, `Magnification/Bridge_to_Magnification.lean`.

## Внешние факты

- **(F-SW)**: псевдослучайная multi-switching lemma (Servedio–Tan, 2018).
- **(F-CNT)**: верхняя оценка числа функций со схемами малого размера.
- **(F-OPS/JACM)**: триггеры магнификации для GapMCSP.

Каждый внешний факт будет оформлен как Lean-теорема в `Facts_Magnification.lean` или `Counting/Count_EasyFuncs.lean` с ссылкой на источник.

## Готовые результаты (таргет)

1. `SAL_Core`: из `Shrinkage` следует существование общего атласа размера `2^{O(t log(1/ε))}`.
2. `SAL_for_AC0`: ссылается на (F-SW) и подставляет параметры для AC^0.
3. `LB_Formulas`: формализованный нижний предел для `(Gap)MCSP` на формулах размера `N^{2+δ}`.
4. `LB_LocalCircuits`: аналогично для локальных схем `N · polylog N`.
5. `Bridge_to_Magnification`: вывод `NP ⊄ P/poly` при выполнении внешних допущений.

## Контрольные вопросы

- Достаточно ли покрыт риск «барьера локальности»? — Да, через явное оформление триггеров из JACM’22.
- Есть ли негативные примеры (паритет)? — Да, тест `Parity_Counterexample.lean` закрепит невозможность SAL без shrinkage.
- Подготовлен ли счёт вариантов покрытий? — Да, через леммы `num_unions`, `covering_power` и производные.

Этот документ будет обновляться по мере закрытия пунктов.
