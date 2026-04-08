# Remaining debt: строгий theorem package для family-specific closure

**Дата:** 2026-04-08
**Статус:** общий редукционный шаг закрыт; осталась только инстанциация для конкретного `F`.

---

## 1) Что уже закрыто строго

В коде уже есть инфраструктура, достаточная для финального перехода:

- builder `smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt`,
- bridge closure `not_globalPpolyDAG_of_eventuallyPromiseYesWeakRoute`,
- class-level closure `NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRoute`.

Следовательно, остаётся только source-side family-specific математика.

---

## 2) Обозначения

Для фиксированных `F, hInDag, n, β`:

- `p := F.paramsOf n β`,
- `T := GapSliceFamily.tableLen F n β`,
- `Y := (gapSliceOfParams p).Yes`,
- `N := (gapSliceOfParams p).No`,
- `P := Y ∪ N`,
- `M := F.Mof n (F.Tof n β)`.

Size-bound: `ppolyDAGSizeBoundOnSlices F hInDag`.

---

## 3) Теорема 1 (strict sufficient theorem)

### Предпосылки

#### (V) YES-валидность

`∀ y, y ∈ Y → ValidEncoding p y`.

#### (Iso) Eventual certificate isolation

Существуют `β0 > 0`, функция `κ : Nat × Rat → Nat`, функция `n_iso(β)` такие, что
для любого `β` с `0 < β < β0`, любого `n ≥ n_iso(β)`, любого корректного `C` под canonical bound,
существуют `D ⊆ Fin(T)` и частичное присваивание `ρ` на `D` со свойствами:

1. `P ∩ [ρ] ≠ ∅`,
2. `P ∩ [ρ] ⊆ Y`,
3. `|D| ≤ κ(n,β)`,
4. `M < 2^(T - κ(n,β))`,
5. `y ∈ [ρ] ∧ ValidEncoding p z ∧ AgreeOnValues (p := p) D y z -> z ∈ [ρ]`.

### Вывод

`∃ β0 > 0, ∀ β, 0 < β → β < β0 → ∃ n0, ∀ n ≥ n0,`

`SmallDAGImpliesPromiseYesSubcubeAt F (ppolyDAGSizeBoundOnSlices F hInDag) n β 1`.

### Доказательство (идея)

Для фиксированных `β,n,C`:

- из (1) выбираем `yYes ∈ P ∩ [ρ]`,
- из (2) получаем `yYes ∈ Y`, из (V) — `ValidEncoding p yYes`,
- берём `S := D`,
- из (4) и `|D| ≤ κ` получаем `M < 2^(T - |D|)` (монотонность `2^m`),
- для любого `z`, согласующегося с `yYes` на `S`, по (5) получаем `z ∈ [ρ]`,
  затем `z ∈ P ∩ [ρ] ⊆ Y`,
- по корректности `C` на YES имеем `eval C z = true`.

Это ровно поля `SmallDAGImpliesPromiseYesSubcubeAt ... n β 1`.

∎

---

## 4) Теорема 2 (прямая форма, ближе к builder)

Достаточно иметь eventual данные без явного цилиндра `[ρ]`:

для каждого допустимого `β,n` и корректного `C` существуют
`yYes ∈ Y`, `D ⊆ Fin(T)` такие, что

1. `ValidEncoding p yYes`,
2. `|D| ≤ κ(n,β)`,
3. `M < 2^(T - κ(n,β))`,
4. `((z ∈ Y ∨ z ∈ N) ∧ ValidEncoding p z ∧ AgreeOnValues (p := p) D yYes z) -> z ∈ Y`.

Тогда тот же eventual payload с `ε := 1` следует напрямую из
`smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt` + численного шага `κ -> |D|`.

---

## 5) Теорема 3 (witness-coordinate presentation ⇒ Теорема 2)

Если family-specific структура даёт:

- малый блок координат `J`,
- принимающий шаблон `a*` на `J`,
- YES-центр `y* ∈ Y` с `y*|_J = a*`,
- `ValidEncoding p y*`,
- `|J| ≤ κ(n,β)`,
- `M < 2^(T - κ(n,β))`,
- forcing: любой promise-valid `z` с `z|_J = a*` лежит в `Y`,

и `AgreeOnValues (p := p) J y* z` эквивалентно совпадению на `J`,
то берём `D := J`, `yYes := y*` и получаем предпосылки Теоремы 2.

---

## 6) Теорема 4 (size-cutoff bridge)

Если source-лемма доказана сначала в альтернативном size-режиме
`size(C) ≤ B_alt(n,β)`, а canonical bound даёт этот режим после `n_size(β)`,
то всё переносится на canonical route с порогом

`max(n0(β), n_size(β))`.

---

## 7) Финальный вывод до endpoint

Если для вашего `F` выполнена гипотеза Теоремы 1 (или 2/3 + 4), равномерно по
`hInDag`, то вместе с `hNP : NP bridge.L` автоматически получаем

`NP_not_subset_PpolyDAG`

через уже реализованный
`NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRoute`.

---

## 8) Что осталось purely family-specific

Нужно прислать/доказать только:

1. явные определения `paramsOf / tableLen / encodedLen / Mof∘Tof` и смысл `Y,N`;
2. точную семантику `AgreeOnValues` в терминах table-координат;
3. family-specific construction (`ρ` или witness-coordinate форма);
4. slack inequality через `κ(n,β)`;
5. при необходимости размерный cutoff bridge.

Больше никакой новой bridge-математики не нужно.

---

## 9) Короткий operational итог

Оставшийся долг эквивалентен одной из двух форм:

- **цилиндровая форма:** eventual one-sided isolating `ρ` + slack-envelope `κ`; или
- **координатная форма:** eventual `(yYes, D)` с forcing-импликацией на YES.

Обе формы напрямую закрывают source-предикат через уже реализованные леммы.
