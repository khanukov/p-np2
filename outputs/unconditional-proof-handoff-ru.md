# Remaining family-specific debt: exact statement and required inputs

**Дата:** 2026-04-08
**Цель:** документ фиксирует только оставшийся математический долг и полный контекст,
достаточный для его решения внешней группой без дополнительного bridge-контекста.

---

## 1) Что уже строго закрыто (не является долгом)

В текущем Lean-пайплайне уже закрыто:

1. eventual one-sided promise-YES payload `⇒ ¬ PpolyDAG bridge.L`,
2. `¬ PpolyDAG bridge.L` + `hNP : NP bridge.L` `⇒ NP_not_subset_PpolyDAG`.

Значит, оставшийся долг целиком source-side.

---

## 2) В этой route нужна версия A (codim/slack), не версия B (relative-density)

По форме `SmallDAGImpliesPromiseYesSubcubeAt` downstream использует:

- `yYes`,
- координатный набор `S`,
- inequality `hSlack`:

  `F.Mof n (F.Tof n β) < 2^(GapSliceFamily.tableLen F n β - S.card)`,
- acceptance всех promise-valid `z`, согласующихся с `yYes` на `S`.

Relative-density внутри promise-domain в этой цели не требуется.

---

## 3) Упрощение payload: `ε` здесь фиктивен для canonical bound

Для canonical bound

`ppolyDAGSizeBoundOnSlices F hInDag`

параметр `ε` не используется (он игнорируется в определении bound).

Поэтому для source-side достаточно доказать payload в форме:

```text
∃ β0 > 0,
  ∀ β, 0 < β → β < β0 →
    ∃ n0, ∀ n ≥ n0,
      SmallDAGImpliesPromiseYesSubcubeAt
        F (ppolyDAGSizeBoundOnSlices F hInDag) n β 1.
```

Далее просто берётся `ε := 1`.

---

## 4) Generic reduction (уже строгая):
##    `certificate isolation + hSlack => SmallDAGImpliesPromiseYesSubcubeAt`

Фиксируем `F, hInDag, n, β`, `p := F.paramsOf n β`, корректный solver `C` под
каноническим bound и предположим существование частичного присваивания `ρ` на
табличных координатах `D ⊆ Fin (GapSliceFamily.tableLen F n β)`, такого что:

1. `((Yes ∪ No) ∩ [ρ]) ≠ ∅`,
2. `((Yes ∪ No) ∩ [ρ]) ⊆ Yes`,
3. `F.Mof n (F.Tof n β) < 2^(GapSliceFamily.tableLen F n β - |D|)`,
4. `AgreeOnValues (p := p) D y z` кодирует совпадение на тех же координатах,
   которые фиксирует `ρ`.

Тогда

`SmallDAGImpliesPromiseYesSubcubeAt F (ppolyDAGSizeBoundOnSlices F hInDag) n β 1`

выполнено.

**Идея построения witness:**

- выбрать `yYes` из непустого `((Yes ∪ No) ∩ [ρ])`,
- по purity получить `yYes ∈ Yes`,
- взять `S := D`,
- для любого promise-valid `z`, согласующегося с `yYes` на `S`, вывести `z ∈ [ρ]`,
  затем `z ∈ Yes`, затем по корректности `C` получить `eval C z = true`,
- `hSlack` берётся из пункта (3).

---

## 5) Численный мост в `hSlack`: через натуральный envelope `κ(n,β)`

Для Lean-аритметики удобнее формулировать budget как

`|dom ρ| ≤ κ(n,β)` с `κ(n,β) : Nat` (например, `⌈cβn⌉`).

Достаточно доказать:

`F.Mof n (F.Tof n β) < 2^(GapSliceFamily.tableLen F n β - κ(n,β))`.

Тогда из `|dom ρ| ≤ κ` и монотонности `2^m` автоматически следует нужный
`hSlack` с `|dom ρ|`.

---

## 6) Эквивалентный остаточный долг (в одной формуле)

Остаточный долг эквивалентен утверждению:

для каждого `hInDag` существует `β0 > 0` и функция `n0(β)`, что для любого
`0 < β < β0`, любого `n ≥ n0(β)` и любого корректного `C` под canonical bound,
существует `ρ` с:

1. non-vacuity promise-цилиндра,
2. one-sided purity,
3. `|dom ρ| ≤ κ(n,β)`,
4. `F.Mof n (F.Tof n β) < 2^(GapSliceFamily.tableLen F n β - κ(n,β))`.

После этого source-payload строится механически (с `ε := 1`).

---

## 7) Что именно сейчас отсутствует (и нужно прислать)

Чтобы закрыть долг family-specific именно для вашего `F`, нужны 5 блоков данных.

### (A) Конкретные определения семейства `F`

Явно дать:

- `F.paramsOf n β`,
- `GapSliceFamily.tableLen F n β`,
- `GapSliceFamily.encodedLen F n β`,
- `F.Mof n (F.Tof n β)`,
- комбинаторное описание
  `Y_n := (gapSliceOfParams p).Yes`,
  `S_n := (gapSliceOfParams p).Yes ∪ (gapSliceOfParams p).No`.

### (B) Family-specific механизм построения `ρ`

Нужно точное statement, например в стиле witness-coordinate presentation:

- малый блок координат `J`,
- membership в `Y_n` внутри `S_n` зависит от `x|_J`,
- есть accepting pattern `a*`,
- `a*` реализуем в promise-domain.

### (C) Численное inequality для slack

Либо готовая лемма

`F.Mof n (F.Tof n β) < 2^(GapSliceFamily.tableLen F n β - κ(n,β))`,

либо формулы/асимптотика, из которых это выводится.

### (D) Семантика `AgreeOnValues` и `ValidEncoding`

Подтвердить/дать леммы:

- `AgreeOnValues (p := p) S y z` = совпадение на table-координатах из `S`,
- `y ∈ Yes -> ValidEncoding p y`.

### (E) Если source-lemma сначала в другом size-режиме

Уточнить:

- `size ≤ 2^(β·?)` по какой длине формулируется (`n`, `encodedLen`, `tableLen`),
- какая лемма даёт переход от canonical bound к этому режиму (size-cutoff).

---

## 8) Минимальный self-contained glossary

```lean
SmallDAGSolver
ppolyDAGSizeBoundOnSlices
SmallDAGImpliesPromiseYesSubcubeAt
AsymptoticDAGLanguageBridge
NP bridge.L
```

Эти пять объектов должны быть известны внешней группе в точной сигнатуре.

---

## 9) Короткий диагноз

Сейчас уже строго установлено: остаток задачи =

> family-specific существование one-sided isolating `ρ` + натуральный slack-envelope `κ(n,β)`.

После получения пунктов (A)–(E) остаётся чистое математическое доказательство
для конкретного `F`; дополнительный bridge-контекст больше не нужен.
