# Handoff для математиков: финальный remaining debt для безусловного закрытия route

**Дата:** 2026-04-08
**Статус:** bridge/magnification инфраструктура уже закрыта; остался только family-specific source-step для конкретного `F`.

---

## 1) Что уже закрыто в коде (не требует новых идей)

### 1.1 Уже реализован generic builder

В коде есть теорема:

- `smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt`

Она переводит изоляционный source-сертификат вида

- YES-центр `yYes`,
- координатный набор `S`,
- slack inequality,
- `AgreeOnValues -> z ∈ Yes`,

в целевой predicate:

- `SmallDAGImpliesPromiseYesSubcubeAt ...`.

То есть source-side больше не обязан отдельно доказывать `eval C z = true` напрямую;
это добирается из корректности solver на YES.

### 1.2 Уже закрыт eventual weak-route bridge

Также в коде есть:

- `not_globalPpolyDAG_of_eventuallyPromiseYesWeakRoute`,
- `NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRoute`.

Значит, после получения нужного eventual source payload pipeline до
`NP_not_subset_PpolyDAG` уже механический.

---

## 2) Что именно осталось доказать математически

Осталась ровно одна family-specific цель:

## `canonical_smallDAG_certificateIsolation_on_slices F`

Смысл: для канонического slice при малых `β` и больших `n`, любой корректный
малый DAG даёт one-sided isolating certificate `ρ` на табличных координатах с
контролируемым budget и нужным slack.

Эквивалентно нужно обеспечить (для каждого `hInDag`):

```text
∃ β0 > 0,
  ∀ β, 0 < β → β < β0 →
    ∃ n0, ∀ n ≥ n0,
      SmallDAGImpliesPromiseYesSubcubeAt
        F (ppolyDAGSizeBoundOnSlices F hInDag) n β 1
```

(для canonical bound параметр `ε` можно фиксировать как `1`).

---

## 3) Минимальный proof-contract (что математически нужно вернуть)

Нужно вернуть theorem-пакет со следующими блоками.

### A. Конкретизация семейства `F`

Явно задать/указать формулы:

- `F.paramsOf n β`,
- `GapSliceFamily.encodedLen F n β`,
- `GapSliceFamily.tableLen F n β`,
- `F.Mof n (F.Tof n β)`,
- описание множеств `Yes` и `No` на slice.

### B. Конструкция изоляции `ρ`

Для любого корректного `C` под canonical bound построить:

- `D ⊆ Fin (tableLen)` и частичное присваивание `ρ` на `D`,

такое что:

1. `(Yes ∪ No) ∩ [ρ] ≠ ∅`;
2. `(Yes ∪ No) ∩ [ρ] ⊆ Yes`;
3. `|D| ≤ κ(n,β)` (или более сильный budget напрямую).

### C. Координатная семантика (`AgreeOnValues`)

Нужна точная usable-лемма:

`y ∈ [ρ] ∧ ValidEncoding p z ∧ AgreeOnValues (p := p) D y z -> z ∈ [ρ]`.

Без неё не закрывается acceptance-шаг builder-леммы.

### D. Slack-оценка

Нужно доказать:

`F.Mof n (F.Tof n β) < 2^(tableLen - κ(n,β))`.

Тогда через `|D| ≤ κ(n,β)` автоматически получается требуемый `hSlack`:

`F.Mof n (F.Tof n β) < 2^(tableLen - |D|)`.

### E. Size-cutoff (если source-лемма сначала в другом режиме)

Если исходная лемма доказывается в режиме `size ≤ 2^(β·m)`, нужно добавить:

- что такое `m` (`n`/`encodedLen`/`tableLen`),
- лемму перехода от `ppolyDAGSizeBoundOnSlices` к этому режиму,
- явный `n0_size(β)`.

---

## 4) Что не нужно доказывать снова

1. Не нужно заново доказывать bridge-level contradiction wrappers.
2. Не нужно заново доказывать class-level closure до `NP_not_subset_PpolyDAG`.
3. Не нужно строить новые API-endpoint'ы: текущие достаточно мощные.

---

## 5) Формат ответа от математиков (приёмка)

Ответ считается достаточным, если в нём есть:

1. Полный statement по кванторам (`β`, `n`, bounds, eventual пороги),
2. Конструкция `ρ` + доказательства non-vacuity/purity,
3. Координатная лемма про `AgreeOnValues`,
4. Натуральный budget `κ(n,β)` + slack inequality,
5. (при необходимости) size-cutoff мост,
6. Явное указание, какие леммы обеспечивают перенос в builder
   `smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt`.

---

## 6) Короткий итог для пересылки

Всё, кроме family-specific source-step, уже закрыто в Lean.

Чтобы полностью завершить route, математикам нужно дать только один пакет:

- построение one-sided isolating certificate `ρ` на канонических slices,
- координатную связку через `AgreeOnValues`,
- и slack через натуральный envelope `κ(n,β)`.

После этого endpoint `NP_not_subset_PpolyDAG` собирается существующими
теоремами без дополнительных архитектурных изменений.
