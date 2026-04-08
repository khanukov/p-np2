# Оставшийся математический долг (единственный) для закрытия route до `NP_not_subset_PpolyDAG`

**Дата:** 2026-04-08
**Назначение документа:** дать внешней математической группе ровно тот контекст, который нужен, чтобы доказать *оставшийся* source-step.
**Что исключено:** исторические детали, альтернативные маршруты и уже закрытые промежуточные мосты, не влияющие на текущий долг.

---

## 1) Что уже закрыто в Lean (и больше не является долгом)

На стороне bridge/wrapper уже есть:

1. переход от eventual one-sided promise-YES payload к `¬ PpolyDAG bridge.L`;
2. переход от этого contradiction + `hNP : NP bridge.L` к `NP_not_subset_PpolyDAG`.

Следовательно, **доказывать нужно только source-side факт**, который поставляет этот eventual payload.

---

## 2) Точная оставшаяся цель (в математической форме)

Нужно доказать (для фиксированного семейства slices `F`) следующий структурный факт:

### `canonical_smallDAG_certificateIsolation_on_slices F`

Для каждого канонического witness-family `hInDag`, для достаточно малых `β` и больших `n`,
любой корректный малый DAG-решатель на соответствующем slice допускает
one-sided isolating certificate `ρ` с тремя свойствами:

1. `S_n ∩ [ρ] ≠ ∅` (non-vacuity),
2. `S_n ∩ [ρ] ⊆ Y_n` (one-sided purity),
3. `|dom ρ| ≤ c·β·n` (small certificate budget).

Здесь `Y_n ⊆ S_n ⊆ {0,1}^n` — YES/promise-domain соответствующего канонического slice.

---

## 3) Какой именно payload должен получиться на выходе source-доказательства

Именно этот формат (для каждого `hInDag`):

```text
∃ ε > 0, ∃ β0 > 0,
  ∀ β, 0 < β → β < β0 →
    ∃ n0, ∀ n ≥ n0,
      SmallDAGImpliesPromiseYesSubcubeAt
        F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε
```

После этого endpoint уже закрывается существующими теоремами.

---

## 4) Критические технические места, которые source-proof обязан покрыть

### 4.1 Мост `certificate isolation -> SmallDAGImpliesPromiseYesSubcubeAt`

Из `ρ` нужно конструктивно получить witness-данные для `...PromiseYesSubcubeAt`:

- выбрать `yYes ∈ S_n ∩ [ρ]`,
- положить `S := dom ρ`,
- доказать acceptance для любого promise-valid `z`, согласующегося с `yYes` на `S`,
  через `S_n ∩ [ρ] ⊆ Y_n` и корректность solver на promise-slice.

### 4.2 Количественный мост в `hSlack`

Нужно явно вывести inequality в точной форме, которую ждёт API:

```text
F.Mof n (F.Tof n β) < 2^(GapSliceFamily.tableLen F n β - S.card)
```

Это не «опционально»: без этого поле `hSlack` цель `...PromiseYesSubcubeAt` не соберётся.

### 4.3 Нормировка density (проверить до начала доказательства)

- Если downstream-предикат использует codim/ambient-density — достаточно версии A.
- Если используется relative-density внутри `S_n` — нужна усиленная версия с lower bound на fibers.

Эта развилка должна быть закрыта *до* финализации proof-пакета.

### 4.4 Size-cutoff (если source-лемма в режиме `size ≤ 2^(βn)`)

Если структурная лемма доказывается только под таким ограничением, нужен отдельный
length-local переход от
`ppolyDAGSizeBoundOnSlices F hInDag`
к `size ≤ 2^(βn)` начиная с некоторого `n0_size(β)`.

---

## 5) Минимальный self-contained словарь (встроен прямо здесь)

Ниже — компактные сигнатуры в стиле Lean, чтобы математики могли работать без
чтения репозитория.

### 5.1 Solver и canonical size-bound

```lean
def SmallDAGSolver
  (F : GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (n : Nat) (β ε : Rat) : Prop :=
  ∃ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) ∧
    CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β))
```

```lean
def ppolyDAGSizeBoundOnSlices
  (F : GapSliceFamily)
  (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
  Nat → Rat → Rat → Nat → Prop :=
  fun n β _ε s => s ≤ (hInDag n β).polyBound (GapSliceFamily.encodedLen F n β)
```

### 5.2 Целевая source-цель на одном slice

```lean
def SmallDAGImpliesPromiseYesSubcubeAt
  (F : GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (n : Nat) (β ε : Rat) : Prop :=
  let p := F.paramsOf n β
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams p) →
      ∃ yYes, yYes ∈ (gapSliceOfParams p).Yes ∧ ValidEncoding p yYes ∧
      ∃ S : Finset (Fin (GapSliceFamily.tableLen F n β)),
        F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableLen F n β - S.card) ∧
        ∀ z,
          (z ∈ (gapSliceOfParams p).Yes ∨ z ∈ (gapSliceOfParams p).No) →
          ValidEncoding p z →
          AgreeOnValues (p := p) S yYes z →
          DagCircuit.eval C z = true
```

### 5.3 Bridge-объект

```lean
structure AsymptoticDAGLanguageBridge (F : GapSliceFamily) where
  L : Language
  sliceEq :
    ∀ n β N x, L N x = gapPartialMCSP_Language (F.paramsOf n β) N x
```

### 5.4 Что требуется от NP-свидетеля

Нужен объект `hNP : ComplexityInterfaces.NP bridge.L` в точной форме текущего
интерфейса проекта (т.е. тот witness/verification package, который уже
используют class-level wrappers).

---

## 6) Что *не* является текущим долгом

1. Пере-доказывать contradiction wrappers и class-level closure.
2. Пере-доказывать eventual packaging helper-ы.
3. Пытаться закрыть «P ≠ NP в абсолютной внешней постановке» вне текущего интерфейса.

Текущий долг ровно один: **family-specific source-step**, описанный в §2–§4.

---

## 7) Формат ответа от внешней математической группы (приёмка)

Ответ считается достаточным, если содержит:

1. финальное statement source-леммы в кванторах (`β`, `n`, size constraints);
2. конструкцию `ρ` и полное доказательство non-vacuity/purity/budget;
3. отдельное доказательство моста в `hSlack` требуемой API-формы;
4. явный size-cutoff (если нужен);
5. явную пометку, какая нормировка используется (A или B) и почему;
6. отсутствие неформализуемых шагов типа “очевидно существует” без извлечения witness.

---

## 8) Итог в одном абзаце

Чтобы закрыть оставшуюся часть route, нужно доказать только одно:
для канонических slices вашего `F` малый корректный DAG всегда даёт one-sided
isolating certificate `ρ` с контролируемым budget, и это превращается в точный
`SmallDAGImpliesPromiseYesSubcubeAt`-payload (включая `hSlack`). Всё остальное
в цепочке до `NP_not_subset_PpolyDAG` уже реализовано.
