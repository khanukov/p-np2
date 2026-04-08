# Handoff (после внедрения non-vacuous eventual route): что уже реализовано и что осталось только от предметной части

**Дата:** 2026-04-08

## Что внедрено в код прямо сейчас

Ниже — фактически реализованный theorem package, который поднимает route с
вакуозного `GapSliceFamily` на живой носитель `GapSliceFamilyEventually`.

### 1) Введены eventual-объекты

В `AsymptoticDAGBarrierTheorems.lean` добавлены:

- `ppolyDAGSizeBoundOnSlicesEventually`
- `SmallDAGSolverEventually`
- `SmallDAGImpliesPromiseYesSubcubeAtEventually`

Это прямые eventual-аналоги старых объектов для legacy-carrier.

### 2) Добавлен локально-валидный builder на eventual-carrier

Добавлена теорема:

- `smallDAGImpliesPromiseYesSubcubeAt_of_yesIsolationAt_localValid_eventually`

Она работает в правильной локальной форме:
в source-гипотезе требуется `ValidEncoding` только для конкретного `yYes`,
а не глобально для всех `y ∈ Yes`.

### 3) Добавлена coherence-лемма с явным использованием `n ≥ F.N0`

Добавлена лемма:

- `eventual_coherence_at`

которая даёт нужные переписывания:

- `(F.paramsOf n β).n = n`,
- `F.Tof n β = (F.paramsOf n β).sNO - 1`,
- `F.Mof n (F.Tof n β) = circuitCountBound ...`,

при условии `F.N0 ≤ n`.

### 4) Добавлен главный envelope->eventual payload theorem на живом носителе

Добавлена теорема:

- `eventual_promiseYesSubcube_onCanonicalSlices_of_eventualIsolationEnvelopeEventually`

с правильным порогом

- `n ≥ max F.N0 (nIso β)`

и с локальной валидностью центра `yYes`.

### 5) Добавлен global-transport bridge на живом носителе

Добавлены:

- `AsymptoticDAGLanguageBridgeEventually`
- `ppolyDAGOnSlicesEventually_of_globalWitness`

То есть global witness на `bridge.L` теперь переносится на все slice-языки
`gapPartialMCSP_Language (F.paramsOf n β)` именно для `GapSliceFamilyEventually`.

### 6) Добавлены closure-теоремы до endpoint на живом носителе

Добавлены:

- `smallDAGSolverEventually_of_inPpolyDAGFamilyOnSlices`
- `no_dag_solver_of_promise_yes_subcube_at_eventually`
- `not_globalPpolyDAG_of_eventuallyPromiseYesWeakRouteEventually`
- `NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRouteEventually`
- `NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually`

Итог: non-vacuous generic bridge-математика теперь закрыта.

---

## Что осталось после этого (действительно только family-specific)

Теперь от предметной части нужны ровно 4 артефакта:

1. `def Fₑ : GapSliceFamilyEventually := ...`
2. `def κ : Nat → Rat → Nat := ...`
3. source-theorem в iso/forcing форме (локально-валидный `yYes` + `D` + forcing)
4. slack-лемма

```lean
Fₑ.Mof n (Fₑ.Tof n β) <
  2 ^ (GapSliceFamilyEventually.tableLen Fₑ n β - κ n β)
```

на нужном eventual-пороге `n ≥ max Fₑ.N0 (nIso β)`.

---

## Что больше НЕ является блокером

- Переход на non-vacuous carrier (`GapSliceFamilyEventually`) — реализован.
- Локальная валидность центра вместо глобального `hYesValid` — реализована.
- Global-to-slices bridge и class-level closure до `NP_not_subset_PpolyDAG` на eventual-carrier — реализованы.

То есть дальше остаётся только конкретная математика для выбранного `Fₑ`,
без новых инфраструктурных дыр.
