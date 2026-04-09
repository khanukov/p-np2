# Handoff (после доработки non-vacuous eventual route): что уже реализовано, что ещё можно сделать generic, и где реальные блокеры

**Дата:** 2026-04-09

## Что внедрено в код прямо сейчас

Ниже — фактически реализованный theorem package, который поднимает route с
вакуозного `GapSliceFamily` на живой носитель `GapSliceFamilyEventually`.

### 0) Зафиксирована «последняя общая теорема» (final generic reduction)

Добавлены новые теоремы:

- `isoStrongFamilyEventually_of_tableForceFamilyEventually`
- `NP_not_subset_PpolyDAG_of_tableForceSlackEventually_of_sliceConst`

Смысл:

1. Из table-force + slack строится `IsoStrongFamilyEventually` (для любого `hInDag`).
2. Через уже существующий адаптер `isoFamily_withPromise_of_isoStrongFamilyEventually`
   получаем wrapper-форму.
3. Через endpoint
   `NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_of_sliceConst`
   выводится
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`.

То есть это именно тот «последний общий редукционный шаг», после которого
остаётся только подстановка конкретных семейных артефактов.

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

### 5) Добавлен global-transport bridge на живом носителе (две версии)

Добавлены:

- `AsymptoticDAGLanguageBridgeEventually`
- `ppolyDAGOnSlicesEventually_of_globalWitness`
- `AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths`
- `ppolyDAGOnSlicesEventually_of_globalWitness_atCanonicalLengths`

Ключевой момент: теперь есть и **безопасная canonical-length поверхность**.
В canonical-length версии перенос делается так:

- на длине `GapSliceFamilyEventually.encodedLen F n β` используется исходное семейство;
- вне canonical-length используется `constFalseDag`;
- корректность off-canonical ветки доказывается через определение
  `gapPartialMCSP_Language` (там по определению `false` вне canonical длины).

Это снимает риск «нечаянного global-collapse» из-за слишком сильного all-length
равенства.

### 6) Добавлены closure-теоремы до endpoint на живом носителе

Добавлены:

- `smallDAGSolverEventually_of_inPpolyDAGFamilyOnSlices`
- `no_dag_solver_of_promise_yes_subcube_at_eventually`
- `not_globalPpolyDAG_of_eventuallyPromiseYesWeakRouteEventually`
- `NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRouteEventually`
- `NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually`
- `not_globalPpolyDAG_of_eventuallyPromiseYesWeakRouteEventually_atCanonicalLengths`
- `NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRouteEventually_atCanonicalLengths`
- `NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_atCanonicalLengths`

То есть endpoint-цепочка теперь доступна и на canonical-length bridge surface
(не только на legacy all-length surface).


### 7) Добавлена лемма покрытия `Yes ∪ No` на canonical длине

Добавлена лемма:

- `mem_yes_or_no_gapSliceOfParams`

Она фиксирует, что для любого
`x : Bitstring (partialInputLen p)` выполняется

- `x ∈ (gapSliceOfParams p).Yes ∨ x ∈ (gapSliceOfParams p).No`.

Практический смысл: в family-specific forcing-леммах дизъюнкт
`(z ∈ Yes ∨ z ∈ No)` обычно можно считать техническим (автоматически истинным
на canonical длине), а содержательная часть — это `ValidEncoding` + agreement.

Итог: non-vacuous generic bridge-математика закрыта **в обеих поверхностях**
(all-length и canonical-length), причём canonical-length является предпочтительной
для избежания искусственных коллапсов.

---

## Что осталось после этого (действительно family-specific + один интерфейсный выбор)

От предметной части всё ещё нужны ровно 4 артефакта:

1. `def Fₑ : GapSliceFamilyEventually := ...`
2. `def κ : Nat → Rat → Nat := ...`
3. source-theorem в iso/forcing форме (локально-валидный `yYes` + `D` + forcing)
4. slack-лемма

```lean
Fₑ.Mof n (Fₑ.Tof n β) <
  2 ^ (GapSliceFamilyEventually.tableLen Fₑ n β - κ n β)
```

на нужном eventual-пороге `n ≥ max Fₑ.N0 (nIso β)`.

И дополнительно нужно выбрать, в какой global-surface вы подаёте NP-гипотезу:

- либо legacy all-length bridge (`AsymptoticDAGLanguageBridgeEventually`);
- либо (предпочтительно) canonical-length bridge
  (`AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths`).

---

## Что больше НЕ является блокером (проверено повторно)

- Переход на non-vacuous carrier (`GapSliceFamilyEventually`) — реализован.
- Локальная валидность центра вместо глобального `hYesValid` — реализована.
- Global-to-slices bridge и class-level closure до `NP_not_subset_PpolyDAG`
  на eventual-carrier — реализованы, включая canonical-length вариант.

То есть дальше остаётся только конкретная математика для выбранного `Fₑ`,
без новых инфраструктурных дыр.


## Нормальная форма семейного долга (после последнего сужения)

В коде добавлен контракт:

- `IsoStrongFamilyEventually`
- `isoFamily_withPromise_of_isoStrongFamilyEventually`

Это фиксирует следующий workflow:

1. Предметная сторона может доказывать **сильную** forcing-форму без явного
   предположения `(z ∈ Yes ∨ z ∈ No)`.
2. Для совместимости с текущими wrapper-ами используется адаптер, который
   восстанавливает требуемую форму с promise-дизъюнктом (технически).

Иными словами, ответственность предметной стороны теперь ещё уже:
нужно дать именно strong-family пакет (`Fₑ`, `κ`, forcing, slack), а bridge-слой
сам дотягивает его до ожидаемого wrapper-интерфейса.


## Ответ на вопрос «можно ли ещё продвинуться к безусловности?» (честный статус)

Коротко: **да, немного можно (и мы продвинулись), но полностью безусловно закрыть
ещё нельзя**.

Что удалось дожать на generic-уровне:

1. Добавлена canonical-length bridge surface и transport, чтобы убрать
   неестественную all-length жёсткость.
2. Добавлены endpoint-теоремы в canonical-length форме, чтобы финальный вывод
   `NP_not_subset_PpolyDAG` можно было получать без all-length предположения.

Что остаётся принципиальным блокером (уже не infrastructure, а content):

1. Не хватает конкретного `Fₑ`.
2. Не хватает конкретного `κ`.
3. Не хватает forcing/isolation инстанса для этого `Fₑ`.
4. Не хватает slack-инстанса для этого `Fₑ` и `κ`.
5. Не хватает содержательной NP-точки входа (`hNP`) для выбранного global `L`.

То есть дальше блокеры не «невозможные вообще», а **неразрешимые без новой
предметной математики** (её нельзя синтезировать из текущего кода автоматически).

## Перепроверка статуса: можно ли уже безусловно закрыть `NP_not_subset_PpolyDAG`?

Короткий ответ: **ещё нет**.

Почему строго:

1. В репозитории по-прежнему отсутствует конкретный объект
   `def Fₑ : GapSliceFamilyEventually := ...`.
2. Нет конкретной функции budget
   `def κ : Nat → Rat → Nat := ...`
   для выбранного `Fₑ`.
3. Нет предметной family-леммы (в strong-форме или table-level форме),
   которая инстанцирует `IsoStrongFamilyEventually` для этого `Fₑ`.
4. Нет предметной slack-леммы для того же `Fₑ` и `κ`.
5. Для class-endpoint дополнительно нужен конкретный `bridge` и `hNP : NP bridge.L`
   (generic route уже умеет их использовать, но не синтезирует из воздуха).

Следовательно, из текущего контекста уже нельзя честно вывести
`NP_not_subset_PpolyDAG` без новых family-specific данных.

Хорошая новость: generic-инфраструктура уже достаточно полная, и при появлении
этих данных остаётся в основном предметная инстанциация без архитектурного
рефакторинга.


## Дополнительное сжатие входных данных (реализовано в коде)

Чтобы математики не тащили лишние формы, в код добавлены следующие
контракты/утилиты:

- `tableForceFamilyEventually`
- `patternForceFamilyEventually`
- `tableForceFamilyEventually_of_patternForceFamilyEventually`
- `canonicalGlobalLanguageEventually`
- `sliceConstFamilyEventually`
- `bridgeEventually_of_sliceConst`
- `NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_of_sliceConst`

Практический смысл:

1. Можно присылать table-level forcing пакет (или ещё более сильный pattern-level),
   не доказывая bitstring-level пакет вручную.
2. Для глобальной части можно прислать не `(bridge, hNP)`, а более лёгкую пару
   `(hSliceConst, hNP0)` относительно `canonicalGlobalLanguageEventually`;
   bridge строится автоматически функцией `bridgeEventually_of_sliceConst`.
3. Это ещё сильнее сужает ответственность предметной стороны до конкретного
   `Fₑ`, `κ`, forcing и slack.
