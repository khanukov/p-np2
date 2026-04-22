# Как довести до конца безусловное доказательство? Что реально не хватает сейчас?

Обновлено: 2026-04-17.

Политика маршрута (canonical lock):
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## Короткий и честный ответ

**Полностью безусловно — пока нет, не всё есть.**

Но важная развилка такая:

1. **Условно `ComplexityInterfaces.NP_not_subset_PpolyDAG` уже можно получать**
   (через готовые wrappers), если вы подаёте недостающий source payload.
2. **Безусловно `ComplexityInterfaces.NP_not_subset_PpolyDAG` пока нельзя**, потому что
   в дереве всё ещё нет внутреннего theorem-level источника этого payload без внешних
   допущений.

И уже после этого остаётся второй шаг до truly zero-arg финала: убрать
остаточный provider payload (`hAsym/hNPbridge`) из публичной поверхности.

---

## Что уже есть «из коробки»

### 1) Интерфейсное определение цели

`ComplexityInterfaces.NP_not_subset_PpolyDAG` уже определён как пропозиция на уровне
интерфейса (`∃ L, NP L ∧ ¬ PpolyDAG L`).

### 2) Готовые конечные маршруты к этой цели (но с входными предпосылками)

Ветка уже содержит рабочие endpoint-теоремы, например:

- `NP_not_subset_PpolyDAG_final_of_asymptotic_blocker` (асимптотический маршрут),
- `NP_not_subset_PpolyDAG_final_of_blocker_TM` (конкретный `_TM` маршрут).

То есть «проводка» от source-предпосылки к финальной DAG-сепарации уже собрана.

### 3) Почему текущий default всё ещё не безусловный

`P_ne_NP_final` сейчас принимает три содержательных аргумента:

- `hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract`,
- `hAsym : AsymptoticFormulaTrackHypothesis`,
- `hNPbridge : AsymptoticNPPullback hAsym`.

Исторический bundle-аргумент `hMag : MagnificationAssumptions` уже вынесен в
compatibility wrapper `P_ne_NP_final_of_magnification` и не является
блокером на default-маршруте.

Дополнительно есть промежуточный шаг closure:

- `P_ne_NP_of_default_formulaSource` закрывает formula-side компонент `hMS`
  через `hasDefaultFormulaSupportRestrictionBoundsPartial`;
- но asymptotic-компонент (`hAsym/hNPbridge`) всё ещё внешний (через
  provider-класс).

---

## Что именно отсутствует для безусловного финала

Для `NP_not_subset_PpolyDAG` основной route в активном дереве уже замкнут на
текущем assumption surface:
`NP_not_subset_PpolyDAG_final hMS hAsym hNPbridge`
(и compatibility-версия `NP_not_subset_PpolyDAG_final_of_magnification hMag`).

Текущий DAG-side маршрут замкнут так:

1. на пороговом canonical slice любой witness `PpolyDAG` переводится в
   witness `PpolyFormula`,
2. support-bounds приходят из `hMS`,
3. дальше срабатывает уже закрытый fixed-slice collapse consumer.

Главный оставшийся долг до безусловного `P_ne_NP`:

1. построить внутренний источник `AsymptoticFormulaTrackHypothesis`
   (для default-route это уже можно подавать через
   `hasDefaultAsymptoticFormulaTrackHypothesis` без provider-класса);
2. доказать внутренний `AsymptoticNPPullback` для него
   (для default-route это формализовано как
   `hasDefaultAsymptoticNPPullbackFor hAsym`);
3. удалить зависимость public endpoint от `FinalPayloadProvider` /
   `AsymptoticPayloadProvider`.

Технический прогресс по этому пункту: добавлен provider-free маршрут
`P_ne_NP_of_constructive_asymptoticData`, где `hAsym/hNPbridge` строятся
внутри из явной структуры `AsymptoticFormulaTrackData` (а не через class-level
provider).

---

## Можно ли «хотя бы доказать `ComplexityInterfaces.NP_not_subset_PpolyDAG`» уже сейчас?

### Да — **условно на текущем наборе предпосылок**

Именно это и делает текущий default:

- `NP_not_subset_PpolyDAG_final hMS hAsym hNPbridge` даёт
  `ComplexityInterfaces.NP_not_subset_PpolyDAG`,
- `P_ne_NP_final hMS hAsym hNPbridge` сразу даёт `ComplexityInterfaces.P_ne_NP`.

### Нет — **безусловно, прямо сейчас**

Потому что в активном дереве всё ещё нет внутренней zero-arg теоремы,
которая сама строит/устраняет весь оставшийся assumption payload.

---


## Комментарий к аудиторскому выводу (текущая позиция ветки)

Да, общий вектор аудитора корректный: literal fixed-slice маршрут не является
рабочим путём к безусловному закрытию и должен считаться no-go веткой.

Важное уточнение по активной ветке: no-go относится к историческому
fixed-slice support-half / blocker hunt. Текущий замкнутый DAG-маршрут другой:
он использует fixed-slice `DAG -> Formula` bridge на пороговом slice и не
воскрешает старую support-half ветку.

---

## Минимальный план закрытия (практически)

1. Сохранить текущую internalized DAG-сепарацию как closed route.
2. Зафиксировать formula-side internalization через
   `P_ne_NP_of_default_formulaSource` как canonical-путь для `hMS`.
3. Построить theorem-level внутренний asymptotic source
   (`hAsym` + `hNPbridge`) без внешнего provider-контракта.
4. Перевести `P_ne_NP` на truly zero-arg интерфейс без provider payload.

### Практический sequencing (что делать прямо сейчас)

1. **Сначала изолировать формально остаток**:
   оставить только `AsymptoticPayloadProvider` как единственный внешний вход
   на default-финале (без возврата к bundle API).
2. **Потом выбить `hAsym` внутри дерева**:
   ввести локальный модуль-поставщик с явными леммами-предпосылками и
   минимальным публичным surface (без новых аксиом/`sorry`).
3. **Затем закрыть `hNPbridge` от построенного `hAsym`**:
   отдельной цепочкой теорем, чтобы bridge не висел как внешний класс.
4. **И только после этого** удалить provider-слой с публичного endpoint,
   оставив compatibility-обёртки исключительно как deprecated-слой.

---

## Definition of done (чтобы честно говорить «безусловно»)

Одновременно должны выполняться все пункты:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` доказан внутри дерева без внешнего DAG-входа.
2. Публичный финал не требует внешнего class-level `NP_not_subset_PpolyDAG`.
3. Публичный финал не требует внешнего assumption payload.
4. В активной ветке выводится zero-arg теорема `P_ne_NP`.
5. `./scripts/check.sh` и аудит-тесты проходят без специальных provider-заглушек.
