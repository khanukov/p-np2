# Как довести до конца безусловное доказательство? Что реально не хватает сейчас?

Обновлено: 2026-04-04.

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

И уже после этого остаётся второй шаг до truly zero-arg финала: убрать `hMag` из
публичного API.

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

Исторический bundle-аргумент `hMag : MagnificationAssumptions` вынесен в
compatibility wrapper `P_ne_NP_final_of_magnification`.

---

## Что именно отсутствует для безусловного `NP_not_subset_PpolyDAG`

Для `NP_not_subset_PpolyDAG` основной route в активном дереве замкнут на
текущем assumption surface:
`NP_not_subset_PpolyDAG_final hMS hAsym hNPbridge`
(и compatibility-версия `NP_not_subset_PpolyDAG_final_of_magnification hMag`).

Текущий DAG-side маршрут замкнут так:

1. на пороговом canonical slice любой witness `PpolyDAG` переводится в
   witness `PpolyFormula`,
2. support-bounds приходят из `hMS`,
3. дальше срабатывает уже закрытый fixed-slice collapse consumer.

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
2. Закрыть formula-side internalization, чтобы
   `NP_not_subset_PpolyFormula_final` больше не принимал `hMag`.
3. Затем убрать residual assumption payload из `P_ne_NP_final`.
4. После этого получить zero-arg `P_ne_NP`.

---

## Definition of done (чтобы честно говорить «безусловно»)

Одновременно должны выполняться все пункты:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` доказан внутри дерева без внешнего DAG-входа.
2. Публичный финал не требует внешнего class-level `NP_not_subset_PpolyDAG`.
3. Публичный финал не требует внешнего assumption payload.
4. В активной ветке выводится zero-arg теорема `P_ne_NP`.
