# Как довести до безусловности: актуальный статус и следующий рабочий трек

Дата фиксации: 2026-04-09.

## Короткий итог

На текущем шаге generic/plumbing-часть существенно очищена:

- non-vacuous eventual-carrier route есть;
- canonical-length bridge surface есть;
- тупиковый table-force/slack путь формально изолирован в failed-routes;
- активный continuation-path вынесен в отдельный модуль accepted-family.

Это означает: следующий прогресс больше не в bridge/plumbing, а в source-side
математике accepted-family типа.

---

## Что уже зафиксировано как закрытое/тупиковое

### 1) Закрытый (неактивный) путь

В `LowerBounds/FailedRoute_EventualTableForceSlackObstruction.lean` зафиксированы
диагностические теоремы:

- `failedRoute_tableForce_slack`
- `failedRoute_tableForce_sliceConst`

Они документируют, что соответствующий source-contract не подходит как активная
цель инстанциации.

### 2) Почему это важно

Мы больше не смешиваем:

- «маршрут, который математически закрыт как тупиковый», и
- «маршрут, по которому реально нужно двигаться дальше».

Это снижает риск ложного прогресса и повторного возврата к dead-end контракту.

---

## Активный continuation-route

В `LowerBounds/RouteNextStep_AcceptedFamily.lean` зафиксирован рабочий alias:

- `NP_not_subset_PpolyDAG_viaAcceptedFamilyRoute`

То есть текущий основной трек: accepted-family source surface
(`SmallDAGImpliesAcceptedFamilyStatement`) и её инстанциация.

---

## Что нужно сделать дальше (реально)

Нужно принести **содержательный accepted-family пакет** для выбранного семейства
(или эквивалентную по силе source-структуру), после чего использовать active
endpoint route.

Минимальный practical checklist:

1. Выбрать concrete family/spec на eventual-carrier.
2. Доказать accepted-family source-условие в форме,
   совместимой с `SmallDAGImpliesAcceptedFamilyStatement`.
3. Подключить это к `NP_not_subset_PpolyDAG_viaAcceptedFamilyRoute`.
4. Проверить, что публичные финальные обёртки не требуют deprecated surfaces.

---

## Что НЕ нужно делать

- не расширять table-force/pattern-force dead-end контракт;
- не возвращаться к convenience-route через `sliceConst` как к активной цели;
- не увеличивать API-слой без нового source theorem payload.

---

## Definition of Done для следующего этапа

Чтобы заявить новый нетривиальный прогресс, должно быть выполнено одновременно:

1. Принесён конкретный accepted-family source theorem (не wrapper-only).
2. Инстанцирован активный endpoint route без опоры на dead-end surfaces.
3. Build проходит на соответствующих модулях.
4. Документация синхронно обновлена (handoff + next-steps) под новый статус.
