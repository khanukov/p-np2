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

`P_ne_NP_final` пока принимает два аргумента:

- `hNPDag : NP_not_subset_PpolyDAG` (реальный оставшийся логический блокер),
- `hMag : MagnificationAssumptions` (compatibility-контекст в сигнатуре).

---

## Что именно отсутствует для безусловного `NP_not_subset_PpolyDAG`

Отсутствует не endpoint, а **внутренний источник** одного из входов в эти endpoint-теоремы.
В практических терминах сейчас не хватает theorem-level результата, который внутри репозитория
(без внешнего `hNPDag`) построит, например, один из следующих payload:

- `dagRouteBSourceBlocker p*`, или
- эквивалентную source-closure/stable-restriction нагрузку,

на sound (невакуумной) поверхности.

Именно это в статусных документах обозначено как главный незакрытый DAG-side theorem debt.

---

## Можно ли «хотя бы доказать `ComplexityInterfaces.NP_not_subset_PpolyDAG`» уже сейчас?

### Да — **условно**

Если у вас уже есть:

- конкретный `W : GapPartialMCSP_TMWitness p`, и
- `hBlocker : dagRouteBSourceBlocker p`,

то `NP_not_subset_PpolyDAG_final_of_blocker_TM W hBlocker` уже даёт
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

### Нет — **безусловно, прямо сейчас**

Потому что в активном дереве нет внутренней теоремы, которая сама (без внешнего импорта
недостающей математики) производит необходимый `hBlocker`/эквивалентный payload.

---


## Комментарий к аудиторскому выводу (текущая позиция ветки)

Да, общий вектор аудитора корректный: literal fixed-slice маршрут не является
рабочим путём к безусловному закрытию и должен считаться no-go веткой.

Важное уточнение по активной ветке: этот no-go уже частично зафиксирован на
уровне специальных модулей исторического маршрута (`FailedRoute_*`), поэтому
новая документация теперь трактует fixed-slice только как legacy plumbing, а
единственный живой closure-route — asymptotic/eventual + length-local.

---

## Минимальный план закрытия (практически)

1. Закрыть один невакуумный source theorem на eventual/length-local поверхности
   (это текущий приоритет roadmap).
2. Из него получить один из существующих blocker/source-closure payload-ов.
3. Прогнать payload через уже готовый финальный wrapper и получить внутренний
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`.
4. Затем убрать `hNPDag` из default финала.
5. Отдельно убрать residual `hMag` (через concrete `_TM` bypass либо internalization
   magnification-пакета), чтобы получить zero-arg `P_ne_NP`.

---

## Definition of done (чтобы честно говорить «безусловно»)

Одновременно должны выполняться все пункты:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` доказан внутри дерева без внешнего DAG-входа.
2. Публичный финал не требует внешнего `hNPDag`.
3. Публичный финал не требует `hMag`.
4. В активной ветке выводится zero-arg теорема `P_ne_NP`.
