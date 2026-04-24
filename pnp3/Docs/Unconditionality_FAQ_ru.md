# Как довести до конца безусловное доказательство? Что реально не хватает сейчас?

Обновлено: 2026-04-23.

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

Публичная поверхность теперь сведена к одному честному frontier-объекту:
`ResearchGapWitness`.  Чтобы получить truly zero-arg финал, нужно доказать этот
witness внутри `pnp3/Magnification/UnconditionalResearchGap.lean`.

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

### 3) Почему текущий public final всё ещё не безусловный

`P_ne_NP_final` сейчас принимает один содержательный аргумент:

- `gap : ResearchGapWitness`.

Этот witness содержит ровно оставшийся математический долг:
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

Старый multiswitching/asymptotic маршрут всё ещё сохранён, но теперь он явно
назван как audit/legacy endpoint:

- `NP_not_subset_PpolyDAG_final_of_multiswitchingData hMS D`,
- `P_ne_NP_final_of_multiswitchingData hMS D`.

`D` содержит и asymptotic slice source, и TM-свидетельство NP-membership, поэтому
`hNPbridge : AsymptoticNPPullback ...` больше не является публичным входом даже
у legacy mainline-маршрута.

Исторический bundle-аргумент `hMag : MagnificationAssumptions` уже вынесен в
compatibility wrapper `P_ne_NP_final_of_magnification` и не является
блокером на default-маршруте.

Дополнительно есть промежуточные closure-шаги, но они больше не маскируются под
финальный безусловный API.  Если они проходят через refuted support-bounds
surface, они остаются compatibility/audit plumbing.

---

## Что именно отсутствует для безусловного финала

Для `NP_not_subset_PpolyDAG` публичный route в активном дереве теперь замкнут на
одном frontier object:
`NP_not_subset_PpolyDAG_final gap`,
где `gap : ResearchGapWitness`.

Legacy compatibility-маршруты вроде
`NP_not_subset_PpolyDAG_final_of_multiswitchingData hMS D` и
`NP_not_subset_PpolyDAG_final_of_magnification hMag` оставлены для аудита и
обратной совместимости, но не считаются безусловным прогрессом.

Старый DAG-side audit-маршрут замкнут так:

1. на пороговом canonical slice любой witness `PpolyDAG` переводится в
   witness `PpolyFormula`,
2. support-bounds приходят из `hMS`,
3. дальше срабатывает уже закрытый fixed-slice collapse consumer.

Главный оставшийся долг до безусловного `P_ne_NP` теперь локализован в одном
поле:

```text
ResearchGapWitness.dagSeparation :
  ComplexityInterfaces.NP_not_subset_PpolyDAG
```

На более низком уровне это может быть доказано через новый formula/locality
source theorem, но такой theorem должен:

1. не использовать refuted
   `FormulaSupportBoundsFromMultiSwitchingContract`;
2. не восстанавливать старый ложный `FormulaSupportRestrictionBoundsPartial`;
3. обходить truth-table hardwiring и singleton/per-formula AC0 provenance;
4. давать настоящий `ComplexityInterfaces.NP_not_subset_PpolyDAG`.

Технический прогресс по этому пункту: `P_ne_NP_final` и
`NP_not_subset_PpolyDAG_final` больше не принимают `hMS`, `hAsym`,
`hNPbridge` или `D` напрямую.  Эти surfaces сохранены только как
compatibility/audit wrappers.

---

## Можно ли «хотя бы доказать `ComplexityInterfaces.NP_not_subset_PpolyDAG`» уже сейчас?

### Да — **условно на текущем наборе предпосылок**

Именно это делает честный frontier endpoint:

- `NP_not_subset_PpolyDAG_final gap` даёт
  `ComplexityInterfaces.NP_not_subset_PpolyDAG`,
- `P_ne_NP_final gap` сразу даёт `ComplexityInterfaces.P_ne_NP`.

Старый audit route тоже остаётся условным:

- `NP_not_subset_PpolyDAG_final_of_multiswitchingData hMS D`,
- `P_ne_NP_final_of_multiswitchingData hMS D`.

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

1. Держать `pnp3/Magnification/UnconditionalResearchGap.lean` как единственный
   файл, где должен появиться breakthrough.
2. Доказать `ResearchGapWitness` без refuted support-bounds surfaces.
3. После этого добавить zero-arg theorem:
   `P_ne_NP_unconditional : ComplexityInterfaces.P_ne_NP`.

### Практический sequencing (что делать прямо сейчас)

1. **Сначала доказать не-вакуозный source theorem**:
   он должен дать `ComplexityInterfaces.NP_not_subset_PpolyDAG` или
   достаточный lower-level theorem, из которого это следует.
2. **Потом построить `ResearchGapWitness` внутри
   `UnconditionalResearchGap.lean`**.
3. **И только после этого** включить commented template
   `P_ne_NP_unconditional`.

---

## Definition of done (чтобы честно говорить «безусловно»)

Одновременно должны выполняться все пункты:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` доказан внутри дерева без внешнего DAG-входа.
2. Публичный финал не требует внешнего class-level `NP_not_subset_PpolyDAG`.
3. Публичный финал не требует внешнего assumption payload.
4. В активной ветке выводится zero-arg теорема `P_ne_NP_unconditional`.
5. `./scripts/check.sh` и аудит-тесты проходят без специальных provider-заглушек.
