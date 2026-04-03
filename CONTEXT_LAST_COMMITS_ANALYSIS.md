# Анализ старого стека коммитов: исторический контекст

Обновлено: 2026-04-03

## Статус файла

Этот файл больше не является источником текущего статуса репозитория.
Он сохраняется как исторический разбор одного старого стека коммитов и не
должен использоваться для ответа на вопрос «где сейчас находится проект».

Для актуального состояния используйте только:

- `README.md`
- `STATUS.md`
- `TODO.md`
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`
- `pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`

## Текущая реальность поверх этого исторического анализа

После описанного здесь старого frontier/payload/refute-стека проект ушёл
дальше. На текущей ветке уже закрыты:

1. hardwire coverage proof для canonical easy family;
2. canonical witness-density / witness-transfer compiler glue;
3. support-half fallback closure до class-level DAG non-inclusion surface;
4. asymptotic fixed-slice DAG wrappers в `Magnification/FinalResult.lean`.

Одновременно всё ещё не закрыты:

1. внутренний theorem `ComplexityInterfaces.NP_not_subset_PpolyDAG`;
2. zero-argument публичный theorem `P_ne_NP`;
3. fixed-slice DAG source theorem, который является ближайшим честным
   blocker'ом.

## Исторический предмет файла

Ниже можно держать старый анализ коммитного стека как пояснение, зачем в
репозитории появились некоторые слои `frontier / payload / consumer`. Но этот
анализ не должен использоваться как roadmap.

Старый фокус:

- модульный `singleton-density` / `gap-target` pipeline;
- усиление consumer-слоя в `LowerBounds`;
- доказательная магистраль старого этапа до cube-refute consumer frontier.

Если нужен текущий roadmap, смотрите
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.
