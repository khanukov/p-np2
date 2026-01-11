# План следующего этапа (важно сделать сейчас)

Ниже зафиксирован **ровно тот план, который сейчас важно доделать**. Он отражает,
что текущая версия уже разделяет слабую (`M²`) и сильную (polylog) оценки
глубины и использует сильную как дефолтную точку входа `ac0DepthBound`.
Конструктивный depth‑2 bound `M²` остаётся в интерфейсе как Stage‑1 оценка
`ac0DepthBound_weak`. Для финального результата (NP ⊄ P/poly без внешних фактов)
нужно вернуть **реальное** switching‑доказательство сильной оценки, чтобы
исключить временные мосты/малость. Этот документ фиксирует
последовательность и приоритеты.

---

## 1) Статус `M²`: финал или промежуточный этап?

**Ответ:**
- **Скорее всего, нет**, `M²` не годится как финальная оценка для цели P≠NP.
- **Да**, `M²` — отличный промежуточный, полностью формальный stage для depth‑2.

**Почему (аккуратная формулировка):**
- Stage‑1 даёт **честный, но грубый** сертификат (например, depthBound ≤ M² для depth‑2 DNF).
- Stage‑2 даёт **сильный** сертификат (polylog‑depthBound), который **заменяет**
  Stage‑1 на нужных параметрах, а не «доминируется» неравенством `M² ≤ polylog`.
- При типичном `M = n^k` условие малости перестаёт работать (кроме малых `k`),
  поэтому Stage‑1 не может быть финальным для целей P≠NP.

**Вывод:**
- Слабая оценка `M²` закреплена как **Stage‑1 (axiom‑free depth‑2)** через
  `ac0DepthBound_weak`.
- Сильная polylog‑оценка уже подключена как **точка входа** `ac0DepthBound`,
  но её корректность пока зависит от внешнего switching‑факта.

---

# Что делать дальше (конкретные шаги)

## Шаг A. Аудит на скрытые аксиомы

Аудит зафиксирован в `pnp3/Audit/Axioms.lean`. Он компилируется вместе
с проектом и печатает список аксиом для ключевых теорем:

```lean
#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0
#print axioms ThirdPartyFacts.ac0PartialWitness  -- если есть
#print axioms ThirdPartyFacts.shrinkage_for_localCircuit
#print axioms P_ne_NP  -- или как называется топ-теорема
```

**Цель:** убедиться, что в активном дереве нет аксиом, а внешние зависимости
действительно оформлены как witness-backed теоремы (без «аксиом под видом witness»).

Плюс быстро проверить, не стали ли финальные теоремы условными:

```lean
#check P_ne_NP
```

**Важно:** `pnp3/Audit/Axioms.lean` отделён от «боевого» кода и используется
только в рамках сборки тестов.

---

## Шаг B. Зафиксировать stage‑контракт в интерфейсе

Сейчас уже реализовано разделение слабой и сильной оценок:

```lean
def ac0DepthBound_weak (params : AC0Parameters) : Nat := params.M^2
def ac0DepthBound_strong (params : AC0Parameters) : Nat := (log₂(M+2))^(d+1)
def ac0DepthBound (params : AC0Parameters) : Nat := ac0DepthBound_strong params
```

Downstream использует `ac0DepthBound` как **верхнюю границу**, а Stage‑1
использует `ac0DepthBound_weak` и свидетелей `AC0SmallEnough`/`AC0DepthBoundWitness`
для конструктивного baseline. Stage‑2 **заменяет** этот путь на реальное
multi‑switching‑доказательство, а не «встраивает» Stage‑1 по неравенству.

---

## Шаг C. Проверить, ломает ли `M²` финальную цель

1) Найти все места использования `AC0SmallEnough` и нового bound:

```bash
rg -n "AC0SmallEnough|ac0DepthBound_weak|ac0DepthBound_strong|ac0DepthBound" pnp3
```

2) Оценить, превращаются ли ключевые теоремы в условные.
Если да — фиксируем: финальный результат требует polylog.

---

# Строго формальный план доказательства `partial_shrinkage_for_AC0` (Multi‑Switching)

Ниже зафиксирован полный план конструктивного доказательства `partial_shrinkage_for_AC0`
через multi‑switching. Этот раздел нужен как **рабочая спецификация** для финального
закрытия внешнего witness. Пишем максимально явно, чтобы по нему можно было
реализовать доказательство в Lean без дополнительных домыслов.

## Критические несостыковки, которые нужно закрыть до финальной интеграции

Ниже перечислены три узких места, без явного закрытия которых реальная индукция
не замкнётся в Lean или окажется математически неверной для снятия
`multi_switching_bound`.

1) **DNF в `Facts_Switching` vs CNF‑pipeline в `MultiSwitching`.**
   Сейчас witness строится на DNF‑термах/подкубах (`AC0Circuit.subcubes`),
   но текущий multi‑switching pipeline формально закрывает CNF‑ветку.
   Это нужно **явно согласовать** и **перепривязать целевой объект**:
   polylog‑цель должна быть про depthBound/PartialDT, а не про длину списка
   DNF‑термов. Иначе multi‑switching лемма доказывает «не тот объект».

2) **Encoding с “толстым” алфавитом (с `n`) ломает Numerics.**
   Encoding на `BitFix n` даёт фактор `2 * n` в базе степени и не совместим
   с `numerical_inequality_3_2`, где база должна быть независима от `n`.
   Нужен Håstad‑style small encoding через `Stars(w, t)` (см. «Шаг 3»).

3) **BadEvent должен быть детерминированным (CCDT‑глубина).**
   Для инъекции с малым алфавитом bad‑событие должно быть определено как
   `depth(CCDT) ≥ t`, а не как «существует трасса длины t». Связь
   `BadEvent → ∃ trace` оставляем как вспомогательную лемму (см. «Шаг 2»).

## Выбор shrinkage‑факта для замены

- Из двух внешних shrinkage‑фактов (A.1 и A.2) **проще полностью формализовать**
  `partial_shrinkage_for_AC0` для AC⁰. Здесь уже есть почти готовый пайплайн
  multi‑switching (AC⁰‑формулы, индукция по глубине, кодирование/инъекция,
  сборка shrinkage‑сертификата).
- Замена A.1 автоматически усиливает A.2 через
  `familyIsLocalCircuit_of_AC0_polylog`, поэтому **фокус на A.1** минимизирует
  общую работу.

## Шаг 1. Согласовать объект polylog‑bound (DNF ↔ CNF)

### 1.1. Архитектура (рекомендуется: DNF через CNF‑дуальность)

Оптимальный путь без ломки интерфейсов: **оставить основную логику в CNF**
и получить DNF‑результат через дуальность, но **polylog‑цель должна быть
переформулирована как bound на shrinkage/PartialDT**, а не на `allSubcubes.length`.

- Вводим перевод DNF → CNF для отрицания:
  - терм ↔ клауза при отрицании литералов;
  - `CNF_of_not_DNF` без экспоненциального роста.
- Лемма: `depth(DT(F|ρ)) = depth(DT((¬F)|ρ))`.

Это позволяет использовать CNF‑pipeline и получать DNF‑bound без изменений
в downstream.

### 1.2. Lean‑реализация (точки интеграции)

Создать модуль `pnp3/AC0/MultiSwitching/Duality.lean`:

- перевод `Term` → `Clause` через отрицание;
- `CNF_of_not_DNF`;
- равенство глубин decision tree для `F` и `¬F`.

Далее в `ThirdPartyFacts/Facts_Switching.lean`:

- либо переключить `AC0PolylogBoundWitness` на CNF‑представление,
- либо оставить DNF‑интерфейс, но доказывать его через CNF‑pipeline + дуальность.

**Definition of Done:** polylog‑bound доказывается для **depthBound**
сертификата shrinkage/PartialDT, а не для длины списка подкубов.
Если требуется оставить старое имя `ac0AllSubcubes_length_le_polylog_of_multi_switching`,
его смысл нужно пересмотреть и связать с depthBound через корректное
преобразование, а не через «количество DNF‑термов».

## Стратегия доказательства (индукция по глубине)

**Идея:** индукция по глубине схемы `d`.

- **База (depth = 2, DNF):**
  - Есть конструктивный partial PDT (список подкубов на термах).
  - Доказано существование сертификата с оценкой
    `ℓ ≤ log₂(M+2)` и `ε = 0` при грубой границе `|subcubes| ≤ M²`.
- **Шаг индукции (depth = d+1):**
  - Предполагаем shrinkage‑свойство для глубины `≤ d` с polylog‑границей.
  - Для глубины `d+1` строим общий partial PDT через CCDT.
  - Multi‑switching аргумент показывает существование хорошей рестрикции,
    на которой глубина PDT ограничена polylog.

## Параметры индукции

Фиксируем числовые параметры с запасом (эти определения уже есть в `Params`):

- `ℓ = ℓParam(M) = ⌊log₂(2M+1)⌋ + 1`.
  Лемма `pow_two_le_ℓParam` даёт `2^ℓ ≥ 2M`.
- `t = tParam(M, n) = ⌊log₂(M(n+2)+1)⌋ + 2`.
  Лемма `pow_two_le_tParam` даёт `2^t ≥ M (n+2)`.
  Это гарантирует малость `O(M · 2^{-t}) < 1/(n+2)`.

## Шаг 2. CCDT‑алгоритм и bad‑событие (детерминированно)

- Рассматриваем семейство формул `F` размера `M`, глубины `d+1`.
- Представляем верхний слой как CNF‑конъюнкцию подформул.
- Определяем детерминированный `CCDTAlgorithm`:
  - На шаге берём первую неудовлетворённую клаузу.
  - Фиксируем первый свободный литерал.
  - Ветвим по обоим значениям (PDT.node).
  - Останавливаемся через `ℓ` шагов, если не завершили раньше.
- **BadEvent фиксируем как детерминированное условие:**
  `BadEvent(ρ) := depth(CCDT(F|ρ)) ≥ t`.
  Это `DecidablePred`, что упрощает фильтрации по `ρ`.
- В `TraceBridge.lean` доказываем вспомогательную лемму:
  `BadEvent(ρ) → ∃ trace длины t` (для кодирования).

## Шаг 3. Множество плохих рестрикций

- Берём `R_s` — рестрикции с ровно `s` свободными битами.
- Выбор `s`: можно связать его с `t` (например, `s := tParam(M, n)`).
  Это синхронизирует параметр свободных переменных с глубиной хвоста.
- Определяем `Bad = {ρ ∈ R_s | BadEvent(ρ)}`.
  Цель: показать `Bad ⊊ R_s`, то есть существует хорошая рестрикция.

## Шаг 4. Encoding & Injection с малым алфавитом (Håstad‑style)

**Ключевой момент:** код **не должен содержать `Fin n`** на каждом шаге,
иначе база в оценке мощности будет содержать `n` и Numerics не закроется.
Нужен классический “small alphabet” encoding через `Stars`.

### 4.1. Структура кода

Вводим `Stars(w, t)` — последовательности непустых подмножеств `Fin w`
с суммарным размером `t`, и доказываем грубую оценку:
`|Stars(w, t)| ≤ (C * w)^t` (важна форма `w^t`, а не константа).

Кодирование имеет вид:

```
encodeBadSmall :
  Bad ∩ R_s → R_{s-t} × Stars(w+1, t) × BitVec t × Fin (m+1)
```

Здесь `R_{s-t}` — модифицированная финальная рестрикция (после применения
вспомогательных назначений, как в классическом proof‑by‑encoding),
`Stars` хранит “звёздные позиции” внутри ширины `w`, а `BitVec t` —
delta‑биты.

### 4.2. Что заменить в текущем encoding‑слое

- Удалить (или вывести как черновой) код, зависящий от `BitFix n`.
- Добавить модуль `AC0/MultiSwitching/Stars.lean` с оценкой
  `card_Stars_le`.
- Добавить `EncodingSmall` (или секцию в `Encoding.lean`) с
  `encodeBadSmall` и `Function.Injective`.

**Итог:** получаем оценку вида
`|Bad| ≤ |R_{s-t}| · (BParam w)^t`, где `BParam` **не зависит от n**.

## Шаг 5. Сравнение мощностей и связь с Numerics (Step 3.2)

Используем:

- `|R_s| = binom(n, s) * 2^{n-s}`
- `|R_{s-t}| = binom(n, s-t) * 2^{n-(s-t)}`

Дальше требуется вывести строгое `|Bad| < |R_s|`. В проекте это делается так:

- Применяем `numerical_inequality_3_2` для `BParam` без `n` в базе.
- Добавляем/используем лемму `tParam m n ≤ sParam n w`
  (держать в `Numerics.lean`, как часть Step 3.2).
- Затем применяем `exists_good_of_card_lt` (в `Counting`) и получаем
  `ρ* ∈ R_s` с `¬ BadEvent(ρ*)`.

## Шаг 6. Построение `PartialCertificate` из хорошей рестрикции

Пусть `ρ* ∈ R_s` — найденная хорошая рестрикция:

- Она задаёт **общий ствол** (trunk) глубины `ℓ = |ρ*|`.
- Для каждой формулы `f ∈ F` хвостовое дерево имеет глубину `< t`
  (из `¬ BadEvent(ρ*)`).
- Далее используем **индукционное предположение** для глубины `d`
  на каждой подформуле, полученной под ограничением `ρ*`.

Итог:

- Получаем `C : PartialCertificate(ℓ, F)`, удовлетворяющий `WorksFor F`.
- Из `C` строим `Shrinkage` (через `Core.PartialCertificate.toShrinkage`).

## Шаг 7. Реальная индукция по глубине (d > 2)

Нужно явно собрать шаг индукции:

- multi‑switching даёт `Good ρ*` для слоя глубины 2;
- хвосты строятся с помощью индукционного предположения для глубины `d`;
- доказываем формулу `depth(trunk ⊕ tails) = trunkDepth + max tailDepth`.

Рекомендуемый файл: `pnp3/AC0/MultiSwitching/DepthInduction.lean`
(или интегрировать в `Main.lean`, если там уже есть каркас).

## Шаг 8. Проверка границ и финальная интеграция

Далее надо проверить все условия в формулировке `partial_shrinkage_for_AC0`:

1) **Ограничение на ствол:**
   - `ℓ = ℓParam(M)` и `ℓ ≤ ⌊log₂(M+2)⌋` (через `pow_two_le_ℓParam` и округления).

2) **Общая глубина:**
   - `C.depthBound + ℓ ≤ ac0DepthBound(params)`.
   - Используется `ac0DepthBound_le_strong` и индукционный гипотезис
     для глубины `d` (polylog).

3) **Ошибка:**
   - По построению `ε = 0`, значит `0 ≤ ε ≤ 1/(n+2)`.

## Точки интеграции в Lean‑код

- **Encoding/Counting/Good‑restriction:** `pnp3/AC0/MultiSwitching/*`
  (уже в основном реализовано).
- **Главная лемма multi‑switching:** `AC0/MultiSwitching/Main.lean`
  (например, `ac0AllSubcubes_length_le_polylog_of_multi_switching`).
- **Свидетель polylog‑границы:** `Facts_Switching.lean`
  (`AC0PolylogBoundWitness` и `ac0DepthBoundWitness_of_polylog`).
- **Финальное внедрение:** заменить внешний witness в
  `ThirdPartyFacts/Facts_Switching.lean` на результат `partial_shrinkage_for_AC0_with_polylog`.

## Шаг 9. Развести типы для Stage‑1/Stage‑2 (depth‑2 DNF vs AC0Formula d)

Чтобы глубинная индукция была честной, нужна **явная граница между моделями**:

- `AC0Depth2Circuit` (текущий DNF depth‑2, Stage‑1 baseline с M²).
- `AC0Formula d` (общая глубина, Stage‑2 multi‑switching).

`FamilyIsAC0`/witness для реального AC⁰ должен ссылаться на `AC0Formula d`,
иначе polylog‑индукция «доказывает не тот тип».

## Expected Outcome (Definition of Done)

- `partial_shrinkage_for_AC0` доказан **без внешних witness** и возвращает
  **shrinkage/PartialDT‑сертификат** с polylog‑bound на глубину.
- `#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0`
  больше не показывает `ac0PolylogBoundWitness_of_multi_switching`.
- `AC0PolylogBoundWitness` и downstream используют **depthBound**, а не
  `allSubcubes.length` как целевой объект.
- Все downstream‑факты (`shrinkage_for_localCircuit`, magnification и т.д.)
  продолжают компилироваться без изменений.

## Минимальный набор команд для проверки после возврата

Точечные сборки:
```bash
lake build pnp3.ThirdPartyFacts.Facts_Switching
lake build pnp3.LowerBounds.LB_Formulas
lake build pnp3.LowerBounds.AntiChecker
lake build pnp3.Magnification.Facts_Magnification
```

Полный прогон:
```bash
lake build
```

Если `Magnification.Facts_Magnification` снова долго компилируется —
разрешён отдельный CI/ночной прогон, но полный build всё равно обязателен
перед важными фиксациями.

## Ключевые файлы, которые нужно помнить

- `pnp3/ThirdPartyFacts/Facts_Switching.lean` — depth‑2 AC⁰ и shrinkage.
- `pnp3/LowerBounds/LB_Formulas.lean` — downstream bounds (k, dictLen).
- `pnp3/LowerBounds/AntiChecker.lean` — bounds в anti‑checker.
- `pnp3/Magnification/Facts_Magnification.lean` — параметры magnification.
- `AC0_SHRINKAGE_PLAN.md` — главный маршрут и приоритеты.

## Важные принципы (чтобы не забыть)

- `ac0DepthBound` — **верхняя граница**, не «точная глубина».
- Stage‑1 (M²) — честный, полностью формальный, но **не финальный**.
- Stage‑2 (polylog) — только через реальную switching‑лемму,
  без bridge‑аксиом; достаточно вероятностного метода/подсчёта, без measure theory.
