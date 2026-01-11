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
- `AC0SmallEnough : M² ≤ ac0DepthBound_strong` ⇒ слабая оценка
  встраивается в polylog‑цель и позволяет перейти к strong‑границам.
- При типичном `M = n^k` условие малости перестаёт работать (кроме малых `k`).
- Значит, финальные теоремы, вероятно, становятся слабее или не применимы к
  нужным диапазонам параметров (зависит от того, что именно обозначает `M`
  и где требуется `AC0SmallEnough`).

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
для конструктивного перехода к сильной цели.

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

## Выбор shrinkage‑факта для замены

- Из двух внешних shrinkage‑фактов (A.1 и A.2) **проще полностью формализовать**
  `partial_shrinkage_for_AC0` для AC⁰. Здесь уже есть почти готовый пайплайн
  multi‑switching (AC⁰‑формулы, индукция по глубине, кодирование/инъекция,
  сборка shrinkage‑сертификата).
- Замена A.1 автоматически усиливает A.2 через
  `familyIsLocalCircuit_of_AC0_polylog`, поэтому **фокус на A.1** минимизирует
  общую работу.

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

## Шаг 1. CCDT‑алгоритм и плохое событие

- Рассматриваем семейство формул `F` размера `M`, глубины `d+1`.
- Представляем верхний слой как CNF‑конъюнкцию подформул.
- Определяем детерминированный `CCDTAlgorithm`:
  - На шаге берём первую неудовлетворённую клаузу.
  - Фиксируем первый свободный литерал.
  - Ветвим по обоим значениям (PDT.node).
  - Останавливаемся через `ℓ` шагов, если не завершили раньше.
- Плохое событие: `BadEvent(ρ)` = «глубина ствола ≥ t».
  Это `DecidablePred`, что упрощает фильтрации по `ρ`.

## Шаг 2. Множество плохих рестрикций

- Берём `R_s` — рестрикции с ровно `s` свободными битами.
- Выбор `s`: можно связать его с `t` (например, `s := tParam(M, n)`).
  Это синхронизирует параметр свободных переменных с глубиной хвоста.
- Определяем `Bad = {ρ ∈ R_s | BadEvent(ρ)}`.
  Цель: показать `Bad ⊊ R_s`, то есть существует хорошая рестрикция.

## Шаг 3. Encoding & Injection (кодирование плохих случаев)

**Общий принцип:** injective‑кодирование bad‑рестрикций в конечное множество,
размер которого можно явно оценить.

1) **Финальная рестрикция после t шагов.**
   - Если `ρ ∈ Bad`, то первые `t` ветвлений CCDT определяют трассу длины `t`.
   - Применяя эти `t` фиксаций к `ρ`, получаем `β = finalRestriction ρ`.
   - Леммы `freeCount_finalRestriction` и `finalRestriction_mem_R_s`
     дают `β ∈ R_{s-t}`.

2) **Код пути (Aux).**
   - Вводим конечное множество `Aux(n, t, k, m)` — все возможные трассы длины `t`.
   - Каждый шаг хранит:
     - какой литерал фиксировали (`BitFix n`),
     - позицию литерала в клаузе (≤ `k`),
     - индекс формулы (≤ `m`).
   - В итоге `|Aux| = (2 * n * k * m)^t`.

3) **Определение кодирования.**
   - `encode(ρ) := (β, code(ρ)) ∈ R_{s-t} × Aux`.
   - Детерминизм CCDT ⇒ `encode` инъективно.

**Итог:** `|Bad| ≤ |R_{s-t}| · |Aux|`,
формализовано как `badRestrictions_card_le_of_aux_encoding`.

## Шаг 4. Сравнение мощностей и существование хорошей рестрикции

Используем:

- `|R_s| = binom(n, s) * 2^{n-s}`
- `|R_{s-t}| = binom(n, s-t) * 2^{n-(s-t)}`

Дальше требуется вывести строгое `|Bad| < |R_s|`. В проекте это делается так:

- Из `2^t ≥ M(n+2)` и грубых оценок на `k, m ≤ M` получаем оценку
  `|Bad| ≤ |R_{s-t}| · (2 n k m)^t`.
- Затем применяем лемму `exists_good_of_card_lt` (в `Counting`) и выводим
  существование `ρ* ∈ R_s` с `¬ BadEvent(ρ*)`.

Ссылки на Lean‑реализацию:

- `badRestrictions_card_le_of_aux_encoding`
- `exists_good_restriction_of_aux_encoding`

## Шаг 5. Построение `PartialCertificate` из хорошей рестрикции

Пусть `ρ* ∈ R_s` — найденная хорошая рестрикция:

- Она задаёт **общий ствол** (trunk) глубины `ℓ = |ρ*|`.
- Для каждой формулы `f ∈ F` хвостовое дерево имеет глубину `< t`
  (из `¬ BadEvent(ρ*)`).
- Далее используем **индукционное предположение** для глубины `d`
  на каждой подформуле, полученной под ограничением `ρ*`.

Итог:

- Получаем `C : PartialCertificate(ℓ, F)`, удовлетворяющий `WorksFor F`.
- Из `C` строим `Shrinkage` (через `Core.PartialCertificate.toShrinkage`).

## Шаг 6. Проверка границ и финальная интеграция

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

## Expected Outcome (Definition of Done)

- `partial_shrinkage_for_AC0` доказан **без внешних witness**.
- `#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0`
  больше не показывает `ac0PolylogBoundWitness_of_multi_switching`.
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
