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

## 2) Что сейчас важнее: математика или чистота кода?

**Ответ:**
- Сначала — **минимальная структурная чистка** (1–2 прохода), чтобы не утонуть.
- Затем — **фокус на математике** (switching lemma / multi‑switching / locality).

### Минимальная чистка (обязательный минимум)

1) **Явно пометить модель depth‑2.**
   Сейчас `AC0Circuit` фактически означает DNF depth‑2.
   Нужно явно это подчеркнуть:
   - либо переименовать в `AC0Depth2Circuit` / `DNF2Circuit`,
   - либо добавить заметный комментарий в `Facts_Switching.lean`, что
     AC⁰ здесь моделируется depth‑2 DNF.

2) **Разнести `Facts_Switching.lean` по файлам.**
   Это снизит риск циклов импортов и упростит будущие изменения
   switching‑леммы (в том числе замены временных мостов).
   Предлагаемая разбивка:
   - `AC0Depth2/DNF_Subcubes.lean`
     (termToSubcube, dnfToSubcubes, coveredB-леммы)
   - `AC0Depth2/Shrinkage_M2.lean`
     (PartialCertificate, PDT из подкубов, bound `M²`)
   - `Facts_Switching.lean`
     (интерфейс и тонкие определения)

### После этого — математика

Дальше главное: формализация настоящей switching‑леммы.
Это единственный корректный путь вернуть polylog‑оценку и сохранить честность.

---

## 3) Тестирование: полный `lake build` или точечно?

**Ответ:**
- Используем **оба режима**.
- **Полный build обязателен** перед важными слияниями.

### Точечные сборки после каждого изменения

```bash
lake build pnp3.ThirdPartyFacts.Facts_Switching
lake build pnp3.LowerBounds.LB_Formulas
lake build pnp3.LowerBounds.AntiChecker
lake build pnp3.Magnification.Facts_Magnification
```

### Полный `lake build` перед важными фиксациями

Lean часто ломается в неожиданных местах, поэтому полный прогон обязателен.
Если сборка `Magnification.Facts_Magnification` слишком долго идёт:
- допускается ночной/CI‑прогон на более мощной машине,
- **но нельзя навсегда заменить full build на только точечные проверки**.

---

# Что делать дальше (конкретные шаги)

## Шаг A. Аудит на скрытые аксиомы

Аудит уже зафиксирован в `pnp3/Tests/AxiomsAudit.lean`. Он компилируется вместе
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

**Важно:** `AxiomsAudit.lean` уже отделён от «боевого» кода (лежит в `Tests/`)
и используется только в рамках сборки тестов.

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

# Если цель — вернуть polylog (Stage‑2), что формализовать первым

Наиболее практичный и Lean‑дружелюбный маршрут:

1) **Truncation ширины** DNF/CNF до `w`:
   ошибка ≤ `M · 2^{-w}`.
2) **Switching lemma для ширины `w`** (комбинаторное доказательство
   через инъекцию Разборова / конспекты О’Доннелла).
3) **Union bound** на семейство формул (если нужен единый сертификат для `F`).

Это даёт polylog‑bound **без bridge‑аксиом и без тяжёлой вероятности**.
Нам достаточно вероятностного метода через подсчёт конечных множеств
ограничений (например, `3^n`), без measure theory: нужна лишь
**существование** подходящего ограничения, а не конструктивность.

---

# Итоговые ответы на вопросы (в нужном формате)

1. **M² — окончательно или нет?**
   **Как промежуточный stage — да. Как финальная цель для P≠NP — нет, нужен возврат
   к polylog через реальную switching‑лемму.**

2. **Фокус: математика или чистый код?**
   **Сначала минимально стабилизировать структуру (переименование/разнос файлов/док),
   потом фокус на математике.**

3. **Тесты: полный build или точечно?**
   **Полный build перед важными фиксациями + точечные сборки после каждого изменения.**

---

# Консервация состояния (handoff без потерь)

Этот раздел фиксирует, **что именно ещё надо сделать**, чтобы можно было
безопасно отложить задачу и позже (даже другим человеком) продолжить без
вопросов и потерь контекста.

## Что ещё нужно сделать прямо сейчас, чтобы «законсервировать» проект

1) **Сделать Audit‑файл с аксиомами и положить в отдельный namespace.**
   - Создать `Audit/Audit.lean` (или аналогичную папку).
   - Убедиться, что он **не импортируется** в production‑модули.
   - Содержимое (минимум):
     ```lean
     #print axioms ThirdPartyFacts.partial_shrinkage_for_AC0
     #print axioms ThirdPartyFacts.ac0PartialWitness  -- если есть
     #print axioms ThirdPartyFacts.shrinkage_for_localCircuit
     #print axioms P_ne_NP  -- или как называется топ‑теорема
     #check P_ne_NP
     ```
   - Цель: зафиксировать, какие именно внешние факты остались.

2) **Явно обозначить depth‑2 модель в коде.**
   - Минимум: заметный комментарий в `ThirdPartyFacts/Facts_Switching.lean`
     (“AC⁰ пока моделируется только depth‑2 DNF”).
   - Лучше: переименование `AC0Circuit → AC0Depth2Circuit` (или `DNF2Circuit`),
     но это можно сделать отдельным коммитом.

3) **Разнести `Facts_Switching.lean` по файлам (минимальная структурная чистка).**
   - Рекомендуемая разбивка:
     - `AC0Depth2/DNF_Subcubes.lean`
       (termToSubcube, dnfToSubcubes, coveredB‑леммы)
     - `AC0Depth2/Shrinkage_M2.lean`
       (PartialCertificate, PDT из подкубов, bound `M²`)
     - `Facts_Switching.lean`
       (интерфейс и тонкие определения)
   - Это снижает риск циклов импортов и упрощает сопровождение
     weak/strong‑слоёв без массовых правок.

4) **Записать точку входа для Stage‑2 (polylog):**
   - Отдельный namespace/target `Facts_Switching_Strong`.
   - Никаких импортов этого слоя в axiom‑free ветку.
   - Ясная формулировка: strong‑слой — это **цель**, а не факт.

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

Если `Magnification.Facts_Magnification` снова долго компилируется —\n
разрешён отдельный CI/ночной прогон, но полный build всё равно обязателен\n
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
