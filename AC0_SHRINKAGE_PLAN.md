# План следующего этапа (важно сделать сейчас)

Ниже зафиксирован **ровно тот план, который сейчас важно доделать**. Он отражает,
что текущая версия уже разделяет слабую (`M²`) и сильную (polylog) оценки
глубины, но **strong нельзя использовать как дефолт**, пока он не доказан.
Конструктивный depth‑2 bound `M²` остаётся в интерфейсе как Stage‑1 оценка
`ac0DepthBound_weak`. Для финального результата (NP ⊄ P/poly без внешних фактов)
нужно вернуть **реальное** switching‑доказательство сильной оценки, чтобы
исключить временные мосты/малость. Этот документ фиксирует
последовательность и приоритеты.


---

# Progress log (обновляется по мере выполнения)

## Status snapshot
- [x] Скан по репозиторию: найдено определение `partial_shrinkage_for_AC0` и точки использования (см. `pnp3/ThirdPartyFacts/Facts_Switching.lean` и тестовые аудиты). Это нужно для корректного изменения цели и для замены внешнего witness.  
  - Источники: `pnp3/ThirdPartyFacts/Facts_Switching.lean` (основная реализация), `pnp3/Tests/AxiomAudit.lean`, `pnp3/Audit/Axioms.lean`, `pnp3/Tests/AxiomsAudit.lean` (аудит аксиом).
- [x] Добавлен модуль дуальности (DNF→¬CNF) на уровне `Core`‑типов для явной связи DNF‑интерфейса с CNF‑пайплайном: `pnp3/AC0/MultiSwitching/Duality.lean` с определениями `Literal.neg`, `DnfTerm.negToClause`, `DNF.negToCNF` и леммами для `eval`.
- [x] Усилен мост дуальности: добавлена лемма двойного отрицания для DNF (`eval_negToCNF_neg`) и равенство семейств функций при переходе `DNF → CNF` (`eval_negDnfFamilyToCnfFamily_family`). Это упрощает переписывания в будущей связке DNF↔CNF.
- [x] Уточнён интерфейс дуальности: `eval_negDnfFamilyToCnfFamily` теперь явно выводится из семейной леммы, чтобы все точечные переписывания опирались на единый факт.
- [x] Добавлен явный мост `AC0.Formulas.DNF → Core.DNF` через функции `toCoreDNF` и лемму `eval_toCoreDNF`, с явными предпосылками `width` и `Nodup` по индексам. Это минимальный конструктивный слой для подключения AC0‑DNF к k‑DNF pipeline при контролируемых предположениях.
- [x] Закрыт пункт «DNF‑certificate из CNF‑pipeline»: добавлена лемма
  `shrinkage_negDnfFamily_to_dnf`, которая строит shrinkage для `F`
  из shrinkage для `¬F` при условии `LeafPartition` на листьях дерева.
  Это формальный мост для DNF↔CNF, требуемый в блокере (DNF vs CNF).
- [x] Переход на малый алфавит закрыт: построен конструктивный декодер
  `decodeAuxTraceSmall`, доказана инъективность
  `encodeBadFamilyDetCNF_small_injective`, и весь блок
  `AuxTraceSmall` теперь полностью конструктивен.
- [x] Шаг A: аудит на скрытые аксиомы выполнен через сборку `lake build Tests.AxiomsAudit`.  
  - Результат: в ключевых теоремах фиксируются базовые аксиомы `propext`, `Classical.choice`, `Quot.sound`.  
  - Список из аудита:
    - `Pnp3.Magnification.P_ne_NP_final` → `[propext, Classical.choice, Quot.sound]`.
    - `Pnp3.Magnification.P_ne_NP_from_partial_formulas` → `[propext, Classical.choice, Quot.sound]`.
    - `Pnp3.Magnification.NP_not_subset_Ppoly_from_partial_formulas` → `[propext, Classical.choice, Quot.sound]`.
    - `Pnp3.ComplexityInterfaces.P_ne_NP_of_nonuniform_separation` → `[propext, Quot.sound]`.
    - `Pnp3.ThirdPartyFacts.partial_shrinkage_for_AC0` → `[propext, Classical.choice, Quot.sound]`.
    - `Pnp3.ThirdPartyFacts.shrinkage_for_localCircuit` → `[propext, Classical.choice, Quot.sound]`.
- [x] Классические аксиомы разрешены: считаем `propext`, `Classical.choice`, `Quot.sound`
  допустимым фоном и не блокируем дальнейшие шаги их устранением.
- [x] Шаг B: stage‑контракт зафиксирован — `ac0DepthBound` переведён в режим Stage‑1 (M²), сильная оценка остаётся отдельной (`ac0DepthBound_strong`).
- [x] Добавлена явная лемма `ac0DepthBound_eq_weak`, фиксирующая дефолт `ac0DepthBound = ac0DepthBound_weak` для стабильного `simp`‑контракта (важно для downstream‑обоснований Stage‑1).
- [x] Шаг 1.1 (архитектура DNF→CNF): добавлен явный перевод DNF‑семейства через отрицание (`negDnfFamilyToCnfFamily`) и лемма про оценку `eval` на уровне семейства (`eval_negDnfFamilyToCnfFamily`) в `pnp3/AC0/MultiSwitching/Definitions.lean`.
- [x] Шаг C (скан использования bounds): выполнен `rg` по `AC0SmallEnough`/`ac0DepthBound*`.
  - Основные узлы: `pnp3/ThirdPartyFacts/Facts_Switching.lean` (источник контрактов),
    `pnp3/LowerBounds/LB_Formulas.lean`, `pnp3/LowerBounds/AntiChecker_Partial.lean`.
  - Прогресс: из `AntiChecker_Partial.lean` убран явный параметр `AC0SmallEnough`,
    так что partial‑трек больше не требует Stage‑1 предположения на уровне
    параметров решателя.
- [x] Получены ответы по архитектуре: canonical depth‑bound, derived leaves‑bound,
  допустимость CNF‑pipeline+negation, линейный ε‑бюджет, и минимизация
  downstream‑правок (см. ответы в разделе вопросов).
- [x] Введён явный derived‑bound на число листьев через depth
  (`leaves ≤ 2^depth`) как compat‑слой для downstream.
- [x] Stage 1–6 (depth‑2 CNF, малый алфавит): добавлена композиция
  `encoding → good restriction → PartialCertificate` с `ε = 0`
  (`stage1_6_complete_small_canonicalCCDT` в `pnp3/AC0/MultiSwitching/Main.lean`).
- [x] Добавлен явный «конструктивный» alias:
  `partial_shrinkage_for_AC0_from_multi_switching` показывает, что при наличии
  `AC0MultiSwitchingWitness` результат `partial_shrinkage_for_AC0` закрывается
  без Stage‑1 предположений (`pnp3/ThirdPartyFacts/Facts_Switching.lean`).
- [x] Заложен «ширинный мост»: добавлены конструктивные функции truncation
  для CNF/DNF, монотонность `eval`, обёртки для семейств формул
  (поэлементное truncation + перенос `eval` по списку и по `evalFamily`),
  а также леммы «идемпотентности» при достаточной ширине
  (`pnp3/AC0/MultiSwitching/Truncation.lean`).
- [x] Для truncation добавлены «структурные» леммы, выделяющие причину
  расхождения: если `CNF` стала ложной/`DNF` стала истинной после truncation,
  то виновен удалённый (широкий) элемент. Это базовый шаг к union‑bound.
- [x] Добавлен union‑bound для CNF‑truncation: вероятность расхождения
  ограничена суммой по широким клаузам, с явным числовым видом
  `disagreement ≤ (#wide) * ε` при предположении локальных ε‑оценок
  (`truncation_disagreement_prob_le`).
- [x] Связка с параметрами `w`/`tParam`: добавлена лемма
  `truncation_disagreement_prob_le_of_pow`, которая при условии
  `2^(w+1) ≥ (m+1)(n+2)` выводит итоговую границу `ε ≤ 1/(n+2)`.
- [x] Добавлен конкретный bound на `clauseFalseSet` через ширину клауз:
  `card ≤ 2^(n - width)` и, в частности, `card ≤ 2^n / 2^(w+1)` для
  широких клауз, включая рациональную форму
  `((card : Q) ≤ (2^n)/(2^(w+1)))` для прямой подстановки в union‑bound.
- [x] Закрыт **Case B** из Step 3.2: если `n < 49*(w+1)` (то есть `sParam = 0`),
  то good restriction существует тривиально; вынесено в
  `exists_good_restriction_small_n` в `Main.lean`.
- [x] Добавлен wrapper для **расширенного** кодирования
  (`FamilyTraceCodeVar`) — `exists_good_restriction_step3_2_expanded` в
  `Main.lean`. Это закрывает переход «числовая оценка → good restriction»
  для базы `(2*n)^t * (2*(w+1))^t` и полезно как промежуточный путь,
  пока инъективность малого алфавита ещё не закрыта.
- [x] Добавлен мост к `BadEvent` для расширенного кода:
  `exists_good_restriction_step3_2_expanded_canonicalCCDT` переводит
  good‑restriction из `BadFamily_deterministic` в `BadEvent` при `t > 0`.
- [x] В `DepthInduction` добавлены базовые численные леммы для индукции по глубине:
  `level_le_maxSteps`, `totalSteps_le_mul_maxSteps`, `maxSteps_le_totalSteps`.
  Это закрывает «арифметический каркас» для будущей склейки depth‑bound по уровням.
- [ ] Шаги 1–9 (multi‑switching pipeline) — **не завершены полностью**:
  Stage 1–6 закрыт для depth‑2 CNF, но **polylog‑оценка для общей глубины**
  (multi‑switching индукция + CCDT для depth>2) остаётся открытой.
  Это **единственный** оставшийся блокер для полного Stage‑2.
  Подробный список недостающих лемм и конструкций вынесен в
  `pnp3/Docs/MultiSwitching_DepthInduction_TODO.md`.

## Аудит внешних аксиом (состояние на сейчас)

* В `pnp3/` остаются **две активные внешние аксиомы** (оба входа Hirahara 2022):
  `ThirdPartyFacts.PartialMCSP_profile_is_NP_Hard_rpoly` и
  `ThirdPartyFacts.PartialMCSP_is_NP_Hard`.
* Блоки shrinkage/switching для AC⁰ и локальных схем
  **не используют внешние аксиомы** — они формализованы как теоремы,
  получающие явные witness через `FamilyIsAC0`/`FamilyIsLocalCircuit`.
* Классические аксиомы (`propext`, `Classical.choice`, `Quot.sound`) считаются
  допустимым фоном и не препятствуют конструктивности witness.

## Questions for experts (добавляйте ответы прямо здесь)
1) **Какой именно формальный целевой объект предпочтителен в `Facts_Switching`:**
   - `PartialDT.depthBound` (или `Shrinkage.t`),
   - или bound на `PDT.leaves` с переходом `leaves ≤ 2^depth`?
   Это важно, чтобы согласовать downstream‑теоремы без дополнительных правок.
   **Ответ:** canonical‑объект — `PartialDT.depthBound`/`Shrinkage.t` (depth),
   а bound на `PDT.leaves` должен быть derived API через
   `leaves ≤ 2^depth` (см. планируемую лемму `leaves_le_pow2_depth`).

2) **Можно ли официально принять дуальность (CNF‑pipeline + negation) как базовую архитектуру**, даже если часть downstream‑кода ожидает DNF‑имена? Если да, нужен список имен, которые допустимо переопределить.
   **Ответ:** да, можно принять CNF‑pipeline как canonical‑ядро, но наружу
   оставить DNF‑имена через `abbrev`/`alias`‑слой и тонкие обёртки
   (`Facts_Switching.DNF_*`), чтобы не ломать downstream.

3) **Предпочтительное распределение ошибки ε по глубине:**
   - линейный бюджет `ε_level ≤ 1/((d+1)*(n+2))`,
   - или геометрический `ε_level ≤ 2^{-level}/(n+2)`?
   **Ответ:** выбираем линейный бюджет как базовый (проще union‑bound и Lean‑арифметика).

4) **Минимальный набор downstream‑файлов, где допустимы изменения интерфейса** (если целевой объект меняется):
   - `pnp3/LowerBounds/LB_Formulas.lean`?
   - `pnp3/LowerBounds/AntiChecker.lean`?
   - `pnp3/Magnification/Facts_Magnification.lean`?
   **Ответ:** по возможности вообще не менять downstream и закрыть всё в
   `Facts_Switching` через derived‑леммы. Если изменения неизбежны, то
   допускаются правки в `LB_Formulas` и `AntiChecker`, а `Facts_Magnification`
   лучше не трогать.

5) **Принимаем ли базовые классические аксиомы как «фон»?**
   В аудите `Tests.AxiomsAudit` ключевые теоремы опираются на `propext`,
   `Classical.choice`, `Quot.sound`. Нужен явный статус: допускаем ли эти
   три аксиомы как неизбежный фон (и тогда Step A считается закрытым), либо
   требуется их устранение/локализация?
   **Ответ:** да, классические аксиомы разрешены как фон; переходим к
   конструктивной части без их устранения.

6) **Нужен ли явный мост между `AC0.Formulas.DNF` (без ширины) и `Core.DNF` с параметром ширины `w`?**
   **Ответ:** да, мост нужен, иначе придётся дублировать multi‑switching или
   вручную протаскивать ширины/`Nodup` на каждом шаге. Фиксируем архитектуру:
   - оставить AC0‑ветку как есть;
   - добавить `width`/`maxWidth` и предикаты `WidthLe` (без изменения типов);
   - нормализация термов для получения `Nodup` (и сохранения `eval`);
   - `toCoreDNF_ofWidthLe` (для фиксированного `w`) и `toCoreDNFΣ` (по умолчанию).
   **Статус:** базовый мост реализован через `toCoreDNF` + `eval_toCoreDNF`;
   следующий шаг — модуль `AC0/Width.lean` и `AC0/Normalize.lean` с
   конструктивными `Nodup`/width‑свидетелями.

7) **Нужно ли добавить инвариант «листья образуют разбиение» для деревьев,
   производимых canonical CCDT?**
   **Ответ:** да, стоит доказать `LeafPartition` для canonical CCDT‑деревьев,
   чтобы убрать предпосылку в `shrinkage_negDnfFamily_to_dnf` без переписывания
   интерфейса. План:
   - (быстрый вариант) добавить лемму `CCDT.leafPartition` и использовать её
     в местах вызова;
   - (чистая архитектура, позже) включить `LeafPartition` в shrinkage‑сертификат.
   **Статус:** запланировано, но ещё не реализовано.

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
- Сильная polylog‑оценка остаётся **целевой** `ac0DepthBound_strong` и не должна
  использоваться как дефолт, пока не построено реальное switching‑доказательство.

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

# Roadmap до полного закрытия (end‑to‑end)

Ниже фиксируем **сквозной план** от текущего состояния до полного
закрытия multi‑switching (depth>2) и последующей интеграции.
Это «единый список», по которому можно шаг за шагом проверять прогресс.

## A. Полное закрытие multi‑switching (depth>2) и замена внешнего switching/shrinkage

### A0. Зафиксировать целевой объект и публичный контракт

**Цель Stage‑2** — bound на глубину дерева:
`PartialDT.depthBound` / `Shrinkage.t`.
Derived‑API для листьев должен идти через стандартное
`leaves ≤ 2^depth`, чтобы downstream не зависел от «числа термов».

**DoD A0**:
* В `Facts_Switching` закреплены:
  `ac0DepthBound_strong`, `ac0DepthBound_weak`, `ac0DepthBound = weak`,
  и леммы вида `leaves_le_pow2_depth`.
* Downstream зависит только от depth/leaves API.

### A1. Мост AC0 ↔ Core(k‑CNF/k‑DNF): ширина и `Nodup`

**Нужно** получить “width‑aware view” AC0‑формул, чтобы multi‑switching
применялся к реальным AC0‑объектам, а не к искусственным структурам.

**DoD A1**:
* `AC0.Term.width`, `AC0.DNF.maxWidth` / `AC0.CNF.maxWidth`.
* Предикаты `WidthLe w` для DNF/CNF.
* Нормализация термов → `Nodup` + сохранение `eval`.
* Конверсия:
  `toCoreDNFΣ : AC0.DNF → Σ w, Core.DNF w` и
  `toCoreDNF_ofWidthLe : AC0.DNF → WidthLe w → Core.DNF w`
  (аналогично для CNF).

### A2. Canonical CCDT: инварианты, обязательные для глубинной индукции

**Нужно** закрепить детерминизм и leaf‑partition для деревьев,
которые реально строит canonical CCDT.

**DoD A2**:
* Дет‑трассы и replay‑леммы в canonical CCDT.
* Инъективность “малого” кодирования (`AuxTraceSmall`).
* `LeafPartition` для `canonicalCCDT` (или включено в shrinkage‑сертификат).

### A3. Depth‑2 “атомарный шаг” как библиотечный кирпич

Эта часть уже почти есть, но должна быть упакована в интерфейс,
подходящий для рекурсивного вызова (depth‑индукция).

**DoD A3**:
* Теорема вида
  `exists_good_restriction_canonicalCCDT : ... → ∃ ρ*, ... ∧ ¬BadEvent_det ρ*`.
* Теорема
  `partialCertificate_from_good_restriction : ... → PartialCertificate`
  (depth‑2).

### A4. Числа и ε‑бюджет для индукции

**Нужно** иметь компактный слой числовых лемм для:
* truncation‑ошибки;
* строгого bound `|Bad| < |R_s|`;
* суммы ε по уровням.

**DoD A4**:
* Леммы `epsilon_add_le`, `epsilon_sum_le` и т.п.
* Явный “линейный бюджет”:
  `ε_level ≤ 1/((d+1)(n+2))` с выводом `ε_total ≤ 1/(n+2)`.

### A5. Главный блок: depth‑индукция (`d → d+1`)

**DoD A5**:
* `DepthInduction.lean` с формальной индукцией по глубине.
* База: depth‑2 (CNF) + DNF через duality.
* Шаг: truncation → good restriction → IH → склейка сертификатов.
* Итог: `AC0MultiSwitchingWitness` / `AC0PolylogBoundWitness` для всех `d`.

### A6. Интеграция в публичный слой

**DoD A6**:
* `partial_shrinkage_for_AC0` доказана через `DepthInduction`.
* `ac0DepthBound` можно переводить на `ac0DepthBound_strong`
  после закрытия polylog‑доказательства.

### A7. Downstream‑проверка (минимальные правки)

**DoD A7**:
* Сборка минимум:
  `LowerBounds/LB_Formulas`,
  `LowerBounds/AntiChecker*`,
  `Magnification/Facts_Magnification`,
  финальный модуль P≠NP.

### A8. Аудит “без внешних switching/shrinkage”

**DoD A8**:
* `#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0`
  не содержит внешних фактов (кроме допустимых `propext`, `Classical.choice`,
  `Quot.sound`).

## B. Полная замена оставшегося внешнего факта (PartialMCSP NP‑hardness)

Этот блок не относится к switching, но нужен для полного “безусловного”
статуса всего проекта.

**DoD B**:
* либо формализация NP‑hardness PartialMCSP в корректной модели
  (если требуется randomized‑reduction — нужно добавить такой интерфейс),
* либо явно зафиксированное и доказанное детерминированное утверждение.

---

# Проверка достаточности плана (чек‑лист)

Этот раздел отвечает на вопрос: **достаточно ли текущего плана, чтобы
получить внутри проекта все witness‑теоремы для switching/shrinkage, и чтобы
вся цепочка P≠NP зависела только от одной внешней аксиомы NP‑трудности?**

## C1. Switching/shrinkage‑часть (без внешних аксиом)

Если выполнены пункты **A0–A8**, то:

* polylog‑witness (`AC0MultiSwitchingWitness` / `AC0PolylogBoundWitness`)
  строится внутри проекта, без внешних допущений;
* `partial_shrinkage_for_AC0` и `shrinkage_for_localCircuit` становятся
  **внутренними теоремами**, а не external facts;
* `ac0DepthBound` можно корректно поднять до `ac0DepthBound_strong`.

**DoD C1**:
* `#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0`
  не содержит внешних фактов (кроме `propext`, `Classical.choice`, `Quot.sound`).
* `#print axioms ThirdPartyFacts.shrinkage_for_localCircuit`
  аналогично.

## C2. Вся цепочка P≠NP с двумя внешними аксиомами

После закрытия C1 остаются две внешние зависимости из Hirahara 2022:
`PartialMCSP_profile_is_NP_Hard_rpoly` и `PartialMCSP_is_NP_Hard`.

**DoD C2**:
* `#print axioms P_ne_NP_final` (или финальный модуль) показывает
  только `PartialMCSP_profile_is_NP_Hard_rpoly`, `PartialMCSP_is_NP_Hard`
  + базовые классические аксиомы.

## C3. Если нужен “полностью безусловный” статус

Тогда закрываем **ветку B**:
либо формализуем NP‑hardness PartialMCSP в корректной модели,
либо явно принимаем более сильное детерминированное утверждение и
фиксируем это как отдельную научную гипотезу.

---

## Шаг B. Зафиксировать stage‑контракт в интерфейсе

Сейчас уже реализовано разделение слабой и сильной оценок:

```lean
def ac0DepthBound_weak (params : AC0Parameters) : Nat := params.M^2
def ac0DepthBound_strong (params : AC0Parameters) : Nat := (log₂(M+2))^(d+1)
-- Важно: ac0DepthBound не должен по умолчанию указывать на strong,
-- пока strong не доказан. Используйте provider/параметр или явно
-- пишите ac0DepthBound_strong только в местах, где есть доказательство.
-- Если нужен alias, оформляйте его как параметр/структуру‑провайдер,
-- а не как определение по умолчанию.
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

**Статус:** скан выполнен. В partial‑треке явный `AC0SmallEnough` уже удалён,
но strong‑witness всё ещё нужен, чтобы закрыть multi‑switching и заменить
внешние предположения в остальных местах.

---

# Ближайшие конструктивные задачи (текущий спринт)

Чтобы реально продвинуться к замене `AC0SmallEnough`, фиксируем ближайшие
конструктивные шаги, которые можно реализовывать независимо:

1) **Связать multi‑switching с shrinkage‑сертификатом (AC⁰, CNF‑ветка).**
   - Цель: получить лемму вида  
     `partial_shrinkage_for_AC0_strong : … → ∃ ℓ C, C.depthBound + ℓ ≤ ac0DepthBound_strong …`
     из multi‑switching pipeline (CNF‑формулы).
   - Файлы‑кандидаты: `pnp3/AC0/MultiSwitching/*`, `pnp3/ThirdPartyFacts/Facts_Switching.lean`.
   - Конкретика: разнести сборку сертификата на шаги (depthBound, ε‑bound,
     family_eq), чтобы downstream‑код мог переиспользовать их по отдельности.

2) **Подключить DNF через дуальность.**
   - Использовать `negDnfFamilyToCnfFamily` из `pnp3/AC0/MultiSwitching/Definitions.lean`
     и показать, что CNF‑сертификат на ¬DNF даёт shrinkage‑сертификат для DNF.
   - Требуемая форма: lemma‑мост с явным `eval`‑переписыванием.

3) **Снять условность в `LowerBounds/AntiChecker_Partial.lean`.**
   - Заменить гипотезу `AC0SmallEnough` на strong‑witness из шага 1
     (или на эквивалентную формулировку `t ≤ ac0DepthBound_strong` и
     bound на словарь).
   - Если потребуется, ввести вспомогательную лемму в `Facts_Switching.lean`,
     которая выводит нужные численные границы напрямую из shrinkage‑сертификата.

Эти три шага дают минимальный, но реальный прогресс к финальному устранению
Stage‑1‑условности и переводят pipeline на multi‑switching.

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
   Нужен малый алфавит (например, `AuxTraceSmall` с базой `2*(w+1)`).

3) **BadEvent должен быть детерминированным (CCDT‑глубина).**
   Для инъекции с малым алфавитом bad‑событие должно быть определено как
   `depth(CCDT) ≥ t`, а не как «существует трасса длины t». Связь
   `BadEvent → ∃ trace` оставляем как вспомогательную лемму (см. «Шаг 2»).

4) **Polylog‑цель должна быть про depth/листья PDT, а не про число DNF‑термов.**
   Multi‑switching контролирует глубину decision tree (и, как следствие,
   количество листьев ≤ 2^t), но не «количество термов» в исходном DNF.
   Поэтому target witness должен быть про shrinkage/PartialDT depthBound
   или про листья PDT, а не про `allSubcubes.length` исходной схемы.

5) **Ошибка ε не обязана быть 0.**
   При частичном дереве ошибка — это доля bad‑веток; параметр `tParam`
   выбирается так, чтобы ε ≤ 1/(n+2), а не чтобы ε = 0.

## Выбор shrinkage‑факта для замены

- Из двух внешних shrinkage‑фактов (A.1 и A.2) **проще полностью формализовать**
  `partial_shrinkage_for_AC0` для AC⁰. Здесь уже есть почти готовый пайплайн
  multi‑switching (AC⁰‑формулы, индукция по глубине, кодирование/инъекция,
  сборка shrinkage‑сертификата).
- A.2 (`shrinkage_for_localCircuit`) **не следует автоматически** из A.1 без
  отдельного моста. После закрытия A.1 нужен явный аудит: используется ли A.2
  в финальном пайплайне, и если да — либо доказывать A.2 отдельно, либо
  перепроектировать место применения.

## Архитектурное решение: используем duality (CNF как основной pipeline)

Чтобы не плодить отдельную DNF‑ветку, фиксируем решение:

- **основной pipeline остаётся CNF**, как в `AC0/MultiSwitching/*`;
- DNF‑факты получаем через duality (отрицание + flip leaf labels).

Это решение обязательное: оно минимизирует правки и согласует объекты
для shrinkage‑сертификатов.

**Уточнение:** duality применяется на уровне `AC0Formula`/CNF‑семейства
(Stage‑2), а Stage‑1 DNF‑термы не участвуют в strong‑пайплайне.

## Шаг 1. Согласовать объект polylog‑bound (DNF ↔ CNF)

### 1.1. Архитектура (рекомендуется: DNF через CNF‑дуальность)

Оптимальный путь без ломки интерфейсов: **оставить основную логику в CNF**
и получить DNF‑результат через дуальность, но **polylog‑цель должна быть
переформулирована как bound на shrinkage/PartialDT**, а не на `allSubcubes.length`.

- Вводим перевод DNF → CNF для отрицания:
  - терм ↔ клауза при отрицании литералов;
  - `CNF_of_not_DNF` без экспоненциального роста.
- Лемма: `depth(DT(F|ρ)) = depth(DT((¬F)|ρ))`.
 - Обязательный мост на уровне сертификатов:
   - для PDT: инвертировать метки листьев;
   - для shrinkage‑сертификата: формально построить `flip`‑преобразование,
     сохраняющее depthBound и корректность.

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
сертификата shrinkage/PartialDT (или для числа листьев PDT через
`leaves ≤ 2^depth`), а не для длины списка подкубов исходного DNF.
Если требуется оставить имя `ac0AllSubcubes_length_le_polylog_of_multi_switching`,
его смысл нужно пересмотреть и связать с **листовыми подкубами PDT**,
а не с `AC0Circuit.subcubes`.

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

**Фиксируем версию multi‑switching:** реализуем Håstad Theorem 3.4
с `ℓ := log(2M)` (в терминах `ℓParam`), чтобы множитель `M` оставался
**вне степени** `(C * k)^t`. Это согласуется с текущей архитектурой
`|Bad| ≤ |R_{s-t}| * M * (BParam w)^t` и упрощает Numerics.

**Про константы:** если строгая Step 3.2 не закрывается при
`sParam := n/(48*(w+1))`, допускается увеличить константу
(`48 → 96/192`) для получения строгого неравенства. Это не ломает
polylog‑характер оценки, а даёт запас в натуральной арифметике.

## Шаг 2. CCDT‑алгоритм и bad‑событие (детерминированно)

- Рассматриваем семейство формул `F` размера `M`, глубины `d+1`.
- Представляем верхний слой как CNF‑конъюнкцию подформул.
- Определяем детерминированный `CCDTAlgorithm`:
  - На шаге берём первую неудовлетворённую клаузу.
  - Фиксируем первый свободный литерал.
  - Ветвим по обоим значениям (PDT.node).
  - Останавливаемся через `ℓ` шагов, если не завершили раньше.
-- **BadEvent фиксируем как детерминированное условие:**
-- `BadEvent_det(ρ) := depth(canonicalCCDT(F, ρ)) ≥ t`, где `canonicalCCDT`
-- — **функция**, задающая единственный общий ℓ‑partial DT по фиксированному
-- правилу выбора pending‑клаузы/литерала.
-- Это `DecidablePred`, что упрощает фильтрации по `ρ`.
-- В `TraceBridge.lean` доказываем эквивалентность с канонической трассой:
-- `BadEvent_det(ρ) ↔ ∃ canonicalTrace длины t`, и для encoding используем
-- именно канонический trace (обе стороны нужны для совместимости с legacy‑леммами).

**Важно:** вводим детерминированный предикат `BadEvent_det` через
`canonicalCCDT`. Все counting/encoding строятся **только** для `BadEvent_det`.
Если старое определение `BadEvent_existsTrace` остаётся, оно должно быть
связано с `BadEvent_det` отдельной леммой и **не использоваться** в counting.

## Шаг 3. Множество плохих рестрикций

- Берём `R_s` — рестрикции с ровно `s` свободными битами.
- Выбор `s`: использовать **`s := sParam(n, w)`** (как в Numerics/Params),
  чтобы Step 3.2 совпал с уже реализованными оценками.
- Определяем `Bad = {ρ ∈ R_s | BadEvent(ρ)}`.
  Цель: показать `Bad ⊊ R_s`, то есть существует хорошая рестрикция.

## Шаг 3.5. Ширинный мост (truncation) для применения multi‑switching

Нужен явный шаг, который связывает общие AC⁰‑формулы с k‑CNF/k‑DNF ширины `w`:

- **Truncation по ширине:** удаляем клаузы/термы ширины `> w`.
- Ошибка оценивается как `≤ M * 2^{-w}` (union bound).

**Статус:** реализовано конструктивное ядро truncation
(определения, монотонность `eval`, версии для семейств формул,
«обёртки» на уровне `evalFamily`/`evalDnfFamily`,
и идемпотентность при достаточной ширине),
а также «структурные» леммы про источники расхождения
(`exists_wide_clause_of_truncate_true_eval_false`,
`exists_wide_term_of_eval_true_truncate_false`) и количественная
оценка для широкой клаузы:
`card ≤ 2^(n - (w+1))` и рациональная форма
`card/2^n ≤ 1/2^(w+1)` (через `clauseFalseSet_card_le_pow_of_wide`,
`clauseFalseSet_card_le_pow_of_wide_q`). См. `pnp3/AC0/MultiSwitching/Truncation.lean`.

Выбор `w` должен быть согласован с `tParam` и `sParam`, например:

```
w := ⌈log₂(M(n+2))⌉ + c
```

так чтобы `M * 2^{-w} ≤ 1/(n+2)`.

Это фиксирует источник параметра `w`, который дальше используется в `BParam w`
и `sParam n w`. Без этого шага Step 3.2 нельзя корректно применить к объектам
общей глубины.

**Уточнение:** truncation нужно привязать к конкретному объекту:
для CNF — клаузы верхнего слоя, для DNF — термы верхнего слоя. Ошибка
должна суммироваться в ε shrinkage‑сертификата, а не «теряться» в середине
индукции.

## Шаг 4. Encoding & Injection с малым алфавитом (AuxTraceSmall)

**Ключевой момент:** код **не должен содержать `Fin n`** на каждом шаге,
иначе база в оценке мощности будет содержать `n` и Numerics не закроется.
Минимальный путь — использовать уже существующий формат **AuxTraceSmall**
с алфавитом `2*(w+1)` и восстановлением шага через детерминированный CCDT.

### 4.1. Структура кода (AuxTraceSmall)

Код хранит только:

- `bit : Bool` — присваиваемое значение;
- `idxWithinClause : Fin (w+1)` — индекс литерала **внутри** pending‑клаузы.

Восстановление конкретной переменной выполняется **детерминированно**:

- имея текущую рестрикцию и canonical CCDT‑алгоритм,
  определяем pending‑клаузы и позицию литерала;
- по `idxWithinClause` восстанавливаем литерал;
- применяем `bit` и переходим к следующей рестрикции.

### 4.2. Что заменить в текущем encoding‑слое

- Удалить/вывести как черновой код, зависящий от `BitFix n`.
- В `Encoding.lean` добавить ветку `encodeBadFamilyCNF_Small` (или аналог),
  где код — это `AuxTraceSmall`.
- Доказать `Function.Injective` через явный декодер
  (симуляция CCDT по шагам).

**Статус:** закрыто. Инъективность малого кодирования доказана
(`encodeBadFamilyDetCNF_small_injective`) с конструктивным декодером
по `AuxTraceSmall`.

**Итог:** получаем оценку вида
`|Bad| ≤ |R_{s-t}| · (BParam w)^t`, где `BParam` **не зависит от n**.

**Замечание о witness:** encoding строится от **канонической** трассы
`canonicalCCDT`, без недетерминизма и без `Classical.choose`.

**Инвариант для инъекции:** нужно явно зафиксировать лемму обратимости
шага канонического CCDT, например:

```
canonicalCCDT_reverse_step_determines_query :
  (F : CNF n) → (ρ_final : Restriction n) → (code : AuxTraceSmall w) →
  ∃! (ρ_prev : Restriction n) (q : BitFix n),
    stepRelation F ρ_prev q ρ_final ∧ smallCodeMatches q code
```

Это техническое ядро, гарантирующее, что `decode(encode ρ) = ρ` и что
малый алфавит действительно инъективен.

**Replay‑контракт:** добавить леммы про детерминированную трассу:

- `canonicalTrace_length_eq_depth` и
- `canonicalTrace_replay` (канонический процесс воспроизводит те же шаги
  при decode).

## Шаг 5. Сравнение мощностей и связь с Numerics (Step 3.2)

Используем:

- `|R_s| = binom(n, s) * 2^{n-s}`
- `|R_{s-t}| = binom(n, s-t) * 2^{n-(s-t)}`

Дальше требуется вывести строгое `|Bad| < |R_s|`. В проекте это делается так:

**Цель Step 3.2 (строгое неравенство):**

```
|R_{s-t}| * (|F|+1) * (2*(w+1))^t < |R_s|
```

Только такое утверждение даёт `|Bad| < |R_s|` напрямую. Все варианты
с дополнительным множителем `(n-s+1)^t` — промежуточные оценки.

**Эквивалентная ratio‑форма (используется в Numerics):**

```
|R_{s-t}| / |R_s| ≤ (2*s/(n-s+1))^t
```

и достаточно доказать строгое поглощение

```
(|F|+1) * (2*(w+1))^t * (2*s)^t < (n-s+1)^t.
```

**Запрет на “cancel”:** отмена множителя допустима только если он стоит
с обеих сторон. Неравенства вида
`|R_{s-t}| * (...) < |R_s| * (n-s+1)^t` сами по себе **не** дают `|Bad| < |R_s|`.

- Применяем `numerical_inequality_3_2` для `BParam` без `n` в базе
  именно к цели выше.
- Добавляем/используем лемму `tParam m n ≤ sParam n w`
  (держать в `Numerics.lean`, как часть Step 3.2).
  Зафиксировать как лемму `tParam_le_sParam_of_big_n` (вариант 4A).
- Затем применяем `exists_good_of_card_lt` (в `Counting`) и получаем
  `ρ* ∈ R_s` с `¬ BadEvent(ρ*)`.
- Явно используем лемму отмены множителя:
  `k > 0 → a * k < b * k → a < b`, чтобы убрать фактор
  `(n - s + 1)^t` из сравнения мощностей.
- Для малых `n` нужно либо отдельное ветвление (тривиальная оценка
  глубины через `n`), либо явная гипотеза `n ≥ n₀(w, m)` в формулировке.
- Обязательное ветвление:
  - **Case A:** `48*(w+1) ≤ n` — используем Step 3.2 как есть.
  - **Case B:** `48*(w+1) > n` — `sParam n w = 0`, все переменные фиксированы,
    глубина дерева 0 и `Bad` пусто (good restriction существует тривиально).

## Шаг 6. Построение `PartialCertificate` из хорошей рестрикции

**Статус:** реализовано для depth‑2 CNF с малым алфавитом.
См. `partialCertificate_from_restriction` в
`pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean` и обёртку
`stage1_6_complete_small_canonicalCCDT` в `pnp3/AC0/MultiSwitching/Main.lean`,
которая замыкает Stage 1–6 в единый результат (`ε = 0`).

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

**Бюджет ошибки ε:** определить явное правило сложения ошибок по уровням.
Например:

- вариант A: `ε_level ≤ 1/((d+1)*(n+2))` и сумма ≤ `1/(n+2)`;
- вариант B: геометрический бюджет `ε_level ≤ 2^{-level}/(n+2)`.

Нужна лемма `epsilon_add_le` для склейки сертификатов.

## Шаг 8. Проверка границ и финальная интеграция

Далее надо проверить все условия в формулировке `partial_shrinkage_for_AC0`:

1) **Ограничение на ствол:**
   - `ℓ = ℓParam(M)` и `ℓ ≤ ⌊log₂(M+2)⌋` (через `pow_two_le_ℓParam` и округления).

2) **Общая глубина:**
   - `C.depthBound + ℓ ≤ ac0DepthBound(params)`.
   - Используется `ac0DepthBound_le_strong` и индукционный гипотезис
     для глубины `d` (polylog).

3) **Ошибка:**
   - По построению `ε` равна bound на bad‑массу (например,
     `ε := (m+1) * (BParam w)^t / (n+2)` в нормализованной форме),
     и требуется доказать `ε ≤ 1/(n+2)` через `tParam`.

## Точки интеграции в Lean‑код

- **Encoding/Counting/Good‑restriction:** `pnp3/AC0/MultiSwitching/*`
  (уже в основном реализовано).
- **Главная лемма multi‑switching:** `AC0/MultiSwitching/Main.lean`
  (например, `ac0AllSubcubes_length_le_polylog_of_multi_switching`).
- **Свидетель polylog‑границы:** `Facts_Switching.lean`
  (`AC0PolylogBoundWitness` и `ac0DepthBoundWitness_of_polylog`).
- **Финальное внедрение:** заменить внешний witness в
  `ThirdPartyFacts/Facts_Switching.lean` на результат `partial_shrinkage_for_AC0_with_polylog`.

**Обязательная смена цели в Facts_Switching:**
`AC0PolylogBoundWitness` должен быть перепривязан к `Shrinkage.t` /
`PartialDT.depth` (или `PDT.leaves ≤ 2^depth`), а не к
`circuits.flatMap AC0Circuit.subcubes`. Иначе multi‑switching
доказывает «не тот объект».
Если остаётся старое имя `ac0AllSubcubes_length_le_polylog_*`, то
оно **строго означает листья PDT**, а не DNF‑термы.

**Порядок действий:** этот рефактор должен быть сделан **до** подключения
multi‑switching пайплайна, иначе типы и цели не совпадут.

## Definition of Done (конкретные леммы/файлы)

- `Encoding.lean`:
  - `encodeBadFamilyCNF_small`, `decodeBadFamilyCNF_small`,
    `decode_encode_small`, `injective_encodeBadFamilyCNF_small`.
- `Counting.lean`:
  - `card_bad_inter_Rs_le_small :
     |Bad ∩ R_s| ≤ |R_{s-t}| * (|F|+1) * (2*(w+1))^t`.
- `Numerics.lean`:
  - `step3_2_strict :
     |R_{s-t}| * (|F|+1) * (2*(w+1))^t < |R_s|`
    (с case‑split по `48*(w+1) ≤ n`).
  - ratio‑лемма для `choose` и поглощение `(|F|+1) * (2*s*BParam w)^t`
    (явно фиксировать коэффициенты и константу `C` в `m+1 ≤ C^t`).
- `Main.lean`:
  - `exists_good_restriction_small :
     ∃ ρ ∈ R_s, ¬ BadEvent_det ρ`.

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
