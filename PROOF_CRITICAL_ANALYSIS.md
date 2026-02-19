# Критический анализ кода доказательства P ≠ NP

## Дата: 2026-02-19
## Область: pnp3/ (активное дерево формализации)

---

## 1. Обзор архитектуры доказательства

Доказательство выстроено в четыре этапа:

```
Part A (Shrinkage)    → SAL: строит атлас из shrinkage-свидетеля
Part B (Counting)     → Covering-Power: ограничивает мощность ApproxClass
Part C (Anti-Checker) → Противоречие: слишком много функций для малого атласа
Part D (Magnification)→ OPS-триггер: NP ⊄ P/poly ⇒ P ≠ NP
```

Финальная теорема `P_ne_NP_final` в `pnp3/Magnification/FinalResult.lean:105-113`
утверждает `P_ne_NP` безусловно.

---

## 2. Явные аксиомы (ложные утверждения в системе типов)

### 2.1. `PartialMCSP_profile_is_NP_Hard_rpoly` (Hirahara2022.lean:30-32)

```lean
axiom PartialMCSP_profile_is_NP_Hard_rpoly :
  ∃ (prof : GapPartialMCSPProfile),
    Is_NP_Hard_rpoly (gapPartialMCSP_Language_profile prof)
```

**Проблема**: Это утверждение ссылается на результат Hirahara (FOCS 2022), но:
- Результат Hirahara доказывает NP-трудность *конкретной* версии MCSP при
  *рандомизированных* сведениях, а не детерминированных.
- Переход от рандомизированных к детерминированным сведениям сам по себе
  является открытой проблемой (требует дерандомизации).
- В коде `Is_NP_Hard_rpoly` определён отдельно, но конкретная формализация
  `rpoly`-сведений не раскрыта в доступных файлах.

**Оценка**: Аксиома формулирует результат сильнее, чем то, что доказано в
литературе. Без формализации типа `Is_NP_Hard_rpoly` невозможно оценить,
не скрывает ли он дополнительных допущений.

### 2.2. `PartialMCSP_is_NP_Hard` (Hirahara2022.lean:38-39)

```lean
axiom PartialMCSP_is_NP_Hard :
  ∃ (p : GapPartialMCSPParams), Is_NP_Hard (gapPartialMCSP_Language p)
```

**Проблема**: Чисто логическая NP-трудность (`Is_NP_Hard`, а не `Is_NP_Hard_rpoly`)
для Partial MCSP. В литературе результат Hirahara доказан для рандомизированных
сведений. Переход к `Is_NP_Hard` (детерминированные many-one сведения) —
существенно более сильное утверждение, не обоснованное ссылкой на публикацию.

**Оценка**: Потенциально ложное усиление результата Hirahara.

### 2.3. `localizedFamilyWitness_partial` (LocalizedWitness_Partial.lean:22-24)

```lean
axiom localizedFamilyWitness_partial
  (p : Models.GapPartialMCSPParams) :
  LowerBounds.LocalizedFamilyWitnessHypothesis_partial p
```

**Проблема**: Это единственная аксиома на *финальном конусе* теоремы
`P_ne_NP_final`. Она утверждает, что для **любого** набора параметров `p`
и **любого** малого общего решателя существует локальный решатель с
определёнными свойствами, включая наличие `FamilyIsLocalCircuit` свидетеля.

Раскрытие типа `LocalizedFamilyWitnessHypothesis_partial` (LB_GeneralFromLocal_Partial.lean:22-32):

```lean
def LocalizedFamilyWitnessHypothesis_partial (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallGeneralCircuitSolver_Partial p,
    ∃ (T : Finset ...) (loc : SmallLocalCircuitSolver_Partial p),
      T.card ≤ polylogBudget ... ∧
      loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
      loc.params.params.ℓ ≤ polylogBudget ... ∧
      loc.params.params.depth ≤ solver.params.params.depth ∧
      FamilyIsLocalCircuit loc.params.params
        (allFunctionsFamily loc.params.params.n)
```

**Критическая проблема**: Последнее условие требует
`FamilyIsLocalCircuit loc.params.params (allFunctionsFamily ...)` — т.е.
наличие shrinkage-свидетеля для **полного** семейства всех функций на
входах длины `n`. Это в точности то, что нужно доказать (и что является
наиболее трудной частью всего доказательства). Аксиома фактически
**постулирует то, что требуется доказать**, упаковывая содержательное
утверждение в техническую обёртку.

**Оценка**: Это главный разрыв в доказательстве. Аксиома утверждает
существование объекта, конструкция которого является основным
нерешённым вопросом.

---

## 3. Скрытые witness-зависимости (не аксиомы, но внешние входы)

### 3.1. `FamilyIsAC0` и `FamilyIsLocalCircuit` — witness predicates

Определения (Facts_Switching.lean:685, 1406):
```lean
def FamilyIsAC0 (params : AC0Parameters) (F : Family params.n) : Prop :=
  Nonempty (AC0FamilyWitness params F)

def FamilyIsLocalCircuit (params : LocalCircuitParameters) (F : Family params.n) : Prop :=
  Nonempty (LocalCircuitWitness params F)
```

Оба определены через `Nonempty`, что само по себе корректно, но
скрывает тот факт, что **конструкция** таких свидетелей нигде
не предоставлена. Все ключевые теоремы (`noSmallAC0Solver_partial`,
`noSmallLocalCircuitSolver_partial`) принимают соответствующий свидетель
как **гипотезу** — но эта гипотеза нигде не доказывается.

### 3.2. `partial_shrinkage_for_AC0` и `shrinkage_for_localCircuit`

Эти теоремы (не аксиомы) строят `Shrinkage` из witness-объекта. Но
сами witness-объекты `AC0FamilyWitness` и `LocalCircuitWitness` нигде
не конструируются для конкретных параметров. Формально это "теоремы
с незамкнутыми предусловиями" — типологический трюк, скрывающий
фактические аксиомы.

---

## 4. Структурные проблемы и ошибки в логике доказательства

### 4.1. Круговая зависимость через `False.elim`

**Файл**: `AntiChecker_Partial.lean:962-964`, `1039-1042`

```lean
theorem antiChecker_exists_large_Y_partial_of_false
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p) (hFalse : False) :
    ∃ ... := by
  exact False.elim hFalse
```

Теорема `antiChecker_exists_testset_partial` (строки 994-1042) строит
свидетельство существования (F, Y, T) следующим образом:

1. Вызывает `antiChecker_exists_large_Y_partial`, получая Y
2. Извлекает `hSubset` и `hCapacity` из результата
3. **Доказывает `False`** через `no_bounded_atlas_of_large_family`
4. Вызывает `False.elim hFalse`

**Проблема**: Все экзистенциальные свидетели (F, Y, T и связанные свойства)
в `antiChecker_exists_testset_partial` конструируются через `False.elim`.
Это означает, что **на самом деле доказано не существование конкретных
объектов, а только то, что предположение о существовании малого решателя
ведёт к противоречию**. С точки зрения Lean это корректно (из False
следует что угодно), но с точки зрения конструктивности это означает,
что реальные свидетели F, Y, T **не были построены**.

Аналогичная структура в `antiChecker_exists_testset_local_partial`
(строки 1193-1237).

### 4.2. Финальная теорема не использует NP-hardness аксиомы

**Файл**: `FinalResult.lean:59-69`

```lean
theorem P_ne_NP_final_asymptotic
    (prof : GapPartialMCSPProfile)
    (hA : MagnificationAssumptions prof) :
    P_ne_NP := by
  rcases hA with ⟨m, δ, hδ, hm_large⟩
  have hLocalized := ThirdPartyFacts.localizedFamilyWitness_partial ...
  exact P_ne_NP_from_partial_formulas ... hδ hLocalized
```

Теорема `P_ne_NP_final_asymptotic` зависит **только** от
`localizedFamilyWitness_partial` (через прямой вызов) и **не использует**
аксиомы `PartialMCSP_profile_is_NP_Hard_rpoly` и `PartialMCSP_is_NP_Hard`.

Аксиомы NP-трудности упоминаются в `partial_mcsp_profile_np_hard_witness`
и `partial_mcsp_np_hard_witness`, но эти теоремы **не вызываются** нигде
в цепочке финального доказательства.

**Вывод**: Аксиомы Hirahara2022 — мёртвый код. Они не участвуют в
финальном конусе, но создают иллюзию связи с реальным результатом
теории сложности.

### 4.3. Отсутствие связи между NP-hardness и anti-checker

Путь anti-checker → lower bound → magnification → P ≠ NP **полностью
обходит** NP-hardness Partial MCSP. Вместо этого доказательство
утверждает:

1. `localizedFamilyWitness_partial` (аксиома): для любого общего решателя
   существует локальный решатель + shrinkage свидетель
2. Из локального решателя + shrinkage → противоречие через SAL + counting
3. Значит, не существует общего решателя Partial MCSP
4. OPS-триггер: не существует P/poly решателя → NP ⊄ P/poly → P ≠ NP

Ключевой шаг — п.4 (OPS_trigger_general_contra_partial в
Facts_Magnification_Partial.lean:69-82):

```lean
theorem OPS_trigger_general_contra_partial ...
  (hLocalized : LocalizedFamilyWitnessHypothesis_partial p) :
  GeneralLowerBoundHypothesisPartial p ε statement →
    ((∀ L, NP L → Ppoly L) → False) := by
  intro hHyp hAll
  have hPpoly := hAll _ (gapPartialMCSP_in_NP p)
  have solver := generalCircuitSolver_of_Ppoly_partial p hPpoly
  exact LB_GeneralFromLocal_partial (p := p) (solver := solver) hLocalized
```

Здесь `gapPartialMCSP_in_NP p` используется — это единственное место,
где появляется принадлежность Partial MCSP к NP. Однако этот факт
доказан **для конкретных фиксированных параметров** `p`, а не для
произвольного профиля.

### 4.4. Универсальный квантор в `localizedFamilyWitness_partial`

Аксиома `localizedFamilyWitness_partial` квантифицирована по **всем**
`p : GapPartialMCSPParams`. Это означает, что она утверждает наличие
shrinkage-свидетеля для **любого** набора параметров, включая
тривиальные случаи, где утверждение может быть ложным.

Структура `GapPartialMCSPParams` (Model_PartialMCSP.lean) требует:
- `n : Nat` с `n_large : 8 ≤ n`
- `sYES`, `sNO` с `gap_ok : sYES < sNO`

Но `localizedFamilyWitness_partial` утверждает нечто для **каждого**
такого `p`. В частности, для `n = 8` (минимальный допустимый) утверждение
о существовании shrinkage-свидетеля для полного семейства всех булевых
функций длины `partialInputLen 8 = 2^9 = 512` выглядит количественно
нереалистичным для имеющихся в литературе bounds.

---

## 5. Проблемы определений классов сложности

### 5.1. Определение P ≠ NP

**Файл**: `Interfaces.lean:156`

```lean
def P_ne_NP : Prop := Facts.PsubsetPpoly.P.{0} ≠ NP
```

Где `P` и `NP` определены как предикаты на языках:
```lean
abbrev P : Language → Prop := Facts.PsubsetPpoly.P.{0}
abbrev NP (L : Language) : Prop := NP_TM L
```

`P ≠ NP` формализовано как **`P ≠ NP` на уровне функций** (extensional
inequality предикатов `Language → Prop`). Это стандартная формализация.

Однако `NP` определено через `NP_TM` (машины Тьюринга), в то время как
`P` импортируется из внешнего пакета `Facts.PsubsetPpoly`. Необходимо
убедиться, что определения `P` из двух разных пакетов совместимы — иначе
`P ≠ NP` может быть тривиально истинным из-за несовместимых определений.

### 5.2. `P_subset_Ppoly_proof` — потенциально нетривиальный факт

**Файл**: `Interfaces.lean:151-153`

```lean
@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly := by
  intro L hL
  exact (ThirdPartyFacts.P_subset_Ppoly_proof (L := L) hL)
```

Делегирует в `ThirdPartyFacts.P_subset_Ppoly_proof`, который
импортируется из `Facts/PsubsetPpoly/`. Необходимо проверить,
что этот пакет не содержит собственных аксиом.

---

## 6. Количественные несоответствия

### 6.1. Параметр `n = 8` в legacy-теореме

**Файл**: `FinalResult.lean:84-113`

```lean
@[simp] def canonicalPartialParams : GapPartialMCSPParams where
  n := 8; sYES := 1; sNO := 3; gap_ok := by decide; n_large := by decide

theorem P_ne_NP_final : P_ne_NP := by
  let hA : MagnificationAssumptions canonicalProfile :=
    { m := 8, δ := (1 : Rat), hδ := zero_lt_one, hm_large := by decide }
  ...
```

При `n = 8`:
- `partialInputLen = 2 * 2^8 = 512`
- Полное семейство: `2^(2^512)` функций — астрономическое число
- Shrinkage bound для AC⁰ при таких параметрах: порядка `2^(512^{0.5})` глубины PDT

Вопрос: может ли аксиома `localizedFamilyWitness_partial` быть истинной
при таких конкретных параметрах? Формально она квантифицирована по всем
`solver`, поэтому должна работать для любого размера P/poly-схемы,
что является содержательным (и, вероятно, ложным без shrinkage) утверждением.

### 6.2. `union_small` в `SmallAC0ParamsPartial`

**Файл**: `AntiChecker_Partial.lean:45-52`

```lean
structure SmallAC0ParamsPartial (p : GapPartialMCSPParams) where
  ac0 : ThirdPartyFacts.AC0Parameters
  same_n : ac0.n = partialInputLen p
  union_small :
    let bound := Nat.pow 2 (ac0DepthBound_strong ac0)
    unionBound bound bound ≤ Nat.pow 2 (Nat.pow 2 ac0.n / (ac0.n + 2))
```

Условие `union_small` требует `unionBound(2^d_strong, 2^d_strong) ≤ 2^(N/(n+2))`.
Это количественное ограничение определяет, какие AC⁰-параметры считаются
"малыми". Проблема в том, что определение `ac0DepthBound_strong` скрыто
в Facts_Switching.lean (большой файл), и необходимо проверить, что оно
корректно калибрировано с реальными bounds из switching lemma.

---

## 7. Основные выводы

### 7.1. Главный дефект: `localizedFamilyWitness_partial`

Единственная аксиома на финальном конусе — `localizedFamilyWitness_partial`.
Она утверждает **существование shrinkage-свидетеля для полного семейства
всех булевых функций** при произвольных параметрах Partial MCSP. Это
нетривиальное утверждение, которое:

- Не следует из результатов Hirahara
- Не следует из switching lemma в известной форме
- Содержит в себе ключевую содержательную часть доказательства
- Квантифицировано слишком сильно (для всех `p`)

### 7.2. Аксиомы Hirahara — мёртвый код

`PartialMCSP_profile_is_NP_Hard_rpoly` и `PartialMCSP_is_NP_Hard` не
используются в цепочке доказательства `P_ne_NP_final`. Они присутствуют
для "будущего использования", но создают ложное впечатление о связи
доказательства с реальными результатами теории сложности.

### 7.3. False.elim конструкции

Ключевые экзистенциальные свидетели (F, Y, T в antiChecker) конструируются
через `False.elim`, что означает, что реальных объектов не построено.
В контексте Lean это корректно (доказательство от противного), но
демонстрирует отсутствие конструктивного содержания.

### 7.4. Маскировка аксиом через witness-типы

Внешние входы `FamilyIsAC0` и `FamilyIsLocalCircuit` определены как
`Nonempty (WitnessType ...)`. Хотя формально это не аксиомы, эти
свидетели **нигде не конструируются**, а передаются как гипотезы.
Фактически это эквивалент аксиом, замаскированных в typesystem.

### 7.5. Что реально доказано

Безусловно (без внешних аксиом) доказано следующее:
1. SAL корректно строит атлас из shrinkage-свидетеля
2. Covering-Power корректно ограничивает мощность аппроксимируемых семейств
3. Если существует малый AC⁰/локальный решатель **и** есть shrinkage-свидетель,
   то получается противоречие
4. P ⊆ P/poly (импортировано из внешнего пакета)
5. NP ⊄ P/poly + P ⊆ P/poly ⇒ P ≠ NP (логический вывод)

**Не доказано** (и скрыто в аксиомах):
- Существование shrinkage-свидетеля для полного семейства функций
- Переход от общих схем к локальным (locality lift) с нужным свидетелем
- NP-трудность Partial MCSP (аксиомы не используются, но и не нужны
  для текущей цепочки)

---

## 8. Рекомендации

1. **Удалить или пометить аксиомы Hirahara как неиспользуемые** — они
   не участвуют в финальном конусе и вводят в заблуждение.

2. **Явно документировать, что `localizedFamilyWitness_partial` — это
   главная содержательная гипотеза**, а не "техническая деталь мостика".

3. **Пересмотреть квантификацию `localizedFamilyWitness_partial`** —
   утверждение для **всех** `p` может быть ложным; нужна фиксация
   конкретного диапазона параметров.

4. **Проверить совместимость определений `P` из разных пакетов** —
   убедиться, что `P_ne_NP` не является тривиально истинным.

5. **Добавить тест, показывающий точный набор аксиом `P_ne_NP_final`** —
   текущий `AxiomsAudit.lean` печатает зависимости, но не проверяет
   их автоматически.
