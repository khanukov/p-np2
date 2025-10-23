# Аудит доказуемых улучшений (без дополнительного контекста)

**Дата:** 2025-10-22
**Цель:** Идентифицировать и реализовать все улучшения, которые можно сделать с использованием только существующей документации и кодовой базы

---

## 📊 Текущая статистика

| Категория | Количество | Файлы |
|-----------|------------|-------|
| **Sorry statements** | 28 | SwitchingLemma.lean |
| **Axioms** | 25 | 8 файлов |
| **Полностью доказанные леммы** | 10+ | SwitchingLemma.lean |

---

## ✅ Что можно улучшить СЕЙЧАС (без блокеров)

### 1. Свойства бинарной энтропии (BinomialBounds.lean)

**Текущее состояние:**
- ✅ Определение `Hbin` готово (lines 53-58)
- ✅ `Hbin_of_mem_openUnitInterval` доказано
- ✅ `Hbin_zero` и `Hbin_one` доказаны

**Что добавить:**

#### 1.1 Монотонность Hbin на [0, 1/2]
```lean
lemma Hbin_mono_on_half {ε ε' : ℚ}
    (hε : 0 ≤ ε ∧ ε ≤ 1/2)
    (hε' : 0 ≤ ε' ∧ ε' ≤ 1/2)
    (h : ε ≤ ε') :
    Hbin ε ≤ Hbin ε' := by
  sorry
```

#### 1.2 Симметрия Hbin
```lean
lemma Hbin_symm (ε : ℚ) (h : 0 ≤ ε ∧ ε ≤ 1) :
    Hbin ε = Hbin (1 - ε) := by
  sorry
```

#### 1.3 Верхняя граница
```lean
lemma Hbin_le_one (ε : ℚ) :
    Hbin ε ≤ 1 := by
  sorry
```

**Приоритет:** ⭐⭐⭐ Высокий
**Усилия:** 1-2 дня
**Блокеры:** Нет

---

### 2. List.findIdx? свойства (SwitchingLemma.lean)

**Текущее состояние:**
- ❌ `List.findIdx?_some_get` имеет sorry (line 163)

**Что сделать:**

#### 2.1 Поиск в Mathlib/Batteries
Проверить наличие готовых лемм:
- `List.findIdx?_eq_some`
- `List.get_findIdx?`
- Альтернативные формулировки

#### 2.2 Доказать самостоятельно
Если не найдено в библиотеке, доказать через индукцию по `List.findIdx?.go`:

```lean
lemma List.findIdx?_some_get {α : Type _} (p : α → Bool) (xs : List α) (i : Nat)
    (h : xs.findIdx? p = some i) :
    i < xs.length ∧ ∃ (hlt : i < xs.length), p (xs.get ⟨i, hlt⟩) = true := by
  -- Proof by induction on the internal go function
  sorry
```

**Приоритет:** ⭐⭐⭐⭐ Критический
**Усилия:** 2-4 часа (если в библиотеке) или 1 день (если доказывать)
**Блокеры:** Нет
**Разблокирует:** 2 леммы (firstAliveTerm?_some_alive, getTerm?_of_firstAliveTerm?)

---

### 3. Улучшения в choose_mul_pow_mul_pow_le_one

**Текущее состояние:**
- ✅ Лемма доказана (lines 124-193)
- Можно улучшить читаемость

**Что сделать:**

#### 3.1 Вынести вспомогательные леммы
```lean
-- Binomial theorem identity
lemma binomial_expansion_sum_eq_one (a b : ℝ) (n : Nat)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (∑ i ∈ Finset.range (n.succ),
        a ^ i * b ^ (n - i) * (Nat.choose n i : ℝ)) = 1 := by
  sorry
```

**Приоритет:** ⭐ Низкий (улучшение читаемости)
**Усилия:** 2-3 часа
**Блокеры:** Нет

---

### 4. Связь между PDT depth и DNF evaluation

**Текущее состояние:**
- ❌ `firstAliveTerm?_some_of_DT_ge_one` имеет sorry (line 195)

**Что нужно:**

#### 4.1 Формализовать "PDT вычисляет F на ρ"
```lean
def PDT.evaluatesOnSubcube (t : PDT n) (F : DNF n) (ρ : Subcube n) : Prop :=
  ∀ x, Core.mem ρ x → DNF.eval F x = true

lemma DT_depth_zero_iff_decided (F : DNF n) (ρ : Subcube n) (t : PDT n)
    (h : t.evaluatesOnSubcube F ρ) :
    t.depth = 0 ↔ (∀ x, Core.mem ρ x → DNF.eval F x = b) ∨ ... := by
  sorry
```

#### 4.2 Доказать основную лемму
```lean
lemma firstAliveTerm?_some_of_DT_ge_one (F : DNF n) (ρ : Restriction n)
    (h : ∃ t : PDT n, t.depth ≥ 1 ∧ t.evaluatesOnSubcube F ρ) :
    firstAliveTerm? F ρ ≠ none := by
  -- Key insight: if depth ≥ 1, formula not decided, so must have alive term
  sorry
```

**Приоритет:** ⭐⭐⭐ Высокий
**Усилия:** 2-3 дня
**Блокеры:** Нужно изучить Core/PDT.lean и Core/BooleanBasics.lean
**Разблокирует:** Критический для buildSteps_length

---

### 5. Encoding length invariant (КРИТИЧНО!)

**Текущее состояние:**
- ❌ Line 681: Доказательство того, что `buildSteps ρ t` возвращает список длины `t`

**Проблема:**
```lean
buildSteps ρ t =
  match t with
  | 0 => []
  | s+1 =>
    match firstAliveTerm? F ρ with
    | none => []  -- RETURNS EMPTY! Length ≠ t
    | some idx => ...
```

**Что доказать:**

#### 5.1 Инвариант живого терма
```lean
lemma alive_term_at_each_step (F : DNF n) (ρ : Restriction n) (t : Nat)
    (hbad : ∃ dt : PDT n, dt.depth ≥ t ∧ dt.evaluatesOnSubcube F ρ) :
    firstAliveTerm? F ρ ≠ none := by
  -- Use firstAliveTerm?_some_of_DT_ge_one
  sorry
```

#### 5.2 Длина buildSteps
```lean
lemma buildSteps_length (F : DNF n) (ρ : Restriction n) (t : Nat)
    (hbad : ∃ dt : PDT n, dt.depth ≥ t ∧ ...) :
    (buildSteps F ρ t).length = t := by
  -- Induction on t
  -- Use alive_term_at_each_step to show none case never happens
  sorry
```

**Приоритет:** ⭐⭐⭐⭐⭐ КРИТИЧЕСКИЙ
**Усилия:** 3-5 дней
**Блокеры:** Зависит от пункта 4 (PDT depth lemma)
**Важность:** Это главный математический пробел!

---

## ⚠️ Что ЗАБЛОКИРОВАНО (требует внешней помощи)

### Блокер 1: Приватный API Term.restrictList

**Проблема:** 7 лемм не могут быть доказаны из-за `private def restrictList` в AC0/Formulas.lean

**Затронутые леммы:**
1. `alive_iff_exists_star` (line 81)
2. `killed_iff_exists_falsified` (lines 84-100)
3. `satisfied_iff_exists_satisfied` (lines 103-119)
4. `ofTerm_singleton_falsified` (line 134)
5. `ofTerm_singleton_satisfied` (line 141)
6. `ofTerm_singleton_unassigned` (line 148)
7. `alive_has_unassigned_lit` (line 411)

**Решение:** Связаться с авторами AC0/Formulas.lean и попросить:
- Сделать `restrictList` публичным
- Или добавить публичные леммы о поведении `Term.restrict`

**Альтернатива:** Аксиоматизировать эти свойства как "internal API facts"

---

### Блокер 2: Теория вероятности

**Проблема:** Mathlib.Probability недостаточна для формализации R_p distribution

**Затронутые леммы:**
1. `encode_injective` (line 566)
2. `decode_encode_id` (line 577)
3. `switching_base` (line 755)
4. `switching_multi_segmented` (line 906)

**Решение:** Либо ждать развития Mathlib, либо принять как "well-documented external facts"

---

### Блокер 3: Circuit-Input Game (Chapman-Williams)

**Проблема:** 4 аксиомы antichecker требуют формализации сложной игры

**Затронутые аксиомы:** (в AntiChecker.lean)
1. `antiChecker_exists_large_Y`
2. `antiChecker_exists_testset`
3. `antiChecker_exists_large_Y_local`
4. `antiChecker_exists_testset_local`

**Решение:** Принять как external facts с подробными proof sketches (уже сделано)

---

## 🎯 Рекомендуемый план работ

### Фаза 1: Немедленные улучшения (1-2 дня)

1. ✅ **List.findIdx?_some_get**
   - Поиск в Mathlib
   - Если не найдено - доказать
   - Разблокирует 2 леммы

2. ✅ **Свойства Hbin**
   - Монотонность
   - Симметрия
   - Границы
   - Полезно для Step B

### Фаза 2: PDT и encoding (3-5 дней)

3. ✅ **PDT depth analysis**
   - Формализовать evaluatesOnSubcube
   - Доказать firstAliveTerm?_some_of_DT_ge_one

4. ✅ **Encoding length invariant**
   - Доказать alive_term_at_each_step
   - Доказать buildSteps_length
   - **КРИТИЧНО для математической корректности!**

### Фаза 3: Документация (1 день)

5. ✅ **Обновить StepAB_Status.md**
   - Отметить прогресс
   - Обновить счетчики sorry
   - Задокументировать блокеры

---

## 📈 Ожидаемые результаты

### После Фазы 1:
- Доказанных лемм: 13-15 (было 10)
- Sorry в SwitchingLemma: 24-26 (было 28)
- Новые свойства Hbin: 3-4 леммы

### После Фазы 2:
- Доказанных лемм: 17-19
- **ГЛАВНОЕ:** Доказана корректность encoding length!
- Sorry в SwitchingLemma: 20-22

### Итого:
- **+7-9 доказанных лемм**
- **-6-8 sorries**
- **Математическая корректность Step A значительно улучшена**

---

## 🔍 Следующие вопросы для уточнения

1. **О PDT.lean:**
   - Есть ли уже определение "PDT вычисляет функцию"?
   - Какие свойства PDT.depth уже доказаны?

2. **О Term.restrictList:**
   - Можно ли открыть API?
   - Есть ли планы добавить публичные леммы?

3. **О стратегии:**
   - Какой уровень формализации требуется?
   - Можно ли принять некоторые факты как аксиомы?

---

## ✅ Заключение

**Доступные улучшения без блокеров:**
- ✅ 3-4 свойства Hbin (1-2 дня)
- ✅ List.findIdx? lemma (0.5-1 день)
- ✅ PDT depth analysis (2-3 дня)
- ✅ Encoding length proof (3-5 дней)

**Итого: 7-11 дней работы → +7-9 доказанных лемм**

**Математический эффект:**
- Закрывает главный пробел (encoding length)
- Усиливает Step B (Hbin properties)
- Разблокирует цепочку доказательств (List.findIdx?)

**Следующий шаг:** Начать с Фазы 1 (List.findIdx? + Hbin)
