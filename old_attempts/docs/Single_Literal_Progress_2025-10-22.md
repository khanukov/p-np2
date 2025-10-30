# Depth-2 Single Literal: Progress Update
**Дата:** 22 октября 2025
**Сессия:** Продолжение формализации depth-2 switching
**Статус:** Структура доказательства создана ✅

---

## Резюме

Создана полная структура доказательства для single literal case - простейшего нетривиального depth-2 случая. PDT инфраструктура оказалась уже готовой (node конструктор существует), что позволило сразу приступить к построению доказательства.

---

## Выполненная работа

### 1. Обнаружение готовой инфраструктуры ✅

**Открытие:** PDT уже имеет `node` конструктор!
```lean
inductive PDT (n : Nat) where
| leaf (R : Subcube n) : PDT n
| node (i : Fin n) (zeroBranch oneBranch : PDT n) : PDT n  -- ✅ Уже есть!
```

**Преимущество:** Не нужно расширять PDT - все готово для ветвления.

---

### 2. Вспомогательные определения ✅

**Созданы функции для restriction подкубов:**
```lean
def restrictToFalse (n : Nat) (i : Fin n) : Subcube n :=
  fun j => if j = i then some false else none

def restrictToTrue (n : Nat) (i : Fin n) : Subcube n :=
  fun j => if j = i then some true else none

def fullSubcube (n : Nat) : Subcube n :=
  fun _ => none
```

**Назначение:** Создание подкубов, которые фиксируют одну переменную.

---

### 3. Структура доказательства single literal ✅

**Теорема:**
```lean
theorem partial_shrinkage_single_literal {n : Nat} (i : Fin n) :
    let f := singleLiteral n i  -- f(x) = xᵢ
    let F := [f]
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ F),
      ℓ = 0 ∧              -- tail depth
      C.depthBound = 1 ∧   -- trunk depth
      C.epsilon = 0        -- exact representation
```

**Конструкция:**
```lean
let β_false := restrictToFalse n i  -- Subcube: i=false, rest free
let β_true := restrictToTrue n i    -- Subcube: i=true, rest free
let tree := PDT.node i (PDT.leaf β_false) (PDT.leaf β_true)

-- Use PartialDT.ofPDT to create PartialDT with tail depth 0
witness := PartialDT.ofPDT tree
selectors := fun g => if g = f then [β_false, β_true] else []
```

**Идея:** Дерево с одним ветвлением на переменной i:
- Левая ветвь (i=false): лист β_false
- Правая ветвь (i=true): лист β_true

---

### 4. Доказанные части ✅

#### selectors_sub ✅
```lean
selectors_sub := by
  intro g γ hg hγ
  simp [F] at hg
  subst hg
  simp at hγ
  simp [PartialDT.realize_ofPDT, tree, PDT.leaves]
  exact hγ
```

**Ключевая лемма:** `PartialDT.realize_ofPDT` - realize of ofPDT is identity.

**Результат:** Доказано что селекторы принадлежат листьям дерева.

#### trunk_depth_le ✅
```lean
trunk_depth_le := by
  simp [PartialDT.ofPDT]
  exact Nat.le_of_eq h_depth
```

где `h_depth : PDT.depth tree = 1` доказано через `simp [tree, PDT.depth]`.

---

### 5. Оставшиеся sorry (4 штуки)

| Лемма | Строка | Сложность | Приоритет |
|-------|--------|-----------|-----------|
| `memB_restrictToFalse` | 66 | 🟢 Низкая | Высокий |
| `memB_restrictToTrue` | 74 | 🟢 Низкая | Высокий |
| `err_le` (main proof) | 142 | 🟡 Средняя | Высокий |
| `partial_shrinkage_single_neg_literal` | 154 | 🟡 Средняя | Средний |

---

## Технические детали

### Проблемы и решения

#### Проблема 1: Путаница с ℓ и depthBound
**Изначально:** Думал что ℓ - это trunk depth
**Реальность:**
- `ℓ` - tail depth bound (максимальная глубина tails)
- `depthBound` - trunk depth bound

**Решение:** Использовать ℓ=0 (ofPDT дает tails как листья), depthBound=1

#### Проблема 2: BitVec ambiguity
**Ошибка:** `BitVec` неоднозначен
**Решение:** Использовать `Core.BitVec` явно

#### Проблема 3: Performance timeout
**Причина:** Слишком агрессивный simp
**Решение:** Упростить proof, оставить детали для вспомогательных лемм

---

## Следующие шаги

### Приоритет 1: Доказать memB леммы 🟢
**Срок:** 1 день
**Сложность:** Низкая

**Требуется доказать:**
```lean
lemma memB_restrictToFalse {n : Nat} (i : Fin n) (x : Core.BitVec n) :
    memB (restrictToFalse n i) x = (x i == false)
```

**Идея:**
- memB проверяет все биты
- restrictToFalse фиксирует только i-й бит на false
- Остальные биты свободны (none) → всегда true

**План:**
1. Развернуть `memB` и `restrictToFalse`
2. Показать что `List.finRange n .all` сводится к проверке i-го бита
3. Использовать extensionality

---

### Приоритет 2: Доказать err_le 🟡
**Срок:** 2 дня
**Сложность:** Средняя

**Требуется:**
```lean
errU f [β_false, β_true] ≤ 0
```

**Стратегия:**
1. Использовать `errU_eq_zero_of_agree`
2. Показать что `f x = coveredB [β_false, β_true] x` для всех x
3. Case split на `x i`:
   - Если `x i = false`: использовать `memB_restrictToFalse`
   - Если `x i = true`: использовать `memB_restrictToTrue`

---

### Приоритет 3: Single negative literal 🟡
**Срок:** 1 день
**Сложность:** Средняя (аналогично positive)

Почти идентично single positive literal, но с отрицанием.

---

## Метрики прогресса

### Depth-2 Single Literal
```
Structure created:       ████████████████████ 100% ✅
Helper definitions:      ████████████████████ 100% ✅
selectors_sub:           ████████████████████ 100% ✅
trunk_depth_le:          ████████████████████ 100% ✅
memB lemmas:             ░░░░░░░░░░░░░░░░░░░░   0% (2 sorry)
err_le:                  ░░░░░░░░░░░░░░░░░░░░   0% (sorry)
Overall:                 ████████░░░░░░░░░░░░  40%
```

### Depth-2 Progress
```
Spec cleanup:            ████████████████░░░░  80% ✅
Single literal:          ████████░░░░░░░░░░░░  40% (in progress)
Single neg literal:      ░░░░░░░░░░░░░░░░░░░░   0% (defined)
Single clause:           ░░░░░░░░░░░░░░░░░░░░   0% (defined)
General depth-2:         ░░░░░░░░░░░░░░░░░░░░   0%
```

---

## Файлы изменены

| Файл | Изменения | Строки | Sorry |
|------|-----------|--------|-------|
| `Depth2_Constructive.lean` | Добавлено single literal proof | 175 | 4 |

**Новые определения:**
- `restrictToFalse`, `restrictToTrue`, `fullSubcube`
- `singleLiteral`, `singleNegLiteral`
- `SingleClause` structure

**Новые леммы (specs):**
- `memB_restrictToFalse` (sorry)
- `memB_restrictToTrue` (sorry)
- `partial_shrinkage_single_literal` (partial)
- `partial_shrinkage_single_neg_literal` (sorry)

---

## Оценка до завершения

### Single literal (текущая задача)
- **memB леммы:** 1 день 🟢
- **err_le proof:** 2 дня 🟡
- **Всего:** 3 дня

### Single negative literal
- **Аналогично positive:** 2 дня 🟡

### Single clause (OR)
- **Сложнее, индукция:** 1 неделя 🟡

### Общий depth-2
- **Обобщение:** 2-3 недели 🟡

**Итоговая оценка до полного depth-2:** ~1 месяц

---

## Выводы

### ✅ Что достигнуто
1. **PDT готов** - node конструктор уже существует
2. **Структура создана** - полный каркас доказательства
3. **40% завершено** - selectors_sub и trunk_depth_le доказаны
4. **Компилируется** - 4 sorry, все документированы

### 🎯 Следующий шаг
**memB леммы** - простые технические леммы (1 день)

### 📈 Реалистичная оценка
```
Single literal:          ████████░░░░░░░░░░░░  40% (3 дня до 100%)
├─ Structure:            ████████████████████ 100% ✅
├─ memB lemmas:          ░░░░░░░░░░░░░░░░░░░░   0% (1 день)
├─ err_le:               ░░░░░░░░░░░░░░░░░░░░   0% (2 дня)
└─ Total:                ████████░░░░░░░░░░░░  40%
```

---

## Честная оценка

### Можно утверждать:
✅ "Структура доказательства single literal создана"
✅ "40% доказательства завершено (selectors_sub, trunk_depth_le)"
✅ "PDT инфраструктура готова"
✅ "3 дня до полного доказательства single literal"

### Нельзя утверждать:
❌ "Single literal доказан"
❌ "Depth-2 switching доказан"
❌ "Нет sorry"

### Реалистичная формулировка:
> "Создана полная структура доказательства single literal case. Доказано 40% (selectors_sub, trunk_depth_le). Остаются 4 sorry: 2 простые технические леммы (memB), 1 основной err_le proof, 1 negative literal (аналогично). Оценка до завершения: 3-5 дней."

---

**Создано:** 22 октября 2025
**Автор:** Claude Code
**Статус:** ✅ Хороший прогресс, 40% single literal complete
