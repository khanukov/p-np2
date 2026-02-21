# Анализ возможных проблем решения

**Дата**: 2026-02-21
**Ревизия**: на основе текущего состояния ветки `main` (коммит 7310b7f)

---

## Резюме

Репозиторий содержит формализацию на Lean 4 **условного** (conditional) вывода
`NP ⊄ PpolyFormula` через pipeline: SAL → Covering-Power → Anti-checker →
Magnification. Код компилируется без `sorry`/`admit`/`axiom` в каталоге `pnp3/`.
Однако итоговый результат **параметризован явными внешними гипотезами**, которые
не являются доказанными теоремами. Ниже перечислены обнаруженные проблемы — от
критических до менее значительных.

---

## 1. КРИТИЧЕСКИЕ ПРОБЛЕМЫ

### 1.1. `StructuredLocalityProviderPartial` — главная незакрытая гипотеза

**Файл**: `pnp3/Magnification/Facts_Magnification_Partial.lean:49–53`

```lean
def StructuredLocalityProviderPartial : Prop :=
  ∀ (p : GapPartialMCSPParams) (δ : Rat),
    FormulaLowerBoundHypothesisPartial p δ →
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) →
      RestrictionLocalityPartial p
```

Это **ключевая гипотеза всего pipeline**: из неё выводится всё, включая
`NP_not_subset_PpolyFormula_final`. Она требует, чтобы из предположения
«gapPartialMCSP_Language лежит в PpolyFormula» можно было извлечь локальный
решатель с polylog-тестсетом. Это аналог locality lift из Williams/Murray-Williams.

**Проблема**: В файле `pnp3/Magnification/LocalityProvider_Partial.lean` прямо
написано:

```lean
def hasDefaultStructuredLocalityProviderPartial : Prop := False
```

Т.е. авторы сами указывают, что конструктивного провайдера для этой гипотезы
**нет**. Вся цепочка теорем, начиная с `NP_not_subset_PpolyFormula_final`,
является условным утверждением вида «IF StructuredLocalityProviderPartial THEN
NP ⊄ PpolyFormula», но гипотеза не доказана.

**Значимость**: Без закрытия этой гипотезы **никакой безусловный результат о
разделении не получен**. Это не мелкая деталь — это главный не формализованный
шаг.

### 1.2. `PpolyFormula` ≡ `PpolyReal`: тавтологическая эквивалентность двух «разных» классов

**Файл**: `pnp3/Complexity/Interfaces.lean:93–118`

Два определения — `InPpolyFormula` и `InPpolyReal` — **полностью идентичны**
по структуре:

```lean
structure InPpolyFormula (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, FormulaCircuit n
  family_size_le : ∀ n, FormulaCircuit.size (family n) ≤ polyBound n
  correct : ∀ n (x : Bitstring n), FormulaCircuit.eval (family n) x = L n x

structure InPpolyReal (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, FormulaCircuit n
  family_size_le : ∀ n, FormulaCircuit.size (family n) ≤ polyBound n
  correct : ∀ n (x : Bitstring n), FormulaCircuit.eval (family n) x = L n x
```

Оба класса используют один тип `FormulaCircuit` (формулы), одну метрику размера
и одну семантику. Это делает `PpolyFormula = PpolyReal` **тавтологией**.

**Проблема**: Мост `GapPartialMCSPFormulaRealization` (преобразование
`PpolyReal → PpolyFormula`) становится тривиальным тождеством, а не
содержательным утверждением. В стандартной теории P/poly включает *общие схемы*
(circuits с fan-in и fan-out), тогда как формулы — это деревья (fan-out 1), и
размер формулы может быть экспоненциально больше размера схемы.
Формализация не различает эти два класса, что делает часть pipeline vacuous.

### 1.3. `Ppoly` — тривиализированный P/poly

**Файл**: `Facts/PsubsetPpoly/Proof/Complexity/Interfaces.lean:60–71`

```lean
structure InPpoly (L : Language) where
  polyBound : Nat → Nat := fun _ => (0 : Nat)
  polyBound_poly : True := trivial
  circuits : ∀ n, Bitstring n → Bool := fun _ _ => false
  correct : ∀ n (x : Bitstring n), circuits n x = L n x := by
    intro n x; rfl
```

Класс `P/poly` определён как **произвольная функция** `Bitstring n → Bool` с
тривиальным (`True`) условием на полиномиальный размер. Поле `polyBound_poly`
имеет тип `True`, а не реальное ограничение вида
`∃ c, ∀ n, polyBound n ≤ n^c + c`. Это означает:

- **Любой язык** автоматически лежит в этом определении `Ppoly`.
- Утверждение `P ⊆ Ppoly` становится тривиальным не потому, что доказан
  содержательный теоретико-сложностный факт, а потому, что `Ppoly = всё`.
- Утверждение `NP ⊄ Ppoly` (в этой формализации) **вообще ложно**, поскольку
  каждый язык из NP автоматически лежит в Ppoly (любая функция — это «схема»
  без ограничений на размер).

**Значимость**: Это полностью обесценивает заявленный мост `NP ⊄ P/poly ⇒ P ≠ NP`.
Класс `Ppoly` в этой формализации не является P/poly из стандартной теории
сложности. Правда, активный путь (через `PpolyFormula`) не использует этот
мост напрямую для финального утверждения, но `P_ne_NP_final` зависит от
дополнительной гипотезы `NP_not_subset_PpolyFormula → NP_not_subset_Ppoly`,
которая в данной формализации не может быть содержательной.

### 1.4. `NP` — определение без реального TM-уровня

**Файл**: `pnp3/Complexity/Interfaces.lean:202–212`

```lean
def NP (L : Language) : Prop :=
  ∃ (c k : Nat)
    (runTime : Nat → Nat)
    (verify : ∀ n, Bitstring n → Bitstring (certificateLength n k) → Bool),
    (∀ n, runTime ... ≤ ...) ∧
    (∀ n (x : Bitstring n), L n x = true ↔ ∃ w ..., verify n x w = true)
```

Функция `runTime` задаётся внешне, но **нигде не связана с реальным временем
работы `verify`**. Верификатор `verify` — просто булева функция. Ограничение
`runTime ≤ polynomial` не гарантирует, что `verify` можно вычислить за это время.
Функция `runTime` — это phantom-параметр.

**Проблема**: Класс `NP` в данной формализации — это фактически класс
`∃/poly` (нестандартная non-uniform existential версия), а не классический NP с
полиномиальным верификатором на Turing-машине. Хотя есть попытка мостить к TM
через `NP_TM → NP`, сам TM не используется в доказательстве
`gapPartialMCSP_in_NP`.

### 1.5. `gapPartialMCSP_in_NP` — верификатор игнорирует сертификат

**Файл**: `pnp3/Models/Model_PartialMCSP.lean:540–574`

```lean
noncomputable def gapPartialMCSP_verify (p : GapPartialMCSPParams) :
    ∀ n, Bitstring n → Bitstring (certificateLength n 2) → Bool := by
  classical
  intro n x _w
  by_cases h : n = partialInputLen p
  · subst h
    exact decide (PartialMCSP_YES p (decodePartial x))
  · exact false
```

Верификатор **не использует сертификат `_w`**. Он просто решает задачу
детерминированно по входу `x`. Доказательство NP-принадлежности строится так:

- YES: выбирается сертификат `fun _ => false` (произвольный), результат не
  зависит от выбора.
- NO: аналогично.

Это показывает, что определение NP здесь не требует реального свидетеля.
В классической теории MCSP ∈ NP — это отдельный нетривиальный вопрос (и даже
открытый для полного MCSP).

---

## 2. СУЩЕСТВЕННЫЕ ПРОБЛЕМЫ

### 2.1. Shrinkage/switching witnesses не формализованы

**Файл**: `pnp3/ThirdPartyFacts/Facts_Switching.lean`

Shrinkage-факты для AC⁰ (`partial_shrinkage_for_AC0`) и локальных схем
(`shrinkage_for_localCircuit`) представлены как теоремы, требующие **внешних
witness-объектов** (`AC0CircuitWitness`, `LocalCircuitWitness`). Эти witness
нигде не конструируются. Фактически это «аксиомы в маскировке» — корректность
кода зависит от их существования, но оно не доказано.

### 2.2. `FamilyIsAC0` и `FamilyIsLocalCircuit` — пустые требования

В anti-checker (`noSmallAC0Solver_partial`) используется гипотеза
`FamilyIsAC0 solver.params.ac0 (allFunctionsFamily ...)` — утверждение, что
**семейство всех булевых функций** принадлежит AC⁰. Это утверждение ложно
в стандартной теории сложности (parity ∉ AC⁰). Однако в данной формализации
`FamilyIsAC0` — структура, предоставленная извне (witness-backed), что
позволяет ей быть тривиально необитаемой. Это создаёт замкнутый круг:
anti-checker «работает» потому, что его гипотеза никогда не может быть
удовлетворена содержательно.

### 2.3. `hCardHalf` — незакрытое обязательство в locality lift

Для использования certificate-driven locality lift требуется условие:

```
restriction.alive.card ≤ Partial.tableLen p.n / 2
```

Это условие передаётся как внешний параметр `hCardHalf` и не доказано
конструктивно.

### 2.4. Канонический shrinkage witness — пустой

**Файл**: `Facts/LocalityLift/Facts/LocalityLift/Proof/ShrinkageWitness.lean:248–259`

```lean
def canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    ShrinkageWitness general := by
  classical
  refine
    { toShrinkageSummary := canonicalSummary (p := p) general
      , restriction := Restriction.ofVector (canonicalAlive p) (zeroVector (inputLen p))
      , restriction_alive := ... }
```

Канонический witness использует пустой набор живых координат
(`canonicalAlive` = ∅), нулевой тест-набор, и локальность 0. Это trivial
placeholder, не несущий содержательной shrinkage-информации.

---

## 3. МЕНЕЕ КРИТИЧНЫЕ ЗАМЕЧАНИЯ

### 3.1. `P_ne_NP` — нестандартное определение

```lean
def P_ne_NP : Prop := Facts.PsubsetPpoly.P.{0} ≠ NP
```

`P ≠ NP` определено как неравенство *функций* `P` и `NP`, где
`Facts.PsubsetPpoly.P` — TM-определение P, а `NP` — абстрактное определение
из `Interfaces.lean`. Это **разные типы определений**: TM-P vs existential-NP.
Для содержательности нужно, чтобы `P L` и `NP L` были определены через
совместимые модели вычисления, что в данной формализации не гарантируется.

### 3.2. `canonicalPartialParams` — фиксированные мелкие параметры

**Файл**: `pnp3/Magnification/FinalResult.lean:13–20`

```lean
@[simp] def canonicalPartialParams : GapPartialMCSPParams where
  n := 8
  sYES := 1
  sNO := 3
```

Используются конкретные маленькие значения (n=8). При n=8 длина входа
`partialInputLen = 2 * 2^8 = 512` бит. Вся теория должна «масштабироваться»
для произвольных n, но фактически pipeline зафиксирован на n=8.

### 3.3. Дублирование `FormulaCircuit` и `Circuit`

В файле `Models/Model_PartialMCSP.lean` определён `Circuit` (для MCSP),
а в `Complexity/Interfaces.lean` — `FormulaCircuit` (для P/poly). Оба типа
имеют идентичную структуру (AND/OR/NOT/CONST/INPUT с fan-in 2). Это приводит
к путанице: circuit complexity в модели MCSP и circuit complexity в определении
P/poly формально не связаны.

---

## 4. ИТОГОВАЯ ОЦЕНКА

| Аспект | Статус |
|---|---|
| `sorry`/`admit` в `pnp3/` | 0 (чисто) |
| `axiom` в `pnp3/` | 0 (чисто) |
| Компилируемость | Да (`lake build` проходит) |
| Безусловный результат | **Нет** |
| Корректность определений классов сложности | **Есть существенные проблемы** |
| Содержательность финальной теоремы | **Условная, зависит от не-тривиальных гипотез** |

### Главная проблема

Проект представляет собой формально корректную условную импликацию:

```
StructuredLocalityProviderPartial → NP ⊄ PpolyFormula
```

Однако:
1. `StructuredLocalityProviderPartial` — **не доказана и не тривиальна**.
2. `PpolyFormula` — **не является стандартным P/poly** (использует формулы, а
   не общие схемы, и к тому же `PpolyFormula ≡ PpolyReal` делает класс
   не содержательным).
3. `NP` — **упрощённое определение**, не гарантирующее реальное полиномиальное
   время верификации.
4. `Ppoly` (из внешнего пакета) — **тривиализирован** (`polyBound_poly : True`),
   что делает утверждение `P ⊆ P/poly` автоматически верным, но бессодержательным.

В результате, даже если бы `StructuredLocalityProviderPartial` была доказана,
итоговый результат не соответствовал бы стандартному `P ≠ NP` из теории
сложности из-за расхождений в определениях базовых классов.
