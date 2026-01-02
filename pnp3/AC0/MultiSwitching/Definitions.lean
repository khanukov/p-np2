import Core.BooleanBasics
import Core.PDT
import Core.SAL_Core
import AC0.MultiSwitching.Restrictions

/-!
  pnp3/AC0/MultiSwitching/Definitions.lean

  Базовые определения для multi‑switching: k‑CNF/k‑DNF, семейства формул и
  их интерпретация как булевых функций. Здесь мы фиксируем минимальный
  «контракт» типов, чтобы остальная формализация могла ссылаться на устойчивые
  имена, а подробные определения (restriction, CCDT и т.д.) достраивать далее.

  Замечание: в этом файле нет доказательств switching‑лемм. Он лишь задаёт
  терминологию и удобные сокращения, на которые будут опираться модули
  Encoding/Counting/Glue.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-! ### k‑CNF / k‑DNF -/

/-- k‑CNF по сути совпадает с `Core.CNF`. -/
abbrev kCNF (n k : Nat) := Core.CNF n k

/-- k‑DNF по сути совпадает с `Core.DNF`. -/
abbrev kDNF (n k : Nat) := Core.DNF n k

variable {n k : Nat}

/-- Интерпретация k‑CNF как булевой функции. -/
@[simp] def evalCNF (F : kCNF n k) : Core.BitVec n → Bool := fun x => F.eval x

/-- Интерпретация k‑DNF как булевой функции. -/
@[simp] def evalDNF (F : kDNF n k) : Core.BitVec n → Bool := fun x => F.eval x

/-! ### Семейства формул -/

/-- Семейство k‑CNF формул (конечный список). -/
abbrev FormulaFamily (n k : Nat) := List (kCNF n k)

/-- Семейство k‑DNF формул (конечный список). -/
abbrev DnfFamily (n k : Nat) := List (kDNF n k)

/-- Перевод семейства k‑CNF в `Core.Family` булевых функций. -/
@[simp] def evalFamily (F : FormulaFamily n k) : Core.Family n :=
  F.map evalCNF

/-- Перевод семейства k‑DNF в `Core.Family` булевых функций. -/
@[simp] def evalDnfFamily (F : DnfFamily n k) : Core.Family n :=
  F.map evalDNF

/-!
### Множество "плохих" рестрикций

Базовая обёртка над `R_s`: фильтруем по вычислимому предикату.
Это используется как в encoding, так и в оценках кардиналов.
-/

variable {n : Nat}

/--
Множество "плохих" рестрикций внутри `R_s`: это просто фильтр по предикату
`bad`. По умолчанию используется `DecidablePred bad`, чтобы лемма была
применима к любому вычислимому условию.
-/
@[simp] def badRestrictions (s : Nat) (bad : Restriction n → Prop)
    [DecidablePred bad] : Finset (Restriction n) :=
  (R_s (n := n) s).filter bad

/-!
  Простейшие свойства `badRestrictions`.

  Эти леммы почти тривиальны, но они избавляют от повторения
  однотипных аргументов `simp`/`filter` в будущих модулях.
-/

/-- Подмножество: `badRestrictions` лежит внутри `R_s`. -/
lemma badRestrictions_subset {s : Nat} {bad : Restriction n → Prop}
    [DecidablePred bad] :
    badRestrictions (n := n) s bad
      ⊆ R_s (n := n) s := by
  intro ρ hmem
  have hmem' : ρ ∈ R_s (n := n) s ∧ bad ρ := by
    simpa [badRestrictions] using hmem
  exact hmem'.1

/--
Кардинал `badRestrictions` никогда не превосходит кардинал `R_s`.

Это базовая оценка, которая в паре с *строгим* неравенством
даёт существование "хорошей" рестрикции.
-/
lemma badRestrictions_card_le {s : Nat} {bad : Restriction n → Prop}
    [DecidablePred bad] :
    (badRestrictions (n := n) s bad).card
      ≤ (R_s (n := n) s).card := by
  classical
  -- `filter` всегда уменьшает кардинал.
  simpa [badRestrictions] using
    (Finset.card_filter_le (s := R_s (n := n) s)
      (p := bad))

@[simp] lemma mem_badRestrictions {s : Nat} {bad : Restriction n → Prop}
    [DecidablePred bad] {ρ : Restriction n} :
    ρ ∈ badRestrictions (n := n) s bad
      ↔ ρ ∈ R_s (n := n) s ∧ bad ρ := by
  classical
  simp [badRestrictions]

/--
Если "плохих" рестрикций строго меньше, чем всего `R_s`,
то существует "хорошая" рестрикция в `R_s`.

Это целевой комбинаторный шаг, который в дальнейшем будет
применяться после доказательства оценки на `card (badRestrictions ...)`.
-/
lemma exists_good_of_card_lt {s : Nat} {bad : Restriction n → Prop}
    [DecidablePred bad]
    (hcard :
      (badRestrictions (n := n) s bad).card
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ bad ρ := by
  classical
  have hsubset :
      badRestrictions (n := n) s bad
        ⊆ R_s (n := n) s := by
    exact badRestrictions_subset (n := n) (s := s) (bad := bad)
  rcases Restriction.exists_not_mem_of_subset_card_lt
      (s := badRestrictions (n := n) s bad)
      (t := R_s (n := n) s)
      hsubset hcard with ⟨ρ, hρt, hρs⟩
  refine ⟨ρ, hρt, ?_⟩
  intro hbad
  have : ρ ∈ badRestrictions (n := n) s bad := by
    exact (mem_badRestrictions (n := n) (s := s) (bad := bad)).2 ⟨hρt, hbad⟩
  exact hρs this

/-!
### Lean‑friendly параметры для multi‑switching

В литературе часто пишут параметры как `ℓ = ⌈log₂(2M)⌉` и
`t = ⌈log₂(M (n+2))⌉ + O(1)`.  В Lean удобнее фиксировать
более простые выражения через `Nat.log2`, добавляя небольшой запас.

Эти определения **не являются** частью доказательства switching‑леммы:
они служат "контрактом" для downstream‑кода (в частности, в
`Facts_Switching.lean`), чтобы имена параметров оставались стабильны.
-/

/--
`ℓParam M` — удобная версия `⌈log₂(2M)⌉` с запасом на округление.

Лемма `pow_two_le` (ниже) позволит доказывать `2^(ℓParam M) ≥ 2M`
без разборов случаев `M=0`.
-/
def ℓParam (M : Nat) : Nat :=
  Nat.log2 (2 * M + 1) + 1

/--
`tParam M n` — безопасный вариант `⌈log₂(M (n+2))⌉ + O(1)`.

Добавка `+2` даёт запас, который обычно нужен при переходе от
`log2` (с округлением вниз) к оценкам вида `2^t ≥ M(n+2)`.
-/
def tParam (M n : Nat) : Nat :=
  Nat.log2 (M * (n + 2) + 1) + 2

/-!
### Минимальные арифметические факты о параметрах

Мы добавляем несколько простых лемм, чтобы downstream‑код мог
использовать их "как есть" без ручного переписывания.
Конкретная форма этих лемм подобрана так, чтобы последующие
неравенства в оценках встречались в точности в нужном виде.
-/

lemma pow_two_le_ℓParam (M : Nat) :
    2 ^ (ℓParam M) ≥ 2 * M := by
  -- Ключевой факт: `x < 2^(log2 x + 1)`.
  have hlt : 2 * M + 1 < 2 ^ (Nat.log2 (2 * M + 1) + 1) := by
    -- Используем общую лемму `lt_pow_succ_log_self` для `log 2`.
    have hlog :
        2 * M + 1 <
          2 ^ (Nat.log 2 (2 * M + 1)).succ := by
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two (2 * M + 1)
    -- Переписываем `log 2` как `log2`.
    simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using hlog
  -- Теперь ослабляем строгую оценку до `≤` и убираем `+1`.
  have hle : 2 * M ≤ 2 ^ (Nat.log2 (2 * M + 1) + 1) := by
    exact Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self (2 * M)) hlt)
  -- Подстановка определения `ℓParam`.
  simpa [ℓParam] using hle

lemma pow_two_le_tParam (M n : Nat) :
    2 ^ (tParam M n) ≥ M * (n + 2) := by
  -- Аналогично `pow_two_le_ℓParam`, но для `M*(n+2)`.
  have hlt : M * (n + 2) + 1 < 2 ^ (Nat.log2 (M * (n + 2) + 1) + 1) := by
    have hlog :
        M * (n + 2) + 1 <
          2 ^ (Nat.log 2 (M * (n + 2) + 1)).succ := by
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two (M * (n + 2) + 1)
    simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using hlog
  have hle : M * (n + 2) ≤ 2 ^ (Nat.log2 (M * (n + 2) + 1) + 1) := by
    exact Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self (M * (n + 2))) hlt)
  -- `tParam` имеет дополнительный запас `+2`, так что достаточно ослабить.
  have hmono :
      2 ^ (Nat.log2 (M * (n + 2) + 1) + 1)
        ≤ 2 ^ (Nat.log2 (M * (n + 2) + 1) + 2) := by
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) (Nat.le_succ _)
  have hle' : M * (n + 2) ≤ 2 ^ (Nat.log2 (M * (n + 2) + 1) + 2) := by
    exact Nat.le_trans hle hmono
  simpa [tParam] using hle'

/-!
### Refinement relation between subcubes

Для multi-switching нам удобно формализовать, что один подкуб
«уточняет» другой: он не противоречит фиксированным битам исходного
подкуба. Это минимальная зависимость, не требующая порядка на `Subcube`.
-/

/-- Подкуб `β` уточняет `γ`, если он согласован со всеми фиксированными битами `γ`. -/
def subcubeRefines (β γ : Subcube n) : Prop :=
  ∀ i b, γ i = some b → β i = some b

/-- Любой подкуб уточняет сам себя. -/
@[simp] lemma subcubeRefines_refl (β : Subcube n) : subcubeRefines β β := by
  intro i b hb
  exact hb

/--
Уточнение транзитивно: если `β` согласован с `γ`, а `γ` — с `δ`,
то `β` согласован и с `δ`.
-/
lemma subcubeRefines_trans {β γ δ : Subcube n}
    (hβγ : subcubeRefines β γ) (hγδ : subcubeRefines γ δ) :
    subcubeRefines β δ := by
  intro i b hδ
  exact hβγ i b (hγδ i b hδ)

/-!
### Минимальный контракт для CCDT (Common Partial Decision Tree)

Чтобы downstream‑код мог опираться на устойчивые имена и поля, мы
фиксируем здесь *каркас* результата CCDT.  Это **не** определение
алгоритма CCDT и **не** его доказательство: лишь структура‑носитель,
которая формулирует те свойства, которые понадобятся в Encoding/Counting
и в индукции по глубине AC⁰.

Важно: мы не фиксируем здесь `canonicalDT` или конкретный формат формул,
чтобы не заморозить слишком рано дизайн.  На практике `FormulaFamily`
достаточно для согласования интерфейсов.
-/

/--
`CCDTResult` хранит общий ствол `trunk` и ключевые инварианты:

* глубина ствола ≤ `t`;
* каждый лист ствола задаёт рестрикцию, уточняющую базовую `ρ0`;
* для любой формулы `φ` из семейства на каждом листе существует
  *локальное* дерево решений глубины ≤ `ℓ`.

Последнее поле (`tail`) здесь дано как **абстрактная функция**: в реальном
доказательстве оно будет строиться через канонический DT, но для
downstream‑интеграции достаточно этой спецификации.
-/
structure CCDTResult (n k : Nat) (ℓ t : Nat)
    (F : FormulaFamily n k) (ρ0 : Restriction n) : Type where
  /-- Общий ствол CCDT. -/
  trunk : PDT n
  /-- Ствол не глубже `t`. -/
  trunk_depth_le : PDT.depth trunk ≤ t
  /-- Каждый лист задаёт рестрикцию, уточняющую базовую. -/
  leaf_refines :
    ∀ β ∈ PDT.leaves trunk, subcubeRefines β ρ0.mask
  /--
  Локальные хвосты: для каждого листа и формулы существует DT глубины ≤ ℓ.
  Мы храним явную функцию `tail` для последующего использования в Counting.
  -/
  tail : ∀ β ∈ PDT.leaves trunk, ∀ φ ∈ F, PDT n
  /-- Глубина каждого хвоста не превосходит ℓ. -/
  tail_depth_le :
    ∀ β hβ φ hφ, PDT.depth (tail β hβ φ hφ) ≤ ℓ

/-!
Дополнительные помощники: простые обёртки, чтобы не переписывать сигнатуры.
Эти леммы ничего не добавляют математически, но улучшают читаемость
дальнейших доказательств.
-/

@[simp] lemma CCDTResult.trunk_le_depth {n k ℓ t : Nat}
    {F : FormulaFamily n k} {ρ0 : Restriction n}
    (C : CCDTResult n k ℓ t F ρ0) :
    PDT.depth C.trunk ≤ t := C.trunk_depth_le

@[simp] lemma CCDTResult.tail_depth_le' {n k ℓ t : Nat}
    {F : FormulaFamily n k} {ρ0 : Restriction n}
    (C : CCDTResult n k ℓ t F ρ0) (β : Subcube n) (hβ : β ∈ PDT.leaves C.trunk)
    (φ : kCNF n k) (hφ : φ ∈ F) :
    PDT.depth (C.tail β hβ φ hφ) ≤ ℓ :=
  C.tail_depth_le β hβ φ hφ

/-!
### Шаблон алгоритма CCDT и событие "плохой рестрикции"

Для encoding/injection (и для дальнейшей combinatorial оценки) нам
понадобится **детерминированная** процедура, которая по рестрикции `ρ`
строит общий ствол `PDT`.  Пока мы фиксируем лишь интерфейс:

* `ccdt` — детерминированная функция `Restriction n → PDT n`;
* `BadEvent` — предикат «получившийся ствол слишком глубокий».

Конкретная реализация (выбор формулы, выбор пути и т.д.) будет добавлена
в модуле `Encoding` после того, как мы зафиксируем канонический DT.
-/

/-- Интерфейс детерминированного CCDT-алгоритма для семейства `F`. -/
structure CCDTAlgorithm (n k : Nat) (ℓ t : Nat)
    (F : FormulaFamily n k) : Type where
  /-- Детерминированный конструктор ствола. -/
  ccdt : Restriction n → PDT n

/-- "Плохое" событие: глубина CCDT-ствола не меньше `t`. -/
def BadEvent {n k ℓ t : Nat} {F : FormulaFamily n k}
    (A : CCDTAlgorithm n k ℓ t F) (ρ : Restriction n) : Prop :=
  t ≤ PDT.depth (A.ccdt ρ)

/-!
`BadEvent` решается по вычислимому сравнению натуральных чисел,
поэтому предикат является `DecidablePred`. Это удобно, чтобы
в последующих модулях не таскать явный аргумент с решаемостью.
-/
instance {n k ℓ t : Nat} {F : FormulaFamily n k}
    (A : CCDTAlgorithm n k ℓ t F) : DecidablePred (BadEvent (A := A)) := by
  intro ρ
  dsimp [BadEvent]
  infer_instance

@[simp] lemma BadEvent_iff {n k ℓ t : Nat} {F : FormulaFamily n k}
    (A : CCDTAlgorithm n k ℓ t F) (ρ : Restriction n) :
    BadEvent (A := A) ρ ↔ t ≤ PDT.depth (A.ccdt ρ) := by
  rfl

/-!
### Множество "плохих" рестрикций

Эта обёртка связывает определение `BadEvent` с моделью `R_s`.
Понадобится в encoding/injection: мы будем считать `Bad` и
сравнивать его с `R_s`.
-/

/-- Множество `Bad` — "плохие" рестрикции в `R_s` для данного алгоритма. -/
@[simp] def Bad {n k ℓ t : Nat} {F : FormulaFamily n k}
    (A : CCDTAlgorithm n k ℓ t F) (s : Nat) :
    Finset (Restriction n) :=
  badRestrictions (n := n) s (BadEvent (A := A))

@[simp] lemma mem_Bad {n k ℓ t : Nat} {F : FormulaFamily n k}
    (A : CCDTAlgorithm n k ℓ t F) {s : Nat} {ρ : Restriction n} :
    ρ ∈ Bad (A := A) s ↔ ρ ∈ R_s (n := n) s ∧ BadEvent (A := A) ρ := by
  classical
  simp [Bad, badRestrictions]

lemma mem_evalFamily_iff {F : FormulaFamily n k} {f : Core.BitVec n → Bool} :
    f ∈ evalFamily F ↔ ∃ G ∈ F, evalCNF (n := n) (k := k) G = f := by
  classical
  constructor
  · intro hmem
    rcases List.mem_map.1 hmem with ⟨G, hG, rfl⟩
    exact ⟨G, hG, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    exact List.mem_map.2 ⟨G, hG, rfl⟩

lemma mem_evalDnfFamily_iff {F : DnfFamily n k} {f : Core.BitVec n → Bool} :
    f ∈ evalDnfFamily F ↔ ∃ G ∈ F, evalDNF (n := n) (k := k) G = f := by
  classical
  constructor
  · intro hmem
    rcases List.mem_map.1 hmem with ⟨G, hG, rfl⟩
    exact ⟨G, hG, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    exact List.mem_map.2 ⟨G, hG, rfl⟩

end MultiSwitching
end AC0
end Pnp3
