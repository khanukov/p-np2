import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Core.BooleanBasics
import Complexity.Promise
import Complexity.Interfaces
import Models.PartialTruthTable

/-!
  pnp3/Models/Model_PartialMCSP.lean

  Модель Partial MCSP, построенная поверх канонического типа
  `PartialFunction (n : Nat) := Fin (2^n) → Option Bool`.

  Ключевые элементы:
  * параметры gap-задачи (аналог параметров total‑MCSP);
  * предикат согласованности схемы с частичной таблицей;
  * формулировки YES/NO-условий;
  * язык gapPartialMCSP_Language с фиксированной кодировкой `mask ++ values`.
-/

namespace Pnp3
namespace Models

open Core
open Complexity
open ComplexityInterfaces

/-!
  ### Базовая модель булевых схем

  Для частичного MCSP мы используем ту же «минимальную» модель схем,
  что и в архивной total‑версии: базис {AND, OR, NOT} с fan‑in 2.
  Это позволяет задать размер и вычисление схемы прямо в этом файле,
  не опираясь на скрытую/архивную реализацию.

  Важно: модель не накладывает ограничений на глубину; ограничения
  появляются позже через классы «малых» решателей и параметры.
-/

/-- Примитивные схемы над `n` входами. -/
inductive Circuit (n : Nat) where
  | input : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n
  deriving Repr

/-- Размер схемы как число вентилей (каждая вершина считается за 1). -/
def Circuit.size {n : Nat} : Circuit n → Nat
  | Circuit.input _ => 1
  | Circuit.const _ => 1
  | Circuit.not c => c.size + 1
  | Circuit.and c₁ c₂ => c₁.size + c₂.size + 1
  | Circuit.or c₁ c₂ => c₁.size + c₂.size + 1

/-- Вычисление схемы на входе `x`. -/
def Circuit.eval {n : Nat} : Circuit n → Core.BitVec n → Bool
  | Circuit.input i => fun x => x i
  | Circuit.const b => fun _ => b
  | Circuit.not c => fun x => !(Circuit.eval c x)
  | Circuit.and c₁ c₂ => fun x => Circuit.eval c₁ x && Circuit.eval c₂ x
  | Circuit.or c₁ c₂ => fun x => Circuit.eval c₁ x || Circuit.eval c₂ x

namespace Circuit

/-- Reindex a circuit from `n` inputs to `n+1` inputs by skipping index `0`. -/
def weaken {n : Nat} : Circuit n → Circuit (n + 1)
  | input i => input i.succ
  | const b => const b
  | not c => not (weaken c)
  | and c₁ c₂ => and (weaken c₁) (weaken c₂)
  | or c₁ c₂ => or (weaken c₁) (weaken c₂)

/-- Drop the first input bit. -/
def tail {n : Nat} (x : Core.BitVec (n + 1)) : Core.BitVec n :=
  fun i => x i.succ

@[simp] lemma eval_weaken {n : Nat} (c : Circuit n) (x : Core.BitVec (n + 1)) :
    Circuit.eval (weaken c) x = Circuit.eval c (tail x) := by
  induction c with
  | input i =>
      simp [weaken, tail, Circuit.eval]
  | const b =>
      simp [weaken, Circuit.eval]
  | not c ih =>
      simp [weaken, Circuit.eval, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [weaken, Circuit.eval, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [weaken, Circuit.eval, ih₁, ih₂]

/-- Canonical decomposition of a bit-vector into head and tail. -/
lemma cons_head_tail {n : Nat} (x : Core.BitVec (n + 1)) :
    Fin.cons (x ⟨0, Nat.succ_pos n⟩) (tail x) = x := by
  funext i
  refine Fin.cases ?h0 ?hs i
  · rfl
  · intro j
    rfl

/--
  Constructive synthesis of a Boolean function into a circuit.

  This is a Shannon-style expansion on the first input variable.
-/
def ofFunction : (n : Nat) → (Core.BitVec n → Bool) → Circuit n
  | 0, f => Circuit.const (f (fun i => False.elim ((Nat.not_lt_zero i.1) i.2)))
  | n + 1, f =>
      let f0 : Core.BitVec n → Bool := fun t => f (Fin.cons false t)
      let f1 : Core.BitVec n → Bool := fun t => f (Fin.cons true t)
      let c0 := ofFunction n f0
      let c1 := ofFunction n f1
      let x0 : Circuit (n + 1) := Circuit.input ⟨0, Nat.succ_pos n⟩
      Circuit.or
        (Circuit.and x0 (weaken c1))
        (Circuit.and (Circuit.not x0) (weaken c0))

theorem eval_ofFunction :
    ∀ {n : Nat} (f : Core.BitVec n → Bool) (x : Core.BitVec n),
      Circuit.eval (ofFunction n f) x = f x
  | 0, f, x => by
      have hx : x = (fun i => False.elim ((Nat.not_lt_zero i.1) i.2)) := by
        funext i
        exact False.elim ((Nat.not_lt_zero i.1) i.2)
      subst hx
      rfl
  | n + 1, f, x => by
      let i0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
      let t : Core.BitVec n := tail x
      let f0 : Core.BitVec n → Bool := fun u => f (Fin.cons false u)
      let f1 : Core.BitVec n → Bool := fun u => f (Fin.cons true u)
      have h1 : Circuit.eval (ofFunction n f1) t = f1 t := eval_ofFunction f1 t
      have h0 : Circuit.eval (ofFunction n f0) t = f0 t := eval_ofFunction f0 t
      have hx :
          x = Fin.cons (x i0) t := by
        simpa [i0, t] using (cons_head_tail x).symm
      cases hbit : x i0 with
      | false =>
          have hx' : x = Fin.cons false t := by simpa [hbit] using hx
          calc
            Circuit.eval (ofFunction (n + 1) f) x
                = ((x i0 && Circuit.eval (weaken (ofFunction n f1)) x) ||
                  (!x i0 && Circuit.eval (weaken (ofFunction n f0)) x)) := by
                    simp [ofFunction, f0, f1, i0, Circuit.eval]
            _ = Circuit.eval (weaken (ofFunction n f0)) x := by simp [hbit]
            _ = Circuit.eval (ofFunction n f0) t := by
                  simpa [t] using (eval_weaken (ofFunction n f0) x)
            _ = f0 t := h0
            _ = f (Fin.cons false t) := rfl
            _ = f x := by simpa [hx']
      | true =>
          have hx' : x = Fin.cons true t := by simpa [hbit] using hx
          calc
            Circuit.eval (ofFunction (n + 1) f) x
                = ((x i0 && Circuit.eval (weaken (ofFunction n f1)) x) ||
                  (!x i0 && Circuit.eval (weaken (ofFunction n f0)) x)) := by
                    simp [ofFunction, f0, f1, i0, Circuit.eval]
            _ = Circuit.eval (weaken (ofFunction n f1)) x := by simp [hbit]
            _ = Circuit.eval (ofFunction n f1) t := by
                  simpa [t] using (eval_weaken (ofFunction n f1) x)
            _ = f1 t := h1
            _ = f (Fin.cons true t) := rfl
            _ = f x := by simpa [hx']

end Circuit

/-!
  ### Вспомогательная кодировка BitVec → Nat

  Используем стандартную интерпретацию битовой строки: младший бит имеет
  индекс 0. Это совпадает с тем, что делалось в legacy‑модели.
-/

/-- Интерпретация битовой строки как числа (младший бит имеет индекс 0). -/
def bitVecToNat {n : Nat} (x : Core.BitVec n) : Nat :=
  (List.finRange n).foldl
    (fun acc i => acc + (if x i then Nat.pow 2 (i : Nat) else 0))
    0

/--
  Параметры Partial MCSP. Структурно повторяют параметры total‑MCSP,
  но семантика относится к частичным функциям.
-/
structure GapPartialMCSPParams where
  n : Nat
  sYES : Nat
  sNO : Nat
  gap_ok : sYES + 1 ≤ sNO
  /-- В оценках сохраняем предположение о «достаточно большом» `n`. -/
  n_large : 8 ≤ n
  deriving Repr

/--
  Асимптотический профиль параметров Partial-MCSP.

  В отличие от `GapPartialMCSPParams` (фиксированная длина), профиль задаёт
  пороги как функции от числа переменных `m`. Это позволяет определить один
  язык на **всех** длинах вида `2 * 2^m`.
-/
structure GapPartialMCSPProfile where
  sYES : Nat → Nat
  sNO : Nat → Nat
  gap_ok : ∀ m, sYES m + 1 ≤ sNO m

/-- Специализация профиля в обычные параметры на фиксированном `m ≥ 8`. -/
@[simp] def GapPartialMCSPProfile.paramsAt
    (prof : GapPartialMCSPProfile) (m : Nat) (hm : 8 ≤ m) : GapPartialMCSPParams where
  n := m
  sYES := prof.sYES m
  sNO := prof.sNO m
  gap_ok := prof.gap_ok m
  n_large := hm

/-- Длина входа partial-MCSP: `2 * 2^n`. -/
def partialInputLen (p : GapPartialMCSPParams) : Nat := Partial.inputLen p.n

/--
  Polylog‑бюджет для тестовых множеств.

  Согласован с описанием в `pnp3/Docs/Parameters.md`:
  `polylogBudget N = (log₂(N+1)+1)^4`.
  Формулировка нужна для локальных схем и magnification‑моста.
-/
def polylogBudget (N : Nat) : Nat :=
  Nat.pow (Nat.log2 (N + 1) + 1) 4

/--
  Индекс для доступа к таблице истинности по `n`-битному входу.
  Это точная копия логики `truthTableFunction` из total MCSP,
  но возвращает индекс в `Fin (2^n)`.
-/
def assignmentIndex {n : Nat} (x : Core.BitVec n) : Fin (Partial.tableLen n) := by
  have hpos : 0 < Partial.tableLen n := by
    have hbase : 0 < (2 : Nat) := by decide
    -- Раскрываем `tableLen` прямо, чтобы избежать лишних симп-этапов.
    dsimp [Partial.tableLen]
    exact Nat.pow_pos hbase
  let _ : NeZero (Partial.tableLen n) := ⟨Nat.ne_of_gt hpos⟩
  exact Fin.ofNat (n := Partial.tableLen n) (bitVecToNat x)

/--
  Преобразуем таблицу истинности в функцию на `n` битах.
  Используем `Fin.ofNat`, что безопасно, поскольку индекс всегда меньше `2^n`.
-/
def truthTableFunction {n : Nat} (table : Core.BitVec (Partial.tableLen n)) :
    Core.BitVec n → Bool := fun x =>
  by
    have hpos : 0 < Partial.tableLen n := by
      have hbase : 0 < (2 : Nat) := by decide
      -- Аналогично для определения тотальной функции из таблицы.
      dsimp [Partial.tableLen]
      exact Nat.pow_pos hbase
    let _ : NeZero (Partial.tableLen n) := ⟨Nat.ne_of_gt hpos⟩
    exact table (Fin.ofNat (n := Partial.tableLen n) (bitVecToNat x))

/-- Схема `c` вычисляет функцию, заданную таблицей `table`. -/
def circuitComputes {n : Nat} (c : Circuit n) (table : Core.BitVec (Partial.tableLen n)) :
    Prop :=
  ∀ x : Core.BitVec n, Circuit.eval c x = truthTableFunction table x

/--
  Согласованность схемы с частичной таблицей: на определённых входах схема
  обязана выдавать тот же бит, на неопределённых — ограничений нет.
-/
def is_consistent {n : Nat} (C : Circuit n) (T : PartialTruthTable n) : Prop :=
  ∀ x : Core.BitVec n,
    match T (assignmentIndex x) with
    | some b => C.eval x = b
    | none => True

/-!
  ### Связь с тотальными таблицами

  Для последующей интеграции в магнификационный конвейер удобно иметь
  *явную* связку между полными таблицами истинности (`BitVec (2^n)`) и
  частичными таблицами (`PartialTruthTable n`).

  Здесь мы фиксируем канонический «встраивающий» перевод:

  * тотальная таблица `table` превращается в partial‑таблицу,
    где *все* значения определены;
  * соответствующий вход partial‑MCSP получается через `encodePartial`,
    т.е. кодировку `mask ++ values` с маской из одних `true`.
-/

/-- Полная таблица истинности как частичная функция (все значения определены). -/
def totalTableToPartial {n : Nat} (table : Core.BitVec (Partial.tableLen n)) :
    PartialTruthTable n :=
  fun i => some (table i)

/-- Кодирование полной таблицы в формат partial‑MCSP (`mask ++ values`). -/
def encodeTotalAsPartial {n : Nat} (table : Core.BitVec (Partial.tableLen n)) :
    Core.BitVec (Partial.inputLen n) :=
  encodePartial (totalTableToPartial (n := n) table)

/-- На тотальных таблицах `is_consistent` эквивалентен `circuitComputes`. -/
lemma is_consistent_total_iff {n : Nat} (C : Circuit n)
    (table : Core.BitVec (Partial.tableLen n)) :
    is_consistent C (totalTableToPartial (n := n) table) ↔
      circuitComputes C table := by
  constructor
  · intro h x
    -- `totalTableToPartial` всегда возвращает `some`, поэтому `is_consistent`
    -- сводится к точному совпадению с `truthTableFunction`.
    have hCons := h x
    -- Разворачиваем обе стороны в явную форму индексации по `bitVecToNat`.
    simpa [is_consistent, totalTableToPartial, circuitComputes,
      truthTableFunction, assignmentIndex] using hCons
  · intro h x
    -- Обратное направление: `circuitComputes` даёт точное совпадение на всех входах.
    have hComp := h x
    simpa [is_consistent, totalTableToPartial, circuitComputes,
      truthTableFunction, assignmentIndex] using hComp

/-- Декодирование полного входа после `encodeTotalAsPartial`. -/
lemma decodePartial_encodeTotal {n : Nat}
    (table : Core.BitVec (Partial.tableLen n)) :
    decodePartial (encodeTotalAsPartial (n := n) table) =
      totalTableToPartial (n := n) table := by
  simpa [encodeTotalAsPartial] using
    (decodePartial_encodePartial (totalTableToPartial (n := n) table))

/-- YES-условие Partial MCSP: существует схема размера ≤ `sYES`, согласованная с T. -/
def PartialMCSP_YES (p : GapPartialMCSPParams) (T : PartialTruthTable p.n) : Prop :=
  ∃ (C : Circuit p.n), C.size ≤ p.sYES ∧ is_consistent C T

/-- NO-условие Partial MCSP: любая согласованная схема имеет размер ≥ `sNO`. -/
def PartialMCSP_NO (p : GapPartialMCSPParams) (T : PartialTruthTable p.n) : Prop :=
  ∀ (C : Circuit p.n), is_consistent C T → p.sNO ≤ C.size

/-!
  ### Рестрикции на уровне входа

  Для устранения «encoding wall» мы хотим формально показать, что применение
  табличной рестрикции к входу остаётся внутри модели: результат снова
  декодируется в `PartialTruthTable p.n`.
-/

/-- Применить рестрикцию к кодированному входу partial‑MCSP. -/
def restrictInput {p : GapPartialMCSPParams}
    (x : Core.BitVec (partialInputLen p))
    (ρ : Restriction (partialInputLen p)) : Core.BitVec (partialInputLen p) :=
  applyRestrictionToInput x ρ

/-- Таблица, полученная после рестрикции входа. -/
def restrictTable {p : GapPartialMCSPParams}
    (x : Core.BitVec (partialInputLen p))
    (ρ : Restriction (partialInputLen p)) : PartialTruthTable p.n :=
  decodePartial (restrictInput (p := p) x ρ)

/-- Рестрикция на уровне входа эквивалентна рестрикции таблицы. -/
lemma restrictTable_eq_applyRestriction {p : GapPartialMCSPParams}
    (x : Core.BitVec (partialInputLen p))
    (ρ : Restriction (partialInputLen p)) :
    restrictTable (p := p) x ρ =
      applyRestrictionToTable (decodePartial x) ρ := by
  simpa [restrictTable, restrictInput] using
    (decodePartial_applyRestrictionToInput (x := x) (ρ := ρ))

/--
Типовая замкнутость: после рестрикции входа мы всё ещё получаем корректную
`PartialTruthTable p.n`. Это центральное свойство для «seamless restriction».
-/
theorem restriction_preserves_type_partial {p : GapPartialMCSPParams}
    (x : Core.BitVec (partialInputLen p))
    (ρ : Restriction (partialInputLen p)) :
    ∃ (T' : PartialTruthTable p.n),
      T' = applyRestrictionToTable (decodePartial x) ρ := by
  exact ⟨restrictTable (p := p) x ρ, by
    simp [restrictTable_eq_applyRestriction]⟩

/-!
  ### Базовые леммы про согласованность

  Эти результаты нужны для переноса рестрикций и операций над частичными
  таблицами в дальнейших доказательствах (anti-checker, magnification).
-/

/-- Забывание значений сохраняет согласованность (требований становится меньше). -/
lemma is_consistent_forget {n : Nat} (C : Circuit n) (T : PartialTruthTable n)
    (S : Finset (Fin (Partial.tableLen n))) :
    is_consistent C T → is_consistent C (forget T S) := by
  intro h x
  by_cases hmem : assignmentIndex x ∈ S
  · simp [forget, hmem]
  · simpa [is_consistent, forget, hmem] using h x

/-- Согласованность с двумя таблицами даёт согласованность с их объединением. -/
lemma is_consistent_mergeLeft {n : Nat} (C : Circuit n)
    (T₁ T₂ : PartialTruthTable n) :
    is_consistent C T₁ → is_consistent C T₂ → is_consistent C (mergeLeft T₁ T₂) := by
  intro h₁ h₂ x
  cases hT₁ : T₁ (assignmentIndex x) with
  | none =>
      -- Здесь используется значение из T₂.
      simpa [is_consistent, mergeLeft, hT₁] using h₂ x
  | some b =>
      -- Здесь используется значение из T₁.
      simpa [is_consistent, mergeLeft, hT₁] using h₁ x

/-!
  ### Promise-формализация Partial MCSP

  Мы используем тот же стиль, что и в total‑MCSP моделях: фиксируем тип
  входов, затем определяем promise-задачу через язык.
-/

/-- Тип входа для partial-MCSP: битовая строка длины `2 * 2^n`. -/
abbrev PartialMCSPInput (p : GapPartialMCSPParams) :=
  Core.BitVec (partialInputLen p)

/--
  Язык gapPartialMCSP: проверяем, есть ли малая согласованная схема.
  Вход обязательно имеет длину `2 * 2^n` и декодируется через `decodePartial`.
-/
noncomputable def gapPartialMCSP_Language (p : GapPartialMCSPParams) : Language := by
  classical
  intro n x
  refine dite (n = partialInputLen p) ?yes ?no
  · intro h
    have encoded : Core.BitVec (partialInputLen p) := by
      simpa [h] using x
    let T : PartialTruthTable p.n := decodePartial encoded
    by_cases hYes : PartialMCSP_YES p T
    · exact true
    · exact false
  · intro _
    exact false

/--
  Длина `N` поддерживается асимптотическим языком Partial-MCSP,
  если `N = 2 * 2^m` для некоторого `m`.

  Мы используем чисто логическое (`Prop`) описание формы длины; это удобно
  в текущем слое, где язык и так определён как `noncomputable`.
-/
def isPartialInputLength (N : Nat) : Prop :=
  ∃ m : Nat, N = Partial.inputLen m

/--
  Асимптотическая версия языка gapPartialMCSP.

  Поведение:
  * если длина входа не имеет вида `2 * 2^m`, возвращаем `false`;
  * если имеет, выбираем соответствующие параметры профиля на этом `m`
    и проверяем YES-условие на декодированной частичной таблице.

  Это устраняет «фиксированную длину» из финального слоя: язык становится
  бесконечным (редким по длинам, но корректно асимптотическим).
-/
noncomputable def gapPartialMCSP_Language_profile
    (prof : GapPartialMCSPProfile) : Language := by
  classical
  intro N x
  by_cases hLen : isPartialInputLength N
  · let m : Nat := Classical.choose hLen
    have hlenEq : N = Partial.inputLen m := Classical.choose_spec hLen
    -- Для малых `m` язык по определению возвращает `false` (асимптотическая зона).
    by_cases hmLarge : 8 ≤ m
    · let p : GapPartialMCSPParams := prof.paramsAt m hmLarge
      have hcast : N = partialInputLen p := by
        simpa [partialInputLen, p, GapPartialMCSPProfile.paramsAt] using hlenEq
      let encoded : Core.BitVec (partialInputLen p) := by
        simpa [hcast] using x
      let T : PartialTruthTable p.n := decodePartial encoded
      by_cases hYes : PartialMCSP_YES p T
      · exact true
      · exact false
    · exact false
  · exact false

/-!
  ### Связь языка и promise-условий

  Эти леммы позволяют заменять проверки `SolvesPromise` на точечное
  равенство с языком, что удобно в анти-чекере и магнификации.
-/

/-- Promise-задача Partial MCSP, определяемая через язык. -/
def GapPartialMCSPPromise (p : GapPartialMCSPParams) :
    PromiseProblem (PartialMCSPInput p) :=
  { Yes := fun x => gapPartialMCSP_Language p (partialInputLen p) x = true
    No := fun x => gapPartialMCSP_Language p (partialInputLen p) x = false
    disjoint := by
      classical
      refine Set.disjoint_left.mpr ?_
      intro x hYes hNo
      have : true = false := Eq.trans (Eq.symm hYes) hNo
      cases this }

/--
  Если PartialMCSP_NO выполнено, то малая согласованная схема невозможна.
  Эта лемма аналогична `onlyLargeCircuits_not_small` из total MCSP.
-/
lemma partial_no_not_yes
    (p : GapPartialMCSPParams) (T : PartialTruthTable p.n) :
    PartialMCSP_NO p T → ¬ PartialMCSP_YES p T := by
  intro hNo hYes
  rcases hYes with ⟨C, hSize, hCons⟩
  have hLower : p.sNO ≤ p.sYES := (hNo C hCons).trans hSize
  have hGap : p.sYES + 1 ≤ p.sYES := (le_trans p.gap_ok hLower)
  exact (Nat.not_succ_le_self _) hGap

/--
  На корректной длине входа язык равен `true` тогда и только тогда, когда
  существует малая согласованная схема.
-/
lemma gapPartialMCSP_language_true_iff_yes
    (p : GapPartialMCSPParams) (x : Core.BitVec (partialInputLen p)) :
    gapPartialMCSP_Language p (partialInputLen p) x = true ↔
      PartialMCSP_YES p (decodePartial x) := by
  classical
  simp [gapPartialMCSP_Language]

/-- Если выполнено NO-условие, язык возвращает `false`. -/
lemma gapPartialMCSP_language_false_of_no
    (p : GapPartialMCSPParams) (x : Core.BitVec (partialInputLen p)) :
    PartialMCSP_NO p (decodePartial x) →
      gapPartialMCSP_Language p (partialInputLen p) x = false := by
  intro hNo
  have hNoYes : ¬ PartialMCSP_YES p (decodePartial x) :=
    partial_no_not_yes p (decodePartial x) hNo
  by_cases hYes : PartialMCSP_YES p (decodePartial x)
  · exact (hNoYes hYes).elim
  · have hNotTrue : gapPartialMCSP_Language p (partialInputLen p) x ≠ true :=
      (gapPartialMCSP_language_true_iff_yes p x).not.mpr hYes
    cases hVal : gapPartialMCSP_Language p (partialInputLen p) x
    · rfl
    · exfalso
      exact hNotTrue hVal

/-- YES-условие переводит вход в YES-область promise-задачи. -/
lemma gapPartialMCSP_yes_of_small
    (p : GapPartialMCSPParams) (x : PartialMCSPInput p) :
    PartialMCSP_YES p (decodePartial x) → x ∈ (GapPartialMCSPPromise p).Yes := by
  intro hYes
  have hLang : gapPartialMCSP_Language p (partialInputLen p) x = true :=
    (gapPartialMCSP_language_true_iff_yes p x).2 hYes
  simpa [GapPartialMCSPPromise] using hLang

/-- NO-условие переводит вход в NO-область promise-задачи. -/
lemma gapPartialMCSP_no_of_large
    (p : GapPartialMCSPParams) (x : PartialMCSPInput p) :
    PartialMCSP_NO p (decodePartial x) → x ∈ (GapPartialMCSPPromise p).No := by
  intro hNo
  have hLang : gapPartialMCSP_Language p (partialInputLen p) x = false :=
    gapPartialMCSP_language_false_of_no p x hNo
  simpa [GapPartialMCSPPromise] using hLang

/-- `SolvesPromise` эквивалентно точечному равенству с языком. -/
theorem solvesPromise_gapPartialMCSP_iff
    {p : GapPartialMCSPParams} {decide : PartialMCSPInput p → Bool} :
    SolvesPromise (GapPartialMCSPPromise p) decide ↔
      ∀ x, decide x = gapPartialMCSP_Language p (partialInputLen p) x := by
  constructor
  · intro h x
    cases hlang : gapPartialMCSP_Language p (partialInputLen p) x
    · have hNo : x ∈ (GapPartialMCSPPromise p).No := by
        simpa [GapPartialMCSPPromise] using hlang
      simpa [hlang] using h.2 x hNo
    · have hYes : x ∈ (GapPartialMCSPPromise p).Yes := by
        simpa [GapPartialMCSPPromise] using hlang
      simpa [hlang] using h.1 x hYes
  · intro h
    constructor
    · intro x hx
      have hx' : gapPartialMCSP_Language p (partialInputLen p) x = true := by
        simpa [GapPartialMCSPPromise] using hx
      have hdec := h x
      simpa [hx'] using hdec
    · intro x hx
      have hx' : gapPartialMCSP_Language p (partialInputLen p) x = false := by
        simpa [GapPartialMCSPPromise] using hx
      have hdec := h x
      simpa [hx'] using hdec

/-!
  ### NP-membership for Partial MCSP
-/

noncomputable def gapPartialMCSP_verify (p : GapPartialMCSPParams) :
    ∀ n, Bitstring n → Bitstring (certificateLength n 2) → Bool := by
  classical
  intro n x _w
  by_cases h : n = partialInputLen p
  · subst h
    exact decide (PartialMCSP_YES p (decodePartial x))
  · exact false

lemma gapPartialMCSP_verify_eq_language
    (p : GapPartialMCSPParams) {n : Nat} (x : Bitstring n)
    (w : Bitstring (certificateLength n 2)) :
    gapPartialMCSP_verify p n x w = gapPartialMCSP_Language p n x := by
  classical
  by_cases h : n = partialInputLen p
  · subst h
    by_cases hYes : PartialMCSP_YES p (decodePartial x)
    · simp [gapPartialMCSP_verify, gapPartialMCSP_Language, hYes]
    · simp [gapPartialMCSP_verify, gapPartialMCSP_Language, hYes]
  · simp [gapPartialMCSP_verify, gapPartialMCSP_Language, h]

/-!
  ### Strict NP-membership scaffold (machine-first)

  Этот блок готовит явный TM-свидетель для `NP_strict`.  Мы оставляем текущую
  `NP`-теорему выше для обратной совместимости и постепенно усиливаем её до
  machine-first варианта.
-/

namespace StrictNP

open Facts.PsubsetPpoly

/-- Фиксированная длина «настоящего» входа языка `gapPartialMCSP_Language p`. -/
@[simp] def targetLen (p : GapPartialMCSPParams) : Nat := partialInputLen p

/-- В strict-NP используем `k = 0`, поэтому длина сертификата равна `1`. -/
@[simp] def certLen (_n : Nat) : Nat := certificateLength _n 0

@[simp] lemma certLen_eq_one (n : Nat) : certLen n = 1 := by
  simp [certLen, certificateLength]

/--
Состояние машины strict-верификатора:
* `scan i buf` — считаны первые `i` бит входа `x` (где `x` имеет длину `targetLen`);
* `accept` / `reject` — финальные поглощающие состояния.
-/
inductive State (p : GapPartialMCSPParams) where
  | scan : Fin (targetLen p + 1) → ComplexityInterfaces.Bitstring (targetLen p) → State p
  | accept : State p
  | reject : State p
  deriving DecidableEq, Fintype

/-- Нулевой буфер (все биты `false`) для фазы сканирования входа. -/
def zeroBuffer (p : GapPartialMCSPParams) : ComplexityInterfaces.Bitstring (targetLen p) :=
  fun _ => false

/-- Точечное обновление буфера на позиции `i`. -/
def writeBit {n : Nat} (buf : ComplexityInterfaces.Bitstring n)
    (i : Fin n) (b : Bool) : ComplexityInterfaces.Bitstring n :=
  fun j => if j = i then b else buf j

@[simp] lemma writeBit_self {n : Nat} (buf : ComplexityInterfaces.Bitstring n)
    (i : Fin n) (b : Bool) :
    writeBit buf i b i = b := by
  simp [writeBit]

@[simp] lemma writeBit_other {n : Nat} (buf : ComplexityInterfaces.Bitstring n)
    (i j : Fin n) (b : Bool)
    (h : j ≠ i) : writeBit buf i b j = buf j := by
  simp [writeBit, h]

/-- Переход `i ↦ i+1` внутри диапазона `Fin (targetLen p + 1)`. -/
def nextIndex {p : GapPartialMCSPParams}
    (i : Fin (targetLen p + 1)) (h : (i : Nat) < targetLen p) :
    Fin (targetLen p + 1) := by
  refine ⟨(i : Nat) + 1, ?_⟩
  exact Nat.succ_lt_succ h

/-- Шаговый переход strict-машины. -/
noncomputable def step (p : GapPartialMCSPParams) :
    State p → Bool → State p × Bool × Facts.PsubsetPpoly.Move := by
  classical
  intro s b
  cases s with
  | accept =>
      exact (State.accept, b, Facts.PsubsetPpoly.Move.stay)
  | reject =>
      exact (State.reject, b, Facts.PsubsetPpoly.Move.stay)
  | scan i buf =>
      by_cases h : (i : Nat) < targetLen p
      · let j : Fin (targetLen p) := ⟨(i : Nat), h⟩
        let buf' := writeBit buf j b
        exact (State.scan (nextIndex i h) buf', b, Facts.PsubsetPpoly.Move.right)
      · by_cases hYes : PartialMCSP_YES p (decodePartial buf)
        · exact (State.accept, b, Facts.PsubsetPpoly.Move.stay)
        · exact (State.reject, b, Facts.PsubsetPpoly.Move.stay)

/--
  Время работы strict-машины:
  * ровно `targetLen p + certLen (targetLen p)` шагов на целевой длине;
  * `0` шагов на остальных длинах.
-/
@[simp] def runTime (p : GapPartialMCSPParams) (m : Nat) : Nat :=
  if _h : m = targetLen p + certLen (targetLen p) then targetLen p + certLen (targetLen p) else 0

/-- Явная TM-машина для strict-верификации fixed-length слоя Partial MCSP. -/
noncomputable def tm (p : GapPartialMCSPParams) : Facts.PsubsetPpoly.TM where
  state := State p
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := State.scan ⟨0, Nat.succ_pos _⟩ (zeroBuffer p)
  accept := State.accept
  step := step p
  runTime := runTime p

@[simp] lemma runTime_target (p : GapPartialMCSPParams) :
    runTime p (targetLen p + certLen (targetLen p)) = targetLen p + certLen (targetLen p) := by
  simp [runTime]

@[simp] lemma runTime_nontarget (p : GapPartialMCSPParams) {m : Nat}
    (h : m ≠ targetLen p + certLen (targetLen p)) :
    runTime p m = 0 := by
  unfold runTime
  split_ifs with hEq
  · exact (h hEq).elim
  · rfl

/-- Грубая полиномиальная оценка времени strict-машины. -/
lemma runTime_poly_bound (p : GapPartialMCSPParams) :
    ∀ n, (tm p).runTime n ≤ n ^ (targetLen p + 1) + (targetLen p + 1) := by
  intro n
  by_cases hTarget : n = targetLen p + certLen (targetLen p)
  · subst hTarget
    have hle_add :
        targetLen p + certLen (targetLen p) ≤
          (targetLen p + certLen (targetLen p)) ^ (targetLen p + 1) + (targetLen p + 1) := by
      have hle_rhs : targetLen p + certLen (targetLen p) ≤ targetLen p + 1 := by
        simp [certLen, certificateLength]
      exact le_trans hle_rhs (Nat.le_add_left _ _)
    simpa [tm, runTime_target] using hle_add
  · have hrt : (tm p).runTime n = 0 := by
      simpa [tm] using runTime_nontarget (p := p) hTarget
    rw [hrt]
    exact Nat.zero_le _

/--
  На нецелевых длинах strict-машина делает `0` шагов и остаётся в стартовом
  состоянии, поэтому `accepts = false`.
-/
lemma accepts_nontarget_false (p : GapPartialMCSPParams) {m : Nat}
    (h : m ≠ targetLen p + certLen (targetLen p))
    (y : ComplexityInterfaces.Bitstring m) :
    Facts.PsubsetPpoly.TM.accepts (M := tm p) (n := m) y = false := by
  classical
  have hrtm :
      (if m = targetLen p + certLen (targetLen p)
        then targetLen p + certLen (targetLen p) else 0) = 0 := by
    exact if_neg h
  have hrt : (tm p).runTime m = 0 := by
    simpa [tm, runTime] using hrtm
  unfold Facts.PsubsetPpoly.TM.accepts Facts.PsubsetPpoly.TM.run
  rw [hrt]
  simp [Facts.PsubsetPpoly.TM.runConfig, tm]

/-- Индекс `i : Fin (targetLen p)` как индекс в строке длины `targetLen p + certLen ...`. -/
def liftInputIdx (p : GapPartialMCSPParams) (i : Fin (targetLen p)) :
    Fin (targetLen p + certLen (targetLen p)) := by
  refine ⟨(i : Nat), ?_⟩
  have hi : (i : Nat) < targetLen p + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self _)
  simpa [certLen, certificateLength] using hi

/-- Последний (сертификатный) индекс в строке длины `targetLen p + certLen ...`. -/
def certIdx (p : GapPartialMCSPParams) : Fin (targetLen p + certLen (targetLen p)) := by
  refine ⟨targetLen p, ?_⟩
  simp [certLen, certificateLength]

/-- Префикс длины `targetLen p` из объединённой строки `x ++ w`. -/
def inputPrefix (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p))) :
    ComplexityInterfaces.Bitstring (targetLen p) :=
  fun i => y (liftInputIdx p i)

lemma inputPrefix_concat (p : GapPartialMCSPParams)
    (x : ComplexityInterfaces.Bitstring (targetLen p))
    (w : ComplexityInterfaces.Bitstring (certLen (targetLen p))) :
    inputPrefix p (concatBitstring x w) = x := by
  funext i
  simp [inputPrefix, liftInputIdx, concatBitstring]

/-- Буфер после чтения первых `k` входных битов: прочитанные позиции фиксируются, остальные `false`. -/
def prefixBuffer (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p)))
    (k : Nat) : ComplexityInterfaces.Bitstring (targetLen p) :=
  fun j => if (j : Nat) < k then inputPrefix p y j else false

@[simp] lemma prefixBuffer_zero (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p))) :
    prefixBuffer p y 0 = zeroBuffer p := by
  funext j
  simp [prefixBuffer, zeroBuffer]

lemma prefixBuffer_succ_of_lt (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p)))
    {k : Nat} (hk : k < targetLen p) :
    prefixBuffer p y (k + 1) =
      writeBit (prefixBuffer p y k) ⟨k, hk⟩ (inputPrefix p y ⟨k, hk⟩) := by
  funext j
  by_cases hEq : j = ⟨k, hk⟩
  · subst hEq
    simp [prefixBuffer, writeBit]
  · have hj_ne : (j : Nat) ≠ k := by
      intro hj_eq
      apply hEq
      exact Fin.ext hj_eq
    by_cases hlt : (j : Nat) < k
    · have hlt_succ : (j : Nat) < k + 1 := Nat.lt_succ_of_lt hlt
      simp [prefixBuffer, writeBit, hEq, hlt, hlt_succ]
    · have hge : k ≤ (j : Nat) := Nat.le_of_not_gt hlt
      have hnot_succ : ¬ (j : Nat) < k + 1 := by
        intro hjlt
        have hjle : (j : Nat) ≤ k := Nat.lt_succ_iff.mp hjlt
        exact hj_ne (Nat.le_antisymm hjle hge)
      simp [prefixBuffer, writeBit, hEq, hlt, hnot_succ]

@[simp] lemma targetTotalLen_eq (p : GapPartialMCSPParams) :
    targetLen p + certLen (targetLen p) = targetLen p + 1 := by
  simp [certLen, certificateLength]

lemma target_lt_tapeLength (p : GapPartialMCSPParams) :
    targetLen p + 1 < (tm p).tapeLength (targetLen p + certLen (targetLen p)) := by
  have hbase :
      targetLen p + 1 <
        targetLen p + certLen (targetLen p) +
          (tm p).runTime (targetLen p + certLen (targetLen p)) + 1 := by
    have hcert : 1 ≤ certLen (targetLen p) := by
      simp [certLen, certificateLength]
    have hle1 : targetLen p + 1 ≤ targetLen p + certLen (targetLen p) :=
      Nat.add_le_add_left hcert _
    have hle2 :
        targetLen p + certLen (targetLen p) ≤
          targetLen p + certLen (targetLen p) +
            (tm p).runTime (targetLen p + certLen (targetLen p)) :=
      Nat.le_add_right _ _
    exact Nat.lt_of_le_of_lt (le_trans hle1 hle2) (Nat.lt_succ_self _)
  simpa [Facts.PsubsetPpoly.TM.tapeLength, Nat.add_assoc] using hbase

def tapeIdx (p : GapPartialMCSPParams) (k : Nat) (hk : k ≤ targetLen p) :
    Fin ((tm p).tapeLength (targetLen p + certLen (targetLen p))) := by
  refine ⟨k, ?_⟩
  have hklt : k < targetLen p + certLen (targetLen p) := by
    have : k < targetLen p + 1 := Nat.lt_succ_of_le hk
    simpa [targetTotalLen_eq] using this
  exact Nat.lt_trans hklt (target_lt_tapeLength p)

lemma inputPrefix_eq_at (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p)))
    (k : Nat) (hk : k < targetLen p) :
    inputPrefix p y ⟨k, hk⟩ = y ⟨k, by simpa [targetTotalLen_eq] using Nat.lt_succ_of_lt hk⟩ := by
  simp [inputPrefix, liftInputIdx, certLen, certificateLength]

lemma prefixBuffer_target_eq_inputPrefix (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p))) :
    prefixBuffer p y (targetLen p) = inputPrefix p y := by
  funext j
  simp [prefixBuffer]

lemma runConfig_succ (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p)))
    (k : Nat) :
    Facts.PsubsetPpoly.TM.runConfig (M := tm p) ((tm p).initialConfig y) (k + 1) =
      Facts.PsubsetPpoly.TM.stepConfig (M := tm p)
        (Facts.PsubsetPpoly.TM.runConfig (M := tm p) ((tm p).initialConfig y) k) := by
  simpa [Facts.PsubsetPpoly.TM.runConfig] using
    (Function.iterate_succ_apply'
      (f := Facts.PsubsetPpoly.TM.stepConfig (M := tm p))
      k ((tm p).initialConfig y))

lemma initial_tape_at_inputIdx (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p)))
    (k : Nat) (hk : k < targetLen p + certLen (targetLen p)) :
    ((tm p).initialConfig y).tape
      ⟨k, Nat.lt_trans hk (target_lt_tapeLength p)⟩ = y ⟨k, hk⟩ := by
  simpa using
    (Facts.PsubsetPpoly.TM.initial_tape_input
      (M := tm p) (x := y)
      (i := ⟨k, Nat.lt_trans hk (target_lt_tapeLength p)⟩)
      (hi := hk))

lemma step_scan_lt (p : GapPartialMCSPParams)
    (i : Fin (targetLen p + 1))
    (buf : ComplexityInterfaces.Bitstring (targetLen p))
    (b : Bool)
    (h : (i : Nat) < targetLen p) :
    step p (State.scan i buf) b =
      (State.scan (nextIndex i h) (writeBit buf ⟨(i : Nat), h⟩ b), b, Facts.PsubsetPpoly.Move.right) := by
  cases i with
  | mk iv ih =>
      dsimp at h
      simp [step, h]

lemma stepConfig_scan_lt (p : GapPartialMCSPParams)
    (c : Facts.PsubsetPpoly.TM.Configuration (M := tm p) (targetLen p + certLen (targetLen p)))
    (i : Fin (targetLen p + 1))
    (buf : ComplexityInterfaces.Bitstring (targetLen p))
    (hstate : c.state = State.scan i buf)
    (h : (i : Nat) < targetLen p) :
    (Facts.PsubsetPpoly.TM.stepConfig (M := tm p) c).state =
      State.scan (nextIndex i h) (writeBit buf ⟨(i : Nat), h⟩ (c.tape c.head)) := by
  unfold Facts.PsubsetPpoly.TM.stepConfig
  rw [hstate]
  have hstep := step_scan_lt (p := p) (i := i) (buf := buf) (b := c.tape c.head) h
  simpa [tm] using congrArg Prod.fst hstep

lemma stepConfig_head_right (p : GapPartialMCSPParams)
    (c : Facts.PsubsetPpoly.TM.Configuration (M := tm p) (targetLen p + certLen (targetLen p)))
    (i : Nat)
    (hhead : (c.head : Nat) = i)
    (hmove : i + 1 < (tm p).tapeLength (targetLen p + certLen (targetLen p))) :
    (Facts.PsubsetPpoly.TM.Configuration.moveHead
      (M := tm p) (c := c) Facts.PsubsetPpoly.Move.right : Nat) = i + 1 := by
  have hmove' : i + 1 <
      (tm p).tapeLength (partialInputLen p + certificateLength (partialInputLen p) 0) := by
    simpa [targetLen, certLen] using hmove
  simp [Facts.PsubsetPpoly.TM.Configuration.moveHead, hmove', hhead]

lemma write_self_tape {p : GapPartialMCSPParams}
    (c : Facts.PsubsetPpoly.TM.Configuration (M := tm p) (targetLen p + certLen (targetLen p))) :
    Facts.PsubsetPpoly.TM.Configuration.write (M := tm p) c c.head (c.tape c.head) = c.tape := by
  funext j
  by_cases h : j = c.head
  · subst h
    simp [Facts.PsubsetPpoly.TM.Configuration.write]
  · simp [Facts.PsubsetPpoly.TM.Configuration.write, h]

lemma runConfig_scan_prefix (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p))) :
    ∀ k, k ≤ targetLen p →
      let c := Facts.PsubsetPpoly.TM.runConfig (M := tm p) ((tm p).initialConfig y) k
      (∃ hki : k < targetLen p + 1,
        c.state = State.scan ⟨k, hki⟩ (prefixBuffer p y k)) ∧
      (c.head : Nat) = k ∧
      c.tape = ((tm p).initialConfig y).tape := by
  intro k hk
  induction k with
  | zero =>
      dsimp [Facts.PsubsetPpoly.TM.runConfig]
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨Nat.succ_pos _, ?_⟩
        simp [tm, prefixBuffer_zero]
      · simp [tm, Facts.PsubsetPpoly.TM.tapeLength]
      · rfl
  | succ k ih =>
      have hkSucc : k + 1 ≤ targetLen p := hk
      have hk0 : k ≤ targetLen p := Nat.le_trans (Nat.le_succ k) hkSucc
      have hklt : k < targetLen p := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hkSucc
      let c0 : Facts.PsubsetPpoly.TM.Configuration (M := tm p)
          (targetLen p + certLen (targetLen p)) :=
        Facts.PsubsetPpoly.TM.runConfig (M := tm p) ((tm p).initialConfig y) k
      have hprev := ih hk0
      rcases hprev.1 with ⟨hki, hstate0⟩
      have hhead0 : (c0.head : Nat) = k := hprev.2.1
      have htape0 : c0.tape = ((tm p).initialConfig y).tape := hprev.2.2
      have hkN : k < targetLen p + certLen (targetLen p) := by
        simpa [targetTotalLen_eq] using Nat.lt_succ_of_lt hklt
      have hcfg :
          Facts.PsubsetPpoly.TM.runConfig (M := tm p) ((tm p).initialConfig y) (k + 1) =
            Facts.PsubsetPpoly.TM.stepConfig (M := tm p) c0 := by
        simpa [c0] using runConfig_succ (p := p) (y := y) k
      rw [hcfg]
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨Nat.lt_succ_of_le hkSucc, ?_⟩
        have hstate1 :
            (Facts.PsubsetPpoly.TM.stepConfig (M := tm p) c0).state =
              State.scan (nextIndex ⟨k, hki⟩ hklt)
                (writeBit (prefixBuffer p y k) ⟨k, hklt⟩ (c0.tape c0.head)) := by
          exact stepConfig_scan_lt (p := p) (c := c0) (i := ⟨k, hki⟩)
            (buf := prefixBuffer p y k) hstate0 hklt
        have hsym : c0.tape c0.head = inputPrefix p y ⟨k, hklt⟩ := by
          have hhead_eq :
              c0.head = ⟨k, Nat.lt_trans hkN (target_lt_tapeLength p)⟩ := by
            apply Fin.ext
            simpa using hhead0
          rw [htape0, hhead_eq]
          have hinit := initial_tape_at_inputIdx (p := p) (y := y) (k := k) hkN
          simpa [inputPrefix_eq_at (p := p) (y := y) (k := k) hklt] using hinit
        have hnext :
            nextIndex (p := p) ⟨k, hki⟩ hklt = ⟨k + 1, Nat.lt_succ_of_le hkSucc⟩ := by
          apply Fin.ext
          rfl
        rw [hstate1, hnext, hsym]
        simp [prefixBuffer_succ_of_lt (p := p) (y := y) hklt]
      · have hmove :
            k + 1 < (tm p).tapeLength (targetLen p + certLen (targetLen p)) := by
          have hle : k + 1 ≤ targetLen p + 1 := Nat.succ_le_succ (Nat.le_of_lt hklt)
          exact lt_of_le_of_lt hle (target_lt_tapeLength p)
        have hhead1 :
            ((Facts.PsubsetPpoly.TM.stepConfig (M := tm p) c0).head : Nat) = k + 1 := by
          have hstep :
              (tm p).step c0.state (c0.tape c0.head) =
                (State.scan (nextIndex ⟨k, hki⟩ hklt)
                    (writeBit (prefixBuffer p y k) ⟨k, hklt⟩ (c0.tape c0.head)),
                 c0.tape c0.head, Facts.PsubsetPpoly.Move.right) := by
            rw [hstate0]
            simpa [tm] using step_scan_lt (p := p) (i := ⟨k, hki⟩)
              (buf := prefixBuffer p y k) (b := c0.tape c0.head) hklt
          simp [Facts.PsubsetPpoly.TM.stepConfig, hstep]
          exact stepConfig_head_right (p := p) (c := c0) (i := k) hhead0 hmove
        exact hhead1
      · unfold Facts.PsubsetPpoly.TM.stepConfig
        have hstep :
            (tm p).step c0.state (c0.tape c0.head) =
              (State.scan (nextIndex ⟨k, hki⟩ hklt)
                  (writeBit (prefixBuffer p y k) ⟨k, hklt⟩ (c0.tape c0.head)),
               c0.tape c0.head, Facts.PsubsetPpoly.Move.right) := by
          rw [hstate0]
          simpa [tm] using step_scan_lt (p := p) (i := ⟨k, hki⟩)
            (buf := prefixBuffer p y k) (b := c0.tape c0.head) hklt
        simp [hstep]
        simpa [write_self_tape (c := c0)] using htape0

lemma accepts_target_iff_yes_inputPrefix (p : GapPartialMCSPParams)
    (y : ComplexityInterfaces.Bitstring (targetLen p + certLen (targetLen p))) :
    Facts.PsubsetPpoly.TM.accepts (M := tm p) (n := targetLen p + certLen (targetLen p)) y = true ↔
      PartialMCSP_YES p (decodePartial (inputPrefix p y)) := by
  classical
  let c0 : Facts.PsubsetPpoly.TM.Configuration (M := tm p) (targetLen p + certLen (targetLen p)) :=
    Facts.PsubsetPpoly.TM.runConfig (M := tm p) ((tm p).initialConfig y) (targetLen p)
  have hscan := runConfig_scan_prefix (p := p) (y := y) (k := targetLen p) (le_rfl)
  rcases hscan.1 with ⟨hki, hstate0⟩
  have hstate0' : c0.state = State.scan ⟨targetLen p, hki⟩ (prefixBuffer p y (targetLen p)) := hstate0
  have hrt :
      (tm p).runTime (targetLen p + certLen (targetLen p)) = targetLen p + certLen (targetLen p) := by
    exact runTime_target p
  have hstep :
      Facts.PsubsetPpoly.TM.runConfig (M := tm p) ((tm p).initialConfig y) (targetLen p + certLen (targetLen p)) =
        Facts.PsubsetPpoly.TM.stepConfig (M := tm p) c0 := by
    simpa [targetTotalLen_eq, c0] using runConfig_succ (p := p) (y := y) (targetLen p)
  have hstate_final :
      (Facts.PsubsetPpoly.TM.stepConfig (M := tm p) c0).state =
        if PartialMCSP_YES p (decodePartial (inputPrefix p y)) then State.accept else State.reject := by
    unfold Facts.PsubsetPpoly.TM.stepConfig
    rw [hstate0']
    have hbuf : prefixBuffer p y (targetLen p) = inputPrefix p y :=
      prefixBuffer_target_eq_inputPrefix (p := p) (y := y)
    have hbuf' : prefixBuffer p y (partialInputLen p) = inputPrefix p y := by
      simpa [targetLen] using hbuf
    rw [hbuf]
    by_cases hYes : PartialMCSP_YES p (decodePartial (inputPrefix p y))
    · simp [tm, step, hYes]
    · simp [tm, step, hYes]
  unfold Facts.PsubsetPpoly.TM.accepts Facts.PsubsetPpoly.TM.run
  rw [hrt, hstep, hstate_final]
  by_cases hYes : PartialMCSP_YES p (decodePartial (inputPrefix p y))
  · simp [tm, hYes]
  · simp [tm, hYes]

theorem gapPartialMCSP_in_NP_TM (p : GapPartialMCSPParams) :
    NP_TM (gapPartialMCSP_Language p) := by
  classical
  refine ⟨tm p, targetLen p + 1, 0, ?_, ?_⟩
  · intro n
    simpa [tm, certLen, certificateLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (runTime_poly_bound (p := p) (n := n + certificateLength n 0))
  · intro n x
    by_cases hn : n = targetLen p
    · subst hn
      constructor
      · intro hLang
        have hYes : PartialMCSP_YES p (decodePartial x) :=
          (gapPartialMCSP_language_true_iff_yes p x).1 hLang
        let w0 : ComplexityInterfaces.Bitstring (certLen (targetLen p)) := fun _ => false
        refine ⟨(fun _ => false), ?_⟩
        have hAccYes :
            Facts.PsubsetPpoly.TM.accepts (M := tm p)
              (n := targetLen p + certLen (targetLen p))
              (concatBitstring x w0) = true := by
          have hpref :
              inputPrefix p
                (concatBitstring x w0) = x := inputPrefix_concat (p := p) (x := x) (w := w0)
          have hYes' : PartialMCSP_YES p
              (decodePartial (inputPrefix p (concatBitstring x w0))) := by
            simpa [hpref] using hYes
          exact (accepts_target_iff_yes_inputPrefix (p := p)
            (y := concatBitstring x w0)).2 hYes'
        simpa [certLen, certificateLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAccYes
      · intro hExists
        rcases hExists with ⟨w, hAcc⟩
        have hYes' : PartialMCSP_YES p
            (decodePartial (inputPrefix p (concatBitstring x w))) :=
          (accepts_target_iff_yes_inputPrefix (p := p) (y := concatBitstring x w)).1 (by
            simpa [certLen, certificateLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAcc)
        have hYes : PartialMCSP_YES p (decodePartial x) := by
          simpa [inputPrefix_concat (p := p) (x := x) (w := w)] using hYes'
        exact (gapPartialMCSP_language_true_iff_yes p x).2 hYes
    · constructor
      · intro hLang
        exfalso
        have hneq : n ≠ partialInputLen p := by
          simpa [targetLen] using hn
        have hFalseLang : gapPartialMCSP_Language p n x = false := by
          simp [gapPartialMCSP_Language, hneq]
        have hContr : False := by
          simp [hFalseLang] at hLang
        exact False.elim hContr
      · intro hExists
        rcases hExists with ⟨w, hAcc⟩
        have hneqTotal :
            n + certificateLength n 0 ≠ targetLen p + certLen (targetLen p) := by
          intro hEq
          have : n = targetLen p := by
            have hs : n + 1 = targetLen p + 1 := by
              simpa [certLen, certificateLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEq
            exact Nat.succ.inj hs
          exact hn this
        have hFalse :
            Facts.PsubsetPpoly.TM.accepts (M := tm p)
              (n := n + certificateLength n 0)
              (concatBitstring x w) = false :=
          accepts_nontarget_false (p := p) (m := n + certificateLength n 0) hneqTotal (concatBitstring x w)
        exfalso
        have hContr : False := by
          simp [hFalse] at hAcc
        exact False.elim hContr


end StrictNP

theorem gapPartialMCSP_in_NP_strict (p : GapPartialMCSPParams) :
    NP_strict (gapPartialMCSP_Language p) :=
  StrictNP.gapPartialMCSP_in_NP_TM p

theorem gapPartialMCSP_in_NP (p : GapPartialMCSPParams) :
    NP (gapPartialMCSP_Language p) :=
  NP_of_NP_TM (StrictNP.gapPartialMCSP_in_NP_TM p)

end Models
end Pnp3
