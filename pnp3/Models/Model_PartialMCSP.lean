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
  deriving DecidableEq, Repr

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
  Upper bound on the cardinality of the Finset of tree-shaped circuits
  of size ≤ `s` over `n` input variables. The recurrence overapproximates
  by closing under NOT/AND/OR at every level.

  f(0) = 0
  f(s+1) ≤ 2·f(s)² + 2·f(s) + n + 2
-/
def circuitCountBound (n s : Nat) : Nat :=
  match s with
  | 0 => 0
  | s + 1 =>
    let prev := circuitCountBound n s
    2 * prev ^ 2 + 2 * prev + n + 2

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
  /-- Non-degenerate YES threshold: at least Circuit.const has size 1 ≤ sYES. -/
  sYES_pos : 1 ≤ sYES
  /-- Shannon counting: the circuit-count bound fits below 2^(tableLen/2). -/
  circuit_bound_ok : circuitCountBound n (sNO - 1) < 2 ^ (Partial.tableLen n / 2)
  deriving Repr

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

/-! ### Binary encoding round-trip -/

private lemma foldl_add_eq_init_add_sum {α : Type*} (f : α → Nat) :
    ∀ (init : Nat) (L : List α),
      L.foldl (fun acc a => acc + f a) init = init + (L.map f).sum
  | _, [] => by simp
  | init, a :: L => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_eq_init_add_sum f _ L]
    omega

private lemma bitVecToNat_eq_list_sum {n : Nat} (x : Core.BitVec n) :
    bitVecToNat x = ((List.finRange n).map
      (fun i : Fin n => if x i then 2 ^ (i : Nat) else 0)).sum := by
  unfold bitVecToNat
  rw [foldl_add_eq_init_add_sum]
  simp

/-- Sum with doubled exponents equals double the sum. -/
private lemma sum_map_pow_succ {n : Nat} (x : Core.BitVec (n + 1))
    (L : List (Fin n)) :
    (L.map (fun j => if x (Fin.succ j) then Nat.pow 2 (Fin.succ j).val else 0)).sum =
    2 * (L.map (fun j => if x (Fin.succ j) then Nat.pow 2 j.val else 0)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have key : Nat.pow 2 (Fin.succ a).val = 2 * Nat.pow 2 a.val := by
      show (2 : Nat) ^ (Fin.succ a).val = 2 * 2 ^ a.val
      rw [Fin.val_succ, pow_succ]; ring
    cases x (Fin.succ a)
    · simp
    · simp only [ite_true, key, Nat.mul_add]

/-- Helper: foldl with shifted function and factored constant. -/
private lemma foldl_shift_factor {n : Nat}
    (x : Core.BitVec (n + 1)) (init : Nat) :
    (List.finRange n).foldl
      (fun acc j => acc + (if x (Fin.succ j) then Nat.pow 2 (Fin.succ j).val else 0)) init =
    init + 2 * (List.finRange n).foldl
      (fun acc j => acc + (if x (Fin.succ j) then Nat.pow 2 j.val else 0)) 0 := by
  rw [foldl_add_eq_init_add_sum, foldl_add_eq_init_add_sum, Nat.zero_add]
  congr 1
  exact sum_map_pow_succ x _

/-- Recursive characterization of bitVecToNat. -/
private lemma bitVecToNat_succ {n : Nat} (x : Core.BitVec (n + 1)) :
    bitVecToNat x = (if x ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) +
      2 * bitVecToNat (fun i : Fin n => x (Fin.succ i)) := by
  unfold bitVecToNat
  rw [List.finRange_succ_eq_map, List.foldl_cons, List.foldl_map]
  rw [foldl_shift_factor]
  simp

/-- Round-trip: bitVecToNat ∘ vecOfNat = id for values below 2^n. -/
lemma bitVecToNat_vecOfNat {n m : Nat} (hm : m < 2 ^ n) :
    bitVecToNat (Core.vecOfNat n m) = m := by
  induction n generalizing m with
  | zero =>
    simp only [bitVecToNat_eq_list_sum, List.finRange_zero, List.map_nil, List.sum_nil, pow_zero]
      at hm ⊢
    omega
  | succ n ih =>
    rw [bitVecToNat_succ]
    -- Don't simp vecOfNat yet; first rewrite the shifted function
    have h_shift : (fun i : Fin n => Core.vecOfNat (n + 1) m (Fin.succ i)) =
        Core.vecOfNat n (m / 2) := by
      funext i; simp [Core.vecOfNat, Fin.val_succ, Nat.testBit_succ]
    rw [h_shift, ih (by omega)]
    -- Goal: (if vecOfNat (n+1) m ⟨0,_⟩ then 1 else 0) + 2 * (m / 2) = m
    -- vecOfNat (n+1) m ⟨0,_⟩ = testBit m 0 = (m % 2 != 0)
    show (if Core.vecOfNat (n + 1) m ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) + 2 * (m / 2) = m
    simp only [Core.vecOfNat, Nat.testBit_zero]
    -- Goal: (if decide (m % 2 = 1) then 1 else 0) + 2 * (m / 2) = m
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h] <;> omega

/-- bitVecToNat stays below 2^n. -/
lemma bitVecToNat_lt {n : Nat} (x : Core.BitVec n) :
    bitVecToNat x < Partial.tableLen n := by
  suffices h : bitVecToNat x < 2 ^ n by simpa [Partial.tableLen] using h
  induction n with
  | zero =>
    simp only [bitVecToNat_eq_list_sum, List.finRange_zero, List.map_nil, List.sum_nil, pow_zero]
    omega
  | succ n ih =>
    rw [bitVecToNat_succ]
    have h_inner := ih (fun i : Fin n => x (Fin.succ i))
    have h_head : (if x ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) ≤ 1 := by split <;> omega
    linarith [pow_succ 2 n]

/-- assignmentIndex is surjective. -/
theorem assignmentIndex_surjective {n : Nat} :
    Function.Surjective (@assignmentIndex n) := by
  intro j
  refine ⟨Core.vecOfNat n j.val, ?_⟩
  have hj : j.val < 2 ^ n := by simpa [Partial.tableLen] using j.isLt
  have h_eq := bitVecToNat_vecOfNat hj
  -- assignmentIndex uses Fin.ofNat which is val % tableLen
  -- Since bitVecToNat result = j.val < 2^n = tableLen, the mod is a no-op
  ext
  show (bitVecToNat (Core.vecOfNat n j.val)) % Partial.tableLen n = j.val
  rw [h_eq, Nat.mod_eq_of_lt]
  simpa [Partial.tableLen] using hj

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

theorem gapPartialMCSP_in_NP (p : GapPartialMCSPParams) :
    NP (gapPartialMCSP_Language p) := by
  classical
  refine ⟨2, 2, (fun t => t ^ 2 + 2), gapPartialMCSP_verify p, ?_, ?_⟩
  · intro n
    simp
  · intro n x
    constructor
    · intro hLang
      refine ⟨(fun _ => false), ?_⟩
      simpa [gapPartialMCSP_verify_eq_language (p := p) (x := x)] using hLang
    · intro hExists
      rcases hExists with ⟨w, hVerify⟩
      simpa [gapPartialMCSP_verify_eq_language (p := p) (x := x)] using hVerify

end Models
end Pnp3
