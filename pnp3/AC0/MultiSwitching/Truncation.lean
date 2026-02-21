import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Core.BooleanBasics
import AC0.MultiSwitching.Definitions

/-!
  pnp3/AC0/MultiSwitching/Truncation.lean

  Ширинный мост (truncation) для CNF/DNF.

  Идея: чтобы применять multi‑switching к формулам фиксированной ширины `w`,
  мы берём исходную формулу и **удаляем** клаузы/термы ширины `> w`.

  На этом этапе мы фиксируем **конструктивное ядро**:

  * определение `truncateWidth`, которое реально удаляет «широкие» элементы;
  * монотонность `eval` относительно truncation (CNF становится «слабее»,
    DNF становится «сильнее»).

  В следующем шаге к этим определениям будет привязан количественный
  бюджет ошибки `ε` (union bound), который зависит от выбранной ширины.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-!
## CNF truncation

Для CNF удаление «широких» клауз делает формулу **легче** выполнить,
поэтому истинность исходной CNF гарантирует истинность truncation.
-/

namespace CNF

/-- Удаляем все клаузы ширины `> w'`, получая CNF ширины `w'`. -/
def truncateWidth {n w : Nat} (F : Core.CNF n w) (w' : Nat) :
    Core.CNF n w' :=
  { clauses := F.clauses.filter (fun C => C.width ≤ w')
    width_le := by
      intro C hC
      have hmem :
          C ∈ F.clauses ∧ C.width ≤ w' := by
        simpa [List.mem_filter] using hC
      exact hmem.2 }

/-- Если исходная CNF истинна, то и её truncation истинна. -/
lemma eval_truncate_true_of_eval_true
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) (x : Core.BitVec n)
    (h : F.eval x = true) :
    (truncateWidth F w').eval x = true := by
  classical
  -- `eval` — это `all` по списку клауз.
  unfold Core.CNF.eval at h ⊢
  -- Каждый элемент `filter` лежит в исходном списке, а значит истинный.
  refine List.all_eq_true.mpr ?_
  intro C hC
  have hmem : C ∈ F.clauses := by
    exact (List.mem_filter.mp hC).1
  have hall := List.all_eq_true.mp h
  exact hall C hmem

/--
  Если truncation истинна, а исходная CNF ложна, то существует «широкая»
  клауза (width > w'), которая отвечает за ложность.

  Это ключевой структурный шаг для будущего union‑bound: различие
  между `F` и `truncateWidth F w'` возможно только из‑за удалённых клауз.
-/
lemma exists_wide_clause_of_truncate_true_eval_false
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) (x : Core.BitVec n)
    (htrunc : (truncateWidth F w').eval x = true)
    (hfalse : F.eval x = false) :
    ∃ C ∈ F.clauses, w' < C.width ∧ C.eval x = false := by
  classical
  -- Из ложности CNF получаем «плохую» клаузу.
  rcases (Core.CNF.eval_eq_false_iff (F := F) (x := x)).1 hfalse with
    ⟨C, hC, hCfalse⟩
  -- Если C была бы узкой, то truncation тоже была бы ложной.
  have hwide : w' < C.width := by
    by_contra hle
    have hle' : C.width ≤ w' := Nat.le_of_not_gt hle
    have hmem_trunc : C ∈ (truncateWidth F w').clauses := by
      exact List.mem_filter.mpr ⟨hC, hle'⟩
    have htrunc_false :
        (truncateWidth F w').eval x = false := by
      exact (Core.CNF.eval_eq_false_iff (F := truncateWidth F w') (x := x)).2
        ⟨C, hmem_trunc, hCfalse⟩
    exact (Bool.false_ne_true (by simpa using htrunc_false)) (by simpa using htrunc)
  exact ⟨C, hC, hwide, hCfalse⟩

/-!
### Union bound для truncation (CNF)

Мы фиксируем «плохое» множество входов, где truncation истинна,
а исходная CNF ложна. По структурной лемме это множество покрывается
объединением событий «широкая клауза ложна».

В результате получаем стандартный union‑bound:
вероятность расхождения ≤ сумма вероятностей широких клауз.
-/

open scoped BigOperators

/-- Множество входов, где truncation истинна, а исходная CNF ложна. -/
def truncationBadSet
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) : Finset (Core.BitVec n) :=
  (Finset.univ : Finset (Core.BitVec n)).filter
    (fun x => F.eval x = false ∧ (truncateWidth F w').eval x = true)

/-- Для индекса `i` берём соответствующую клаузу. -/
def clauseAt
    {n w : Nat} (F : Core.CNF n w) (i : Fin F.clauses.length) : CnfClause n :=
  F.clauses.get i

/-- Индексы «широких» клауз. -/
def wideClauseIdxs
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) :
    Finset (Fin F.clauses.length) :=
  (Finset.univ : Finset (Fin F.clauses.length)).filter
    (fun i => w' < (clauseAt F i).width)

/-- Множество входов, где клауза `i` ложна. -/
def clauseFalseSet
    {n w : Nat} (F : Core.CNF n w) (i : Fin F.clauses.length) :
    Finset (Core.BitVec n) :=
  (Finset.univ : Finset (Core.BitVec n)).filter
    (fun x => (clauseAt F i).eval x = false)

/-!
### Явный bound для `clauseFalseSet`

Мы показываем, что для любой клаузы ширины `k` множество входов,
на которых она ложна, имеет мощность не более `2^(n-k)`.
Это и есть «локальная» ε‑оценка, которая затем подставляется
в union‑bound.
-/

/-- Вспомогательная лемма: если `find?` нашёл элемент, он действительно в списке. -/
lemma find?_some_mem {α : Type _} (p : α → Bool) (xs : List α) (a : α) :
    xs.find? p = some a → p a = true ∧ a ∈ xs := by
  intro h
  induction xs with
  | nil => simp [List.find?] at h
  | cons x rest ih =>
      simp [List.find?] at h
      by_cases hp : p x
      · simp [hp] at h
        cases h
        exact ⟨hp, by simp⟩
      · simp [hp] at h
        rcases ih h with ⟨hpa, hmem⟩
        exact ⟨hpa, by simp [hmem]⟩

lemma bool_ne_iff_eq_not (a b : Bool) : a ≠ b ↔ a = !b := by
  cases a <;> cases b <;> simp

/-- Подкуб, фиксирующий все литералы к значению «делает клаузу ложной». -/
def falseSubcube {n : Nat} (C : CnfClause n) : Subcube n :=
  fun j =>
    match C.literals.find? (fun ℓ => ℓ.idx = j) with
    | some ℓ => some (!ℓ.value)
    | none => none

lemma falseSubcube_some_iff
    {n : Nat} (C : CnfClause n) (j : Fin n) :
    falseSubcube C j ≠ none ↔ ∃ ℓ ∈ C.literals, ℓ.idx = j := by
  classical
  constructor
  · intro h
    cases hfind : C.literals.find? (fun ℓ => ℓ.idx = j) with
    | none =>
        simp [falseSubcube, hfind] at h
    | some ℓ =>
        have hmem := find?_some_mem (p := fun ℓ => ℓ.idx = j)
          (xs := C.literals) (a := ℓ) hfind
        refine ⟨ℓ, hmem.2, ?_⟩
        simpa using hmem.1
  · rintro ⟨ℓ, hℓ, hidx⟩
    -- `find?` должен найти хотя бы этот литерал.
    have hfound : C.literals.find? (fun ℓ' => ℓ'.idx = j) ≠ none := by
      have : (fun ℓ' => ℓ'.idx = j) ℓ = true := by
        simpa [hidx]
      -- Используем `find?` на элементе из списка.
      induction C.literals with
      | nil =>
          cases hℓ
      | cons x rest ih =>
          simp [List.find?, this] at *
          by_cases hx : (fun ℓ' => ℓ'.idx = j) x
          · simp [hx]
          · have hℓ' : ℓ ∈ rest := by
              simpa [hx] using hℓ
            have := ih hℓ'
            simp [hx, this]
    simp [falseSubcube, hfound]

lemma falseSubcube_some_of_mem
    {n : Nat} {C : CnfClause n} {ℓ : Literal n}
    (hℓ : ℓ ∈ C.literals) :
    falseSubcube C ℓ.idx ≠ none := by
  exact (falseSubcube_some_iff (C := C) (j := ℓ.idx)).2 ⟨ℓ, hℓ, rfl⟩

lemma mem_falseSubcube_of_eval_false
    {n : Nat} (C : CnfClause n) (x : BitVec n)
    (hfalse : C.eval x = false) :
    mem (falseSubcube C) x := by
  classical
  have hfalse' :
      ∀ ℓ ∈ C.literals, Literal.eval ℓ x = false := by
    exact (CnfClause.eval_eq_false_iff (C := C) (x := x)).1 hfalse
  -- Показываем условие `mem` для каждого зафиксированного индекса.
  apply (mem_iff (β := falseSubcube C) (x := x)).2
  intro i b hsome
  -- `find?` возвращает литерал с индексом `i`.
  cases hfind : C.literals.find? (fun ℓ' => ℓ'.idx = i) with
  | none =>
      simp [falseSubcube, hfind] at hsome
  | some ℓ' =>
      have hmem' := find?_some_mem (p := fun ℓ' => ℓ'.idx = i)
        (xs := C.literals) (a := ℓ') hfind
      have hidx' : ℓ'.idx = i := by simpa using hmem'.1
      have hfalseℓ := hfalse' ℓ' hmem'.2
      have hx' : x ℓ'.idx ≠ ℓ'.value := by
        exact (Literal.eval_eq_false_iff (ℓ := ℓ') (x := x)).1 hfalseℓ
      have hx : x i = !ℓ'.value := by
        simpa [hidx'] using (bool_ne_iff_eq_not _ _).1 hx'
      -- `hsome` фиксирует значение `!ℓ'.value`.
      simp [falseSubcube, hfind, hidx'] at hsome
      simpa [hsome, hidx'] using hx

lemma clauseFalseSet_subset_falseSubcube
    {n w : Nat} (F : Core.CNF n w) (i : Fin F.clauses.length) :
    clauseFalseSet F i
      ⊆ (Finset.univ : Finset (Core.BitVec n)).filter
        (fun x => mem (falseSubcube (clauseAt F i)) x) := by
  classical
  intro x hx
  have hx' : (clauseAt F i).eval x = false := by
    simpa [clauseFalseSet] using hx
  have hmem := mem_falseSubcube_of_eval_false (C := clauseAt F i) (x := x) hx'
  simp [hmem]

lemma clauseFalseSet_card_le_pow
    {n w : Nat} (F : Core.CNF n w) (i : Fin F.clauses.length) :
    (clauseFalseSet F i).card
      ≤ Nat.pow 2 (n - (clauseAt F i).width) := by
  classical
  -- Переводим к подкубу и используем `subcube_card_pow`.
  have hsubset :=
    clauseFalseSet_subset_falseSubcube (F := F) (i := i)
  have hcard_eq :
      (clauseFalseSet F i).card
        ≤ (Finset.univ.filter
          (fun x => mem (falseSubcube (clauseAt F i)) x)).card := by
    exact Finset.card_le_of_subset hsubset
  have hsubcube :=
    subcube_card_pow (β := falseSubcube (clauseAt F i))
  rcases hsubcube with ⟨t, ht_le, hcard⟩
  -- Число фиксированных координат ≥ ширине клаузы.
  have hwidth_le : (clauseAt F i).width ≤ t := by
    -- Каждая литеральная координата фиксируется в `falseSubcube`.
    let fixedSet :=
      (Finset.univ : Finset (Fin n)).filter
        (fun j => falseSubcube (clauseAt F i) j ≠ none)
    have hsubset :
        (clauseAt F i).literals.map (·.idx) |>.toFinset ⊆ fixedSet := by
      intro j hj
      have hj' : j ∈ (clauseAt F i).literals.map (·.idx) := by
        simpa using hj
      rcases List.mem_map.1 hj' with ⟨ℓ, hℓ, rfl⟩
      have hsome :
          falseSubcube (clauseAt F i) ℓ.idx ≠ none := by
        exact (falseSubcube_some_iff (C := clauseAt F i) ℓ.idx).2
          ⟨ℓ, hℓ, rfl⟩
      simpa [fixedSet] using hsome
    have hcard_le :
        (clauseAt F i).width
          ≤ fixedSet.card := by
      -- `nodupIdx` даёт корректную длину.
      have hnodup := (clauseAt F i).nodupIdx
      have hcard :
          ((clauseAt F i).literals.map (·.idx)).toFinset.card
            = (clauseAt F i).width := by
        simpa [CnfClause.width] using
          List.toFinset_card_of_nodup (l := (clauseAt F i).literals.map (·.idx))
      have hcard' :
          ((clauseAt F i).literals.map (·.idx)).toFinset.card
            ≤ fixedSet.card :=
        Finset.card_le_of_subset hsubset
      simpa [hcard] using hcard'
    -- В `subcube_card_pow` фиксированное число = `fixedSet.card`.
    -- Поэтому `t ≥ width`.
    exact hcard_le
  have hpow_le :
      Nat.pow 2 (n - t) ≤ Nat.pow 2 (n - (clauseAt F i).width) := by
    -- `t ≥ width` ⇒ `n - t ≤ n - width`.
    have hsub : n - t ≤ n - (clauseAt F i).width := by
      omega
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) hsub
  -- Сводим к кардиналу подкуба.
  have hcard_sub :
      (Finset.univ.filter
        (fun x => mem (falseSubcube (clauseAt F i)) x)).card
        = Nat.pow 2 (n - t) := by
    -- Используем `subcube_card_pow` и переводим через `Fintype.card`.
    have hcard_subtype :
        Fintype.card {x : BitVec n // mem (falseSubcube (clauseAt F i)) x}
          = Nat.pow 2 (n - t) := by
      simpa using hcard
    -- Кардинал фильтра равен кардиналу подтипа.
    have hcard_filter :
        (Finset.univ.filter
          (fun x => mem (falseSubcube (clauseAt F i)) x)).card
          = Fintype.card {x : BitVec n // mem (falseSubcube (clauseAt F i)) x} := by
      simpa using
        (Fintype.card_coe
          (s := (Finset.univ.filter
            (fun x => mem (falseSubcube (clauseAt F i)) x))))
    simpa [hcard_filter] using hcard_subtype
  -- Итоговая оценка.
  calc
    (clauseFalseSet F i).card
        ≤ (Finset.univ.filter
          (fun x => mem (falseSubcube (clauseAt F i)) x)).card := hcard_eq
    _ = Nat.pow 2 (n - t) := hcard_sub
    _ ≤ Nat.pow 2 (n - (clauseAt F i).width) := hpow_le

/-!
`width` любой клаузы не превосходит `n`, поскольку индексы литералов лежат в `Fin n`
и список литералов без повторов.
-/
lemma clause_width_le_n {n : Nat} (C : CnfClause n) : C.width ≤ n := by
  classical
  have hcard :
      ((C.literals.map (·.idx)).toFinset.card) = C.width := by
    simpa [CnfClause.width] using
      List.toFinset_card_of_nodup (l := C.literals.map (·.idx))
  have hcard_le :
      ((C.literals.map (·.idx)).toFinset.card)
        ≤ (Finset.univ : Finset (Fin n)).card := by
    apply Finset.card_le_of_subset
    intro j hj
    simp
  have hcard_le' :
      ((C.literals.map (·.idx)).toFinset.card) ≤ n := by
    simpa using hcard_le
  simpa [hcard] using hcard_le'

lemma clauseFalseSet_card_le_pow_of_wide
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) (i : Fin F.clauses.length)
    (hwide : w' < (clauseAt F i).width) :
    (clauseFalseSet F i).card
      ≤ Nat.pow 2 (n - (w' + 1)) := by
  have hbase := clauseFalseSet_card_le_pow (F := F) (i := i)
  have hwidth : w' + 1 ≤ (clauseAt F i).width := by
    exact Nat.succ_le_iff.2 hwide
  have hsub : n - (clauseAt F i).width ≤ n - (w' + 1) := by
    exact Nat.sub_le_sub_left hwidth n
  have hpow :
      Nat.pow 2 (n - (clauseAt F i).width)
        ≤ Nat.pow 2 (n - (w' + 1)) := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) hsub
  exact hbase.trans hpow

/-!
Числовая (в `Q`) версия для широкой клаузы:
если `width > w'`, то
`card(clauseFalseSet) ≤ 2^n / 2^(w'+1)`.
-/
lemma clauseFalseSet_card_le_pow_of_wide_q
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) (i : Fin F.clauses.length)
    (hwide : w' < (clauseAt F i).width) :
    ((clauseFalseSet F i).card : Q)
      ≤ (2 ^ n : Q) / (2 ^ (w' + 1) : Q) := by
  have hnat := clauseFalseSet_card_le_pow_of_wide (F := F) (w' := w') (i := i) hwide
  have hq :
      ((clauseFalseSet F i).card : Q)
        ≤ (Nat.pow 2 (n - (w' + 1)) : Q) := by
    exact_mod_cast hnat
  have hwidth_le_n : w' + 1 ≤ n := by
    have hwidth_le : (clauseAt F i).width ≤ n :=
      clause_width_le_n (clauseAt F i)
    exact (Nat.succ_le_iff.2 hwide).trans hwidth_le
  have hpow_sub :
      (2 : Q) ^ (n - (w' + 1))
        = (2 : Q) ^ n / (2 : Q) ^ (w' + 1) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (pow_sub (a := (2 : Q)) hwidth_le_n)
  -- Переводим оценку в требуемый вид.
  calc
    ((clauseFalseSet F i).card : Q)
        ≤ (2 : Q) ^ (n - (w' + 1)) := hq
    _ = (2 : Q) ^ n / (2 : Q) ^ (w' + 1) := hpow_sub

lemma mem_truncationBadSet_iff
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) {x : Core.BitVec n} :
    x ∈ truncationBadSet F w' ↔
      F.eval x = false ∧ (truncateWidth F w').eval x = true := by
  classical
  simp [truncationBadSet]

lemma truncationBadSet_subset_union
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) :
    truncationBadSet F w'
      ⊆ (wideClauseIdxs F w').biUnion (fun i => clauseFalseSet F i) := by
  classical
  intro x hx
  have hx' := (mem_truncationBadSet_iff (F := F) (w' := w')).1 hx
  rcases exists_wide_clause_of_truncate_true_eval_false
      (F := F) (w' := w') (x := x)
      (htrunc := hx'.2) (hfalse := hx'.1) with ⟨C, hC, hwide, hCfalse⟩
  -- Получаем индекс `i` для `C` в списке клауз.
  rcases List.mem_iff_get.mp hC with ⟨i, hi, hget⟩
  have hi' : i < F.clauses.length := by
    simpa using hi
  let idx : Fin F.clauses.length := ⟨i, hi'⟩
  have hCeq : clauseAt F idx = C := by
    simpa [clauseAt, hget]
  -- Показываем, что x входит в объединение по широким клаузам.
  have hmem_idx : idx ∈ wideClauseIdxs F w' := by
    simp [wideClauseIdxs, clauseAt, hCeq, hwide]
  have hmem_false : x ∈ clauseFalseSet F idx := by
    simp [clauseFalseSet, clauseAt, hCeq, hCfalse]
  exact Finset.mem_biUnion.mpr ⟨idx, hmem_idx, hmem_false⟩

lemma truncationBadSet_card_le_sum
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) :
    (truncationBadSet F w').card
      ≤ ∑ i in wideClauseIdxs F w', (clauseFalseSet F i).card := by
  classical
  -- Кардинал подмножества ≤ кардинала объединения, затем `card_biUnion_le`.
  have hsubset := truncationBadSet_subset_union (F := F) (w' := w')
  have hcard_le :
      (truncationBadSet F w').card
        ≤ ((wideClauseIdxs F w').biUnion (fun i => clauseFalseSet F i)).card :=
    Finset.card_le_of_subset hsubset
  have hcard_union_le :
      ((wideClauseIdxs F w').biUnion (fun i => clauseFalseSet F i)).card
        ≤ ∑ i in wideClauseIdxs F w', (clauseFalseSet F i).card := by
    exact Finset.card_biUnion_le
  exact hcard_le.trans hcard_union_le

/--
  Числовой union‑bound: если каждая широкая клауза «плохая» не более `ε`,
  то вероятность расхождения между `F` и truncation также ≤ `#wide * ε`.

  Здесь вероятность определяется как `card / 2^n`.
-/
lemma truncation_disagreement_prob_le
    {n w : Nat} (F : Core.CNF n w) (w' : Nat) (ε : Q)
    (hε :
      ∀ i ∈ wideClauseIdxs F w',
        ((clauseFalseSet F i).card : Q) ≤ (2 ^ n : Q) * ε) :
    ((truncationBadSet F w').card : Q) / (2 ^ n : Q)
      ≤ (wideClauseIdxs F w').card * ε := by
  classical
  have hcard :=
    truncationBadSet_card_le_sum (F := F) (w' := w')
  have hsum :
      ((truncationBadSet F w').card : Q)
        ≤ ∑ i in wideClauseIdxs F w', ((clauseFalseSet F i).card : Q) := by
    exact_mod_cast hcard
  have hsum' :
      ∑ i in wideClauseIdxs F w', ((clauseFalseSet F i).card : Q)
        ≤ ∑ i in wideClauseIdxs F w', (2 ^ n : Q) * ε := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hε i hi
  have hsum'' :
      ∑ i in wideClauseIdxs F w', (2 ^ n : Q) * ε
        = (wideClauseIdxs F w').card * ((2 ^ n : Q) * ε) := by
    simp
  -- Делим на `2^n` (положительно) и упрощаем.
  have hpos : 0 < (2 ^ n : Q) := by
    exact pow_pos (by decide : (0 : Q) < 2) _
  have hle :
      ((truncationBadSet F w').card : Q)
        ≤ (wideClauseIdxs F w').card * ((2 ^ n : Q) * ε) := by
    exact hsum.trans (hsum'.trans hsum'')
  have hdiv :
      ((truncationBadSet F w').card : Q) / (2 ^ n : Q)
        ≤ (wideClauseIdxs F w').card * ε := by
    -- Используем эквивалентность `a / b ≤ c ↔ a ≤ c * b` при `b > 0`.
    have hpos' : 0 < (2 ^ n : Q) := hpos
    apply (div_le_iff hpos').2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hle
  exact hdiv

/--
  Числовой вариант, связывающий ε‑оценку с параметром `w'`:
  если для каждой широкой клаузы выполнено
  `card(clauseFalseSet) ≤ 2^n / 2^(w'+1)`, а число широких клауз
  не превосходит `m+1`, то общий ε‑бюджет контролируется
  неравенством `2^(w'+1) ≥ (m+1)(n+2)`.

  Эта форма напрямую соответствует выбору `w' := tParam m n`.
-/
lemma truncation_disagreement_prob_le_of_pow
    {n w : Nat} (F : Core.CNF n w) (w' m : Nat)
    (hwide_le : (wideClauseIdxs F w').card ≤ m + 1)
    (hclause :
      ∀ i ∈ wideClauseIdxs F w',
        ((clauseFalseSet F i).card : Q)
          ≤ (2 ^ n : Q) / (2 ^ (w' + 1) : Q))
    (ht : 2 ^ (w' + 1) ≥ (m + 1) * (n + 2)) :
    ((truncationBadSet F w').card : Q) / (2 ^ n : Q)
      ≤ (1 : Q) / (n + 2) := by
  classical
  -- Применяем union‑bound с ε = 1 / 2^(w'+1).
  have hε :
      ((truncationBadSet F w').card : Q) / (2 ^ n : Q)
        ≤ (wideClauseIdxs F w').card * ((1 : Q) / (2 ^ (w' + 1) : Q)) := by
    apply truncation_disagreement_prob_le (F := F) (w' := w')
    intro i hi
    have := hclause i hi
    -- Переписываем `2^n * (1 / 2^(w'+1))` как `(2^n) / 2^(w'+1)`.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- Оцениваем число широких клауз через `m+1`.
  have hwide_le_q :
      ((wideClauseIdxs F w').card : Q) ≤ (m + 1 : Q) := by
    exact_mod_cast hwide_le
  have hε' :
      (wideClauseIdxs F w').card * ((1 : Q) / (2 ^ (w' + 1) : Q))
        ≤ (m + 1 : Q) * ((1 : Q) / (2 ^ (w' + 1) : Q)) := by
    exact mul_le_mul_of_nonneg_right hwide_le_q (by
      have : 0 ≤ (1 : Q) / (2 ^ (w' + 1) : Q) := by
        exact div_nonneg (by norm_num) (by
          have : 0 ≤ (2 ^ (w' + 1) : Q) := by
            exact le_of_lt (pow_pos (by norm_num) _)
          exact this)
      exact this)
  -- Показываем `(m+1)/2^(w'+1) ≤ 1/(n+2)` из неравенства `2^(w'+1) ≥ (m+1)(n+2)`.
  have hpos_w : 0 < (2 ^ (w' + 1) : Q) := by
    exact pow_pos (by norm_num) _
  have hpos_n : 0 < (n + 2 : Q) := by
    exact_mod_cast Nat.succ_pos _
  have hratio :
      (m + 1 : Q) / (2 ^ (w' + 1) : Q) ≤ (1 : Q) / (n + 2 : Q) := by
    -- `a/b ≤ 1/d` ↔ `a*d ≤ b`.
    apply (div_le_div_iff hpos_w hpos_n).2
    -- `a * d ≤ b` в ℕ переносится в ℚ.
    exact_mod_cast ht
  -- Собираем цепочку.
  have hmid :
      (wideClauseIdxs F w').card * ((1 : Q) / (2 ^ (w' + 1) : Q))
        ≤ (1 : Q) / (n + 2 : Q) := by
    have h1 :
        (wideClauseIdxs F w').card * ((1 : Q) / (2 ^ (w' + 1) : Q))
          ≤ (m + 1 : Q) * ((1 : Q) / (2 ^ (w' + 1) : Q)) := hε'
    have h2 :
        (m + 1 : Q) * ((1 : Q) / (2 ^ (w' + 1) : Q))
          = (m + 1 : Q) / (2 ^ (w' + 1) : Q) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have h3 :
        (m + 1 : Q) * ((1 : Q) / (2 ^ (w' + 1) : Q))
          ≤ (1 : Q) / (n + 2 : Q) := by
        simpa [h2] using hratio
    exact h1.trans h3
  exact hε.trans hmid

end CNF

/-!
## DNF truncation

Для DNF удаление «широких» термов делает формулу **сильнее** (труднее
удовлетворить), поэтому истинность truncation гарантирует истинность
исходной DNF.
-/

namespace DNF

/-- Удаляем все термы ширины `> w'`, получая DNF ширины `w'`. -/
def truncateWidth {n w : Nat} (F : Core.DNF n w) (w' : Nat) :
    Core.DNF n w' :=
  { terms := F.terms.filter (fun T => T.width ≤ w')
    width_le := by
      intro T hT
      have hmem :
          T ∈ F.terms ∧ T.width ≤ w' := by
        simpa [List.mem_filter] using hT
      exact hmem.2 }

/-- Если truncation DNF истинна, то и исходная DNF истинна. -/
lemma eval_true_of_eval_truncate_true
    {n w : Nat} (F : Core.DNF n w) (w' : Nat) (x : Core.BitVec n)
    (h : (truncateWidth F w').eval x = true) :
    F.eval x = true := by
  classical
  unfold Core.DNF.eval at h ⊢
  -- `eval` — это `any` по списку термов; `filter` даёт подсписок.
  rcases List.any_eq_true.mp h with ⟨T, hT, hval⟩
  have hmem : T ∈ F.terms := by
    exact (List.mem_filter.mp hT).1
  exact List.any_eq_true.mpr ⟨T, hmem, hval⟩

/--
  Если исходная DNF истинна, а truncation ложна, то существует «широкий»
  терм (width > w'), который отвечает за истинность исходной формулы.

  Это симметричный к CNF факт: различие возможно только из‑за удалённых термов.
-/
lemma exists_wide_term_of_eval_true_truncate_false
    {n w : Nat} (F : Core.DNF n w) (w' : Nat) (x : Core.BitVec n)
    (htrue : F.eval x = true)
    (htrunc_false : (truncateWidth F w').eval x = false) :
    ∃ T ∈ F.terms, w' < T.width ∧ T.eval x = true := by
  classical
  -- Из истинности DNF получаем «хороший» терм.
  rcases (Core.DNF.eval_eq_true_iff (F := F) (x := x)).1 htrue with
    ⟨T, hT, hTtrue⟩
  have hTtrue_eval : T.eval x = true := by
    exact (Core.DnfTerm.eval_eq_true_iff (T := T) (x := x)).2 hTtrue
  -- Если бы T был узким, truncation была бы истинной.
  have hwide : w' < T.width := by
    by_contra hle
    have hle' : T.width ≤ w' := Nat.le_of_not_gt hle
    have hmem_trunc : T ∈ (truncateWidth F w').terms := by
      exact List.mem_filter.mpr ⟨hT, hle'⟩
    have htrunc_true :
        (truncateWidth F w').eval x = true := by
      exact List.any_eq_true.mpr ⟨T, hmem_trunc, hTtrue_eval⟩
    exact (Bool.false_ne_true (by simpa using htrunc_false)) (by simpa using htrunc_true)
  exact ⟨T, hT, hwide, hTtrue_eval⟩

end DNF

/-!
## Truncation для семейств формул

Чтобы использовать ширинный мост в multi‑switching пайплайне, удобно
уметь работать сразу с семьями `FormulaFamily`/`DnfFamily` и переносить
оценки `eval` на весь список.
-/

/-- Truncation для семейства CNF: поэлементно удаляем «широкие» клаузы. -/
def truncateCnfFamilyWidth {n w : Nat} (F : FormulaFamily n w) (w' : Nat) :
    FormulaFamily n w' :=
  F.map (fun G => CNF.truncateWidth G w')

/-- Truncation для семейства DNF: поэлементно удаляем «широкие» термы. -/
def truncateDnfFamilyWidth {n w : Nat} (F : DnfFamily n w) (w' : Nat) :
    DnfFamily n w' :=
  F.map (fun G => DNF.truncateWidth G w')

/-!
### Идемпотентность при достаточной ширине

Если все клаузы (соответственно термы) уже имеют ширину `≤ w'`,
то truncation ничего не меняет. Эти леммы полезны для «граничных»
случаев в дальнейшем, когда ширина выбирается заведомо большой.
-/

lemma truncateCnfFamilyWidth_eq_of_width_le
    {n w : Nat} (F : FormulaFamily n w) (w' : Nat)
    (hwidth :
      ∀ G ∈ F, ∀ C ∈ G.clauses, C.width ≤ w') :
    truncateCnfFamilyWidth F w' = F := by
  classical
  induction F with
  | nil =>
      simp [truncateCnfFamilyWidth]
  | cons G rest ih =>
      have hwidth_rest :
          ∀ G' ∈ rest, ∀ C ∈ G'.clauses, C.width ≤ w' := by
        intro G' hG' C hC
        exact hwidth G' (by simp [hG']) C hC
      have hGwidth : ∀ C ∈ G.clauses, C.width ≤ w' := by
        intro C hC
        exact hwidth G (by simp) C hC
      have htruncG : CNF.truncateWidth G w' = G := by
        -- Сверяем список клауз через фильтр по ширине.
        ext C
        constructor
        · intro hC
          exact (List.mem_filter.mp hC).1
        · intro hC
          exact List.mem_filter.mpr ⟨hC, hGwidth C hC⟩
      simp [truncateCnfFamilyWidth, htruncG, ih hwidth_rest]

lemma truncateDnfFamilyWidth_eq_of_width_le
    {n w : Nat} (F : DnfFamily n w) (w' : Nat)
    (hwidth :
      ∀ G ∈ F, ∀ T ∈ G.terms, T.width ≤ w') :
    truncateDnfFamilyWidth F w' = F := by
  classical
  induction F with
  | nil =>
      simp [truncateDnfFamilyWidth]
  | cons G rest ih =>
      have hwidth_rest :
          ∀ G' ∈ rest, ∀ T ∈ G'.terms, T.width ≤ w' := by
        intro G' hG' T hT
        exact hwidth G' (by simp [hG']) T hT
      have hGwidth : ∀ T ∈ G.terms, T.width ≤ w' := by
        intro T hT
        exact hwidth G (by simp) T hT
      have htruncG : DNF.truncateWidth G w' = G := by
        ext T
        constructor
        · intro hT
          exact (List.mem_filter.mp hT).1
        · intro hT
          exact List.mem_filter.mpr ⟨hT, hGwidth T hT⟩
      simp [truncateDnfFamilyWidth, htruncG, ih hwidth_rest]

/-!
### Монотонность `eval` для семейств

Для CNF: истинность исходного семейства (покомпонентно) ⇒ истинность truncation.
Для DNF: истинность truncation (покомпонентно) ⇒ истинность исходного семейства.
-/

lemma eval_truncate_family_true_of_eval_true
    {n w : Nat} (F : FormulaFamily n w) (w' : Nat) (x : Core.BitVec n)
    (h : List.Forall (fun G => G.eval x = true) F) :
    List.Forall (fun G => G.eval x = true) (truncateCnfFamilyWidth F w') := by
  induction F with
  | nil =>
      simp [truncateCnfFamilyWidth]
  | cons G rest ih =>
      simp [truncateCnfFamilyWidth] at h ⊢
      rcases h with ⟨hG, hrest⟩
      refine ⟨?_, ih hrest⟩
      exact CNF.eval_truncate_true_of_eval_true (F := G) (w' := w') (x := x) hG

lemma eval_true_of_eval_truncate_family_true
    {n w : Nat} (F : DnfFamily n w) (w' : Nat) (x : Core.BitVec n)
    (h : List.Forall (fun G => G.eval x = true) (truncateDnfFamilyWidth F w')) :
    List.Forall (fun G => G.eval x = true) F := by
  induction F with
  | nil =>
      simp [truncateDnfFamilyWidth]
  | cons G rest ih =>
      simp [truncateDnfFamilyWidth] at h ⊢
      rcases h with ⟨hG, hrest⟩
      refine ⟨?_, ih hrest⟩
      exact DNF.eval_true_of_eval_truncate_true (F := G) (w' := w') (x := x) hG

/-!
### Те же леммы, но на уровне `evalFamily`

Это удобные «обёртки», которые позволяют применять truncation
непосредственно к `Family` (списку булевых функций), без ручного
раскрытия `evalFamily`.
-/

lemma evalFamily_truncateCnf_true_of_evalFamily_true
    {n w : Nat} (F : FormulaFamily n w) (w' : Nat) (x : Core.BitVec n)
    (h : List.Forall (fun f => f x = true) (evalFamily F)) :
    List.Forall (fun f => f x = true) (evalFamily (truncateCnfFamilyWidth F w')) := by
  -- Переписываем `evalFamily` и сводим к лемме для списка CNF.
  simpa [evalFamily, evalCNF] using
    (eval_truncate_family_true_of_eval_true (F := F) (w' := w') (x := x) h)

lemma evalFamily_true_of_evalFamily_truncateDnf_true
    {n w : Nat} (F : DnfFamily n w) (w' : Nat) (x : Core.BitVec n)
    (h :
      List.Forall (fun f => f x = true)
        (evalDnfFamily (truncateDnfFamilyWidth F w'))) :
    List.Forall (fun f => f x = true) (evalDnfFamily F) := by
  -- Переписываем `evalDnfFamily` и сводим к лемме для списка DNF.
  simpa [evalDnfFamily, evalDNF] using
    (eval_true_of_eval_truncate_family_true (F := F) (w' := w') (x := x) h)

end MultiSwitching
end AC0
end Pnp3
