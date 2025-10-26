/-
  pnp3/ThirdPartyFacts/RandomRestriction.lean

  Этот модуль реализует базовые детерминированные конструкции, которые
  понадобятся при формализации вероятностного распределения exact-ℓ
  рестрикций.  Мы выделяем структуру «оси» (`Axis`) — множества из ровно ℓ
  свободных переменных — и задаём способ построить из неё подкуб, где
  остальные координаты фиксированы.  Эти определения служат строительными
  блоками для последующих вероятностных аргументов switching-леммы.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.MeasureTheory.ProbabilityMassFunction.Basic
import Mathlib.Tactic
import Core.BooleanBasics
import Core.PDT
import Core.ShrinkageWitness

namespace Pnp3
namespace ThirdPartyFacts
namespace RandomRestriction

open Core
open Finset

/-!
### Оси (наборы свободных переменных)

`Axis n ℓ` — это точное множество из `ℓ` индексов в `Fin n`, которые мы
оставляем свободными после применения рестрикции.  Остальные переменные
будут фиксированы.
-/
structure Axis (n ℓ : Nat) where
  /-- Подмножество индексов, которое останется свободным. -/
  support : Finset (Fin n)
  /-- Кардинальное условие: ровно `ℓ` свободных координат. -/
  card_support : support.card = ℓ
  deriving DecidableEq

namespace Axis

variable {n ℓ : Nat}

@[simp] lemma card (A : Axis n ℓ) : A.support.card = ℓ := A.card_support

/-- Дополнение к множеству свободных координат: индексы, которые будут
зафиксированы. -/
@[simp] def fixed (A : Axis n ℓ) : Finset (Fin n) := A.supportᶜ

@[simp] lemma mem_fixed {A : Axis n ℓ} {i : Fin n} :
    i ∈ A.fixed ↔ i ∉ A.support := by
  classical
  simp [fixed]

/-- Количество фиксированных координат равно `n - ℓ`.  Это прямое
следствие формулы для мощности дополнения. -/
lemma card_fixed (A : Axis n ℓ) : A.fixed.card = n - ℓ := by
  classical
  simpa [fixed, card] using
    (Finset.card_compl (s := A.support) : A.supportᶜ.card = _)

/-!
Чтобы впоследствии задать вероятностное распределение на осях, полезно иметь
явный свидетель существования `Axis n ℓ` при условии `ℓ ≤ n`.  В качестве
оси возьмём первые `ℓ` индексов.
-/

/-- Вспомогательная конструкция: первые `ℓ` элементов из `Fin n`. -/
@[simp] def initialSlice (n ℓ : Nat) : Finset (Fin n) :=
  (Finset.univ.filter fun i : Fin n => (i : Nat) < ℓ)

@[simp] lemma mem_initialSlice {n ℓ : Nat} {i : Fin n} :
    i ∈ initialSlice n ℓ ↔ (i : Nat) < ℓ := by
  classical
  simp [initialSlice]

/-- Кардинальность «первого слоя» — ровно `ℓ` (при `ℓ ≤ n`).
Доказательство по индукции по `ℓ`. -/
lemma initialSlice_card {n ℓ : Nat} (hℓ : ℓ ≤ n) :
    (initialSlice n ℓ).card = ℓ := by
  classical
  revert n
  induction ℓ with
  | zero =>
      intro n _
      simp [initialSlice]
  | succ ℓ ih =>
      intro n hℓ'
      have hℓn : ℓ < n :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self ℓ) hℓ'
      have hℓ_le : ℓ ≤ n := Nat.le_of_lt hℓn
      have hrec := ih n hℓ_le
      -- Конкретный индекс, добавляющийся при переходе ℓ → ℓ + 1.
      let pivot : Fin n := ⟨ℓ, hℓn⟩
      -- Покажем, что фильтр для ℓ+1 равен вставке pivot в предыдущий слой.
      have hstep :
          initialSlice n (Nat.succ ℓ)
              = insert pivot (initialSlice n ℓ) := by
        ext i
        constructor
        · intro hi
          have hi_lt : (i : Nat) < Nat.succ ℓ :=
            (mem_initialSlice (n := n) (ℓ := Nat.succ ℓ)).1 hi
          have hi_le : (i : Nat) ≤ ℓ := Nat.lt_succ_iff.mp hi_lt
          have hi_cases := Nat.lt_or_eq_of_le hi_le
          cases hi_cases with
          | inl hi_strict =>
              have hi_mem : i ∈ initialSlice n ℓ :=
                (mem_initialSlice (n := n) (ℓ := ℓ)).2 hi_strict
              exact Or.inr hi_mem
          | inr hi_eq =>
              have : i = pivot := by
                apply Fin.ext
                simpa [pivot] using hi_eq
              exact Or.inl this
        · intro hi
          have hi_cases := (Finset.mem_insert).1 hi
          cases hi_cases with
          | inl hi_eq =>
              subst hi_eq
              have : (pivot : Nat) < Nat.succ ℓ := by
                simp [pivot]
              exact (mem_initialSlice (n := n) (ℓ := Nat.succ ℓ)).2 this
          | inr hi_mem =>
              have hi_lt : (i : Nat) < ℓ :=
                (mem_initialSlice (n := n) (ℓ := ℓ)).1 hi_mem
              have : (i : Nat) < Nat.succ ℓ := Nat.lt_succ_of_lt hi_lt
              exact (mem_initialSlice (n := n) (ℓ := Nat.succ ℓ)).2 this
      -- Уточним, что pivot отсутствует в предыдущем слое.
      have hpivot_not_mem : pivot ∉ initialSlice n ℓ := by
        intro hcontr
        have : (pivot : Nat) < ℓ :=
          (mem_initialSlice (n := n) (ℓ := ℓ)).1 hcontr
        exact Nat.lt_irrefl _ this
      -- Теперь считаем мощности.
      have hcard_insert :
          (initialSlice n (Nat.succ ℓ)).card
              = (initialSlice n ℓ).card + 1 := by
        simpa [hstep] using
          Finset.card_insert (s := initialSlice n ℓ)
            (a := pivot) hpivot_not_mem
      -- Заключаем индуктивный шаг.
      simpa [hrec] using hcard_insert

/-- Построение оси из условия `ℓ ≤ n`: берём первые `ℓ` индексов. -/
@[simp] def ofLE {n ℓ : Nat} (hℓ : ℓ ≤ n) : Axis n ℓ where
  support := initialSlice n ℓ
  card_support := initialSlice_card (n := n) (ℓ := ℓ) hℓ

/-- Оси существуют всякий раз, когда `ℓ ≤ n`. -/
lemma nonempty {n ℓ : Nat} (hℓ : ℓ ≤ n) :
    Nonempty (Axis n ℓ) := ⟨ofLE (n := n) (ℓ := ℓ) hℓ⟩

/-- Тривиальное отображение, забывающее структурные данные `Axis`. -/
@[simp] def toSubtype (A : Axis n ℓ) :
    { S : Finset (Fin n) // S.card = ℓ } := ⟨A.support, A.card_support⟩

/-- Обратное отображение к `Axis.toSubtype`. -/
@[simp] def ofSubtype (S : { S : Finset (Fin n) // S.card = ℓ }) :
    Axis n ℓ := ⟨S.1, S.2⟩

/-- Изоморфизм между осями и подмножествами `Fin n` фиксированной мощности. -/
@[simp] def equivSubtype (n ℓ : Nat) :
    Axis n ℓ ≃ { S : Finset (Fin n) // S.card = ℓ } where
  toFun := toSubtype
  invFun := ofSubtype
  left_inv := by
    intro A
    cases A
    simp [Axis.toSubtype, Axis.ofSubtype]
  right_inv := by
    intro S
    cases S
    simp [Axis.toSubtype, Axis.ofSubtype]

/-!
`Axis n ℓ` — конечный тип: он эквивалентен подмножествам `Fin n` мощности `ℓ`.
Далее фиксируем стандартные инстансы `Finite`/`Fintype`, чтобы иметь доступ
к `Finset.univ` и суммированию по всем осям.
-/

@[simp] theorem finite (n ℓ : Nat) : Finite (Axis n ℓ) := by
  classical
  have : Finite { S : Finset (Fin n) // S.card = ℓ } := by infer_instance
  simpa using (Axis.equivSubtype n ℓ).finite_iff.mpr this

noncomputable instance instFintype (n ℓ : Nat) : Fintype (Axis n ℓ) :=
  Fintype.ofFinite _

/--
  Чтобы строить решающие деревья, полезно нумеровать свободные координаты
  оси.  Биекция `supportEquivFin` связывает подтип «элемент принадлежит
  `support`» с конечным типом `Fin ℓ`.
-/
noncomputable def supportEquivFin (A : Axis n ℓ) :
    { i : Fin n // i ∈ A.support } ≃ Fin ℓ :=
  Fintype.equivFinOfCardEq <| by
    classical
    simpa [Axis.card]
      using (Fintype.card_coe (s := A.support))

/-- Обратное отображение к `supportEquivFin`: по номеру `j : Fin ℓ`
    получаем соответствующую координату и доказательство её принадлежности
    `support`. -/
noncomputable def supportEnum (A : Axis n ℓ) :
    Fin ℓ ≃ { i : Fin n // i ∈ A.support } :=
  (supportEquivFin (n := n) (ℓ := ℓ) A).symm

/-- `coord A j` — сам индекс `Fin n`, стоящий на `j`-й позиции оси. -/
noncomputable def coord (A : Axis n ℓ) (j : Fin ℓ) : Fin n :=
  (supportEnum (n := n) (ℓ := ℓ) A j).1

@[simp] lemma coord_mem_support (A : Axis n ℓ) (j : Fin ℓ) :
    coord (n := n) (ℓ := ℓ) A j ∈ A.support :=
  (supportEnum (n := n) (ℓ := ℓ) A j).property

/-- Номер координаты `i`, находящейся в оси. -/
noncomputable def indexOf (A : Axis n ℓ) {i : Fin n} (hi : i ∈ A.support) :
    Fin ℓ :=
  supportEquivFin (n := n) (ℓ := ℓ) A ⟨i, hi⟩

@[simp] lemma coord_indexOf (A : Axis n ℓ) {i : Fin n} (hi : i ∈ A.support) :
    coord (n := n) (ℓ := ℓ) A (indexOf (n := n) (ℓ := ℓ) A hi) = i := by
  classical
  have := congrArg Subtype.val
    ((supportEquivFin (n := n) (ℓ := ℓ) A).right_inv ⟨i, hi⟩)
  simpa [coord, indexOf] using this

@[simp] lemma indexOf_coord (A : Axis n ℓ) (j : Fin ℓ) :
    indexOf (n := n) (ℓ := ℓ) A (coord_mem_support (n := n) (ℓ := ℓ) A j)
      = j := by
  classical
  have := (supportEquivFin (n := n) (ℓ := ℓ) A).left_inv j
  simpa [coord, indexOf] using this

/--
  Подкуб, соответствующий назначению `α` на живых координатах оси.  На
  свободных позициях возвращается `none`, а на координатах из `support`
  подставляется конкретный бит `α`.
-/
noncomputable def partialSubcube (A : Axis n ℓ) (α : BitVec ℓ) : Subcube n :=
  fun i =>
    if hi : i ∈ A.support then
      some (α (indexOf (n := n) (ℓ := ℓ) A hi))
    else
      none

@[simp] lemma partialSubcube_apply_mem (A : Axis n ℓ) (α : BitVec ℓ)
    {i : Fin n} (hi : i ∈ A.support) :
    partialSubcube (n := n) (ℓ := ℓ) A α i
      = some (α (indexOf (n := n) (ℓ := ℓ) A hi)) := by
  classical
  simp [partialSubcube, hi]

@[simp] lemma partialSubcube_apply_not_mem (A : Axis n ℓ) (α : BitVec ℓ)
    {i : Fin n} (hi : i ∉ A.support) :
    partialSubcube (n := n) (ℓ := ℓ) A α i = none := by
  classical
  simp [partialSubcube, hi]

lemma mem_partialSubcube_iff (A : Axis n ℓ) (α : BitVec ℓ) (x : BitVec n) :
    mem (partialSubcube (n := n) (ℓ := ℓ) A α) x ↔
      ∀ i (hi : i ∈ A.support), x i = α (indexOf (n := n) (ℓ := ℓ) A hi) := by
  classical
  constructor
  · intro hmem i hi
    have hx :=
      (mem_iff (β := partialSubcube (n := n) (ℓ := ℓ) A α) (x := x)).mp hmem
    have hvalue :=
      partialSubcube_apply_mem (n := n) (ℓ := ℓ) (A := A) (α := α) hi
    have := hx i (α (indexOf (n := n) (ℓ := ℓ) A hi)) hvalue
    simpa using this
  · intro h
    refine
      (mem_iff (β := partialSubcube (n := n) (ℓ := ℓ) A α) (x := x)).mpr ?_
    intro i b hb
    by_cases hi : i ∈ A.support
    · have hvalue :=
        partialSubcube_apply_mem (n := n) (ℓ := ℓ) (A := A) (α := α) hi
      have hb' : α (indexOf (n := n) (ℓ := ℓ) A hi) = b := by
        have hrewrite :
            some (α (indexOf (n := n) (ℓ := ℓ) A hi)) = some b := by
          simpa [hvalue] using hb
        exact Option.some.inj hrewrite
      have hx' := h i hi
      simpa [hb'] using hx'
    · have hnone :=
        partialSubcube_apply_not_mem (n := n) (ℓ := ℓ) (A := A) (α := α) hi
      -- Случай `hi = false` невозможен: подкуб возвращает `none`.
      have : False := by simpa [hnone] using hb
      exact this.elim

/--
  Полный список листьев, соответствующих всем возможным назначениям оси.
  Мы определяем его рекурсивно: база (`ℓ = 0`) состоит из единственного
  листа «все свободно», а переход `ℓ → ℓ + 1` добавляет ветвление по биту
  `pivot`, рекурсивно обрабатывая хвостовую ось.
-/
noncomputable def leafList : ∀ {ℓ : Nat}, Axis n ℓ → List (Subcube n)
| 0, _ => [fun _ => (none : Option Bool)]
| Nat.succ ℓ, A =>
    let tail := leafList (n := n) (ℓ := ℓ) (removePivot (n := n) (ℓ := ℓ) A)
    let pivot := pivot (n := n) (ℓ := ℓ) A
    let zero := tail.map (fun β => assign (n := n) β pivot false)
    let one  := tail.map (fun β => assign (n := n) β pivot true)
    zero ++ one

@[simp] lemma leafList_length :
    ∀ {ℓ : Nat} (A : Axis n ℓ),
      (leafList (n := n) (ℓ := ℓ) A).length = Nat.pow 2 ℓ
| 0, _ => by
    simp [leafList]
| Nat.succ ℓ, A => by
    classical
    have htail :=
      leafList_length (n := n) (ℓ := ℓ)
        (A := removePivot (n := n) (ℓ := ℓ) A)
    simp [leafList, htail, Nat.pow_succ, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc]

/--
  Значения листа `β` вне опорного множества оси равны `none`.  То есть ствол
  действительно фиксирует только свободные координаты и не затрагивает
  остальные переменные.
-/
lemma leafList_value_of_not_mem_support
    : ∀ {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
        (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A)
        {i : Fin n} (hi : i ∉ A.support), β i = none
| 0, A, β, hβ, i, hi => by
     classical
     -- В базе `ℓ = 0` список состоит из единственного полностью свободного
     -- подкуба, поэтому все координаты равны `none`.
     have hsingleton : β = (fun _ => (none : Option Bool)) := by
       simpa [leafList] using hβ
     simpa [hsingleton]
 | Nat.succ ℓ, A, β, hβ, i, hi => by
     classical
     -- Разбиваем список листьев на левую и правую часть (бит pivot = 0/1).
     set tail := leafList (n := n) (ℓ := ℓ)
       (removePivot (n := n) (ℓ := ℓ) A)
     set pivot := pivot (n := n) (ℓ := ℓ) A
     have hpivot_mem : pivot ∈ A.support :=
       pivot_mem_support (n := n) (ℓ := ℓ) (A := A)
     have hipivot_ne : i ≠ pivot := by
       intro hcontr
       exact hi (by simpa [hcontr] using hpivot_mem)
     have hi_tail :
         i ∉ (removePivot (n := n) (ℓ := ℓ) A).support := by
       intro hitail
       -- Попадание в support хвостовой оси означает принадлежность исходной
       -- оси (за исключением pivot), что противоречит `hi`.
       have hiA : i ∈ A.support := by
         rcases Finset.mem_erase.mp hitail with ⟨_, hiA⟩
         exact hiA
       exact hi hiA
     -- Конструкции `zero` и `one` из определения `leafList`.
     set zero := tail.map (fun β₀ => assign (n := n) β₀ pivot false)
     set one  := tail.map (fun β₀ => assign (n := n) β₀ pivot true)
     have hcases := List.mem_append.mp (show β ∈ zero ++ one by simpa [leafList, zero, one] using hβ)
     cases hcases with
     | inl hzero =>
         -- Случай `pivot = 0`: лист получен из хвостового β₀ присвоением false.
         rcases List.mem_map.mp hzero with ⟨β₀, hβ₀_mem, rfl⟩
         have hiβ₀ :=
           leafList_value_of_not_mem_support
             (n := n) (ℓ := ℓ)
             (A := removePivot (n := n) (ℓ := ℓ) A)
             (β := β₀) hβ₀_mem (i := i) hi_tail
        have hassign := assign_other (n := n)
          (β := β₀) (i := pivot) (j := i)
          (b := false) hipivot_ne
        simpa [zero, one, hassign]
          using hiβ₀
     | inr hone =>
         -- Случай `pivot = 1`: полностью аналогичен предыдущему.
         rcases List.mem_map.mp hone with ⟨β₀, hβ₀_mem, rfl⟩
         have hiβ₀ :=
           leafList_value_of_not_mem_support
             (n := n) (ℓ := ℓ)
             (A := removePivot (n := n) (ℓ := ℓ) A)
             (β := β₀) hβ₀_mem (i := i) hi_tail
        have hassign := assign_other (n := n)
          (β := β₀) (i := pivot) (j := i)
          (b := true) hipivot_ne
        simpa [zero, one, hassign]
          using hiβ₀

/-- Значение листа на свободной координате `i ∈ A.support` всегда определено.
Это позволит дальше считать число фиксированных координат листа и работать с
кардинальностями подкубов. -/
lemma leafList_value_of_mem_support
    : ∀ {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
        (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A)
        {i : Fin n} (hi : i ∈ A.support), ∃ b : Bool, β i = some b
| 0, A, β, hβ, i, hi => by
    classical
    -- В случае `ℓ = 0` множество опоры пусто, поэтому предпосылка невозможна.
    have hsupport_empty : A.support = (∅ : Finset (Fin n)) := by
      refine Finset.card_eq_zero.mp ?_
      simpa [Axis.card] using (A.card : A.support.card = 0)
    have : False := by simpa [hsupport_empty] using hi
    exact this.elim
| Nat.succ ℓ, A, β, hβ, i, hi => by
    classical
    -- Разделяем список листьев на ветви `pivot = 0` и `pivot = 1`.
    set pivot := pivot (n := n) (ℓ := ℓ) A
    set tailAxis := removePivot (n := n) (ℓ := ℓ) A
    set tail := leafList (n := n) (ℓ := ℓ) tailAxis
    set zero := tail.map (fun β₀ => assign (n := n) β₀ pivot false)
    set one  := tail.map (fun β₀ => assign (n := n) β₀ pivot true)
    have hsplit : β ∈ zero ++ one := by
      simpa [leafList, tail, zero, one, pivot, tailAxis] using hβ
    have hpivot_mem : pivot ∈ A.support :=
      pivot_mem_support (n := n) (ℓ := ℓ) (A := A)
    by_cases hipivot : i = pivot
    · -- Если рассматриваем сам `pivot`, то значение определяется веткой.
      subst hipivot
      have hcases : β ∈ zero ∨ β ∈ one := List.mem_append.mp hsplit
      refine hcases.elim ?hzero ?hone
      · intro hzero
        rcases List.mem_map.mp hzero with ⟨β₀, -, rfl⟩
        exact ⟨false, by simp [zero, assign]⟩
      · intro hone
        rcases List.mem_map.mp hone with ⟨β₀, -, rfl⟩
        exact ⟨true, by simp [one, assign]⟩
    · -- Иначе координата принадлежит хвостовой оси.
      have hipivot_ne : i ≠ pivot := hipivot
      have hi_tail : i ∈ tailAxis.support := by
        have : i ∈ A.support.erase pivot :=
          Finset.mem_erase.mpr ⟨hipivot_ne, hi⟩
        simpa [tailAxis, removePivot_support] using this
      have hcases : β ∈ zero ∨ β ∈ one := List.mem_append.mp hsplit
      refine hcases.elim ?hzero ?hone
      · intro hzero
        rcases List.mem_map.mp hzero with ⟨β₀, hβ₀_mem, rfl⟩
        obtain ⟨b, hb⟩ :=
          leafList_value_of_mem_support
            (n := n) (ℓ := ℓ) (A := tailAxis)
            (β := β₀) hβ₀_mem (i := i) hi_tail
        refine ⟨b, ?_⟩
        simp [zero, assign_other (n := n)
          (β := β₀) (i := pivot) (j := i) (b := false), hipivot_ne, hb]
      · intro hone
        rcases List.mem_map.mp hone with ⟨β₀, hβ₀_mem, rfl⟩
        obtain ⟨b, hb⟩ :=
          leafList_value_of_mem_support
            (n := n) (ℓ := ℓ) (A := tailAxis)
            (β := β₀) hβ₀_mem (i := i) hi_tail
        refine ⟨b, ?_⟩
        simp [one, assign_other (n := n)
          (β := β₀) (i := pivot) (j := i) (b := true), hipivot_ne, hb]

/-- Для листа совершеного ствола значение `none` встречается ровно на координатах,
которые не лежат в опорном множестве. -/
lemma leafList_value_none_iff
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) {i : Fin n} :
    β i = none ↔ i ∉ A.support := by
  classical
  constructor
  · intro hvalue hi
    obtain ⟨b, hb⟩ :=
      leafList_value_of_mem_support
        (n := n) (ℓ := ℓ) (A := A) (β := β) hβ (i := i) hi
    have : some b = (none : Option Bool) := by
      simpa [hb] using congrArg id hvalue
    cases this
  · intro hi
    exact leafList_value_of_not_mem_support
      (n := n) (ℓ := ℓ) (A := A) (β := β) hβ (i := i) hi

/-- На координатах оси значение листа никогда не равно `none`. -/
lemma leafList_value_ne_none_iff
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) {i : Fin n} :
    β i ≠ none ↔ i ∈ A.support := by
  classical
  have hnone := leafList_value_none_iff
    (n := n) (ℓ := ℓ) (A := A) (β := β) hβ (i := i)
  constructor
  · intro hne
    by_contra hi
    exact hne (hnone.mpr hi)
  · intro hi
    have hnot : β i = none → False := by
      intro hzero
      have : i ∉ A.support := hnone.mp hzero
      exact this hi
    simpa using hnot

/-- Множество фиксированных координат листа совпадает с `A.fixed`. -/
lemma leafList_fixed_eq
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) :
    ((Finset.univ : Finset (Fin n)).filter fun i => β i = none)
      = A.fixed := by
  classical
  ext i
  simp [Axis.fixed, leafList_value_none_iff (n := n) (ℓ := ℓ)
    (A := A) (β := β) hβ]

/-- Число фиксированных координат листа равно `ℓ`. -/
lemma leafList_fixed_card
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) :
    ((Finset.univ : Finset (Fin n)).filter fun i => β i ≠ none).card = ℓ := by
  classical
  -- Комплемент множества `β i = none` совпадает с опорой `A`.
  have hfilter_eq :
      (Finset.univ.filter fun i : Fin n => β i ≠ none)
        = A.support := by
    ext i
    have hiff := leafList_value_ne_none_iff
      (n := n) (ℓ := ℓ) (A := A) (β := β) hβ (i := i)
    by_cases hi : β i ≠ none
    · have : i ∈ A.support := (hiff.mp hi)
      simp [Finset.mem_filter, hi, this]
    · have hzero : β i = none := by
        classical
        cases hβ' : β i with
        | none => simpa [hβ']
        | some _ => exact (hi (by simpa [hβ'] : β i ≠ none))).elim
      have : i ∉ A.support :=
        (leafList_value_none_iff
          (n := n) (ℓ := ℓ) (A := A) (β := β) hβ (i := i)).mp hzero
      simp [Finset.mem_filter, hi, hzero, this]
  simpa [hfilter_eq, Axis.card (A := A)]

/-- Значение листа на осевой координате, извлечённое из свидетельства
существования.  Определяется через `Classical.choose` и используется при
построении биекций. -/
noncomputable def leafSupportValue
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A)
    {i : Fin n} (hi : i ∈ A.support) : Bool :=
  Classical.choose
    (leafList_value_of_mem_support
      (n := n) (ℓ := ℓ) (A := A) (β := β) hβ (i := i) hi)

lemma leafSupportValue_spec
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A)
    {i : Fin n} (hi : i ∈ A.support) :
    β i = some (leafSupportValue (n := n) (ℓ := ℓ)
      (A := A) (β := β) hβ (i := i) hi) := by
  classical
  exact Classical.choose_spec
    (leafList_value_of_mem_support
      (n := n) (ℓ := ℓ) (A := A) (β := β) hβ (i := i) hi)

/-- Биеция между множеством точек, покрытых листом, и функциями на `A.fixed`. -/
noncomputable def leafMemEquiv
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) :
    {x : BitVec n // mem β x} ≃ (A.fixed → Bool) := by
  classical
  let encodeFun : {x : BitVec n // mem β x} → A.fixed → Bool :=
    fun x i => x.1 i
  let decodeFun : (A.fixed → Bool) → {x : BitVec n // mem β x} :=
    fun f =>
      let g : BitVec n := fun i =>
        if hi : i ∈ A.support then
          leafSupportValue (n := n) (ℓ := ℓ)
            (A := A) (β := β) hβ (i := i) hi
        else
          f ⟨i, by simpa [Axis.fixed, hi]⟩
      have hmem : mem β g := by
        refine (mem_iff (β := β) (x := g)).2 ?_
        intro i b hvalue
        by_cases hi : i ∈ A.support
        · have hspec :=
            leafSupportValue_spec (n := n) (ℓ := ℓ)
              (A := A) (β := β) hβ (i := i) hi
          have hb : b = leafSupportValue (n := n) (ℓ := ℓ)
              (A := A) (β := β) hβ (i := i) hi := by
            have : some b = some (leafSupportValue (n := n) (ℓ := ℓ)
                (A := A) (β := β) hβ (i := i) hi) := by
              simpa [g, hi, hspec] using hvalue
            exact Option.some.inj this
          subst hb
          simp [g, hi, hspec]
        · have hnone :=
            (leafList_value_none_iff
              (n := n) (ℓ := ℓ) (A := A) (β := β) hβ (i := i)).mpr hi
          have : False := by simpa [g, hi, hnone] using hvalue
          exact this.elim
      ⟨g, hmem⟩
  refine
    { toFun := encodeFun
      , invFun := decodeFun
      , left_inv := ?left
      , right_inv := ?right }
  · intro x
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ A.support
    · have hspec :=
        leafSupportValue_spec (n := n) (ℓ := ℓ)
          (A := A) (β := β) hβ (i := i) hi
      have hvalue :=
        (mem_iff (β := β) (x := x.1)).1 x.2 i
          (leafSupportValue (n := n) (ℓ := ℓ)
            (A := A) (β := β) hβ (i := i) hi) hspec
      simp [encodeFun, decodeFun, hi, hvalue]
    · simp [encodeFun, decodeFun, hi]
  · intro f
    funext i
    have hi : (Subtype.val i) ∉ A.support := by
      simpa [Axis.fixed] using i.property
    simp [encodeFun, decodeFun, hi]

/-- Мощность множества точек, покрытых листом, равна `2^(n - ℓ)`. -/
lemma leaf_mem_card
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) :
    Fintype.card {x : BitVec n // mem β x} = Nat.pow 2 (n - ℓ) := by
  classical
  have := Fintype.card_congr
    (leafMemEquiv (n := n) (ℓ := ℓ) (A := A) (β := β) hβ)
  have hfixed_card : Fintype.card (A.fixed → Bool)
      = Nat.pow 2 (A.fixed.card) := by
    simp [Fintype.card_fun]
  have hcard_fixed : A.fixed.card = n - ℓ := A.card_fixed
  simpa [this, hfixed_card, hcard_fixed]

/-- Каноническая точка подкуба-листа: берём предобраз функции, постоянно
равной `false`, в биеции `leafMemEquiv`.  Эта точка используется в качестве
репрезентативного элемента класса. -/
noncomputable def leafPoint
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) : BitVec n :=
  ((leafMemEquiv (n := n) (ℓ := ℓ) (A := A) (β := β) hβ).symm
    (fun _ => false)).1

lemma leafPoint_mem
    {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) :
    mem β (leafPoint (n := n) (ℓ := ℓ) (A := A) (β := β) hβ) := by
  classical
  exact ((leafMemEquiv (n := n) (ℓ := ℓ) (A := A) (β := β) hβ).symm
    (fun _ => false)).2

/-- Свойство «функция постоянна на каждом листе».  Оно означает, что значения
`f` зависят только от выбора ветви в совершенном стволе. -/
def constantOnLeaves
    {ℓ : Nat} (A : Axis n ℓ) (f : BitVec n → Bool) : Prop :=
  ∀ ⦃β : Subcube n⦄ (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A)
    {x y : BitVec n}, mem β x → mem β y → f x = f y

/-- Значение функции `f` на листе определяется через каноническую точку. -/
noncomputable def leafValue
    {ℓ : Nat} (A : Axis n ℓ) (f : BitVec n → Bool)
    {β : Subcube n} (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) : Bool :=
  f (leafPoint (n := n) (ℓ := ℓ) (A := A) (β := β) hβ)

lemma leafValue_eq_of_mem
    {ℓ : Nat} {A : Axis n ℓ} {f : BitVec n → Bool}
    (hconst : constantOnLeaves (n := n) (ℓ := ℓ) A f)
    {β : Subcube n} (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A)
    {x : BitVec n} (hx : mem β x) :
    leafValue (n := n) (ℓ := ℓ) (A := A) (f := f) hβ = f x := by
  classical
  have hcanonical := leafPoint_mem (n := n) (ℓ := ℓ) (A := A)
    (β := β) hβ
  have := hconst hβ hcanonical hx
  simpa [leafValue, leafPoint] using this.symm

/--
  Список `leafList` действительно покрывает весь булев куб: для любого `x`
  найдётся лист, который согласован с `x` на всех фиксированных координатах.
-/
lemma leafList_covers (A : Axis n ℓ) (x : BitVec n) :
    covered (leafList (n := n) (ℓ := ℓ) A) x := by
  classical
  induction ℓ with
  | zero =>
      -- База: единственный лист «всё свободно» покрывает любой `x`.
      refine ⟨_, by simp [leafList], ?_⟩
      refine (mem_iff (β := fun _ => (none : Option Bool)) (x := x)).2 ?_
      intro i b hi
      -- Противоречие: в полностью свободном подкубе нет фиксированных значений.
      cases hi
  | succ ℓ ih =>
      -- Индукция по числу свободных координат.
      classical
      set pivot := pivot (n := n) (ℓ := ℓ) A
      set tailAxis := removePivot (n := n) (ℓ := ℓ) A
      set tail := leafList (n := n) (ℓ := ℓ) tailAxis
      set zero := tail.map (fun β => assign (n := n) β pivot false)
      set one  := tail.map (fun β => assign (n := n) β pivot true)
      -- По предположению индукции хвостовая ось полностью покрывает `x`.
      obtain ⟨β₀, hβ₀_mem, hβ₀_cov⟩ := ih (A := tailAxis) (x := x)
      have hβ₀_free : β₀ pivot = (none : Option Bool) :=
        leafList_value_of_not_mem_support
          (n := n) (ℓ := ℓ) (A := tailAxis)
          (β := β₀) hβ₀_mem (i := pivot)
          (by
            -- В хвостовой оси pivot отсутствует по построению.
            intro hcontr
            rcases Finset.mem_erase.mp hcontr with ⟨hpivot, _⟩
            exact hpivot rfl)
      -- В зависимости от бита `x pivot` выбираем левую или правую ветвь.
      cases hbit : x pivot with
      | false =>
          refine ⟨assign (n := n) β₀ pivot false, ?_, ?_⟩
          · -- Лист лежит в левой половине (`pivot = 0`).
            have hmap : assign (n := n) β₀ pivot false ∈ zero :=
              List.mem_map.mpr ⟨β₀, hβ₀_mem, rfl⟩
            have hcover : assign (n := n) β₀ pivot false ∈ zero ++ one :=
              List.mem_append.mpr (Or.inl hmap)
            simpa [leafList, tail, pivot, zero, one] using hcover
          · -- Убеждаемся, что точка действительно принадлежит выбранному листу.
            have hmem :=
              (mem_assign_of_none (n := n) (β := β₀) (i := pivot)
                (b := false) hβ₀_free x).2 ⟨hβ₀_cov, hbit⟩
            simpa [leafList, tail, pivot, zero, one]
              using hmem
      | true =>
          refine ⟨assign (n := n) β₀ pivot true, ?_, ?_⟩
          · have hmap : assign (n := n) β₀ pivot true ∈ one :=
              List.mem_map.mpr ⟨β₀, hβ₀_mem, rfl⟩
            have hcover : assign (n := n) β₀ pivot true ∈ zero ++ one :=
              List.mem_append.mpr (Or.inr hmap)
            simpa [leafList, tail, pivot, zero, one] using hcover
          · have hmem :=
              (mem_assign_of_none (n := n) (β := β₀) (i := pivot)
                (b := true) hβ₀_free x).2 ⟨hβ₀_cov, hbit⟩
            simpa [leafList, tail, pivot, zero, one]
              using hmem

/-- Логическая форма утверждения о покрытии: булев индикатор всегда истинен. -/
lemma leafList_coveredB (A : Axis n ℓ) (x : BitVec n) :
    coveredB (leafList (n := n) (ℓ := ℓ) A) x = true := by
  have h := leafList_covers (n := n) (ℓ := ℓ) (A := A) (x := x)
  exact (covered_iff (n := n)
    (Rset := leafList (n := n) (ℓ := ℓ) A) (x := x)).1 h

/-- Ошибка аппроксимации нулевая, если выбрать все листья ствола. -/
lemma errU_leafList_constTrue (A : Axis n ℓ) :
    errU (fun _ : BitVec n => true) (leafList (n := n) (ℓ := ℓ) A) = 0 := by
  apply errU_eq_zero_of_agree
  intro x
  have hcov := leafList_coveredB (n := n) (ℓ := ℓ) (A := A) (x := x)
  simp [hcov]

/--
  Для дальнейшей работы с частичными сертификатами нам понадобится явное
  описание того листа совершеного ствола, который соответствует конкретной
  точке `x`.  Функция `leafForPoint` строит этот лист, последовательно
  повторяя ветвление ствола и фиксируя значения запросных переменных так же,
  как это делает путь, соответствующий `x`.
-/
noncomputable def leafForPoint :
    ∀ {ℓ : Nat}, Axis n ℓ → BitVec n → Subcube n
| 0, _, _ => fun _ => (none : Option Bool)
| Nat.succ ℓ, A, x =>
    let pivot := pivot (n := n) (ℓ := ℓ) A
    let tailAxis := removePivot (n := n) (ℓ := ℓ) A
    let tailLeaf := leafForPoint (n := n) (ℓ := ℓ) tailAxis x
    assign (n := n) tailLeaf pivot (x pivot)

/--
  Построенный лист действительно входит в список `leafList`.  Доказательство
  идёт по индукции по числу свободных координат: на каждом шаге значение
  очередного `pivot` определяет, в какую половину списка попадает лист.
-/
lemma leafForPoint_mem :
    ∀ {ℓ : Nat} (A : Axis n ℓ) (x : BitVec n),
      leafForPoint (n := n) (ℓ := ℓ) A x
        ∈ leafList (n := n) (ℓ := ℓ) A
| 0, A, x => by
    -- При `ℓ = 0` список содержит единственный полностью свободный подкуб.
    simp [leafForPoint, leafList]
| Nat.succ ℓ, A, x => by
    classical
    -- Обозначения для хвоста и соответствующих списков.
    set pivot := pivot (n := n) (ℓ := ℓ) A
    set tailAxis := removePivot (n := n) (ℓ := ℓ) A
    set tail := leafList (n := n) (ℓ := ℓ) tailAxis
    set zero := tail.map (fun β => assign (n := n) β pivot false)
    set one  := tail.map (fun β => assign (n := n) β pivot true)
    have htail :
        leafForPoint (n := n) (ℓ := ℓ) tailAxis x ∈ tail :=
      by simpa [tail] using leafForPoint_mem (n := n) (ℓ := ℓ)
        (A := tailAxis) (x := x)
    -- Разбираем значение бита `pivot` и попадаем в соответствующую половину.
    cases hbit : x pivot with
    | false =>
        have hzero : assign (n := n)
            (leafForPoint (n := n) (ℓ := ℓ) tailAxis x)
            pivot false ∈ zero := by
          refine List.mem_map.mpr ?_
          exact ⟨_, htail, rfl⟩
        have hmem :
            assign (n := n)
              (leafForPoint (n := n) (ℓ := ℓ) tailAxis x)
              pivot (x pivot) ∈ zero := by
          simpa [zero, hbit]
            using hzero
        -- В заключение отмечаем, что `leafList` склеивает левую и правую части.
        have : assign (n := n)
              (leafForPoint (n := n) (ℓ := ℓ) tailAxis x)
              pivot (x pivot)
                ∈ zero ++ one :=
          List.mem_append.mpr (Or.inl hmem)
        simpa [leafForPoint, pivot, tailAxis, tail, zero, one]
          using this
    | true =>
        have hone : assign (n := n)
            (leafForPoint (n := n) (ℓ := ℓ) tailAxis x)
            pivot true ∈ one := by
          refine List.mem_map.mpr ?_
          exact ⟨_, htail, rfl⟩
        have hmem :
            assign (n := n)
              (leafForPoint (n := n) (ℓ := ℓ) tailAxis x)
              pivot (x pivot) ∈ one := by
          simpa [one, hbit]
            using hone
        have : assign (n := n)
              (leafForPoint (n := n) (ℓ := ℓ) tailAxis x)
              pivot (x pivot)
                ∈ zero ++ one :=
          List.mem_append.mpr (Or.inr hmem)
        simpa [leafForPoint, pivot, tailAxis, tail, zero, one]
          using this

/--
  Построенный лист согласован с исходной точкой `x`: она удовлетворяет всем
  фиксированным координатам подкуба, возникающим вдоль пути в стволе.
-/
lemma mem_leafForPoint :
    ∀ {ℓ : Nat} (A : Axis n ℓ) (x : BitVec n),
      mem (leafForPoint (n := n) (ℓ := ℓ) A x) x
| 0, A, x => by
    -- При пустой оси подкуб не фиксирует ни одной координаты.
    refine (mem_iff (β := fun _ => (none : Option Bool)) (x := x)).2 ?_
    intro i b hi
    -- Противоречие: в полностью свободном подкубе нет фиксированных значений.
    cases hi
| Nat.succ ℓ, A, x => by
    classical
    set pivot := pivot (n := n) (ℓ := ℓ) A
    set tailAxis := removePivot (n := n) (ℓ := ℓ) A
    set tailLeaf := leafForPoint (n := n) (ℓ := ℓ) tailAxis x
    have htail_mem : mem tailLeaf x :=
      mem_leafForPoint (n := n) (ℓ := ℓ)
        (A := tailAxis) (x := x)
    -- Узнаём, что `pivot` действительно отсутствует в хвостовой оси.
    have hpivot_not_mem : pivot ∉ tailAxis.support := by
      classical
      -- В `removePivot` опорное множество равно `erase pivot`.
      simpa [tailAxis, removePivot]
    -- Значит, значение хвостового листа на `pivot` равно `none`.
    have htail_free : tailLeaf pivot = (none : Option Bool) := by
      have htail_in : tailLeaf ∈
          leafList (n := n) (ℓ := ℓ) tailAxis :=
        leafForPoint_mem (n := n) (ℓ := ℓ)
          (A := tailAxis) (x := x)
      simpa [tailLeaf]
        using leafList_value_of_not_mem_support
          (n := n) (ℓ := ℓ) (A := tailAxis)
          (β := tailLeaf) htail_in (i := pivot) hpivot_not_mem
    -- Теперь достаточно применить лемму о `assign`, фиксирующем значение pivot.
    have hassign :
        mem (assign (n := n) tailLeaf pivot (x pivot)) x := by
      have := (mem_assign_of_none (n := n)
        (β := tailLeaf) (i := pivot) (b := x pivot)
        htail_free x).2 ?_
      · simpa using this
      · exact ⟨htail_mem, rfl⟩
    simpa [leafForPoint, tailLeaf, pivot, tailAxis]
      using hassign

/--
  Любой лист, покрывающий `x`, совпадает с `leafForPoint`.  Таким образом,
  у каждой точки есть единственный представитель в списке `leafList`.
-/
lemma leafForPoint_unique :
    ∀ {ℓ : Nat} (A : Axis n ℓ) {β : Subcube n}
      (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A)
      {x : BitVec n} (hx : mem β x),
        β = leafForPoint (n := n) (ℓ := ℓ) A x
| 0, A, β, hβ, x, hx => by
    -- База: список из одного элемента, равного `leafForPoint`.
    simp [leafList, leafForPoint] at hβ
    simpa [leafForPoint, hβ]
| Nat.succ ℓ, A, β, hβ, x, hx => by
    classical
    set pivot := pivot (n := n) (ℓ := ℓ) A
    set tailAxis := removePivot (n := n) (ℓ := ℓ) A
    set tail := leafList (n := n) (ℓ := ℓ) tailAxis
    set zero := tail.map (fun β => assign (n := n) β pivot false)
    set one  := tail.map (fun β => assign (n := n) β pivot true)
    have hpivot_not_mem : pivot ∉ tailAxis.support := by
      classical
      simpa [tailAxis, removePivot]
    -- Разбираем ветвление по значению `x pivot`.
    cases hbit : x pivot with
    | false =>
        -- Выясняем, в какую половину списка попадает данный лист.
        have hcases : β ∈ zero ∨ β ∈ one := by
          have : β ∈ zero ++ one := by
            simpa [leafList, zero, one]
              using hβ
          exact List.mem_append.mp this
        -- Убедимся, что лист не может находиться в правой половине.
        have hnot_one : β ∉ one := by
          intro hone
          rcases List.mem_map.mp hone with ⟨β₀, hβ₀, hβ_eq⟩
          -- Для листов правой половины `x pivot = true`, что противоречит `hbit`.
          have hfree : β₀ pivot = (none : Option Bool) := by
            have hβ₀_free :=
              leafList_value_of_not_mem_support
                (n := n) (ℓ := ℓ) (A := tailAxis)
                (β := β₀) hβ₀ (i := pivot) hpivot_not_mem
            simpa [tailAxis] using hβ₀_free
          have hx_true : x pivot = true := by
            have hx_assign := (mem_assign_of_none (n := n)
              (β := β₀) (i := pivot) (b := true) hfree x).1 ?_
            · exact hx_assign.2
            · simpa [hβ_eq, assign] using hx
          -- Противоречие `false = true`.
          simpa [hbit] using hx_true
        -- Значит, рассматриваем только левую половину.
        rcases hcases with hzero | hone
        · rcases List.mem_map.mp hzero with ⟨β₀, hβ₀, hβ_eq⟩
          -- Получаем условия на хвостовой лист через лемму об assign.
          have hfree : β₀ pivot = (none : Option Bool) := by
            have hβ₀_free :=
              leafList_value_of_not_mem_support
                (n := n) (ℓ := ℓ) (A := tailAxis)
                (β := β₀) hβ₀ (i := pivot) hpivot_not_mem
            simpa [tailAxis] using hβ₀_free
          have hconditions := (mem_assign_of_none (n := n)
              (β := β₀) (i := pivot) (b := false) hfree x).1 ?_
          · obtain ⟨hmem_tail, hx_false⟩ := hconditions
            -- Индуктивное предположение для хвоста.
            have hrec := leafForPoint_unique (n := n) (ℓ := ℓ)
              (A := tailAxis) (β := β₀) hβ₀ (x := x) hmem_tail
            have htail : leafForPoint (n := n) (ℓ := ℓ) tailAxis x = β₀ :=
              by simpa using hrec.symm
            -- Завершаем: оба листа — это одно и то же присвоение pivot = false.
            simp [leafForPoint, pivot, tailAxis, hbit, hβ_eq, htail]
          · simpa [hβ_eq, assign] using hx
        · cases hnot_one hone
    | true =>
        -- Случай зеркален предыдущему.
        have hcases : β ∈ zero ∨ β ∈ one := by
          have : β ∈ zero ++ one := by
            simpa [leafList, zero, one]
              using hβ
          exact List.mem_append.mp this
        -- Лист не может находиться в левой половине, иначе `x pivot = false`.
        have hnot_zero : β ∉ zero := by
          intro hzero
          rcases List.mem_map.mp hzero with ⟨β₀, hβ₀, hβ_eq⟩
          have hfree : β₀ pivot = (none : Option Bool) := by
            have hβ₀_free :=
              leafList_value_of_not_mem_support
                (n := n) (ℓ := ℓ) (A := tailAxis)
                (β := β₀) hβ₀ (i := pivot) hpivot_not_mem
            simpa [tailAxis] using hβ₀_free
          have hx_false : x pivot = false := by
            have hx_assign := (mem_assign_of_none (n := n)
              (β := β₀) (i := pivot) (b := false) hfree x).1 ?_
            · exact hx_assign.2
            · simpa [hβ_eq, assign] using hx
          simpa [hbit] using hx_false
        rcases hcases with hzero | hone
        · cases hnot_zero hzero
        · rcases List.mem_map.mp hone with ⟨β₀, hβ₀, hβ_eq⟩
          have hfree : β₀ pivot = (none : Option Bool) := by
            have hβ₀_free :=
              leafList_value_of_not_mem_support
                (n := n) (ℓ := ℓ) (A := tailAxis)
                (β := β₀) hβ₀ (i := pivot) hpivot_not_mem
            simpa [tailAxis] using hβ₀_free
          have hconditions := (mem_assign_of_none (n := n)
              (β := β₀) (i := pivot) (b := true) hfree x).1 ?_
          · obtain ⟨hmem_tail, hx_true⟩ := hconditions
            have hrec := leafForPoint_unique (n := n) (ℓ := ℓ)
              (A := tailAxis) (β := β₀) hβ₀ (x := x) hmem_tail
            have htail : leafForPoint (n := n) (ℓ := ℓ) tailAxis x = β₀ :=
              by simpa using hrec.symm
            simp [leafForPoint, pivot, tailAxis, hbit, hβ_eq, htail]
          · simpa [hβ_eq, assign] using hx

/-- Эквивалентность «лист соответствует точке `x`» ↔ «`x` принадлежит листу». -/
lemma leafForPoint_eq_iff_mem {ℓ : Nat} (A : Axis n ℓ)
    {β : Subcube n} (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A)
    {x : BitVec n} :
    leafForPoint (n := n) (ℓ := ℓ) A x = β ↔ mem β x := by
  constructor
  · intro hleaf
    -- Подставляем равенство листов в известный факт о принадлежности `x`.
    have hmem := mem_leafForPoint (n := n) (ℓ := ℓ) (A := A) (x := x)
    simpa [hleaf]
      using hmem
  · intro hx
    -- Единственность листа, содержащего `x`, даёт требуемое равенство.
    exact (leafForPoint_unique (n := n) (ℓ := ℓ) (A := A)
      (β := β) hβ (x := x) hx).symm

/--
  Удобная форма свойства покрытия: для любого списка `S`, состоящего из листьев
  совершеного ствола, булев индикатор `coveredB S x` эквивалентен факту, что
  лист `leafForPoint A x` присутствует в `S`.
-/
lemma coveredB_of_leafSubset
    {ℓ : Nat} (A : Axis n ℓ) (S : List (Subcube n))
    (hsubset : ∀ {β : Subcube n}, β ∈ S →
      β ∈ leafList (n := n) (ℓ := ℓ) A) (x : BitVec n) :
    coveredB S x = true ↔ leafForPoint (n := n) (ℓ := ℓ) A x ∈ S := by
  classical
  constructor
  · intro hcov
    rcases List.any_eq_true.mp hcov with ⟨β, hβS, hmem⟩
    have hβleaf := hsubset hβS
    have hunique := leafForPoint_unique (n := n) (ℓ := ℓ)
      (A := A) (β := β) hβleaf (x := x) hmem
    simpa [hunique]
      using hβS
  · intro hleaf
    have hmem := mem_leafForPoint (n := n) (ℓ := ℓ) (A := A) (x := x)
    exact List.any_eq_true.mpr ⟨_, hleaf, hmem⟩

/--
  Удобная вспомогательная конструкция: фильтрация списка листьев по булевому
  предикату `g`.  Этот список естественным образом используется как словарь
  селекторов при построении частичного сертификата.
-/
def leafSelector {ℓ : Nat} (A : Axis n ℓ) (g : Subcube n → Bool) :
    List (Subcube n) :=
  (leafList (n := n) (ℓ := ℓ) A).filter (fun β => g β)

lemma leafSelector_subset {ℓ : Nat} (A : Axis n ℓ)
    (g : Subcube n → Bool) {β : Subcube n} :
    β ∈ leafSelector (n := n) (ℓ := ℓ) A g →
      β ∈ leafList (n := n) (ℓ := ℓ) A := by
  classical
  intro hβ
  have := List.mem_filter.mp hβ
  exact this.1

/--
  Раскрытие булева индикатора покрытия для списка `leafSelector A g`.  На входе
  мы получаем точку `x`, на выходе — значение предиката `g` на листе, который
  соответствует пути `x` в совершенном стволе.
-/
lemma coveredB_leafSelector {ℓ : Nat} (A : Axis n ℓ)
    (g : Subcube n → Bool) (x : BitVec n) :
    coveredB (leafSelector (n := n) (ℓ := ℓ) A g) x = true ↔
      g (leafForPoint (n := n) (ℓ := ℓ) A x) = true := by
  classical
  have hsubset :=
    leafSelector_subset (n := n) (ℓ := ℓ) (A := A) (g := g)
  have hcovered :=
    coveredB_of_leafSubset (n := n) (ℓ := ℓ) (A := A)
      (S := leafSelector (n := n) (ℓ := ℓ) A g) hsubset (x := x)
  -- Преобразуем условие принадлежности через явное описание фильтрации.
  constructor
  · intro h
    have hmem := (hcovered.1 h)
    have hfilter := List.mem_filter.mp hmem
    exact hfilter.2
  · intro h
    -- Список `leafSelector` содержит лист тогда и только тогда, когда `g = true`.
    have hmem :
        leafForPoint (n := n) (ℓ := ℓ) A x
            ∈ leafSelector (n := n) (ℓ := ℓ) A g := by
      refine List.mem_filter.mpr ?_
      constructor
      · -- Лист всегда присутствует в полном списке `leafList`.
        exact leafForPoint_mem (n := n) (ℓ := ℓ) (A := A) (x := x)
      · simpa using h
    exact (hcovered.2 hmem)

/--
  Подмножество листьев совершенного ствола, на которых значение `f` расходится
  с предикатом `g`.  В дальнейшем мы покажем, что ошибка аппроксимации равна
  доле таких листьев.
-/
def badLeafSet {ℓ : Nat} (A : Axis n ℓ) (f : BitVec n → Bool)
    (g : Subcube n → Bool) : Finset (Subcube n) :=
  ((leafList (n := n) (ℓ := ℓ) A).toFinset.filter fun β =>
      ∃ hβ : β ∈ leafList (n := n) (ℓ := ℓ) A,
        leafValue (n := n) (ℓ := ℓ) (A := A) (f := f) hβ ≠ g β)

lemma mem_badLeafSet {ℓ : Nat} (A : Axis n ℓ) (f : BitVec n → Bool)
    (g : Subcube n → Bool) {β : Subcube n} :
    β ∈ badLeafSet (n := n) (ℓ := ℓ) A f g ↔
      ∃ hβ : β ∈ leafList (n := n) (ℓ := ℓ) A,
        leafValue (n := n) (ℓ := ℓ) (A := A) (f := f) hβ ≠ g β := by
  classical
  constructor
  · intro hβ
    rcases Finset.mem_filter.mp hβ with ⟨_, hβ_bad⟩
    exact hβ_bad
  · rintro ⟨hβ_leaf, hβ_bad⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · exact List.mem_toFinset.mpr hβ_leaf
    · exact ⟨hβ_leaf, hβ_bad⟩

/--
  Все точки булева куба, принадлежащие листу `β`, представлены как подмножество
  полного множества `BitVec n`.  Мы фиксируем это множество в виде `Finset`,
  чтобы затем вычислять мощности и объединения.
-/
def leafPoints {ℓ : Nat} (A : Axis n ℓ) (β : Subcube n) :
    Finset (BitVec n) :=
  (Finset.univ.filter fun x => mem β x)

lemma leafPoints_card {ℓ : Nat} (A : Axis n ℓ)
    {β : Subcube n} (hβ : β ∈ leafList (n := n) (ℓ := ℓ) A) :
    (leafPoints (n := n) (ℓ := ℓ) (A := A) β).card
      = Nat.pow 2 (n - ℓ) := by
  classical
  -- Сравним мощность фильтра с подтипом `{x // mem β x}`.
  have hsubtype :
      Fintype.card {x : BitVec n // x ∈ leafPoints (n := n) (ℓ := ℓ) (A := A) β}
        = (leafPoints (n := n) (ℓ := ℓ) (A := A) β).card := by
    simpa [leafPoints] using
      (Fintype.card_subtype (s := Finset.univ.filter fun x => mem β x))
  -- Опишем явную биекцию между двумя подтипами.
  let e : {x : BitVec n // x ∈ leafPoints (n := n) (ℓ := ℓ) (A := A) β}
      ≃ {x : BitVec n // mem β x} :=
    { toFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
      , invFun := fun x =>
          ⟨x.1,
            by
              have hx : x.1 ∈ (Finset.univ : Finset (BitVec n)) := by simp
              exact Finset.mem_filter.mpr ⟨hx, x.2⟩⟩
      , left_inv := by
          intro x; ext <;> rfl
      , right_inv := by
          intro x; ext <;> rfl }
  have hcard := leaf_mem_card (n := n) (ℓ := ℓ)
    (A := A) (β := β) hβ
  have hcongr := Fintype.card_congr e
  have hcard' :
      Fintype.card {x : BitVec n // x ∈ leafPoints (n := n) (ℓ := ℓ) (A := A) β}
        = Nat.pow 2 (n - ℓ) := by
    simpa [hcongr] using hcard
  -- Объединяем равенства кардинальностей.
  simpa [hsubtype] using hcard'

lemma leafPoints_disjoint {ℓ : Nat} (A : Axis n ℓ)
    {β₁ β₂ : Subcube n}
    (hβ₁ : β₁ ∈ leafList (n := n) (ℓ := ℓ) A)
    (hβ₂ : β₂ ∈ leafList (n := n) (ℓ := ℓ) A)
    (hne : β₁ ≠ β₂) :
    Disjoint (leafPoints (n := n) (ℓ := ℓ) (A := A) β₁)
      (leafPoints (n := n) (ℓ := ℓ) (A := A) β₂) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro x hx₁ hx₂
  have hx₁' := (Finset.mem_filter.mp hx₁).2
  have hx₂' := (Finset.mem_filter.mp hx₂).2
  -- Вычисляем уникальный лист, покрывающий `x`.
  have huniq₁ :=
    leafForPoint_unique (n := n) (ℓ := ℓ) (A := A)
      (β := β₁) hβ₁ (x := x) hx₁'
  have huniq₂ :=
    leafForPoint_unique (n := n) (ℓ := ℓ) (A := A)
      (β := β₂) hβ₂ (x := x) hx₂'
  exact hne (by simpa [huniq₁, huniq₂])

/--
  Если объединить множества `leafPoints` по произвольному подмножеству листьев,
  то мощность объединения равна числу выбранных листьев, умноженному на
  `2^(n - ℓ)`.  Эта формула будет использоваться для перевода оценок по листам
  в подсчёт точек булева куба.
-/
lemma leafPoints_union_card {ℓ : Nat} (A : Axis n ℓ)
    (badLeaves : Finset (Subcube n))
    (hsubset : badLeaves ⊆ (leafList (n := n) (ℓ := ℓ) A).toFinset) :
    (Finset.biUnion badLeaves (fun β _ =>
        leafPoints (n := n) (ℓ := ℓ) (A := A) β)).card
      = badLeaves.card * Nat.pow 2 (n - ℓ) := by
  classical
  -- Попарная дизъюнктность множества точек разных листьев.
  have hdisjoint :
      ∀ β₁ ∈ badLeaves, ∀ β₂ ∈ badLeaves, β₁ ≠ β₂ →
        Disjoint (leafPoints (n := n) (ℓ := ℓ) (A := A) β₁)
          (leafPoints (n := n) (ℓ := ℓ) (A := A) β₂) := by
    intro β₁ hβ₁ β₂ hβ₂ hneq
    have hβ₁_leaf : β₁ ∈ leafList (n := n) (ℓ := ℓ) A := by
      have := hsubset hβ₁
      exact List.mem_toFinset.mp this
    have hβ₂_leaf : β₂ ∈ leafList (n := n) (ℓ := ℓ) A := by
      have := hsubset hβ₂
      exact List.mem_toFinset.mp this
    exact leafPoints_disjoint (n := n) (ℓ := ℓ) (A := A)
      hβ₁_leaf hβ₂_leaf hneq
  -- Выражаем мощность объединения через сумму мощностей слагаемых.
  have hcard :=
    Finset.card_biUnion
      (s := badLeaves)
      (t := fun β => leafPoints (n := n) (ℓ := ℓ) (A := A) β)
      hdisjoint
  -- Каждое слагаемое в сумме равно `2^(n - ℓ)`.
  have hconst :
      ∀ β ∈ badLeaves,
        (leafPoints (n := n) (ℓ := ℓ) (A := A) β).card
          = Nat.pow 2 (n - ℓ) := by
    intro β hβ
    have hβ_leaf : β ∈ leafList (n := n) (ℓ := ℓ) A := by
      have := hsubset hβ
      exact List.mem_toFinset.mp this
    simpa using
      (leafPoints_card (n := n) (ℓ := ℓ) (A := A)
        (β := β) hβ_leaf)
  have hsum :
      ∑ β in badLeaves,
          (leafPoints (n := n) (ℓ := ℓ) (A := A) β).card
        = badLeaves.card * Nat.pow 2 (n - ℓ) := by
    refine Finset.sum_congr rfl ?_
    intro β hβ
    simp [hconst β hβ]
  simpa [hsum] using hcard.symm

/--
  Преобразование ошибки на уровне точек в условие на листе: несоответствие
  возникает тогда и только тогда, когда значение `f` на рассматриваемом листе
  расходится с предикатом `g` для этого же листа.
-/
lemma mismatch_iff_leafValue {ℓ : Nat} (A : Axis n ℓ)
    (f : BitVec n → Bool) (g : Subcube n → Bool)
    (hconst : constantOnLeaves (n := n) (ℓ := ℓ) A f)
    (x : BitVec n) :
    let β := leafForPoint (n := n) (ℓ := ℓ) A x
    let hβ := leafForPoint_mem (n := n) (ℓ := ℓ) (A := A) (x := x)
    let selectors := leafSelector (n := n) (ℓ := ℓ) A g
    f x ≠ coveredB selectors x ↔
      leafValue (n := n) (ℓ := ℓ) (A := A) (f := f) hβ ≠ g β := by
  classical
  intro β hβ selectors
  have hx_leaf := hβ
  have hf_leaf :
      leafValue (n := n) (ℓ := ℓ) (A := A) (f := f) hx_leaf = f x :=
    leafValue_eq_of_mem (n := n) (ℓ := ℓ) (A := A)
      (f := f) hconst (β := β) (hβ := hx_leaf) (x := x) hβ
  have hcovered :=
    coveredB_leafSelector (n := n) (ℓ := ℓ) (A := A)
      (g := g) (x := x)
  -- Разбираем два возможных значения предиката `g` на листе.
  cases hgb : g β with
  | false =>
      have hfalse : coveredB selectors x = false := by
        -- Значение `true` невозможно, иначе `g β = true` по лемме выше.
        have hnot : coveredB selectors x ≠ true := by
          intro htrue
          have := (hcovered.1 htrue)
          simpa [hgb] using this
        cases hvalue : coveredB selectors x with
        | false => rfl
        | true => exact (hnot rfl).elim
      simp [selectors, hf_leaf, hgb, hfalse]
  | true =>
      have htrue : coveredB selectors x = true :=
        (hcovered.2 hgb)
      simp [selectors, hf_leaf, hgb, htrue]

lemma mismatches_as_union {ℓ : Nat} (A : Axis n ℓ)
    (f : BitVec n → Bool) (g : Subcube n → Bool)
    (hconst : constantOnLeaves (n := n) (ℓ := ℓ) A f) :
    let selectors := leafSelector (n := n) (ℓ := ℓ) A g
    (Finset.univ.filter fun x : BitVec n =>
        f x ≠ coveredB selectors x)
      = Finset.biUnion (badLeafSet (n := n) (ℓ := ℓ) A f g)
          (fun β _ => leafPoints (n := n) (ℓ := ℓ) (A := A) β) := by
  classical
  intro selectors
  ext x
  constructor
  · intro hx
    set β := leafForPoint (n := n) (ℓ := ℓ) A x
    have hβ_mem := leafForPoint_mem (n := n) (ℓ := ℓ) (A := A) (x := x)
    have hx_prop : f x ≠ coveredB selectors x :=
      (Finset.mem_filter.mp hx).2
    have hx_equiv :
        f x ≠ coveredB selectors x ↔
          leafValue (n := n) (ℓ := ℓ) (A := A) (f := f) hβ_mem ≠ g β := by
      simpa [β, selectors]
        using (mismatch_iff_leafValue (n := n) (ℓ := ℓ) (A := A)
          (f := f) (g := g) hconst (x := x))
    have hβ_bad : leafValue (n := n) (ℓ := ℓ) (A := A) (f := f) hβ_mem
        ≠ g β := (hx_equiv.1 hx_prop)
    have hx_points :
        x ∈ leafPoints (n := n) (ℓ := ℓ) (A := A) β := by
      have hx_univ : x ∈ (Finset.univ : Finset (BitVec n)) := by simp
      exact Finset.mem_filter.mpr ⟨hx_univ, hβ_mem⟩
    have hβ_bad_set : β ∈ badLeafSet (n := n) (ℓ := ℓ) A f g :=
      (mem_badLeafSet (n := n) (ℓ := ℓ) (A := A)
        (f := f) (g := g) (β := β)).2 ⟨hβ_mem, hβ_bad⟩
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨β, hβ_bad_set, hx_points⟩
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨β, hβ_bad, hx_leaf⟩
    rcases (mem_badLeafSet (n := n) (ℓ := ℓ) (A := A)
      (f := f) (g := g) (β := β)).1 hβ_bad with ⟨hβ_mem, hβ_bad_val⟩
    have hx_mem : mem β x := (Finset.mem_filter.mp hx_leaf).2
    have hleaf :=
      leafForPoint_unique (n := n) (ℓ := ℓ) (A := A)
        (β := β) hβ_mem (x := x) hx_mem
    have hx_equiv :
        f x ≠ coveredB selectors x ↔
          leafValue (n := n) (ℓ := ℓ) (A := A) (f := f)
            (leafForPoint_mem (n := n) (ℓ := ℓ) (A := A) (x := x))
            ≠ g (leafForPoint (n := n) (ℓ := ℓ) A x) := by
      simpa [selectors]
        using (mismatch_iff_leafValue (n := n) (ℓ := ℓ) (A := A)
          (f := f) (g := g) hconst (x := x))
    have hx_bad :
        leafValue (n := n) (ℓ := ℓ) (A := A) (f := f)
          (leafForPoint_mem (n := n) (ℓ := ℓ) (A := A) (x := x))
          ≠ g (leafForPoint (n := n) (ℓ := ℓ) A x) := by
      simpa [β, hleaf] using hβ_bad_val
    have hx_prop : f x ≠ coveredB selectors x :=
      (hx_equiv.2 hx_bad)
    have hx_univ : x ∈ (Finset.univ : Finset (BitVec n)) := by simp
    exact Finset.mem_filter.mpr ⟨hx_univ, hx_prop⟩

lemma mismatches_card {ℓ : Nat} (A : Axis n ℓ)
    (f : BitVec n → Bool) (g : Subcube n → Bool)
    (hconst : constantOnLeaves (n := n) (ℓ := ℓ) A f) :
    let selectors := leafSelector (n := n) (ℓ := ℓ) A g
    ((Finset.univ.filter fun x : BitVec n =>
        f x ≠ coveredB selectors x).card)
      = (badLeafSet (n := n) (ℓ := ℓ) A f g).card
          * Nat.pow 2 (n - ℓ) := by
  classical
  intro selectors
  -- Переписываем фильтр через объединение листовых множеств.
  have hrewrite :=
    mismatches_as_union (n := n) (ℓ := ℓ) (A := A)
      (f := f) (g := g) hconst
  -- Гарантия попарной дизъюнктности для применения `card_biUnion`.
  have hdisjoint :
      ∀ (β₁ ∈ badLeafSet (n := n) (ℓ := ℓ) A f g)
        (β₂ ∈ badLeafSet (n := n) (ℓ := ℓ) A f g), β₁ ≠ β₂ →
          Disjoint (leafPoints (n := n) (ℓ := ℓ) (A := A) β₁)
            (leafPoints (n := n) (ℓ := ℓ) (A := A) β₂) := by
    intro β₁ hβ₁ β₂ hβ₂ hneq
    rcases (mem_badLeafSet (n := n) (ℓ := ℓ) (A := A)
      (f := f) (g := g) (β := β₁)).1 hβ₁ with ⟨hβ₁_leaf, _⟩
    rcases (mem_badLeafSet (n := n) (ℓ := ℓ) (A := A)
      (f := f) (g := g) (β := β₂)).1 hβ₂ with ⟨hβ₂_leaf, _⟩
    exact leafPoints_disjoint (n := n) (ℓ := ℓ) (A := A)
      hβ₁_leaf hβ₂_leaf hneq
  -- Оценка мощности объединения: сумма мощностей слагаемых.
  have hcard :=
    Finset.card_biUnion
      (s := badLeafSet (n := n) (ℓ := ℓ) A f g)
      (t := fun β => leafPoints (n := n) (ℓ := ℓ) (A := A) β)
      hdisjoint
  -- Переписываем через формулу для `leafPoints_card`.
  have hsum :
      ∑ β in badLeafSet (n := n) (ℓ := ℓ) A f g,
          (leafPoints (n := n) (ℓ := ℓ) (A := A) β).card
        = (badLeafSet (n := n) (ℓ := ℓ) A f g).card
            * Nat.pow 2 (n - ℓ) := by
    classical
    -- Индукция по конечному множеству плохих листьев.
    refine Finset.induction_on
      (s := badLeafSet (n := n) (ℓ := ℓ) A f g)
      (motive := fun s =>
        ∑ β in s, (leafPoints (n := n) (ℓ := ℓ) (A := A) β).card
          = s.card * Nat.pow 2 (n - ℓ))
      ?base ?step
    · simp
    · intro β s hβ_not hIH
      have hβ_mem : β ∈ insert β s := Finset.mem_insert_self _ _
      rcases (mem_badLeafSet (n := n) (ℓ := ℓ) (A := A)
        (f := f) (g := g) (β := β)).1 hβ_mem with ⟨hβ_leaf, _⟩
      have hβ_value :
          (leafPoints (n := n) (ℓ := ℓ) (A := A) β).card
            = Nat.pow 2 (n - ℓ) :=
        leafPoints_card (n := n) (ℓ := ℓ) (A := A)
          (β := β) hβ_leaf
      simp [Finset.sum_insert, hβ_not, hβ_value, hIH,
        Finset.card_insert, hβ_not, Nat.succ_mul, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]
  -- Собираем выражение.
  have hfiltered_card :
      (Finset.univ.filter fun x : BitVec n =>
          f x ≠ coveredB selectors x).card
        = (badLeafSet (n := n) (ℓ := ℓ) A f g).card
            * Nat.pow 2 (n - ℓ) := by
    simpa [hrewrite] using hcard.trans hsum
  exact hfiltered_card

/--
  Итоговая формула: ошибка аппроксимации равна доле плохих листьев.  Это
  связывает вероятностные оценки с `errU` и позволяет в дальнейшем
  контролировать ошибку через мощности множеств.
-/
lemma errU_leafSelector {ℓ : Nat} (A : Axis n ℓ)
    (f : BitVec n → Bool) (g : Subcube n → Bool)
    (hconst : constantOnLeaves (n := n) (ℓ := ℓ) A f) :
    let selectors := leafSelector (n := n) (ℓ := ℓ) A g
    errU f selectors
      = ((badLeafSet (n := n) (ℓ := ℓ) A f g).card : Q)
          / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  intro selectors
  -- Выписываем формулу для счётчика несоответствий.
  have hmismatch :=
    mismatches_card (n := n) (ℓ := ℓ) (A := A)
      (f := f) (g := g) hconst (selectors := selectors)
  -- Преобразуем определения и переходим к дробям.
  have hℓ_le : ℓ ≤ n := by
    classical
    have := Finset.card_le_univ (s := A.support)
    simpa [Axis.card] using this
  have hdenom_cast :
      ((Nat.pow 2 n : Nat) : Q)
        = ((Nat.pow 2 (n - ℓ) : Nat) : Q)
            * ((Nat.pow 2 ℓ : Nat) : Q) := by
    have hsplit : n = (n - ℓ) + ℓ := Nat.sub_add_cancel hℓ_le
    have := Nat.pow_add (2 : Nat) (n - ℓ) ℓ
    simp [hsplit, Nat.cast_mul, Nat.cast_pow, Nat.pow] at this
    simpa using this
  have hpow_ne_zero :
      ((Nat.pow 2 (n - ℓ) : Nat) : Q) ≠ 0 := by
    have hpos : 0 < Nat.pow 2 (n - ℓ) :=
      Nat.pow_pos (by decide : 0 < 2) _
    exact_mod_cast (ne_of_gt hpos)
  -- Вычисляем `errU` через ранее полученную формулу для количества ошибок.
  have hmismatch_q :
      ((Finset.univ.filter fun x : BitVec n =>
          f x ≠ coveredB selectors x).card : Q)
        = ((badLeafSet (n := n) (ℓ := ℓ) A f g).card : Q)
            * ((Nat.pow 2 (n - ℓ) : Nat) : Q) := by
    exact_mod_cast hmismatch
  -- Финальный расчёт ошибки.
  unfold errU
  simp [selectors, hmismatch_q, hdenom_cast, hpow_ne_zero,
    mul_comm, mul_left_comm, mul_assoc,
    mul_div_mul_left]

/--
  Если количество «плохих» листьев ограничено сверху числом `badBound`,
  то ошибка аппроксимации не превышает `badBound / 2^ℓ`.  Это удобная форма
  для последующего управления `errU` по чисто комбинаторным оценкам.
-/
lemma errU_leafSelector_le_of_card_le {ℓ : Nat} (A : Axis n ℓ)
    (f : BitVec n → Bool) (g : Subcube n → Bool)
    (hconst : constantOnLeaves (n := n) (ℓ := ℓ) A f)
    {badBound : Nat}
    (hbad_le : (badLeafSet (n := n) (ℓ := ℓ) A f g).card ≤ badBound) :
    let selectors := leafSelector (n := n) (ℓ := ℓ) A g
    errU f selectors
      ≤ (badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  intro selectors
  -- Подставляем точную формулу для `errU`, полученную ранее.
  have herr := errU_leafSelector (n := n) (ℓ := ℓ) (A := A)
    (f := f) (g := g) hconst (selectors := selectors)
  -- Определяем знаменатель и фиксируем его положительность.
  set denom : Q := ((Nat.pow 2 ℓ : Nat) : Q) with hdenom
  have hdenom_pos : 0 < denom := by
    have hpos : 0 < (Nat.pow 2 ℓ : Nat) := Nat.pow_pos (by decide : 0 < 2) _
    have : 0 < ((Nat.pow 2 ℓ : Nat) : Q) := by exact_mod_cast hpos
    simpa [denom, hdenom] using this
  have hdenom_inv_nonneg : 0 ≤ denom⁻¹ := by
    exact inv_nonneg.mpr hdenom_pos.le
  -- Переводим ограничение мощности «плохих» листьев в рациональное неравенство.
  have hcard_le :
      ((badLeafSet (n := n) (ℓ := ℓ) A f g).card : Q)
        ≤ (badBound : Q) := by
    exact_mod_cast hbad_le
  -- Преобразуем обе части через умножение на `denom⁻¹`.
  calc
    errU f selectors
        = ((badLeafSet (n := n) (ℓ := ℓ) A f g).card : Q) / denom := by
            simpa [denom, hdenom] using herr
    _ = ((badLeafSet (n := n) (ℓ := ℓ) A f g).card : Q) * denom⁻¹ := by
            simp [denom, hdenom, div_eq_mul_inv]
    _ ≤ (badBound : Q) * denom⁻¹ := by
            exact mul_le_mul_of_nonneg_right hcard_le hdenom_inv_nonneg
    _ = (badBound : Q) / denom := by
            simp [denom, hdenom, div_eq_mul_inv]

/--
  Если удаётся перечислить «плохие» листья, на которых итоговое покрытие
  расходится с функцией `f`, то ошибка аппроксимации ограничена их числом,
  делённым на `2^ℓ`.  Этот результат не делает дополнительных предположений
  о структуре хвостов: достаточно лишь знать, что все несовпадения происходят
  внутри заранее выделенного множества листьев.
-/
lemma errU_selectorsFromTails_le_of_badLeaves {ℓ : Nat} (A : Axis n ℓ)
    (tailSelectors : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A →
        (BitVec n → Bool) → List (Subcube n))
    (f : BitVec n → Bool)
    (badLeaves : Finset (Subcube n))
    (hsubset : badLeaves ⊆ (leafList (n := n) (ℓ := ℓ) A).toFinset)
    (hmismatch : ∀ x,
        f x ≠ coveredB
          (selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors := tailSelectors) f) x →
          leafForPoint (n := n) (ℓ := ℓ) A x ∈ badLeaves) :
    errU f
        (selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
          (tailSelectors := tailSelectors) f)
      ≤ (badLeaves.card : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  set selectors :=
    selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
      (tailSelectors := tailSelectors) f with hselectors
  -- Множество всех точек, попадающих в «плохие» листья.
  set badSet :=
    Finset.biUnion badLeaves
      (fun β _ => leafPoints (n := n) (ℓ := ℓ) (A := A) β) with hbadSet
  -- Любая несовпадающая точка обязательно лежит в `badSet`.
  have hmismatch_subset :
      ((Finset.univ : Finset (BitVec n)).filter
          (fun x => f x ≠ coveredB selectors x))
        ⊆ badSet := by
    intro x hx
    have hx_mismatch : f x ≠ coveredB selectors x :=
      (Finset.mem_filter.mp hx).2
    have hx_leaf :=
      hmismatch x (by simpa [hselectors] using hx_mismatch)
    -- Точка принадлежит листу `leafForPoint A x`, который лежит в `badLeaves`.
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨_, hx_leaf, ?_⟩
    have hx_mem : mem
        (leafForPoint (n := n) (ℓ := ℓ) (A := A) x) x :=
      leafForPoint_mem (n := n) (ℓ := ℓ) (A := A) (x := x)
    have hx_univ : x ∈ (Finset.univ : Finset (BitVec n)) := by simp
    exact Finset.mem_filter.mpr ⟨hx_univ, hx_mem⟩
  -- Следовательно, мощность множества несовпадений не превосходит `badSet.card`.
  have hmismatch_card_le :
      ((Finset.univ : Finset (BitVec n)).filter
          (fun x => f x ≠ coveredB selectors x)).card
        ≤ badSet.card :=
    Finset.card_le_of_subset hmismatch_subset
  -- Применяем общую оценку для `errU` через число несовпадений.
  have herr := Core.errU_le_of_mismatch_card_le
      (n := n) (f := f) (Rset := selectors)
      (badBound := badSet.card)
      (by simpa [badSet, hbadSet] using hmismatch_card_le)
  -- Переписываем мощность объединения через число плохих листьев.
  have hbad_card : badSet.card =
      badLeaves.card * Nat.pow 2 (n - ℓ) := by
    have := leafPoints_union_card (n := n) (ℓ := ℓ) (A := A)
      (badLeaves := badLeaves) hsubset
    simpa [badSet, hbadSet]
      using this
  -- Превращаем оценку в явную дробь `badLeaves.card / 2^ℓ`.
  have hpow_le : ℓ ≤ n := by
    classical
    have := Finset.card_le_univ (s := A.support)
    simpa [Axis.card] using this
  have hx_cast :
      ((badLeaves.card * Nat.pow 2 (n - ℓ)) : Q)
        = (badLeaves.card : Q)
            * ((Nat.pow 2 (n - ℓ) : Nat) : Q) := by
    norm_cast
  have hpow_nat :
      Nat.pow 2 n = Nat.pow 2 (n - ℓ) * Nat.pow 2 ℓ := by
    have hsplit : n = (n - ℓ) + ℓ := Nat.sub_add_cancel hpow_le
    simpa [hsplit] using Nat.pow_add (2 : Nat) (n - ℓ) ℓ
  have hy_cast :
      ((Nat.pow 2 n : Nat) : Q)
        = ((Nat.pow 2 (n - ℓ) : Nat) : Q)
            * ((Nat.pow 2 ℓ : Nat) : Q) := by
    have := congrArg (fun k : Nat => (k : Q)) hpow_nat
    simpa [Nat.cast_mul, Nat.cast_pow] using this
  have hbq_pos : 0 < ((Nat.pow 2 (n - ℓ) : Nat) : Q) := by
    have htwo_pos : 0 < (2 : Q) := by norm_num
    have hpow := pow_pos htwo_pos (n - ℓ)
    simpa [Nat.cast_pow] using hpow
  have hbq_ne :
      ((Nat.pow 2 (n - ℓ) : Nat) : Q) ≠ 0 := by
    exact (ne_of_gt hbq_pos)
  have hcq_pos : 0 < ((Nat.pow 2 ℓ : Nat) : Q) := by
    have htwo_pos : 0 < (2 : Q) := by norm_num
    have hpow := pow_pos htwo_pos ℓ
    simpa [Nat.cast_pow] using hpow
  have hcq_ne :
      ((Nat.pow 2 ℓ : Nat) : Q) ≠ 0 := by
    exact (ne_of_gt hcq_pos)
  have hcalc :
      ((badLeaves.card * Nat.pow 2 (n - ℓ)) : Q)
          / ((Nat.pow 2 n : Nat) : Q)
        = (badLeaves.card : Q)
            / ((Nat.pow 2 ℓ : Nat) : Q) := by
    simp [hx_cast, hy_cast, div_eq_mul_inv, hbq_ne, hcq_ne,
      mul_comm, mul_left_comm, mul_assoc]
  have herr' : errU f selectors
      ≤ (badLeaves.card : Q)
          / ((Nat.pow 2 ℓ : Nat) : Q) := by
    have := herr
    simpa [hbad_card, hcalc] using this
  -- Возвращаемся к исходному выражению селекторов.
  simpa [hselectors] using herr'

/--
  Для оси положительной размерности выделим «последнюю» свободную координату —
  ту, которая соответствует элементу `Fin.last ℓ` в упорядоченной нумерации.
  Этот элемент будет служить точкой разбиения при рекурсивных построениях
  ствола PDT: сначала обрабатываем остальные `ℓ` переменных, а затем добавляем
  ветвление по `pivot`.
-/
noncomputable def pivot (A : Axis n (Nat.succ ℓ)) : Fin n :=
  coord (n := n) (ℓ := Nat.succ ℓ) A (Fin.last ℓ)

@[simp] lemma pivot_mem_support (A : Axis n (Nat.succ ℓ)) :
    pivot (n := n) (ℓ := ℓ) A ∈ A.support := by
  classical
  simpa [pivot]
    using coord_mem_support (n := n) (ℓ := Nat.succ ℓ)
      (A := A) (j := Fin.last ℓ)

/--
  Удаляя `pivot`, получаем ось меньшей размерности.  Эту операцию мы будем
  использовать при индукции по `ℓ`: хвостовая ось содержит все «оставшиеся»
  свободные координаты, что позволяет применять индуктивное предположение.
-/
noncomputable def removePivot (A : Axis n (Nat.succ ℓ)) : Axis n ℓ :=
  { support := A.support.erase (pivot (n := n) (ℓ := ℓ) A)
    card_support := by
      classical
      -- `pivot` действительно принадлежит опорному множеству.
      have hpivot :
          pivot (n := n) (ℓ := ℓ) A ∈ A.support :=
        pivot_mem_support (n := n) (ℓ := ℓ) A
      -- Кардинальность после удаления уменьшается ровно на один.
      have hcard :=
        Finset.card_erase_add_one (s := A.support)
          (a := pivot (n := n) (ℓ := ℓ) A) hpivot
      -- Переписываем равенство через `Nat.succ` и устраняем `+1`.
      have hsucc :
          Nat.succ ((A.support.erase (pivot (n := n) (ℓ := ℓ) A)).card)
            = Nat.succ ℓ := by
        simpa [Axis.card, Nat.succ_eq_add_one]
          using hcard
      -- `Nat.succ` инъективна, значит искомое равенство следует сразу.
      exact Nat.succ.inj hsucc }

@[simp] lemma removePivot_support
    (A : Axis n (Nat.succ ℓ)) :
    (removePivot (n := n) (ℓ := ℓ) A).support
      = A.support.erase (pivot (n := n) (ℓ := ℓ) A) := rfl

@[simp] lemma removePivot_card
    (A : Axis n (Nat.succ ℓ)) :
    (removePivot (n := n) (ℓ := ℓ) A).support.card = ℓ := by
  classical
  -- Раскрываем определение и повторно используем доказательство выше.
  simpa [removePivot]

/-- После удаления `pivot` множество фиксированных координат пополняется
  ровно одним элементом — это пригодится при работе с `Axis.subcube`.
-/
lemma pivot_mem_fixed (A : Axis n (Nat.succ ℓ)) :
    pivot (n := n) (ℓ := ℓ) A ∈ A.fixed := by
  classical
  simp [Axis.fixed, pivot_mem_support (n := n) (ℓ := ℓ) A]

/-!
### Совершенный ствол PDT, ветвящийся по координатам оси

В последующих разделах нам понадобится детерминированный «каркас» дерева
решений, которое опрашивает только свободные переменные заданной оси.  В
этом блоке мы строим такой каркас и собираем простейшие свойства:
глубину и количество листьев.  Позже к этим листьям будут прикреплены
хвосты, кодирующие остаточные формулы.
-/

/-- Фиксация значения координаты `i` в подкубе `β`. -/
@[simp] def assign (β : Subcube n) (i : Fin n) (b : Bool) : Subcube n :=
  fun j => if j = i then some b else β j

@[simp] lemma assign_self (β : Subcube n) (i : Fin n) (b : Bool) :
    assign (n := n) β i b i = some b := by
  simp [assign]

@[simp] lemma assign_other {β : Subcube n} {i j : Fin n}
    {b : Bool} (hij : j ≠ i) :
    assign (n := n) β i b j = β j := by
  simp [assign, hij]

/--
  Присвоение значения свободной координате `i` дополняет условие на `x i = b`,
  не затрагивая остальные ограничения подкуба.  Лемма записана в форме
  эквивалентности: принадлежность обновлённому подкубу означает, что точка
  удовлетворяет исходному подкубу и имеет нужное значение на `i`.
-/
lemma mem_assign_of_none {β : Subcube n} {i : Fin n} {b : Bool}
    (hfree : β i = (none : Option Bool)) (x : BitVec n) :
    mem (assign (n := n) β i b) x ↔ mem β x ∧ x i = b := by
  classical
  constructor
  · intro hassign
    have hmem := (mem_iff (β := assign (n := n) β i b) (x := x)).1 hassign
    have hvalue :=
      hmem i b (by simpa [assign_self])
    have hbase : mem β x :=
      (mem_iff (β := β) (x := x)).2 (by
        intro j c hjc
        by_cases hij : j = i
        · subst hij
          -- Противоречие: в исходном подкубе координата `i` свободна.
          simpa [hfree] using hjc
        · have hrewrite : assign (n := n) β i b j = β j :=
            assign_other (n := n) (β := β) (i := i) (j := j) (b := b) hij
          have hsome : assign (n := n) β i b j = some c := by
            simpa [hrewrite] using hjc
          exact hmem j c hsome)
    exact ⟨hbase, hvalue⟩
  · intro hconditions
    rcases hconditions with ⟨hbase, hbit⟩
    refine (mem_iff (β := assign (n := n) β i b) (x := x)).2 ?_
    intro j c hjc
    by_cases hij : j = i
    · subst hij
      have hsome := by simpa [assign_self] using hjc
      -- После раскрытия равенства убеждаемся, что `c = b` и получаем цель.
      have hc : c = b := by
        have hcompare : some c = some b := by
          simpa [assign_self] using hjc
        exact Option.some.inj hcompare
      simpa [hc, hbit]
    · have hrewrite : assign (n := n) β i b j = β j :=
        assign_other (n := n) (β := β) (i := i) (j := j) (b := b) hij
      have hbase_val : β j = some c := by
        simpa [hrewrite] using hjc
      have := (mem_iff (β := β) (x := x)).1 hbase j c hbase_val
      simpa using this

/--
  Совершенное PDT, ветвящееся по координатам оси.  Конструкция идёт по
  индукции по числу свободных переменных: если ось пуста, дерево состоит
  из одного листа; если ось содержит `succ ℓ` элементов, то на верхнем
  уровне спрашивается `pivot`, а оба поддерева строятся рекурсивно для
  оси без `pivot`, после чего значение `pivot` фиксируется в каждом
  листе соответствующей ветви.
-/
noncomputable def trunk : ∀ {ℓ : Nat}, Axis n ℓ → PDT n
| 0, _ => PDT.leaf (fun _ => (none : Option Bool))
| Nat.succ ℓ, A =>
    let pivot := pivot (n := n) (ℓ := ℓ) A
    let tail := trunk (n := n) (ℓ := ℓ) (removePivot (n := n) (ℓ := ℓ) A)
    let zeroTail :=
      PDT.mapLeaves (fun β => assign (n := n) β pivot false) tail
    let oneTail :=
      PDT.mapLeaves (fun β => assign (n := n) β pivot true) tail
    PDT.node pivot zeroTail oneTail

@[simp] lemma trunk_depth_zero (A : Axis n 0) :
    PDT.depth (trunk (n := n) (ℓ := 0) A) = 0 := rfl

/-- Глубина совершеного ствола равна числу свободных координат. -/
lemma trunk_depth :
    ∀ {ℓ : Nat} (A : Axis n ℓ),
      PDT.depth (trunk (n := n) (ℓ := ℓ) A) = ℓ
| 0, _ => rfl
| Nat.succ ℓ, A => by
    classical
    simp [trunk, PDT.depth_mapLeaves, Nat.max_self,
      trunk_depth (A := removePivot (n := n) (ℓ := ℓ) A)]

/-- Число листьев совершеного ствола совпадает с `2^ℓ`. -/
lemma trunk_leaves_length :
    ∀ {ℓ : Nat} (A : Axis n ℓ),
      (PDT.leaves (trunk (n := n) (ℓ := ℓ) A)).length = Nat.pow 2 ℓ
| 0, _ => by
    simp [trunk]
| Nat.succ ℓ, A => by
    classical
    have htail := trunk_leaves_length (n := n)
      (A := removePivot (n := n) (ℓ := ℓ) A)
    simp [trunk, PDT.leaves_mapLeaves, List.length_map,
      htail, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Листья совершеного ствола совпадают с рекурсивно построенным списком `leafList`. -/
@[simp] lemma trunk_leaves :
    ∀ {ℓ : Nat} (A : Axis n ℓ),
      PDT.leaves (trunk (n := n) (ℓ := ℓ) A)
        = leafList (n := n) (ℓ := ℓ) A
| 0, _ => rfl
| Nat.succ ℓ, A => by
    classical
    have htail := trunk_leaves (n := n)
      (ℓ := ℓ) (A := removePivot (n := n) (ℓ := ℓ) A)
    simp [trunk, leafList, PDT.leaves_mapLeaves,
      htail, List.map_append, List.append_assoc]

/--
  Частичное PDT с совершенным стволом по оси.  Хвосты передаются явно
  как функция `tails`, определённая на списке `leafList`.  Параметр `τ`
  ограничивает глубину каждого хвоста.
-/
noncomputable def partialDT {τ : Nat}
    {ℓ : Nat} (A : Axis n ℓ)
    (tails : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A → PDT n)
    (htails : ∀ β hβ, PDT.depth (tails β hβ) ≤ τ) :
    PartialDT n τ :=
  { trunk := trunk (n := n) (ℓ := ℓ) A
    tails :=
      fun β hβ =>
        let hβ' : β ∈ leafList (n := n) (ℓ := ℓ) A := by
          simpa [Axis.trunk_leaves (n := n) (ℓ := ℓ) (A := A)] using hβ
        tails β hβ'
    tail_depth_le := by
      intro β hβ
      have hβ' : β ∈ leafList (n := n) (ℓ := ℓ) A := by
        simpa [Axis.trunk_leaves (n := n) (ℓ := ℓ) (A := A)] using hβ
      exact htails β hβ' }

@[simp] lemma partialDT_trunk
    {τ ℓ : Nat} {A : Axis n ℓ}
    {tails : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A → PDT n}
    {htails : ∀ β hβ, PDT.depth (tails β hβ) ≤ τ} :
    (partialDT (n := n) (ℓ := ℓ) (A := A)
      (tails := tails) (htails := htails)).trunk
        = trunk (n := n) (ℓ := ℓ) A := rfl

@[simp] lemma partialDT_leafDict
    {τ ℓ : Nat} {A : Axis n ℓ}
    {tails : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A → PDT n}
    {htails : ∀ β hβ, PDT.depth (tails β hβ) ≤ τ} :
    (partialDT (n := n) (ℓ := ℓ) (A := A)
      (tails := tails) (htails := htails)).leafDict
        = leafList (n := n) (ℓ := ℓ) A := by
  simp [partialDT]

/-!
### Конструктор частичных сертификатов

Используя совершенный ствол и произвольные хвосты, можно собрать объект
`PartialCertificate`.  Для этого требуется дополнительная информация:

* верхняя граница на глубину ствола (`depthBound`),
* списки листьев для каждой функции семейства `F`,
* доказательства того, что выбранные листья действительно появляются в
  соответствующих хвостах,
* оценка ошибки `errU`.

Следующая лемма аккумулирует эти предпосылки.  Она будет использоваться на
финальном этапе формализации switching-леммы, когда все вероятностные оценки
уже получены и остаётся собрать Lean-объект.
-/
section PartialCertificateBuilder

variable {F : Family n}

/--
  Общий конструктор частичных сертификатов на базе совершенного ствола.
  Предполагается, что каждая выбранная точка (`β`) действительно встречается
  в каком-то хвосте, после чего мы переносим этот факт на реализованное дерево.
-/
noncomputable def buildPartialCertificate
    {ℓ τ depthBound : Nat}
    (A : Axis n ℓ)
    (tails : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A → PDT n)
    (htails : ∀ β hβ, PDT.depth (tails β hβ) ≤ τ)
    (epsilon : Q)
    (selectors : (BitVec n → Bool) → List (Subcube n))
    (selectors_mem : ∀ {f : BitVec n → Bool} (hf : f ∈ F)
        {β : Subcube n}, β ∈ selectors f →
          ∃ β₀ (hβ₀ : β₀ ∈ leafList (n := n) (ℓ := ℓ) A),
            β ∈ PDT.leaves (tails β₀ hβ₀))
    (err_le : ∀ {f : BitVec n → Bool}, f ∈ F →
        errU f (selectors f) ≤ epsilon)
    (hdepth : ℓ ≤ depthBound) :
    Core.PartialCertificate n τ F := by
  classical
  -- Ствол и хвосты: используем ранее построенный `partialDT`.
  let witness :=
    partialDT (n := n) (ℓ := ℓ) (A := A)
      (tails := tails) (htails := htails)
  -- Основная часть конструкции — упаковка данных в `PartialCertificate`.
  refine
    { witness := witness
      depthBound := depthBound
      epsilon := epsilon
      trunk_depth_le := ?_
      selectors := selectors
      selectors_sub := ?_
      err_le := ?_ }
  · -- Глубина ствола равна `ℓ`, значит ограничение следует из `hdepth`.
    have htrunk :
        PDT.depth witness.trunk = ℓ := by
      simpa [witness, partialDT] using
        (trunk_depth (n := n) (ℓ := ℓ) (A := A))
    simpa [htrunk]
      using hdepth
  · -- Любой выбранный лист появляется в некотором хвосте, следовательно
    -- принадлежит реализованному дереву.
    intro f β hf hβ
    obtain ⟨β₀, hβ₀_leaf, hβ_tail⟩ := selectors_mem hf hβ
    -- Преобразуем доказательство принадлежности для ствола.
    have hβ₀_trunk :
        β₀ ∈ PDT.leaves witness.trunk := by
      simpa [witness, partialDT, trunk_leaves] using hβ₀_leaf
    -- Приводим хвост к форме, понятной `PartialDT.mem_realize_of_mem_tail`.
    have hβ_tail' :
        β ∈ PDT.leaves (witness.tails β₀ hβ₀_trunk) := by
      simpa [witness, partialDT, trunk_leaves] using hβ_tail
    -- Теперь заключаем принадлежность реализованному дереву.
    exact Core.PartialDT.mem_realize_of_mem_tail
      (Q := witness) hβ₀_trunk hβ_tail'
  · -- Оценка ошибки передаётся напрямую из предпосылок.
      intro f hf
      exact err_le hf

/-!
Следующий блок автоматизирует работу с селекторами, построенными по листам
ствола.  В большинстве применений удобно задавать для каждого листа хвоста
отдельный список «хороших» подкубов, после чего объединить все эти списки в
общий словарь.  Чтобы не переписывать однотипные рассуждения заново, мы
выделяем вспомогательные определения и леммы.
-/

/-- Объединить селекторы по всем листьям `leafList`. -/
noncomputable def selectorsFromTails
    (A : Axis n ℓ)
    (tailSelectors : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A →
        (BitVec n → Bool) → List (Subcube n))
    (f : BitVec n → Bool) : List (Subcube n) :=
  ((leafList (n := n) (ℓ := ℓ) A).attach).bind
    (fun β => tailSelectors β.1 β.2 f)

lemma mem_selectorsFromTails
    (A : Axis n ℓ)
    (tailSelectors : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A →
        (BitVec n → Bool) → List (Subcube n))
    {f : BitVec n → Bool} {β : Subcube n}
    (hβ : β ∈ selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
      (tailSelectors := tailSelectors) f) :
    ∃ β₀ (hβ₀ : β₀ ∈ leafList (n := n) (ℓ := ℓ) A),
      β ∈ tailSelectors β₀ hβ₀ f := by
  classical
  unfold selectorsFromTails at hβ
  rcases List.mem_bind.1 hβ with ⟨s, hs, hmem⟩
  refine ⟨s.1, ?_, ?_⟩
  · exact s.2
  · simpa using hmem

lemma selectorsFromTails_mem_leaves
    (A : Axis n ℓ)
    (tails : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A → PDT n)
    (tailSelectors : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A →
        (BitVec n → Bool) → List (Subcube n))
    (hsel : ∀ {β hβ f β'}, β' ∈ tailSelectors β hβ f →
        β' ∈ PDT.leaves (tails β hβ))
    {f : BitVec n → Bool} {β : Subcube n}
    (hβ : β ∈ selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
      (tailSelectors := tailSelectors) f) :
    ∃ β₀ (hβ₀ : β₀ ∈ leafList (n := n) (ℓ := ℓ) A),
      β ∈ PDT.leaves (tails β₀ hβ₀) := by
  classical
  obtain ⟨β₀, hβ₀_mem, hβ_tail⟩ :=
    mem_selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
      (tailSelectors := tailSelectors) (f := f) (β := β) hβ
  refine ⟨β₀, hβ₀_mem, ?_⟩
  exact hsel hβ_tail

/--
  Специализация конструктора частичных сертификатов: хвосты снабжены локальными
  списками селекторов, которые автоматически объединяются в глобальный
  словарь.  Предположения полностью аналогичны предыдущей лемме, но теперь
  не требуется вручную выписывать разбиение по листам.
-/
noncomputable def buildPartialCertificateFromTailSelectors
    {ℓ τ depthBound : Nat}
    (A : Axis n ℓ)
    (tails : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A → PDT n)
    (htails : ∀ β hβ, PDT.depth (tails β hβ) ≤ τ)
    (epsilon : Q)
    (tailSelectors : ∀ β, β ∈ leafList (n := n) (ℓ := ℓ) A →
        (BitVec n → Bool) → List (Subcube n))
    (tailSelectors_mem : ∀ {β hβ f β'},
        β' ∈ tailSelectors β hβ f → β' ∈ PDT.leaves (tails β hβ))
    (err_le : ∀ {f : BitVec n → Bool}, f ∈ F →
        errU f (selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
          (tailSelectors := tailSelectors) f) ≤ epsilon)
    (hdepth : ℓ ≤ depthBound) :
    Core.PartialCertificate n τ F := by
  classical
  -- Глобальный словарь формируется автоматически из локальных селекторов.
  set selectors :=
    selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
      (tailSelectors := tailSelectors)
  -- Свойства селекторов следуют из локальных предпосылок.
  have selectors_mem :
      ∀ {f : BitVec n → Bool} (hf : f ∈ F) {β : Subcube n},
          β ∈ selectors f →
            ∃ β₀ (hβ₀ : β₀ ∈ leafList (n := n) (ℓ := ℓ) A),
              β ∈ PDT.leaves (tails β₀ hβ₀) := by
    intro f hf β hβ
    have := selectorsFromTails_mem_leaves (n := n) (ℓ := ℓ) (A := A)
      (tails := tails) (tailSelectors := tailSelectors)
      (hsel := tailSelectors_mem) (f := f) (β := β)
      (by simpa [selectors] using hβ)
    simpa using this
  -- Ошибка передаётся напрямую из предпосылок.
  have err_le' : ∀ {f : BitVec n → Bool}, f ∈ F →
      errU f (selectors f) ≤ epsilon := by
    intro f hf
    simpa [selectors] using err_le (f := f) hf
  -- Вызываем основной конструктор, подставляя полученные данные.
  exact buildPartialCertificate (n := n) (ℓ := ℓ) (τ := τ)
    (depthBound := depthBound) (A := A)
    (tails := tails) (htails := htails)
    (epsilon := epsilon) (selectors := selectors)
    (selectors_mem := selectors_mem) (err_le := err_le')
    (hdepth := hdepth)

end PartialCertificateBuilder

end Axis

/-!
### Подкуб, соответствующий оси и частичному назначению

Фиксируем ось `A` и таблицу значений `σ` для всех переменных.  На
свободных координатах подкуб хранит `none`, на остальных — `some (σ i)`.
-/

/-- Конвертация оси в подкуб: свободные переменные не фиксируем, остальные
получают значения из `σ`. -/
@[simp] def Axis.subcube {n ℓ : Nat} (A : Axis n ℓ) (σ : BitVec n) :
    Subcube n := fun i => if i ∈ A.support then none else some (σ i)

@[simp] lemma Axis.subcube_apply_mem {n ℓ : Nat} (A : Axis n ℓ)
    (σ : BitVec n) {i : Fin n} (hi : i ∈ A.support) :
    Axis.subcube A σ i = none := by
  classical
  simp [Axis.subcube, hi]

@[simp] lemma Axis.subcube_apply_not_mem {n ℓ : Nat} (A : Axis n ℓ)
    (σ : BitVec n) {i : Fin n} (hi : i ∉ A.support) :
    Axis.subcube A σ i = some (σ i) := by
  classical
  simp [Axis.subcube, hi]

/-- Условия принадлежности подкубу: точка `x` совпадает с `σ` на всех
фиксированных координатах. -/
lemma Axis.mem_subcube_iff {n ℓ : Nat} (A : Axis n ℓ) (σ x : BitVec n) :
    mem (Axis.subcube A σ) x ↔ ∀ ⦃i : Fin n⦄, i ∉ A.support → x i = σ i := by
  classical
  constructor
  · intro hx i hi
    have hx_prop :=
      (mem_iff (β := Axis.subcube A σ) (x := x)).1 hx
    have hβ : Axis.subcube A σ i = some (σ i) :=
      Axis.subcube_apply_not_mem (A := A) (σ := σ) (i := i) hi
    exact hx_prop i (σ i) hβ
  · intro h
    apply (mem_iff (β := Axis.subcube A σ) (x := x)).2
    intro i b hβ
    have hi : i ∉ A.support := by
      intro hi'
      have : Axis.subcube A σ i = none :=
        Axis.subcube_apply_mem (A := A) (σ := σ) (i := i) hi'
      simpa [hβ]
    have hb : σ i = b := by
      have := by simpa [Axis.subcube, hi] using hβ.symm
      exact Option.some.inj this
    have hx : x i = σ i := h hi
    simpa [hb]

/-- Эквивалентная запись условия через дополнение множества свободных
координат. -/
lemma Axis.mem_subcube_iff_fixed {n ℓ : Nat} (A : Axis n ℓ)
    (σ x : BitVec n) :
    mem (Axis.subcube A σ) x ↔ ∀ i ∈ A.fixed, x i = σ i := by
  classical
  constructor
  · intro hx i hi
    have hi' : i ∉ A.support := by
      simpa [Axis.fixed] using hi
    exact (Axis.mem_subcube_iff (A := A) (σ := σ) (x := x)).1 hx hi'
  · intro hx
    refine (Axis.mem_subcube_iff (A := A) (σ := σ) (x := x)).2 ?_
    intro i hi
    have : i ∈ A.fixed := by
      simpa [Axis.fixed] using hi
    exact hx i this

/-- Для свободной координаты подкуба значение действительно не задано. -/
@[simp] lemma Axis.subcube_isNone_iff {n ℓ : Nat} (A : Axis n ℓ)
    (σ : BitVec n) {i : Fin n} :
    (Axis.subcube A σ i).isNone ↔ i ∈ A.support := by
  classical
  by_cases hi : i ∈ A.support
  · simp [Axis.subcube, hi]
  · simp [Axis.subcube, hi]

/-- На фиксированных координатах подкуб содержит `some`. -/
@[simp] lemma Axis.subcube_isSome_iff {n ℓ : Nat} (A : Axis n ℓ)
    (σ : BitVec n) {i : Fin n} :
    (Axis.subcube A σ i).isSome ↔ i ∈ A.fixed := by
  classical
  by_cases hi : i ∈ A.support
  · simp [Axis.fixed, Axis.subcube, hi]
  · simp [Axis.fixed, Axis.subcube, hi]

/-!
### Exact-ℓ рестрикция как структура

Далее удобно упаковать ось и конкретное назначение фиксированных битов в
один объект.
-/

structure ExactRestriction (n ℓ : Nat) where
  axis   : Axis n ℓ
  values : BitVec n
  deriving DecidableEq

namespace ExactRestriction

variable {n ℓ : Nat}

@[simp] def toSubcube (ρ : ExactRestriction n ℓ) : Subcube n :=
  Axis.subcube ρ.axis ρ.values

@[simp] lemma mem_toSubcube {ρ : ExactRestriction n ℓ} {x : BitVec n} :
    mem ρ.toSubcube x ↔ ∀ ⦃i : Fin n⦄, i ∉ ρ.axis.support → x i = ρ.values i :=
  Axis.mem_subcube_iff (A := ρ.axis) (σ := ρ.values) (x := x)

@[simp] lemma mem_toSubcube_fixed {ρ : ExactRestriction n ℓ} {x : BitVec n} :
    mem ρ.toSubcube x ↔ ∀ i ∈ ρ.axis.fixed, x i = ρ.values i :=
  Axis.mem_subcube_iff_fixed (A := ρ.axis) (σ := ρ.values) (x := x)

@[simp] lemma freeCoordinate {ρ : ExactRestriction n ℓ} {i : Fin n} :
    ρ.toSubcube i = none ↔ i ∈ ρ.axis.support :=
  Axis.subcube_isNone_iff (A := ρ.axis) (σ := ρ.values) (i := i)

@[simp] lemma fixedCoordinate {ρ : ExactRestriction n ℓ} {i : Fin n} :
    ρ.toSubcube i = some (ρ.values i) ↔ i ∈ ρ.axis.fixed := by
  classical
  constructor
  · intro hi
    have : (ρ.toSubcube i).isSome := by
      simpa [Option.isSome_iff_exists] using ⟨ρ.values i, hi⟩
    have hmem := (Axis.subcube_isSome_iff (A := ρ.axis)
        (σ := ρ.values) (i := i)).1 this
    simpa [ExactRestriction.toSubcube] using hmem
  · intro hi
    have hnot : i ∉ ρ.axis.support := by
      classical
      simpa [Axis.fixed] using hi
    have : Axis.subcube ρ.axis ρ.values i = some (ρ.values i) := by
      simp [Axis.subcube, hnot]
    simpa [ExactRestriction.toSubcube] using this

/-- Число свободных координат точной рестрикции равно `ℓ`. -/
lemma freeCount {ρ : ExactRestriction n ℓ} :
    ρ.axis.support.card = ℓ := by
  simpa using ρ.axis.card

/-- Число фиксированных координат — `n - ℓ`. -/
lemma fixedCount {ρ : ExactRestriction n ℓ} :
    ρ.axis.fixed.card = n - ℓ := ρ.axis.card_fixed

/--
  Лист совершенного ствола, соответствующий точной рестрикции: он определяется
  уникальной ветвью, которая согласована с таблицей значений `ρ.values`.
-/
noncomputable def toLeaf (ρ : ExactRestriction n ℓ) : Subcube n :=
  Axis.leafForPoint (n := n) (ℓ := ℓ) ρ.axis ρ.values

/-- Полученный лист действительно входит в список `leafList` выбранной оси. -/
lemma toLeaf_mem (ρ : ExactRestriction n ℓ) :
    toLeaf (n := n) (ℓ := ℓ) ρ
      ∈ Axis.leafList (n := n) (ℓ := ℓ) ρ.axis := by
  classical
  simpa [toLeaf] using
    (Axis.leafForPoint_mem (n := n) (ℓ := ℓ)
      (A := ρ.axis) (x := ρ.values))

/-- Значение `ρ.values` удовлетворяет всем ограничениям листа `toLeaf ρ`. -/
lemma mem_toLeaf_values (ρ : ExactRestriction n ℓ) :
    mem (toLeaf (n := n) (ℓ := ℓ) ρ) ρ.values := by
  classical
  simpa [toLeaf] using
    (Axis.mem_leafForPoint (n := n) (ℓ := ℓ)
      (A := ρ.axis) (x := ρ.values))

/--
  Если лист `β` принадлежит совершенном стволу оси `ρ.axis`, то `β` совпадает с
  `toLeaf ρ` тогда и только тогда, когда таблица значений `ρ.values` принадлежит
  подкубу `β`.
-/
lemma toLeaf_eq_iff_mem {ρ : ExactRestriction n ℓ}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) ρ.axis) :
    toLeaf (n := n) (ℓ := ℓ) ρ = β ↔ mem β ρ.values := by
  classical
  simpa [toLeaf] using
    (Axis.leafForPoint_eq_iff_mem (n := n) (ℓ := ℓ)
      (A := ρ.axis) (β := β) hβ (x := ρ.values))

/--
  Множество точных рестрикций с фиксированной осью `A`, чей лист совпадает с `β`,
  содержит ровно `2^(n - ℓ)` элементов.  Эквивалентно, столько же точек лежит на
  самом листе `β`.
-/
lemma axisLeafFiber_card (A : Axis n ℓ)
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A) :
    (Finset.univ.filter fun ρ : ExactRestriction n ℓ =>
        ρ.axis = A ∧ toLeaf (n := n) (ℓ := ℓ) ρ = β).card
      = Nat.pow 2 (n - ℓ) := by
  classical
  -- Опишем подтип таких рестрикций через явную биекцию с точками листа `β`.
  have hcard_subtype :
      Fintype.card {ρ : ExactRestriction n ℓ //
          ρ.axis = A ∧ toLeaf (n := n) (ℓ := ℓ) ρ = β}
        = Nat.pow 2 (n - ℓ) := by
    let e :
        {ρ : ExactRestriction n ℓ //
            ρ.axis = A ∧ toLeaf (n := n) (ℓ := ℓ) ρ = β}
          ≃ {x : BitVec n // mem β x} :=
      { toFun := by
          intro ρ
          rcases ρ with ⟨ρ, hρ⟩
          rcases hρ with ⟨haxis, hleaf⟩
          have hβ' : β ∈ Axis.leafList (n := n) (ℓ := ℓ) ρ.axis := by
            simpa [haxis] using hβ
          have hmem : mem β ρ.values :=
            (toLeaf_eq_iff_mem (n := n) (ℓ := ℓ) (ρ := ρ) hβ').mp hleaf
          exact ⟨ρ.values, hmem⟩
        , invFun := by
            intro x
            rcases x with ⟨x, hx⟩
            refine ⟨⟨A, x⟩, ?_⟩
            constructor
            · rfl
            · have hβ' : β ∈ Axis.leafList (n := n) (ℓ := ℓ)
                (⟨A, x⟩ : ExactRestriction n ℓ).axis := by
                simpa using hβ
              exact
                (toLeaf_eq_iff_mem (n := n) (ℓ := ℓ)
                  (ρ := ⟨A, x⟩) hβ').mpr hx
        , left_inv := by
            intro ρ
            rcases ρ with ⟨ρ, hρ⟩
            rcases hρ with ⟨haxis, hleaf⟩
            have hβ' : β ∈ Axis.leafList (n := n) (ℓ := ℓ) ρ.axis := by
              simpa [haxis] using hβ
            have hmem : mem β ρ.values :=
              (toLeaf_eq_iff_mem (n := n) (ℓ := ℓ) (ρ := ρ) hβ').mp hleaf
            cases ρ with
            | mk axis values =>
                cases haxis
                apply Subtype.ext
                simp [hmem]
        , right_inv := by
            intro x
            rcases x with ⟨x, hx⟩
            have hβ' : β ∈ Axis.leafList (n := n) (ℓ := ℓ)
                (⟨A, x⟩ : ExactRestriction n ℓ).axis := by
              simpa using hβ
            have hleaf :
                toLeaf (n := n) (ℓ := ℓ) ⟨A, x⟩ = β :=
              (toLeaf_eq_iff_mem (n := n) (ℓ := ℓ)
                (ρ := ⟨A, x⟩) hβ').mpr hx
            simp [hleaf]
      }
    have hcongr := Fintype.card_congr e
    have hleaf := leaf_mem_card (n := n) (ℓ := ℓ) (A := A) (β := β) hβ
    simpa [hleaf] using hcongr
  -- Переводим мощность подтипа в мощность фильтра на `Finset.univ`.
  have hfilter :
      (Finset.univ.filter fun ρ : ExactRestriction n ℓ =>
          ρ.axis = A ∧ toLeaf (n := n) (ℓ := ℓ) ρ = β).card
        = Fintype.card {ρ : ExactRestriction n ℓ //
            ρ.axis = A ∧ toLeaf (n := n) (ℓ := ℓ) ρ = β} := by
    simpa using
      (Fintype.card_subtype
        (p := fun ρ : ExactRestriction n ℓ =>
          ρ.axis = A ∧ toLeaf (n := n) (ℓ := ℓ) ρ = β)).symm
  simpa [hfilter, hcard_subtype]

/-- Изоморфизм между точными рестрикциями и парами «ось + таблица значений». -/
@[simp] def equivAxisBitVec (n ℓ : Nat) :
    ExactRestriction n ℓ ≃ Axis n ℓ × BitVec n where
  toFun := fun ρ => (ρ.axis, ρ.values)
  invFun := fun p =>
    { axis := p.1
      values := p.2 }
  left_inv := by intro ρ; cases ρ <;> simp
  right_inv := by intro p; cases p <;> simp

/-- Тип `ExactRestriction n ℓ` конечно, так как эквивалентен декартову
произведению конечных множеств. -/
@[simp] theorem finite (n ℓ : Nat) : Finite (ExactRestriction n ℓ) := by
  classical
  have : Finite (Axis n ℓ × BitVec n) := by infer_instance
  simpa using (equivAxisBitVec n ℓ).finite_iff.mpr this

noncomputable instance instFintype (n ℓ : Nat) :
    Fintype (ExactRestriction n ℓ) := Fintype.ofFinite _

end ExactRestriction

/-!
### Вероятностная модель exact-ℓ рестрикций

Для формального доказательства switching-леммы нам потребуется аккуратное
описание распределения на точных рестрикциях.  В этом разделе мы собираем
все необходимые определения и арифметические факты, чтобы позднее не
отвлекаться на подсчёты.
-/

open scoped ENNReal

namespace Distribution

variable {n ℓ : Nat}

/-- Равномерное распределение на множествах свободных координат. -/
noncomputable def axisUniform (n ℓ : Nat) : PMF (Axis n ℓ) :=
  PMF.uniform (Axis n ℓ)

@[simp] lemma axisUniform_apply (n ℓ : Nat) (A : Axis n ℓ) :
    axisUniform n ℓ A = (1 : ℝ≥0∞)
        / Fintype.card (Axis n ℓ) := by
  classical
  simpa [axisUniform] using (PMF.uniform_apply (α := Axis n ℓ) A)

/--
  Равномерное распределение на точных рестрикциях строится как образ
  равномерного распределения на произведении `Axis × BitVec` через
  биекцию из `ExactRestriction.equivAxisBitVec`.
-/
noncomputable def restrictionUniform (n ℓ : Nat) : PMF (ExactRestriction n ℓ) :=
  (PMF.uniform (Axis n ℓ × BitVec n)).map
    (fun p => (ExactRestriction.equivAxisBitVec n ℓ).symm p)

@[simp] lemma restrictionUniform_apply (n ℓ : Nat)
    (ρ : ExactRestriction n ℓ) :
    restrictionUniform n ℓ ρ =
      (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) := by
  classical
  simpa [restrictionUniform]
    using (PMF.uniform_map_equiv
        (α := Axis n ℓ × BitVec n)
        (ExactRestriction.equivAxisBitVec n ℓ).symm ρ)

/-- Число точных рестрикций равно `|Axis| * |BitVec|`. -/
@[simp] lemma restriction_card (n ℓ : Nat) :
    Fintype.card (ExactRestriction n ℓ)
      = Fintype.card (Axis n ℓ) * Fintype.card (BitVec n) := by
  classical
  have := Fintype.card_congr (ExactRestriction.equivAxisBitVec n ℓ)
  simpa [Fintype.card_prod] using this

/-- Биекция между рестрикциями с фиксированной осью и `BitVec`. -/
@[simp] def fiberEquiv (A : Axis n ℓ) :
    { ρ : ExactRestriction n ℓ // ρ.axis = A } ≃ BitVec n where
  toFun := fun ρ => ρ.1.values
  invFun := fun σ =>
    ⟨{ axis := A, values := σ }, by simp⟩
  left_inv := by
    intro ρ
    cases' ρ with ρ hρ
    simp
  right_inv := by
    intro σ
    simp

@[simp] lemma fiber_card (A : Axis n ℓ) :
    Fintype.card { ρ : ExactRestriction n ℓ // ρ.axis = A }
      = Fintype.card (BitVec n) := by
  classical
  have := Fintype.card_congr (fiberEquiv (n := n) (ℓ := ℓ) A)
  simpa using this

/--
  Проекция равномерного распределения на рестрикциях обратно даёт ровно
  равномерное распределение на множествах свободных координат.
-/
lemma map_axis_uniform (n ℓ : Nat) :
    (restrictionUniform n ℓ).map (fun ρ => ρ.axis) = axisUniform n ℓ := by
  classical
  -- Нормирующий множитель равномерного распределения на рестрикциях.
  set mass : ℝ≥0∞ :=
      (1 : ℝ≥0∞) / Fintype.card (ExactRestriction n ℓ) with hmass
  have hmass_apply :
      ∀ ρ : ExactRestriction n ℓ, restrictionUniform n ℓ ρ = mass := by
    intro ρ
    have := restrictionUniform_apply (n := n) (ℓ := ℓ) ρ
    -- Заменяем мощность произведения на мощность самого типа рестрикций.
    have hcard :
        (Fintype.card (Axis n ℓ × BitVec n) : ℝ≥0∞)
          = Fintype.card (ExactRestriction n ℓ) := by
      have := restriction_card (n := n) (ℓ := ℓ)
      exact_mod_cast this.symm
    simpa [hmass, hcard]
  -- Вычисляем массу проекции в терминах суммы по файберу над конкретной осью.
  ext A
  have hsum :
      (restrictionUniform n ℓ).map (fun ρ => ρ.axis) A
        = ∑ ρ : ExactRestriction n ℓ,
            if ρ.axis = A then mass else 0 := by
    have := tsum_fintype
        (fun ρ : ExactRestriction n ℓ => if ρ.axis = A then mass else 0)
    -- Разворачиваем определение `PMF.map` и подставляем `mass`.
    simpa [PMF.map_apply, hmass_apply, hmass]
      using this.symm
  -- Переписываем сумму через фильтрованное множество.
  have hfilter :
      ∑ ρ : ExactRestriction n ℓ,
          if ρ.axis = A then mass else 0
        = ∑ ρ in Finset.univ.filter (fun ρ => ρ.axis = A), mass := by
    simpa using
      (Finset.sum_filter
        (s := Finset.univ)
        (p := fun ρ : ExactRestriction n ℓ => ρ.axis = A)
        (f := fun _ => mass)).symm
  -- Сумма константы равна числу элементов файбера, умноженному на `mass`.
  have hconst :
      ∑ ρ in Finset.univ.filter (fun ρ : ExactRestriction n ℓ => ρ.axis = A), mass
        = ((Finset.univ.filter (fun ρ : ExactRestriction n ℓ => ρ.axis = A)).card : ℝ≥0∞)
            * mass := by
    simpa [nsmul_eq_mul]
      using
        (Finset.sum_const
          (s := Finset.univ.filter (fun ρ : ExactRestriction n ℓ => ρ.axis = A))
          (a := mass))
  -- Замечаем, что мощность фильтра совпадает с мощностью файбера.
  have hcard :
      ((Finset.univ.filter (fun ρ : ExactRestriction n ℓ => ρ.axis = A)).card : ℝ≥0∞)
        = Fintype.card { ρ : ExactRestriction n ℓ // ρ.axis = A } := by
    have := Fintype.card_subtype (fun ρ : ExactRestriction n ℓ => ρ.axis = A)
    simpa using (congrArg (fun k : Nat => (k : ℝ≥0∞)) this)
  -- Собираем вычисления.
  have hproj :
      (restrictionUniform n ℓ).map (fun ρ => ρ.axis) A
        = (Fintype.card { ρ : ExactRestriction n ℓ // ρ.axis = A } : ℝ≥0∞)
            * mass := by
    simpa [hsum, hfilter, hconst, hcard]
  -- Кардинальность каждого файбера равна `|BitVec n|`.
  have hfiber := fiber_card (n := n) (ℓ := ℓ) A
  -- Переписываем mass через произведение мощностей.
  have hmass_prod :
      mass = (1 : ℝ≥0∞)
          / (Fintype.card (Axis n ℓ) * Fintype.card (BitVec n)) := by
    have := restriction_card (n := n) (ℓ := ℓ)
    have hcast :
        (Fintype.card (ExactRestriction n ℓ) : ℝ≥0∞)
          = Fintype.card (Axis n ℓ) * Fintype.card (BitVec n) := by
      exact_mod_cast this
    simpa [hmass, hcast]
  -- Преобразуем произведение к целевому виду.
  have hmul :
      (Fintype.card (BitVec n) : ℝ≥0∞)
          * ((1 : ℝ≥0∞)
              / (Fintype.card (Axis n ℓ) * Fintype.card (BitVec n)))
        = (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ) := by
    by_cases haxis : Fintype.card (Axis n ℓ) = 0
    · -- Пустой случай невозможен из-за наличия `A`, но формула остаётся корректной.
      have : (Fintype.card (Axis n ℓ) : ℝ≥0∞) = 0 := by
        exact_mod_cast haxis
      simp [haxis, this]
    · -- Основной случай: можно сократить по `|BitVec n|`.
      have hbit : (Fintype.card (BitVec n) : ℝ≥0∞) ≠ 0 := by
        have hpos : (0 : Nat) < Fintype.card (BitVec n) := by
          -- `BitVec n` всегда содержит хотя бы нулевой вектор.
          refine Fintype.card_pos_iff.mpr ?_
          refine ⟨0, ?_⟩
          simp
        exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
      have haxis' : (Fintype.card (Axis n ℓ) : ℝ≥0∞) ≠ 0 := by
        have hpos : (0 : Nat) < Fintype.card (Axis n ℓ) := by
          -- Из существования `A` следует непустота множества.
          haveI : Nonempty (Axis n ℓ) := ⟨A⟩
          exact Fintype.card_pos_iff.mpr inferInstance
        exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
      -- Используем рациональное тождество `b / (a * b) = 1 / a`.
      have hcalc :=
        ENNReal.mul_div_mul_left
          (1 : ℝ≥0∞)
          (Fintype.card (BitVec n) : ℝ≥0∞)
          (Fintype.card (Axis n ℓ) : ℝ≥0∞)
          (by exact hbit)
      -- Раскрываем и перенося множители.
      have hswap :
          (Fintype.card (Axis n ℓ) : ℝ≥0∞)
              * (Fintype.card (BitVec n) : ℝ≥0∞)
          = (Fintype.card (BitVec n) : ℝ≥0∞)
              * (Fintype.card (Axis n ℓ) : ℝ≥0∞) := by
        simpa using mul_comm _ _
      -- Подставляем в формулу и упрощаем.
      simpa [hswap, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hcalc
  -- Наконец, сравниваем с явным выражением для `axisUniform`.
  have hproj' :
      (restrictionUniform n ℓ).map (fun ρ => ρ.axis) A
        = (Fintype.card (BitVec n) : ℝ≥0∞)
            * ((1 : ℝ≥0∞)
                / (Fintype.card (Axis n ℓ) * Fintype.card (BitVec n))) := by
    simpa [hproj, hfiber, hmass_prod]
  have htarget := axisUniform_apply (n := n) (ℓ := ℓ) A
  -- Переходим от промежуточного выражения к явной формуле `axisUniform`.
  have hvalue :
      (Fintype.card (BitVec n) : ℝ≥0∞)
          * ((1 : ℝ≥0∞)
              / (Fintype.card (Axis n ℓ) * Fintype.card (BitVec n)))
        = axisUniform n ℓ A := by
    simpa [axisUniform, htarget] using hmul
  exact hproj'.trans hvalue

end Distribution

end RandomRestriction
end ThirdPartyFacts
end Pnp3
