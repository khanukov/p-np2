/-
  pnp3/Core/BooleanBasics.lean

  Базовые определения для SAL:
  - BitVec n  := Fin n → Bool
  - Subcube n := Fin n → Option Bool   (some b = фиксированный бит, none = свободно)
  - memB      : булева принадлежность x подкубу β
  - coveredB  : индикатор "x покрыт объединением подкубов"
  - errU      : ошибка аппроксимации по равномерному распределению (через полный перебор)
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace List

/--
`flatMap` по одноэлементным спискам совпадает с обычным `map`.
-/
lemma flatMap_singleton_eq_map {α β : Type _} (f : α → β) :
    ∀ L : List α, L.flatMap (fun x => [f x]) = L.map f
  | [] => by simp
  | x :: L => by
      simpa [List.flatMap_cons, List.map_cons,
        flatMap_singleton_eq_map (f := f) (L := L)]

end List

open scoped BigOperators

namespace Pnp3
namespace Core

abbrev Q := Rat
abbrev BitVec (n : Nat) := Fin n → Bool
abbrev Subcube (n : Nat) := Fin n → Option Bool

/--
`Subcube.assign β i b` пытается зафиксировать `i`-й бит подкуба `β` значением `b`.

* Если координата `i` ещё не фиксирована (`β i = none`), мы создаём новый
  подкуб, совпадающий с `β` на всех прочих координатах и хранящий `some b`
  в позиции `i`.
* Если координата уже содержит `some b`, дополнительных ограничений не
  появляется, и мы возвращаем исходный подкуб `β`.
* Если же координата уже фиксирована противоположным значением, операция
  противоречива и возвращает `none`.
-/
def Subcube.assign {n : Nat} (β : Subcube n) (i : Fin n) (b : Bool) :
    Option (Subcube n) :=
  match β i with
  | none      =>
      -- Новый подкуб: на `i` ставим `b`, остальные координаты оставляем как были.
      some fun j => if j = i then some b else β j
  | some bOld  =>
      -- Совместимость возможна только при совпадающих значениях.
      if b = bOld then
        some β
      else
        none

/--
Одна фиксация бита — пара «индекс, значение».  Мы выделяем этот тип в отдельное
имя, чтобы в дальнейшем говорить о списках фиксаций.
-/
abbrev BitFix (n : Nat) := Fin n × Bool

/--
Одновременное применение последовательности фиксаций.  Если какое-то из
присваиваний противоречит уже установленным значениям, результатом будет `none`.
В противном случае мы последовательно сужаем подкуб и возвращаем итоговый
результат.
-/
def Subcube.assignMany {n : Nat} (β : Subcube n) : List (BitFix n) → Option (Subcube n)
  | [] =>
      -- Пустой список не добавляет ограничений.
      some β
  | (i, b) :: rest =>
      -- Сначала фиксируем текущую координату, затем рекурсивно обрабатываем хвост.
      match Subcube.assign β i b with
      | none      => none
      | some β'   => Subcube.assignMany β' rest

@[simp] lemma assignMany_nil {n : Nat} (β : Subcube n) :
    Subcube.assignMany β [] = some β := rfl

/-- Присваивание одного бита — тот же `Subcube.assign`. -/
@[simp] lemma assignMany_singleton {n : Nat} (β : Subcube n)
    (i : Fin n) (b : Bool) :
    Subcube.assignMany β [(i, b)] = Subcube.assign β i b := by
  cases hstep : Subcube.assign β i b with
  | none => simp [Subcube.assignMany, hstep]
  | some β' => simp [Subcube.assignMany, hstep]

/--
Развёрнутое описание обработки головы списка.  Лемма пригодится при индуктивных
доказательствах свойств `assignMany`.
-/
@[simp] lemma assignMany_cons {n : Nat} (β : Subcube n)
    (i : Fin n) (b : Bool) (rest : List (BitFix n)) :
    Subcube.assignMany β ((i, b) :: rest) =
      match Subcube.assign β i b with
      | none      => none
      | some β'   => Subcube.assignMany β' rest := rfl

/-- Bool → Nat (true ↦ 1, false ↦ 0). -/
@[inline] def b2n (b : Bool) : Nat := if b then 1 else 0

@[simp] lemma b2n_true : b2n true = 1 := by simp [b2n]

@[simp] lemma b2n_false : b2n false = 0 := by simp [b2n]

/-- "xor" для Bool (без зависимостей). -/
@[inline] def boolXor (a b : Bool) : Bool := if a = b then false else true

@[simp] lemma boolXor_self (a : Bool) : boolXor a a = false := by
  simp [boolXor]

@[simp] lemma boolXor_false_right (a : Bool) : boolXor a false = a := by
  cases a <;> simp [boolXor]

@[simp] lemma boolXor_false_left (a : Bool) : boolXor false a = a := by
  cases a <;> simp [boolXor]

/-- Удобная эквивалентность: терм `if p then true else false` равен `true` тогда и только тогда, когда выполняется `p`. -/
lemma ite_true_false_eq_true_iff {p : Prop} [Decidable p] :
    (if p then true else false) = true ↔ p := by
  by_cases hp : p <;> simp [hp]

/-- Булева принадлежность точки x подкубу β. -/
def memB {n : Nat} (β : Subcube n) (x : BitVec n) : Bool :=
  (List.finRange n).all (fun i =>
    match β i with
    | none    => true
    | some b  => if x i = b then true else false)

/-- Пропозиционная принадлежность: эквивалент булевому индикатору. -/
def mem {n : Nat} (β : Subcube n) (x : BitVec n) : Prop :=
  memB β x = true

lemma mem_iff_memB {n : Nat} (β : Subcube n) (x : BitVec n) :
    mem β x ↔ memB β x = true := Iff.rfl

/--
`memB β x = true` ⇔ "каждый зафиксированный бит β совпадает со значением x".

Формулируем это через удобную пропозицию: если `β i = some b`, то `x i = b`.
-/
lemma memB_eq_true_iff {n : Nat} (β : Subcube n) (x : BitVec n) :
    memB β x = true ↔ ∀ i : Fin n, ∀ b : Bool, β i = some b → x i = b := by
  classical
  constructor
  · intro h
    have hall := List.all_eq_true.mp h
    intro i b hib
    have hi := hall i (List.mem_finRange _)
    -- Раскрываем определение `memB` и используем предыдущую эквивалентность.
    have hi' : (if x i = b then true else false) = true := by
      simpa [memB, hib] using hi
    exact (ite_true_false_eq_true_iff).mp hi'
  · intro h
    -- Покажем, что для каждого индекса из `finRange` выполняется проверка в `memB`.
    have hall : ∀ i ∈ List.finRange n,
        (match β i with
          | none => true
          | some b => if x i = b then true else false) = true := by
      intro i hi
      cases hβ : β i with
      | none => simp
      | some b =>
          have hx : x i = b := h i b hβ
          simp [hx]
    exact List.all_eq_true.mpr hall

/-- Удобная пропозициональная версия условия принадлежности. -/
lemma mem_iff {n : Nat} (β : Subcube n) (x : BitVec n) :
    mem β x ↔ ∀ i : Fin n, ∀ b : Bool, β i = some b → x i = b := by
  simpa [mem] using memB_eq_true_iff (β := β) (x := x)

/-- Тривиальный подкуб, у которого все координаты свободны, содержит любую точку. -/
@[simp] lemma mem_top {n : Nat} (x : BitVec n) :
    mem (fun _ : Fin n => (none : Option Bool)) x := by
  classical
  simp [mem, memB]

/--
Если мы успешно присваиваем значение `b` координате `i`, то принадлежность
новому подкубу эквивалентна одновременному выполнению старых ограничений и
условия `x i = b`.
-/
lemma mem_assign_iff {n : Nat} {β : Subcube n} {i : Fin n} {b : Bool}
    {γ : Subcube n}
    (hassign : Subcube.assign β i b = some γ)
    (x : BitVec n) :
    mem γ x ↔ mem β x ∧ x i = b := by
  classical
  cases hβ : β i with
  | none =>
      -- Координата была свободной: вычислим явную форму `γ`.
      have hassign' :
          some (fun j => if j = i then some b else β j) = some γ := by
        simpa [Subcube.assign, hβ] using hassign
      have hγ : γ = fun j => if j = i then some b else β j :=
        (Option.some.inj hassign').symm
      subst hγ
      constructor
      · intro hγ
        have hγ' :=
          (mem_iff (β := fun j => if j = i then some b else β j) (x := x)).1 hγ
        have hβprop : ∀ j : Fin n, ∀ c : Bool, β j = some c → x j = c := by
          intro j c hj
          by_cases hji : j = i
          · subst hji
            have : False := by simpa [hβ] using hj
            exact False.elim this
          · have : (if j = i then some b else β j) = some c := by
              simpa [hji, hj]
            exact hγ' j c this
        have hβmem : mem β x :=
          (mem_iff (β := β) (x := x)).2 hβprop
        have hi : x i = b := by
          have : (if i = i then some b else β i) = some b := by simp
          have hinst := hγ' i b this
          simpa using hinst
        exact ⟨hβmem, hi⟩
      · intro hx
        rcases hx with ⟨hβmem, hib⟩
        have hβ' := (mem_iff (β := β) (x := x)).1 hβmem
        refine
          (mem_iff (β := fun j => if j = i then some b else β j) (x := x)).2 ?_
        intro j c hj
        by_cases hji : j = i
        · subst hji
          have hj' : some b = some c := by simpa using hj
          have hb' : b = c := by simpa using Option.some.inj hj'
          have : c = b := hb'.symm
          simp [this, hib]
        · have : β j = some c := by simpa [hji] using hj
          exact hβ' j c this
  | some bOld =>
      -- Координата уже фиксирована. Возможны два случая: согласие или конфликт.
      have hb' : b = bOld := by
        by_contra hbneq
        have : Subcube.assign β i b = none := by
          simp [Subcube.assign, hβ, hbneq]
        have hcontra : none = some γ := by
          simpa [Subcube.assign, hβ, hbneq] using hassign
        cases hcontra
      have hγ : γ = β := by
        have hassign' : some β = some γ := by
          simpa [Subcube.assign, hβ, hb'] using hassign
        exact (Option.some.inj hassign').symm
      constructor
      · intro hγmem
        have hβmem : mem β x := by simpa [hγ] using hγmem
        have hprop := (mem_iff (β := β) (x := x)).1 hβmem
        have hi : x i = bOld := by simpa using hprop i bOld hβ
        have hi' : x i = b := by simpa [hb'] using hi
        exact ⟨hβmem, hi'⟩
      · intro hx
        exact (by simpa [hγ] using hx.1)

/--
Если серия присваиваний `assignMany` успешно завершилась, то принадлежность
построенному подкубу эквивалентна исходной принадлежности и выполнению всех
зафиксированных битов.
-/
lemma mem_assignMany_iff {n : Nat} {β γ : Subcube n}
    {updates : List (BitFix n)}
    (hassign : Subcube.assignMany β updates = some γ)
    (x : BitVec n) :
    mem γ x ↔ mem β x ∧ ∀ u ∈ updates, x u.1 = u.2 := by
  classical
  induction updates generalizing β γ with
  | nil =>
      -- Пустой список: получаем тот же подкуб без дополнительных условий.
      have hγ : β = γ := by
        simpa [Subcube.assignMany] using hassign
      subst hγ
      simp
  | cons ub rest ih =>
      -- Разбираем первое присваивание и рекурсивно применяем гипотезу индукции.
      rcases ub with ⟨i, b⟩
      dsimp [Subcube.assignMany] at hassign
      cases hstep : Subcube.assign β i b with
      | none =>
          -- Конфликт невозможен, ведь результат объявлен как `some γ`.
          simpa [Subcube.assignMany, hstep] using hassign
      | some β' =>
          have hrest : Subcube.assignMany β' rest = some γ := by
            simpa [Subcube.assignMany, hstep] using hassign
          have htail := ih (β := β') (γ := γ) hrest
          -- Эквивалентность для первого шага: принадлежность β' ↔ (β ∧ нужный бит).
          have hhead :=
            (mem_assign_iff (β := β) (γ := β') (i := i) (b := b)
              (x := x) hstep)
          -- Склеиваем два эквивалента и приводим результат к компактному виду.
          have hcombined :
              mem γ x ↔ (mem β x ∧ x i = b) ∧ ∀ u ∈ rest, x u.1 = u.2 := by
            simpa [hhead, and_left_comm, and_assoc] using htail
          -- Завершаем преобразование, переписывая условие на список.
          simpa [List.forall_mem_cons, and_left_comm, and_assoc] using hcombined


/-- Индикатор покрытия x объединением подкубов из списка Rset. -/
def coveredB {n : Nat} (Rset : List (Subcube n)) (x : BitVec n) : Bool :=
  Rset.any (fun β => memB β x)

/-- Покрытие в терминах пропозициональной принадлежности. -/
def covered {n : Nat} (Rset : List (Subcube n)) (x : BitVec n) : Prop :=
  ∃ β ∈ Rset, mem β x

lemma covered_iff {n : Nat} (Rset : List (Subcube n)) (x : BitVec n) :
    covered Rset x ↔ coveredB Rset x = true := by
  classical
  constructor
  · intro h
    rcases h with ⟨β, hβ, hmem⟩
    exact List.any_eq_true.mpr ⟨β, hβ, hmem⟩
  · intro h
    rcases List.any_eq_true.mp h with ⟨β, hβ, hmem⟩
    exact ⟨β, hβ, hmem⟩

@[simp] lemma coveredB_nil {n : Nat} (x : BitVec n) :
    coveredB ([] : List (Subcube n)) x = false := by
  simp [coveredB]

/-- Явная формула для `coveredB` на конструкторе `cons`. -/
lemma coveredB_cons {n : Nat} (β : Subcube n) (R : List (Subcube n))
    (x : BitVec n) :
    coveredB (β :: R) x = (memB β x || coveredB R x) := by
  classical
  simp [coveredB]

/-- Эквивалентность `covered` и `coveredB` в явной форме через конструктор. -/
lemma covered_cons {n : Nat} (β : Subcube n) (R : List (Subcube n))
    (x : BitVec n) :
    covered (β :: R) x ↔ mem β x ∨ covered R x := by
  classical
  constructor
  · intro h
    rcases h with ⟨γ, hγ, hx⟩
    simp at hγ
    rcases hγ with hγ | hγ
    · left; subst hγ; simpa [mem] using hx
    · right; exact ⟨γ, hγ, hx⟩
  · intro h
    rcases h with h | h
    · exact ⟨β, by simp, h⟩
    · rcases h with ⟨γ, hγ, hx⟩; exact ⟨γ, by simp [hγ], hx⟩

/-- Удаление дубликатов не меняет факт покрытия точки объединением подкубов. -/
lemma covered_dedup {n : Nat} [DecidableEq (Subcube n)]
    (R : List (Subcube n)) (x : BitVec n) :
    covered (R.dedup) x ↔ covered R x := by
  classical
  constructor
  · intro h
    rcases h with ⟨β, hβ, hx⟩
    refine ⟨β, ?_, hx⟩
    have : β ∈ R.dedup := by simpa using hβ
    exact (List.mem_dedup.mp this)
  · intro h
    rcases h with ⟨β, hβ, hx⟩
    refine ⟨β, ?_, hx⟩
    exact (List.mem_dedup.mpr hβ)

/-- Булев индикатор покрытия также не чувствителен к дубликатам. -/
lemma coveredB_dedup {n : Nat} [DecidableEq (Subcube n)]
    (R : List (Subcube n)) (x : BitVec n) :
    coveredB (R.dedup) x = coveredB R x := by
  classical
  by_cases hcov : covered R x
  · have hcov' : covered (R.dedup) x :=
      (covered_dedup (n := n) R x).mpr hcov
    have htrue : coveredB R x = true :=
      (covered_iff (Rset := R) x).mp hcov
    have htrue' : coveredB (R.dedup) x = true :=
      (covered_iff (Rset := R.dedup) x).mp hcov'
    simp [htrue, htrue']
  · have hcov' : ¬ covered (R.dedup) x := by
      intro h'; exact hcov ((covered_dedup (n := n) R x).mp h')
    have hfalse : coveredB R x = false := by
      cases hcase : coveredB R x with
      | false => rfl
      | true =>
          have : covered R x :=
            (covered_iff (Rset := R) x).mpr (by simpa [hcase])
          exact (hcov this).elim
    have hfalse' : coveredB (R.dedup) x = false := by
      cases hcase : coveredB (R.dedup) x with
      | false => rfl
      | true =>
          have : covered (R.dedup) x :=
            (covered_iff (Rset := R.dedup) x).mpr (by simpa [hcase])
          exact (hcov' this).elim
    simp [hfalse, hfalse']

/--
  Если два списка содержат одни и те же элементы (с точностью до перестановки
  и кратности), то их булевые индикаторы покрытия совпадают.
-/
lemma coveredB_eq_of_mem_equiv {n : Nat}
    {R₁ R₂ : List (Subcube n)}
    (h : ∀ β, β ∈ R₁ ↔ β ∈ R₂) :
    (fun x => coveredB R₁ x) = fun x => coveredB R₂ x :=
  by
    classical
    funext x
    have hcovered : covered R₁ x ↔ covered R₂ x := by
      constructor
      · intro hx
        rcases hx with ⟨β, hβ, hmem⟩
        have hβ' : β ∈ R₂ := (h β).1 hβ
        exact ⟨β, hβ', hmem⟩
      · intro hx
        rcases hx with ⟨β, hβ, hmem⟩
        have hβ' : β ∈ R₁ := (h β).2 hβ
        exact ⟨β, hβ', hmem⟩
    by_cases hcov : covered R₁ x
    · -- Обе функции возвращают `true`.
      have hcov' : covered R₂ x := (hcovered.mp hcov)
      have htrue₁ : coveredB R₁ x = true :=
        (covered_iff (Rset := R₁) x).mp hcov
      have htrue₂ : coveredB R₂ x = true :=
        (covered_iff (Rset := R₂) x).mp hcov'
      simp [htrue₁, htrue₂]
    · -- Обе функции возвращают `false`.
      have hcov' : ¬ covered R₂ x := by
        intro hx
        exact hcov (hcovered.mpr hx)
      have hfalse₁ : coveredB R₁ x = false := by
        by_cases hb : coveredB R₁ x = true
        · have hx := (covered_iff (Rset := R₁) x).mpr hb
          exact (hcov hx).elim
        · cases hcase : coveredB R₁ x with
          | false => simp [hcase]
          | true => cases hb hcase
      have hfalse₂ : coveredB R₂ x = false := by
        by_cases hb : coveredB R₂ x = true
        · have hx := (covered_iff (Rset := R₂) x).mpr hb
          exact (hcov' hx).elim
        · cases hcase : coveredB R₂ x with
          | false => simp [hcase]
          | true => cases hb hcase
      simp [hfalse₁, hfalse₂]

/--
  Если финитные множества уникальных элементов списков совпадают, то и
  функции покрытия идентичны.  В сочетании с предыдущей леммой это позволяет
  рассуждать в терминах `List.toFinset`, не отслеживая явные биекции между
  списками.
-/
lemma coveredB_eq_of_toFinset_eq {n : Nat}
    {R₁ R₂ : List (Subcube n)}
    (h : R₁.toFinset = R₂.toFinset) :
    (fun x => coveredB R₁ x) = fun x => coveredB R₂ x := by
  classical
  refine coveredB_eq_of_mem_equiv (n := n) ?_
  intro β
  constructor <;> intro hβ
  · have hβ' : β ∈ R₁.toFinset := by
      simpa [List.mem_toFinset] using hβ
    have hβ'' : β ∈ R₂.toFinset := by simpa [h] using hβ'
    simpa [List.mem_toFinset] using hβ''
  · have hβ' : β ∈ R₂.toFinset := by
      simpa [List.mem_toFinset] using hβ
    have hβ'' : β ∈ R₁.toFinset := by simpa [h] using hβ'
    simpa [List.mem_toFinset] using hβ''

/-- Построить BitVec длины n из числа k (по двоичным битам). -/
def vecOfNat (n : Nat) (k : Nat) : BitVec n :=
  fun i => Nat.testBit k i.val

/-- Полный список всех BitVec длины n. -/
def allBitVec (n : Nat) : List (BitVec n) :=
  (List.range (Nat.pow 2 n)).map (vecOfNat n)

/- Ошибка аппроксимации: доля входов, где f(x) ≠ coveredB Rset x. -/
def errU {n : Nat} (f : BitVec n → Bool) (Rset : List (Subcube n)) : Q :=
  let mismatches :=
    ((Finset.univ : Finset (BitVec n)).filter
      (fun x => f x ≠ coveredB Rset x)).card
  ((mismatches : Nat) : Q) / ((Nat.pow 2 n : Nat) : Q)

/-- Ошибка аппроксимации не меняется при удалении дубликатов подкубов. -/
lemma errU_dedup {n : Nat} [DecidableEq (Subcube n)]
    (f : BitVec n → Bool) (R : List (Subcube n)) :
    errU f (R.dedup) = errU f R := by
  classical
  unfold errU
  have hfun :
      (fun x : BitVec n => f x ≠ coveredB (R.dedup) x) =
        (fun x : BitVec n => f x ≠ coveredB R x) := by
    funext x
    have hcov := coveredB_dedup (n := n) (R := R) (x := x)
    have hiff : f x = coveredB (R.dedup) x ↔ f x = coveredB R x := by
      constructor <;> intro hfx
      · exact hfx.trans hcov
      · exact hfx.trans hcov.symm
    have hnot := not_congr hiff
    exact propext hnot
  simp [hfun]

/-- Если функция `f` совпадает с покрытием `coveredB`, то ошибка аппроксимации
равна нулю. -/
lemma errU_eq_zero_of_agree {n : Nat}
    (f : BitVec n → Bool) (Rset : List (Subcube n))
    (h : ∀ x, f x = coveredB Rset x) :
    errU f Rset = 0 := by
  unfold errU
  set mismatches :=
    ((Finset.univ : Finset (BitVec n)).filter
      (fun x => f x ≠ coveredB Rset x)).card
  have hfilter :
      ((Finset.univ : Finset (BitVec n)).filter
        (fun x => f x ≠ coveredB Rset x)) = (∅ : Finset (BitVec n)) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨_, hneq⟩
      exact (hneq (h x)).elim
    · intro hx; simpa using hx
  have hmismatch : mismatches = 0 := by
    simpa [mismatches, hfilter]
  simp [mismatches, hmismatch]

/-- Частный случай: пустой набор подкубов идеально аппроксимирует константный
нуль. -/
@[simp] lemma errU_false_nil {n : Nat} :
    errU (fun (_ : BitVec n) => false) ([] : List (Subcube n)) = 0 := by
  apply errU_eq_zero_of_agree
  intro x
  simp

/-- Решимость принадлежности точки подкубу: определяется через булев индикатор. -/
instance mem_decidable {n : Nat} (β : Subcube n) :
    DecidablePred (fun x : BitVec n => mem β x) := by
  intro x
  unfold mem
  infer_instance

/--
  Размер подкуба равен `2^(n - t)`, где `t` — число фиксированных координат.
  Мы явно строим биекцию между функциями в подкубе и булевыми присваиваниями
  на множестве свободных координат.
-/
theorem subcube_card_pow {n : Nat} (β : Subcube n) :
    ∃ t : Nat, t ≤ n ∧
        Fintype.card {x : BitVec n // mem β x} = Nat.pow 2 (n - t) :=
  by
    classical
    -- Индексы, на которых подкуб фиксирует значение, и свободные индексы.
    let FixedIndex : Type := {i : Fin n // ∃ b : Bool, β i = some b}
    let FreeIndex : Type := {i : Fin n // β i = none}
    -- Удобные преобразования между ``≠ none`` и существованием `some`.
    have exists_of_ne_none : ∀ {i : Fin n}, β i ≠ none → ∃ b, β i = some b := by
      intro i h
      cases hβ : β i with
      | none => exact (h hβ).elim
      | some b => exact ⟨b, rfl⟩
    have ne_none_of_exists : ∀ {i : Fin n}, (∃ b, β i = some b) → β i ≠ none :=
      by
        intro i h
        rcases h with ⟨b, hb⟩
        intro hnone
        simpa [hb] using hnone
    -- Finset-представление фиксированных и свободных координат.
    let fixedSet :=
      (Finset.univ : Finset (Fin n)).filter fun i => β i ≠ none
    let freeSet :=
      (Finset.univ : Finset (Fin n)).filter fun i => β i = none
    -- `FixedIndex` эквивалентен подтипу `fixedSet`.
    have fixedEquiv : FixedIndex ≃ {i : Fin n // i ∈ fixedSet} :=
      { toFun := fun i =>
          ⟨i.1, by
              have hi : β i.1 ≠ none := ne_none_of_exists i.2
              refine Finset.mem_filter.mpr ?_
              exact ⟨Finset.mem_univ _, hi⟩⟩
        , invFun := fun i =>
            ⟨i.1, by
                have hi : β i.1 ≠ none := (Finset.mem_filter.mp i.2).2
                exact exists_of_ne_none (i := i.1) hi⟩
        , left_inv := by intro i; ext; rfl
        , right_inv := by intro i; ext; rfl }
    have freeEquiv : FreeIndex ≃ {i : Fin n // i ∈ freeSet} :=
      { toFun := fun i =>
          ⟨i.1, by
              refine Finset.mem_filter.mpr ?_
              exact ⟨Finset.mem_univ _, i.2⟩⟩
        , invFun := fun i =>
            ⟨i.1, by
                exact (Finset.mem_filter.mp i.2).2⟩
        , left_inv := by intro i; ext; rfl
        , right_inv := by intro i; ext; rfl }
    have hfixed_card : Fintype.card FixedIndex = fixedSet.card := by
      simpa using Fintype.card_congr fixedEquiv
    have hfree_card : Fintype.card FreeIndex = freeSet.card := by
      simpa using Fintype.card_congr freeEquiv
    -- Разбиение `Fin n` на две части.
    have hsplit : freeSet.card + fixedSet.card = (Finset.univ : Finset (Fin n)).card := by
      have := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun i : Fin n => β i = none)
      simpa [freeSet, fixedSet] using this
    -- Количество фиксированных координат и его ограничение.
    let t : Nat := fixedSet.card
    have ht_le : t ≤ n := by
      have := Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
        (p := fun i : Fin n => β i ≠ none)
      simpa [t, fixedSet, Finset.card_fin] using this
    -- Число свободных координат выражается через `n - t`.
    have hfree_count : freeSet.card = n - t := by
      have hsum : freeSet.card + t = n := by
        simpa [t, Finset.card_fin] using hsplit
      have hsum' : freeSet.card + t = (n - t) + t := by
        calc
          freeSet.card + t = n := hsum
          _ = (n - t) + t := (Nat.sub_add_cancel ht_le).symm
      exact Nat.add_right_cancel hsum'
    -- Сопоставляем элементы подкуба присваиваниям свободных координат.
    let encode : {x : BitVec n // mem β x} → FreeIndex → Bool :=
      fun x i => x.1 i.1
    let decodeFun : (FreeIndex → Bool) → BitVec n :=
      fun f i =>
        if h : β i = none then
          f ⟨i, h⟩
        else
          Classical.choose (exists_of_ne_none (i := i) h)
    -- Вспомогательные леммы: удобно сворачивать определение `decodeFun`.
    have decode_eval_none (f : FreeIndex → Bool) (i : Fin n)
        (h : β i = none) : decodeFun f i = f ⟨i, h⟩ := by
      simp [decodeFun, h]
    have decode_eval_some (f : FreeIndex → Bool) (i : Fin n)
        {b : Bool} (h : β i = some b) : decodeFun f i = b := by
      have hne : β i ≠ none := by
        intro hnone; simpa [hnone] using h
      have hspec := Classical.choose_spec (exists_of_ne_none (i := i) hne)
      have hval : Classical.choose (exists_of_ne_none (i := i) hne) = b := by
        have : some (Classical.choose (exists_of_ne_none (i := i) hne)) = some b := by
          simpa [h] using hspec
        exact Option.some.inj this
      simp [decodeFun, h, hne, hval]
    let decode : (FreeIndex → Bool) → {x : BitVec n // mem β x} :=
      fun f =>
        let g := decodeFun f
        have hmem : mem β g := by
          refine (memB_eq_true_iff (β := β) (x := g)).mpr ?_
          intro i b hi
          cases hβ : β i with
          | none =>
              -- Противоречие: `β i` одновременно `none` и `some b`.
              cases (hβ ▸ hi)
          | some b' =>
              have hb' : b' = b := by
                have : some b' = some b := by simpa [hβ] using hi
                exact Option.some.inj this
              -- Удобно переписать цель через `decodeFun` и свернуть сопоставление.
              change decodeFun f i = b
              have : decodeFun f i = b' := decode_eval_some f i hβ
              simpa [hb'] using this
        ⟨g, hmem⟩
    have left_inv_decode : Function.LeftInverse decode encode := by
      intro x
      apply Subtype.ext
      funext i
      cases hβ : β i with
      | none =>
          -- Свободная координата: декодер возвращает исходный бит.
          change decodeFun (encode x) i = x.1 i
          have hdecode := decode_eval_none (encode x) i hβ
          simpa [encode] using hdecode
      | some b =>
          have hmem : x.1 i = b :=
            (memB_eq_true_iff (β := β) (x := x.1)).1 x.2 i b hβ
          change decodeFun (encode x) i = x.1 i
          have hdecode := decode_eval_some (encode x) i hβ
          simpa [encode, hmem] using hdecode
    have right_inv_decode : Function.RightInverse decode encode := by
      intro f
      funext i
      cases i with
      | mk i hi =>
          -- На свободной координате декодер просто возвращает соответствующий бит.
          change decodeFun f i = f ⟨i, hi⟩
          simpa using decode_eval_none f i hi
    let witnessEquiv : {x : BitVec n // mem β x} ≃ (FreeIndex → Bool) :=
      { toFun := encode
        , invFun := decode
        , left_inv := left_inv_decode
        , right_inv := right_inv_decode }
    have hcube_card :
        Fintype.card {x : BitVec n // mem β x}
          = Fintype.card (FreeIndex → Bool) :=
      Fintype.card_congr witnessEquiv
    have hfun_card :
        Fintype.card (FreeIndex → Bool)
          = 2 ^ Fintype.card FreeIndex := by
      simpa using (Fintype.card_fun FreeIndex Bool)
    have hfreeIndex_card : Fintype.card FreeIndex = n - t := by
      simpa [hfree_card, hfree_count]
    have hfinal :
        Fintype.card {x : BitVec n // mem β x} = 2 ^ (n - t) := by
      calc
        Fintype.card {x : BitVec n // mem β x}
            = Fintype.card (FreeIndex → Bool) := hcube_card
        _ = 2 ^ Fintype.card FreeIndex := hfun_card
        _ = 2 ^ (n - t) := by simpa [hfreeIndex_card, Fintype.card_bool]

    exact ⟨t, ht_le, hfinal⟩

/--
## Булевы формулы ограниченной ширины и частичные ограничения

В прикладных леммах о switching нам потребуются явные структуры, описывающие
литералы, клаузы, формулы в КНФ/ДНФ и операции применения случайных
ограничений.  Ранее эти определения жили во вспомогательном модуле в разделе
`ThirdPartyFacts`.  После обсуждения мы переместили их в ядро `Core`, чтобы
использовать уже готовую инфраструктуру подкубов (`Subcube`) и облегчить
дальнейшую интеграцию с остальными частями SAL.

Ниже собраны:

* структура `Literal`, представляющая требование `xᵢ = b`;
* клаузы `CnfClause` и формулы `CNF` ограниченной ширины;
* термы `DnfTerm` и формулы `DNF`;
* структура `Restriction`, расширяющая `Subcube` операциями `override` и
  `assign`;
* базовые технические леммы о применении ограничения и подсчёте вероятности
  неудачи.

Большая часть доказательств — аккуратная «арифметика списков» на уровне Lean;
они тщательно документированы, чтобы позднее использоваться в формализации
switching-лемм более высоких уровней.
-/

/- ### Литералы и клаузы -/

/- Литерал булевой формулы: пара «индекс, требуемое значение». -/
structure Literal (n : Nat) where
  idx   : Fin n
  value : Bool
  deriving DecidableEq, Repr

namespace Literal

@[simp] lemma mk_eta {n : Nat} (ℓ : Literal n) :
    Literal.mk ℓ.idx ℓ.value = ℓ := by cases ℓ <;> rfl

/-- Булева оценка литерала на точке `x`. -/
@[simp] def eval {n : Nat} (ℓ : Literal n) (x : BitVec n) : Bool :=
  if x ℓ.idx = ℓ.value then true else false

/-- Пропозиционное представление истиности литерала. -/
@[simp] def holds {n : Nat} (ℓ : Literal n) (x : BitVec n) : Prop :=
  x ℓ.idx = ℓ.value

lemma eval_eq_true_iff {n : Nat} (ℓ : Literal n) (x : BitVec n) :
    ℓ.eval x = true ↔ ℓ.holds x := by
  unfold eval holds
  by_cases hx : x ℓ.idx = ℓ.value
  · simp [hx]
  · simp [hx]

lemma eval_eq_false_iff {n : Nat} (ℓ : Literal n) (x : BitVec n) :
    ℓ.eval x = false ↔ x ℓ.idx ≠ ℓ.value := by
  unfold eval
  by_cases hx : x ℓ.idx = ℓ.value
  · simp [hx]
  · simp [hx]

lemma holds_of_eval_true {n : Nat} {ℓ : Literal n} {x : BitVec n}
    (h : ℓ.eval x = true) : ℓ.holds x :=
  (ℓ.eval_eq_true_iff x).1 h

lemma eval_true_of_holds {n : Nat} {ℓ : Literal n} {x : BitVec n}
    (h : ℓ.holds x) : ℓ.eval x = true :=
  (ℓ.eval_eq_true_iff x).2 h

end Literal

/--
Дизъюнктивная клауза (для КНФ): список литералов без повторов по индексам.
Условие `nodupIdx` предотвращает одновременное присутствие противоположных
литералов одной переменной.
-/
structure CnfClause (n : Nat) where
  literals : List (Literal n)
  nodupIdx : (literals.map (·.idx)).Nodup
  deriving Repr

namespace CnfClause

/-- Ширина клаузы — длина списка литералов. -/
@[simp] def width {n : Nat} (C : CnfClause n) : Nat :=
  C.literals.length

/-- Дизъюнктивная оценка клаузы. -/
@[simp] def eval {n : Nat} (C : CnfClause n) (x : BitVec n) : Bool :=
  C.literals.any (fun ℓ => Literal.eval ℓ x)

/-- Пропозиционное описание истинности клаузы. -/
@[simp] def holds {n : Nat} (C : CnfClause n) (x : BitVec n) : Prop :=
  ∃ ℓ ∈ C.literals, Literal.holds ℓ x

lemma eval_eq_true_iff {n : Nat} (C : CnfClause n) (x : BitVec n) :
    C.eval x = true ↔ C.holds x := by
  classical
  unfold eval holds
  constructor
  · intro h
    rcases List.any_eq_true.mp h with ⟨ℓ, hmem, hval⟩
    exact ⟨ℓ, hmem, Literal.holds_of_eval_true hval⟩
  · intro h
    rcases h with ⟨ℓ, hmem, hholds⟩
    exact List.any_eq_true.mpr ⟨ℓ, hmem, Literal.eval_true_of_holds hholds⟩

lemma eval_eq_false_iff {n : Nat} (C : CnfClause n) (x : BitVec n) :
    C.eval x = false ↔ ∀ ℓ ∈ C.literals, Literal.eval ℓ x = false := by
  classical
  unfold eval
  simpa using List.any_eq_false

lemma holds_of_mem_eval_true {n : Nat} {C : CnfClause n} {x : BitVec n}
    {ℓ : Literal n} (hmem : ℓ ∈ C.literals) (hval : Literal.eval ℓ x = true) :
    C.eval x = true := by
  classical
  unfold eval
  exact List.any_eq_true.mpr ⟨ℓ, hmem, hval⟩

end CnfClause

/--
Конъюнктивная нормальная форма ширины `w`: набор клауз, каждая из которых не
длиннее `w`.
-/
structure CNF (n w : Nat) where
  clauses : List (CnfClause n)
  width_le : ∀ C ∈ clauses, C.width ≤ w
  deriving Repr

namespace CNF

/-- Вычисление КНФ: конъюнкция клауз. -/
@[simp] def eval {n w : Nat} (F : CNF n w) (x : BitVec n) : Bool :=
  F.clauses.all (fun C => C.eval x)

/-- Пропозиционное описание истинности КНФ. -/
@[simp] def holds {n w : Nat} (F : CNF n w) (x : BitVec n) : Prop :=
  ∀ C ∈ F.clauses, C.holds x

lemma eval_eq_true_iff {n w : Nat} (F : CNF n w) (x : BitVec n) :
    F.eval x = true ↔ F.holds x := by
  classical
  unfold eval holds
  constructor
  · intro h
    intro C hC
    have hall := List.all_eq_true.mp h
    have hval : C.eval x = true := hall C hC
    exact (CnfClause.eval_eq_true_iff (C := C) (x := x)).1 hval
  · intro h
    refine List.all_eq_true.mpr ?_
    intro C hC
    have hholds : C.holds x := h C hC
    exact (CnfClause.eval_eq_true_iff (C := C) (x := x)).2 hholds

lemma eval_eq_false_iff {n w : Nat} (F : CNF n w) (x : BitVec n) :
    F.eval x = false ↔ ∃ C ∈ F.clauses, C.eval x = false := by
  classical
  unfold eval
  simpa using List.all_eq_false

end CNF

/- ### Термы и формулы ДНФ -/

/-- Термы ДНФ переиспользуют `CnfClause`, трактуя список литералов как
конъюнкцию. -/
abbrev DnfTerm (n : Nat) := CnfClause n

namespace DnfTerm

/-- Оценка терма: все литералы должны быть истинны. -/
@[simp] def eval {n : Nat} (T : DnfTerm n) (x : BitVec n) : Bool :=
  T.literals.all (fun ℓ => Literal.eval ℓ x)

/-- Пропозиционное описание истинности терма. -/
@[simp] def holds {n : Nat} (T : DnfTerm n) (x : BitVec n) : Prop :=
  ∀ ℓ ∈ T.literals, Literal.holds ℓ x

lemma eval_eq_true_iff {n : Nat} (T : DnfTerm n) (x : BitVec n) :
    T.eval x = true ↔ T.holds x := by
  classical
  unfold eval holds
  constructor
  · intro h
    have hall := List.all_eq_true.mp h
    intro ℓ hℓ
    exact Literal.holds_of_eval_true (hall ℓ hℓ)
  · intro h
    refine List.all_eq_true.mpr ?_
    intro ℓ hℓ
    exact Literal.eval_true_of_holds (h ℓ hℓ)

lemma eval_eq_false_iff {n : Nat} (T : DnfTerm n) (x : BitVec n) :
    T.eval x = false ↔ ∃ ℓ ∈ T.literals, Literal.eval ℓ x = false := by
  classical
  unfold eval
  simpa using List.all_eq_false

end DnfTerm

/-- ДНФ ширины `w`: дизъюнкция термов ограниченной длины. -/
structure DNF (n w : Nat) where
  terms : List (DnfTerm n)
  width_le : ∀ T ∈ terms, T.width ≤ w
  deriving Repr

namespace DNF

@[simp] def eval {n w : Nat} (F : DNF n w) (x : BitVec n) : Bool :=
  F.terms.any (fun T => T.eval x)

@[simp] def holds {n w : Nat} (F : DNF n w) (x : BitVec n) : Prop :=
  ∃ T ∈ F.terms, T.holds x

lemma eval_eq_true_iff {n w : Nat} (F : DNF n w) (x : BitVec n) :
    F.eval x = true ↔ F.holds x := by
  classical
  unfold eval holds
  constructor
  · intro h
    obtain ⟨T, hmem, hval⟩ := List.any_eq_true.mp h
    exact ⟨T, hmem, (DnfTerm.eval_eq_true_iff (T := T) (x := x)).1 hval⟩
  · intro h
    rcases h with ⟨T, hmem, hholds⟩
    exact List.any_eq_true.mpr ⟨T, hmem, (DnfTerm.eval_eq_true_iff (T := T) (x := x)).2 hholds⟩

lemma eval_eq_false_iff {n w : Nat} (F : DNF n w) (x : BitVec n) :
    F.eval x = false ↔ ∀ T ∈ F.terms, T.eval x = false := by
  classical
  unfold eval
  simpa using List.any_eq_false

end DNF

/- ### Состояния литералов и клауз под ограничениями -/

/--
`LiteralStatus` фиксирует воздействие ограничения на отдельный литерал.
-/
inductive LiteralStatus
  | satisfied
  | falsified
  | unassigned
  deriving DecidableEq, Repr

namespace LiteralStatus

@[simp] lemma eq_satisfied_or_eq_falsified_or_eq_unassigned
    (s : LiteralStatus) :
    s = satisfied ∨ s = falsified ∨ s = unassigned := by
  cases s <;> simp

end LiteralStatus

/- ### Частичные ограничения `Restriction`

Ограничение реализуется через подкуб `Subcube n`, но снабжено удобными
операциями `override` и `assign`, которые активно используются в рассуждениях
о решающих деревьях.
-/

structure Restriction (n : Nat) where
  mask : Subcube n
  deriving Repr

namespace Restriction

variable {n : Nat}

/-- Полностью свободное ограничение. -/
@[simp] def free (n : Nat) : Restriction n :=
  { mask := fun _ => none }

/-- Три варианта для каждой координаты: `*`, `0`, `1`. -/
@[simp] def optionChoices : List (Option Bool) := [none, some false, some true]

/-- Применение ограничения к вектору: зафиксированные координаты затираются. -/
@[simp] def override (ρ : Restriction n) (x : BitVec n) : BitVec n :=
  fun i => match ρ.mask i with
    | none => x i
    | some b => b

/-- Проверяем, совместима ли точка `x` с ограничением `ρ`. -/
@[simp] def compatible (ρ : Restriction n) (x : BitVec n) : Bool :=
  memB ρ.mask x

@[simp] lemma compatible_iff {ρ : Restriction n} {x : BitVec n} :
    ρ.compatible x = true ↔ mem ρ.mask x := Iff.rfl

/-- Расширенная точка всегда удовлетворяет ограничению. -/
lemma override_mem (ρ : Restriction n) (x : BitVec n) :
    mem ρ.mask (ρ.override x) := by
  classical
  apply (mem_iff (β := ρ.mask) (x := ρ.override x)).mpr
  intro i b hβ
  unfold override
  cases hρ : ρ.mask i with
  | none => simpa [hρ] using hβ
  | some b' =>
      have hb : b' = b := by
        have hsome : some b' = some b := by simpa [hρ] using hβ
        exact Option.some.inj hsome
      simp [hρ, hb]

/-- Если `x` удовлетворяет ограничению, `override` не меняет вектор. -/
lemma override_eq_of_mem {ρ : Restriction n} {x : BitVec n}
    (h : mem ρ.mask x) : ρ.override x = x := by
  classical
  funext i
  unfold override
  cases hρ : ρ.mask i with
  | none => rfl
  | some b =>
      have hx := (mem_iff (β := ρ.mask) (x := x)).1 h i b ?_
      · simpa [hρ, hx]
      · simpa [hρ]

/-- Совместимость эквивалентна тождественности `override`. -/
lemma compatible_iff_override_eq {ρ : Restriction n} {x : BitVec n} :
    ρ.compatible x = true ↔ ρ.override x = x := by
  constructor
  · intro hcompat
    have hmem : mem ρ.mask x := hcompat
    simpa using ρ.override_eq_of_mem hmem
  · intro hover
    have hmem : mem ρ.mask (ρ.override x) := ρ.override_mem x
    simpa [hover] using hmem

/-- Повторное применение `override` стабилизируется. -/
lemma override_idem (ρ : Restriction n) (x : BitVec n) :
    ρ.override (ρ.override x) = ρ.override x :=
  ρ.override_eq_of_mem (ρ.override_mem x)

/-- Фиксируем координату `i` значением `b`. -/
@[simp] def assign (ρ : Restriction n) (i : Fin n) (b : Bool) :
    Option (Restriction n) :=
  match Subcube.assign ρ.mask i b with
  | none => none
  | some β => some ⟨β⟩

lemma assign_mask_eq {ρ : Restriction n} {i : Fin n} {b : Bool}
    {ρ' : Restriction n} (h : ρ.assign i b = some ρ') :
    ∀ j : Fin n, ρ'.mask j = (if j = i then some b else ρ.mask j) := by
  classical
  dsimp [assign] at h
  cases hassign : Subcube.assign ρ.mask i b with
  | none => simp [hassign] at h
  | some β =>
      have hβ : Restriction.mk β = ρ' := by
        simpa [assign, hassign] using h
      subst hβ
      cases hmask : ρ.mask i with
      | none =>
          intro j
          have hβeq : β = fun j => if j = i then some b else ρ.mask j := by
            apply Option.some.inj
            simpa [Subcube.assign, hmask] using hassign.symm
          subst hβeq
          simp
      | some bOld =>
          have hb : b = bOld := by
            by_contra hbneq
            have : none = some β := by
              simpa [Subcube.assign, hmask, hbneq] using hassign.symm
            cases this
          intro j
          have hβeq : β = ρ.mask := by
            apply Option.some.inj
            simpa [Subcube.assign, hmask, hb] using hassign.symm
          subst hβeq
          by_cases hij : j = i
          · subst hij; simp [hmask, hb]
          · simp [hij]

lemma assign_override_eq {ρ : Restriction n} {i : Fin n} {b : Bool}
    {ρ' : Restriction n} (h : ρ.assign i b = some ρ') (x : BitVec n) :
    ρ'.override x = fun j : Fin n => if j = i then b else ρ.override x j := by
  classical
  funext j
  have hmask := assign_mask_eq (ρ := ρ) (ρ' := ρ') (i := i) (b := b) h j
  by_cases hij : j = i
  · subst hij; simp [Restriction.override, hmask]
  · simp [Restriction.override, hmask, hij]

lemma mask_eq_some_of_not_none {ρ : Restriction n} {i : Fin n}
    (h : ρ.mask i ≠ none) : ∃ b : Bool, ρ.mask i = some b := by
  cases hmask : ρ.mask i with
  | none => cases h <| by simpa [hmask]
  | some b => exact ⟨b, rfl⟩

/-/
Список свободных координат (там, где маска равна `none`).
-/
def freeIndicesList (ρ : Restriction n) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (ρ.mask i = none))

@[simp] lemma mem_freeIndicesList {ρ : Restriction n} {i : Fin n} :
    i ∈ ρ.freeIndicesList ↔ ρ.mask i = none := by
  classical
  unfold freeIndicesList
  constructor
  · intro hi
    have hi' : decide (ρ.mask i = none) = true := (List.mem_filter.mp hi).2
    exact of_decide_eq_true hi'
  · intro hnone
    refine List.mem_filter.mpr ?_
    exact ⟨List.mem_finRange _, (decide_eq_true_iff (p := ρ.mask i = none)).mpr hnone⟩

/-/
Число свободных координат.
-/
@[simp] def freeCount (ρ : Restriction n) : Nat := ρ.freeIndicesList.length

lemma freeCount_le (ρ : Restriction n) : ρ.freeCount ≤ n := by
  classical
  unfold freeCount freeIndicesList
  have := List.length_filter_le (l := List.finRange n)
    (p := fun i => decide (ρ.mask i = none))
  simpa using this

lemma freeCount_pos_of_mem_freeIndicesList {ρ : Restriction n} {i : Fin n}
    (hmem : i ∈ ρ.freeIndicesList) : 0 < ρ.freeCount := by
  classical
  unfold freeCount at *
  exact List.length_pos_of_mem hmem

lemma freeIndicesList_nodup (ρ : Restriction n) : ρ.freeIndicesList.Nodup := by
  classical
  unfold freeIndicesList
  simpa using (List.nodup_finRange n).filter
    (fun i => decide (ρ.mask i = none))

lemma assign_some_of_mem_freeIndicesList {ρ : Restriction n} {i : Fin n}
    {b : Bool} (hmem : i ∈ ρ.freeIndicesList) :
    ∃ ρ' : Restriction n, ρ.assign i b = some ρ' := by
  classical
  have hmask : ρ.mask i = none := (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).1 hmem
  refine ⟨⟨fun j => if j = i then some b else ρ.mask j⟩, ?_⟩
  simp [Restriction.assign, Subcube.assign, hmask]

/--
Добавляем новую координату в ограничение: значение `choice` назначается
нулевой позиции, а остальные индексы копируются из исходного `ρ`.
-/
@[simp] def cons (choice : Option Bool) (ρ : Restriction n) :
    Restriction (Nat.succ n) :=
  { mask := fun i => Fin.cases choice (fun j => ρ.mask j) i }

@[simp] lemma cons_mask_zero (choice : Option Bool) (ρ : Restriction n) :
    (Restriction.cons choice ρ).mask 0 = choice := rfl

@[simp] lemma cons_mask_succ (choice : Option Bool) (ρ : Restriction n)
    (i : Fin n) :
    (Restriction.cons choice ρ).mask i.succ = ρ.mask i := rfl

/--
Хвост ограничения: отбрасываем нулевую координату и сдвигаем индексы вниз.
-/
@[simp] def tail (ρ : Restriction (Nat.succ n)) : Restriction n :=
  { mask := fun i => ρ.mask i.succ }

@[simp] lemma tail_mask (ρ : Restriction (Nat.succ n)) (i : Fin n) :
    ρ.tail.mask i = ρ.mask i.succ := rfl

@[simp] lemma tail_cons (choice : Option Bool) (ρ : Restriction n) :
    (Restriction.cons choice ρ).tail = ρ := by
  cases ρ
  simp [tail, Restriction.cons]

/-- Применяем ограничение к булевой функции, не изменяя размерность входа. -/
@[simp] def restrict (ρ : Restriction n) (f : BitVec n → Bool) :
    BitVec n → Bool :=
  fun x => f (ρ.override x)

lemma restrict_agree_of_compatible (ρ : Restriction n)
    (f : BitVec n → Bool) {x : BitVec n}
    (h : ρ.compatible x = true) :
    ρ.restrict f x = f x := by
  unfold restrict
  have hover := (ρ.compatible_iff_override_eq).mp h
  simpa [hover]

lemma restrict_override (ρ : Restriction n) (f : BitVec n → Bool)
    (x : BitVec n) : ρ.restrict f (ρ.override x) = f (ρ.override x) := by
  unfold restrict
  simp [override_idem]

/-- Проверяем, стала ли функция константной после ограничения. -/
@[simp] def isConstantOn (ρ : Restriction n) (f : BitVec n → Bool) : Bool :=
  decide (∀ x y : BitVec n, ρ.restrict f x = ρ.restrict f y)

lemma isConstantOn_iff {ρ : Restriction n} {f : BitVec n → Bool} :
    ρ.isConstantOn f = true ↔
      (∀ x y : BitVec n, ρ.restrict f x = ρ.restrict f y) := by
  classical
  unfold isConstantOn
  simpa using (decide_eq_true_iff
    (p := ∀ x y : BitVec n, ρ.restrict f x = ρ.restrict f y))

lemma isConstantOn_of_no_free (ρ : Restriction n) (f : BitVec n → Bool)
    (hfree : ∀ i : Fin n, ρ.mask i ≠ none) : ρ.isConstantOn f = true := by
  classical
  have hover : ∀ x y : BitVec n, ρ.override x = ρ.override y := by
    intro x y; funext i
    obtain ⟨b, hb⟩ := mask_eq_some_of_not_none (ρ := ρ) (i := i) (h := hfree i)
    simp [Restriction.override, hb]
  have hconst : ∀ x y : BitVec n, ρ.restrict f x = ρ.restrict f y := by
    intro x y
    unfold Restriction.restrict
    simpa using congrArg f (hover x y)
  have := (Restriction.isConstantOn_iff (ρ := ρ) (f := f)).mpr hconst
  simpa using this

lemma isConstantOn_of_freeCount_eq_zero (ρ : Restriction n)
    (f : BitVec n → Bool) (hcount : ρ.freeCount = 0) : ρ.isConstantOn f = true := by
  classical
  have hfree : ∀ i : Fin n, ρ.mask i ≠ none := by
    intro i
    by_contra hnone
    have hi : i ∈ ρ.freeIndicesList :=
      (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).2 hnone
    have hpos : 0 < ρ.freeCount :=
      freeCount_pos_of_mem_freeIndicesList (ρ := ρ) hi
    have hneq : ρ.freeCount ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    exact hneq hcount
  exact isConstantOn_of_no_free (ρ := ρ) (f := f) hfree

/-- Рекурсивная проверка существования PDT глубины ≤ `t`. -/
def hasDecisionTreeOfDepth
    (ρ : Restriction n) (f : BitVec n → Bool) (t : Nat) : Bool :=
  match t with
  | 0 => ρ.isConstantOn f
  | Nat.succ t' =>
      if ρ.isConstantOn f = true then
        true
      else
        (ρ.freeIndicesList).any (fun i =>
          match ρ.assign i false, ρ.assign i true with
          | some ρ0, some ρ1 =>
              hasDecisionTreeOfDepth ρ0 f t' && hasDecisionTreeOfDepth ρ1 f t'
          | _, _ => false)

@[simp] lemma hasDecisionTreeOfDepth_zero
    (ρ : Restriction n) (f : BitVec n → Bool) :
    hasDecisionTreeOfDepth ρ f 0 = ρ.isConstantOn f := by
  unfold hasDecisionTreeOfDepth
  simp

/-- Вес ограничения в распределении `𝓡_p`. -/
@[simp] def weight (ρ : Restriction n) (p : Q) : Q :=
  ∏ i : Fin n,
    match ρ.mask i with
    | none => p
    | some _ => ((1 : Q) - p) / 2

lemma weight_cons (choice : Option Bool) (ρ : Restriction n) (p : Q) :
    (Restriction.cons choice ρ).weight p =
      (match choice with
        | none => p
        | some _ => ((1 : Q) - p) / 2) * ρ.weight p := by
  classical
  cases choice with
  | none =>
      simp [weight, Fin.prod_univ_succ, cons_mask_zero, cons_mask_succ]
  | some b =>
      simp [weight, Fin.prod_univ_succ, cons_mask_zero, cons_mask_succ]

/--
Вес ограничения всегда неотрицателен при условии `0 ≤ p ≤ 1`.  В каждой точке
перемножаются либо `p`, либо `(1 - p) / 2`, и обе величины неотрицательны при
таких ограничениях на `p`.
-/
lemma weight_nonneg (ρ : Restriction n) {p : Q}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ ρ.weight p := by
  classical
  unfold weight
  refine Finset.prod_nonneg ?_
  intro i _
  cases hmask : ρ.mask i with
  | none =>
      simpa [hmask, hp₀]
  | some _ =>
      have hsub : 0 ≤ (1 - p) := sub_nonneg.mpr hp₁
      have : 0 ≤ (1 - p) / 2 := by
        have htwo : (0 : Q) ≤ 2 := by norm_num
        exact div_nonneg hsub htwo
      simpa [hmask] using this

/-- Суммарный вес трёх продолжений (`свободный`, `0`, `1`) выражается через вес исходного ограничения. -/
lemma weight_cons_sum (ρ : Restriction n) (p : Q) :
    (Restriction.cons none ρ).weight p
      + (Restriction.cons (some false) ρ).weight p
      + (Restriction.cons (some true) ρ).weight p
        = (p + (1 - p)) * ρ.weight p := by
  classical
  set w := ρ.weight p
  have hnone : (Restriction.cons none ρ).weight p = p * w := by
    simpa [w] using (weight_cons (choice := none) (ρ := ρ) (p := p))
  have hfalse : (Restriction.cons (some false) ρ).weight p = ((1 - p) / 2) * w := by
    simpa [w] using (weight_cons (choice := some false) (ρ := ρ) (p := p))
  have htrue : (Restriction.cons (some true) ρ).weight p = ((1 - p) / 2) * w := by
    simpa [w] using (weight_cons (choice := some true) (ρ := ρ) (p := p))
  have hhalves : ((1 - p) / 2 + (1 - p) / 2) = (1 - p) := by
    ring
  have hsum :
      (Restriction.cons none ρ).weight p
        + (Restriction.cons (some false) ρ).weight p
        + (Restriction.cons (some true) ρ).weight p
          = p * w + ((1 - p) / 2) * w + ((1 - p) / 2) * w := by
    calc
      (Restriction.cons none ρ).weight p
          + (Restriction.cons (some false) ρ).weight p
          + (Restriction.cons (some true) ρ).weight p
        = p * w + (Restriction.cons (some false) ρ).weight p
            + (Restriction.cons (some true) ρ).weight p := by
              simpa [hnone]
      _ = p * w + ((1 - p) / 2) * w + (Restriction.cons (some true) ρ).weight p := by
              simpa [hfalse]
      _ = p * w + ((1 - p) / 2) * w + ((1 - p) / 2) * w := by
              simpa [htrue]
  calc
    (Restriction.cons none ρ).weight p
        + (Restriction.cons (some false) ρ).weight p
        + (Restriction.cons (some true) ρ).weight p
          = p * w + ((1 - p) / 2) * w + ((1 - p) / 2) * w := hsum
    _ = (p + ((1 - p) / 2 + (1 - p) / 2)) * w := by
            ring
    _ = (p + (1 - p)) * w := by
            simpa [hhalves]
    _ = (p + (1 - p)) * ρ.weight p := by
            simpa [w]

/-- Полный список всех ограничений размера `n`. -/
@[simp] def enumerate : (n : Nat) → List (Restriction n)
  | 0 =>
      [{ mask := fun i => False.elim (Fin.elim0 i) }]
  | Nat.succ n =>
      List.flatMap
        (fun (ρ : Restriction n) =>
          [Restriction.cons none ρ,
           Restriction.cons (some false) ρ,
           Restriction.cons (some true) ρ])
        (enumerate n)

/--
Полная масса распределения `𝓡_p` на уровне `n` — сумма весов всех ограничений.
Мы реализуем её через свёртку по списку `enumerate`, чтобы удобно рассуждать
индукцией по `n`.
-/
@[simp] def totalWeight (n : Nat) (p : Q) : Q :=
  ((enumerate n).map (fun ρ => ρ.weight p)).sum

/-- Помощник: выносим общий множитель из суммы по списку. -/
lemma sum_map_mul_left {α : Type _} (c : Q) (f : α → Q) :
    ∀ L : List α, ((L.map fun x => c * f x).sum) = c * (L.map f).sum
  | [] => by simp
  | x :: L =>
      -- Выпишем обе суммы явно и применим индуктивную гипотезу.
      calc
        (( (x :: L).map fun y => c * f y).sum)
            = c * f x + ((L.map fun y => c * f y).sum) := by
                simp [List.map_cons, List.sum_cons]
        _ = c * f x + c * (L.map f).sum := by
                simpa using sum_map_mul_left (c := c) (f := f) (L := L)
        _ = c * (f x + (L.map f).sum) := by ring
        _ = c * ((x :: L).map f).sum := by
                simp [List.map_cons, List.sum_cons, mul_add]

/-- Базовый случай: в нулевой размерности единственное ограничение имеет вес 1. -/
lemma totalWeight_zero (p : Q) : totalWeight 0 p = 1 := by
  simp [totalWeight]

/--
Рекурсивное соотношение: при добавлении новой координаты суммарная масса
умножается на нормировочный фактор `p + (1 - p)`.

Интуитивно, каждому ограничению на первых `n` координатах соответствуют три
продолжения (`*`, `0`, `1`), чьи веса складываются в точности в соответствии с
леммой `weight_cons_sum`.
-/
lemma sum_weights_flatMap_g (p : Q) (g : Restriction n → List (Restriction (n+1)))
    (h_g_sum : ∀ ρ, ((g ρ).map (fun τ => τ.weight p)).sum = (p + (1 - p)) * ρ.weight p) :
    ∀ L : List (Restriction n),
      ((L.flatMap g).map (fun τ => τ.weight p)).sum = (p + (1 - p)) * (L.map (fun ρ => ρ.weight p)).sum := by
  intro L
  induction L with
  | nil => simp
  | cons ρ L' ih =>
    have hρ := h_g_sum ρ
    have htail := ih
    have hsum_decomp :
        (((ρ :: L').flatMap g).map (fun τ => τ.weight p)).sum
          = ((g ρ).map (fun τ => τ.weight p)).sum
              + ((L'.flatMap g).map (fun τ => τ.weight p)).sum := by
      simp [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        add_comm, add_left_comm, add_assoc]
    have hsum_left :
        ((g ρ).map (fun τ => τ.weight p)).sum
            + ((L'.flatMap g).map (fun τ => τ.weight p)).sum
            = (p + (1 - p)) * ρ.weight p
              + ((L'.flatMap g).map (fun τ => τ.weight p)).sum := by
      simpa [hρ] using congrArg (fun x => x + ((L'.flatMap g).map (fun τ => τ.weight p)).sum) hρ
    have hsum_right :
        (p + (1 - p)) * ρ.weight p
            + ((L'.flatMap g).map (fun τ => τ.weight p)).sum
            = (p + (1 - p)) * ρ.weight p
              + (p + (1 - p)) * (L'.map fun ρ => ρ.weight p).sum := by
      simpa [htail] using congrArg (fun x => (p + (1 - p)) * ρ.weight p + x) htail
    have hsum_rewrite := hsum_left.trans hsum_right
    have hsum_factor :
        (p + (1 - p)) * ρ.weight p
            + (p + (1 - p)) * (L'.map fun ρ => ρ.weight p).sum
            = (p + (1 - p)) * (ρ.weight p + (L'.map fun ρ => ρ.weight p).sum) := by
      ring
    have hmap_cons :
        ((ρ :: L').map (fun ρ => ρ.weight p)).sum
          = ρ.weight p + (L'.map fun ρ => ρ.weight p).sum := by
      simp [List.map_cons, List.sum_cons]
    calc
      (((ρ :: L').flatMap g).map (fun τ => τ.weight p)).sum
          = ((g ρ).map (fun τ => τ.weight p)).sum
              + ((L'.flatMap g).map (fun τ => τ.weight p)).sum := hsum_decomp
      _ = (p + (1 - p)) * ρ.weight p
              + (p + (1 - p)) * (L'.map fun ρ => ρ.weight p).sum := hsum_rewrite
      _ = (p + (1 - p)) *
              (ρ.weight p + (L'.map fun ρ => ρ.weight p).sum) := hsum_factor
      _ = (p + (1 - p)) * ((ρ :: L').map (fun ρ => ρ.weight p)).sum := by
                simpa [hmap_cons, add_comm]

lemma totalWeight_succ (n : Nat) (p : Q) :
    totalWeight (Nat.succ n) p = (p + (1 - p)) * totalWeight n p := by
  classical
  -- Вспомогательная функция: тройка продолжений каждой маски.
  let g : Restriction n → List (Restriction (Nat.succ n)) := fun ρ =>
    [Restriction.cons none ρ,
     Restriction.cons (some false) ρ,
     Restriction.cons (some true) ρ]
  have h_g_sum : ∀ ρ, ((g ρ).map (fun τ => τ.weight p)).sum = (p + (1 - p)) * ρ.weight p := by
    intro ρ
    have hsum : ((g ρ).map (fun τ => τ.weight p)).sum
        = (Restriction.cons none ρ).weight p
          + (Restriction.cons (some false) ρ).weight p
          + (Restriction.cons (some true) ρ).weight p := by
      simp [g, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_comm, add_left_comm,
        add_assoc]
    calc
      ((g ρ).map (fun τ => τ.weight p)).sum
          = (Restriction.cons none ρ).weight p
              + (Restriction.cons (some false) ρ).weight p
              + (Restriction.cons (some true) ρ).weight p := hsum
      _ = (p + (1 - p)) * ρ.weight p := weight_cons_sum (ρ := ρ) (p := p)

  let haux := sum_weights_flatMap_g p g h_g_sum (enumerate n)

  -- Переписываем `totalWeight` через раскрытое перечисление.
  calc
    totalWeight (Nat.succ n) p
        = ((enumerate (Nat.succ n)).map (fun ρ => ρ.weight p)).sum := rfl
    _ = (((enumerate n).flatMap g).map (fun τ => τ.weight p)).sum := by
          simp [totalWeight, enumerate, g, List.flatMap_singleton_eq_map]
    _ = (p + (1 - p)) * ((enumerate n).map (fun ρ => ρ.weight p)).sum := haux
    _ = (p + (1 - p)) * totalWeight n p := by
          simp [totalWeight]

  /-- Явная формула для суммы весов: она образует геометрическую прогрессию. -/
  lemma totalWeight_closed_form (n : Nat) (p : Q) :
      totalWeight n p = (p + (1 - p)) ^ n := by
  induction n with
  | zero =>
      simp [totalWeight_zero]
  | succ n ih =>
      calc
        totalWeight (Nat.succ n) p
            = (p + (1 - p)) * totalWeight n p :=
                totalWeight_succ (n := n) (p := p)
        _ = (p + (1 - p)) * (p + (1 - p)) ^ n := by
                rw [ih]
        _ = (p + (1 - p)) ^ n * (p + (1 - p)) := by
                simpa [mul_comm]
        _ = (p + (1 - p)) ^ Nat.succ n := by
                simpa [pow_succ] using (pow_succ (p + (1 - p)) n).symm

/-- Полная масса распределения равна 1: `𝓡_p` корректно нормирована. -/
lemma totalWeight_eq_one (n : Nat) (p : Q) : totalWeight n p = 1 := by
  have hnorm : p + (1 - p) = (1 : Q) := by ring
  have hclosed := totalWeight_closed_form n p
  have hone : (p + (1 - p)) ^ n = 1 := by
    simpa [hnorm] using (one_pow n : (1 : Q) ^ n = 1)
  exact hclosed.trans hone

/--
Масса всех ограничений, которые оставляют нулевую координату свободной,
равна `p` умножить на общую массу ограничений меньшей размерности.
-/
lemma sum_weights_mask_none_zero (n : Nat) (p : Q) :
    (((enumerate (Nat.succ n)).filter
        (fun ρ => ρ.mask 0 = none)).map (fun ρ => ρ.weight p)).sum
      = p * totalWeight n p := by
  classical
  -- Удобные сокращения: фильтр по свободной первой координате и тройка продолжений.
  let P : Restriction (Nat.succ n) → Bool := fun ρ => decide (ρ.mask 0 = none)
  let g : Restriction n → List (Restriction (Nat.succ n)) :=
    fun ρ => [cons none ρ, cons (some false) ρ, cons (some true) ρ]
  -- Расписываем перечисление через `flatMap`.
  have henum :
      enumerate (Nat.succ n) = (enumerate n).flatMap g := by
    simp [enumerate, g]
  -- Отфильтрованный список — это просто продолжения с `*` на нулевой позиции.
  have hfiltered_flat :
      List.filter P ((enumerate n).flatMap g)
        = (enumerate n).map (cons none) := by
    classical
    have haux :
        ∀ L : List (Restriction n),
          List.filter P (L.flatMap g)
            = L.map (cons none) := by
      intro L; induction L with
      | nil => simp
      | cons ρ L ih =>
          have hhead : List.filter P (g ρ) = [cons none ρ] := by
            simp [P, g]
          calc
            List.filter P ((ρ :: L).flatMap g)
                = List.filter P (g ρ ++ L.flatMap g) := by
                    simp [g, List.flatMap_cons]
            _ = List.filter P (g ρ)
                  ++ List.filter P (L.flatMap g) := by
                    simp [List.filter_append]
            _ = [cons none ρ]
                  ++ List.filter P (L.flatMap g) := by
                    simpa [hhead]
            _ = cons none ρ :: List.filter P (L.flatMap g) := by
                    simp
            _ = cons none ρ :: L.map (cons none) := by
                    simpa [P, g, ih]
            _ = List.map (cons none) (ρ :: L) := by
                    simp
    simpa using haux (enumerate n)
  have hfiltered :
      (enumerate (Nat.succ n)).filter P
        = (enumerate n).map (cons none) := by
    simpa [henum] using hfiltered_flat
  -- Сумма весов по этому списку.
  have hsum :
      (((enumerate (Nat.succ n)).filter P).map (fun ρ => ρ.weight p)).sum
        = ((enumerate n).map fun ρ => (cons none ρ).weight p).sum := by
    have := congrArg (List.map (fun ρ => ρ.weight p)) hfiltered
    simpa using congrArg List.sum this
  have hweight :
      ∀ ρ : Restriction n,
        (cons none ρ).weight p = p * ρ.weight p := by
    intro ρ
    simpa using (weight_cons (choice := none) (ρ := ρ) (p := p))
  have hsum' :
      ((enumerate n).map
          (fun ρ => (cons none ρ).weight p)).sum
        = ((enumerate n).map fun ρ => p * ρ.weight p).sum := by
    induction enumerate n with
    | nil => simp [hweight]
    | cons ρ L ih =>
        have hw := hweight ρ
        calc
          ((ρ :: L).map (fun ρ => (cons none ρ).weight p)).sum
              = (cons none ρ).weight p + (L.map (fun ρ => (cons none ρ).weight p)).sum := by
                  simp [List.map_cons, List.sum_cons]
          _ = p * ρ.weight p + (L.map (fun ρ => (cons none ρ).weight p)).sum := by
                  simpa using congrArg (fun x => x + (L.map (fun ρ => (cons none ρ).weight p)).sum) hw
          _ = p * ρ.weight p + (L.map fun ρ => p * ρ.weight p).sum := by
                  simpa [List.map_cons, List.sum_cons, add_comm,
                    add_left_comm, add_assoc]
                    using congrArg (fun s => p * ρ.weight p + s) ih
          _ = ((ρ :: L).map fun ρ => p * ρ.weight p).sum := by
                  simp [List.map_cons, List.sum_cons]
  calc
    (((enumerate (Nat.succ n)).filter P).map (fun ρ => ρ.weight p)).sum
        = ((enumerate n).map
            (fun ρ => (cons none ρ).weight p)).sum := hsum
    _ = ((enumerate n).map fun ρ => p * ρ.weight p).sum := hsum'
    _ = p * ((enumerate n).map fun ρ => ρ.weight p).sum := by
            exact sum_map_mul_left
              (L := enumerate n) (c := p)
              (f := fun ρ => ρ.weight p)
    _ = p * totalWeight n p := rfl

/-
Фильтрация списка, полученного через `flatMap`, может быть перенесена на
исходный список, если результат фильтрации каждой «ветки» зависит только от
самого элемента, а не от конкретного продолжения.
-/
lemma filter_flatMap_eq_flatMap_filter {α β : Type _}
    (L : List α) (g : α → List β)
    (P : β → Prop) [DecidablePred P]
    (Q : α → Prop) [DecidablePred Q]
    (hcond : ∀ a, List.filter P (g a) = if Q a then g a else []) :
    List.filter P (L.flatMap g)
      = (L.filter Q).flatMap g := by
  classical
  induction L with
  | nil =>
      simp
  | cons a L ih =>
      have hhead := hcond a
      by_cases hQa : Q a
      · have hfilter_head : List.filter P (g a) = g a := by
          simpa [hQa] using hhead
        simp [List.flatMap_cons, List.filter_append, hfilter_head,
          ih, hQa]
      · have hfilter_head : List.filter P (g a) = [] := by
          simpa [hQa] using hhead
        simp [List.flatMap_cons, List.filter_append, hfilter_head,
          ih, hQa]

lemma sum_weights_mask_none (n : Nat) :
    ∀ (i : Fin (Nat.succ n)) (p : Q),
      (((enumerate (Nat.succ n)).filter
          (fun ρ => ρ.mask i = none)).map (fun ρ => ρ.weight p)).sum
        = p * totalWeight n p := by
  classical
  induction n with
  | zero =>
      intro i p
      cases i using Fin.cases with
      | zero =>
          -- Единственный индекс — нулевой, используем предыдущую лемму.
          simpa using sum_weights_mask_none_zero (n := 0) (p := p)
      | succ j => exact False.elim (Fin.elim0 j)
  | succ n ih =>
      intro i p
      cases i using Fin.cases with
      | zero =>
          -- Нулевая координата сведена к исходному утверждению.
          simpa using sum_weights_mask_none_zero (n := Nat.succ n) (p := p)
      | succ i' =>
        -- Рассматриваем ограничение вида `cons choice ρ` и изучаем фильтр.
        let P : Restriction (Nat.succ (Nat.succ n)) → Prop :=
          fun ρ => ρ.mask i'.succ = none
        let Q : Restriction (Nat.succ n) → Prop :=
          fun ρ => ρ.mask i' = none
        let g : Restriction (Nat.succ n) → List (Restriction (Nat.succ (Nat.succ n))) :=
          fun ρ => [Restriction.cons none ρ,
            Restriction.cons (some false) ρ,
            Restriction.cons (some true) ρ]
        have henum :
            enumerate (Nat.succ (Nat.succ n))
              = (enumerate (Nat.succ n)).flatMap g := by
          simp [enumerate, g]
        have hbranch :
            ∀ ρ : Restriction (Nat.succ n),
              List.filter P (g ρ)
                = if Q ρ then g ρ else [] := by
          intro ρ
          classical
          by_cases hnone : Q ρ
          · have hmask : ρ.mask i' = none := hnone
            simp [g, P, Q, hmask, Restriction.cons_mask_succ, hnone]
          · have hmask : ρ.mask i' ≠ none := hnone
            obtain ⟨b, hb⟩ := Restriction.mask_eq_some_of_not_none
              (ρ := ρ) (i := i') hmask
            simp [g, P, Q, Restriction.cons_mask_succ, hb, hnone]
        -- Переносим фильтрацию с расширенного списка на исходный.
        have hfiltered :
            List.filter P (enumerate (Nat.succ (Nat.succ n)))
              = ((enumerate (Nat.succ n)).filter Q).flatMap g := by
          simpa [henum]
            using filter_flatMap_eq_flatMap_filter
              (L := enumerate (Nat.succ n))
              (g := g) (P := P) (Q := Q) hbranch

        have h_g_sum : ∀ ρ, ((g ρ).map (fun τ => τ.weight p)).sum = (p + (1 - p)) * ρ.weight p := by
          intro ρ
          have hsum : ((g ρ).map (fun τ => τ.weight p)).sum
              = (Restriction.cons none ρ).weight p
                + (Restriction.cons (some false) ρ).weight p
                + (Restriction.cons (some true) ρ).weight p := by
            simp [g, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_comm, add_left_comm,
              add_assoc]
          calc
            ((g ρ).map (fun τ => τ.weight p)).sum
                = (Restriction.cons none ρ).weight p
                    + (Restriction.cons (some false) ρ).weight p
                    + (Restriction.cons (some true) ρ).weight p := hsum
            _ = (p + (1 - p)) * ρ.weight p := weight_cons_sum (ρ := ρ) (p := p)

        have hflat_sum := sum_weights_flatMap_g p g h_g_sum ((enumerate (Nat.succ n)).filter Q)

        -- Теперь собираем все вычисления вместе.
        calc
          (((enumerate (Nat.succ (Nat.succ n))).filter P).map (fun ρ => ρ.weight p)).sum
              = ((((enumerate (Nat.succ n)).filter Q).flatMap g).map (fun ρ => ρ.weight p)).sum := by
                rw [hfiltered]
          _ = (p + (1 - p)) * (((enumerate (Nat.succ n)).filter Q).map (fun ρ => ρ.weight p)).sum := hflat_sum
          _ = (p + (1 - p)) * (p * totalWeight n p) := by
                  -- Индукционная гипотеза применима к индексу `i'`.
                  have hIH := ih i' p
                  simpa [Q] using hIH
          _ = p * ((p + (1 - p)) * totalWeight n p) := by
                  simp [mul_assoc, mul_comm, mul_left_comm]
          _ = p * totalWeight (Nat.succ n) p := by
                  rw [totalWeight_succ n p]
/- Если на каждом элементе списка `f x ≤ g x`, то и суммы `map f` и `map g`
сохраняют это неравенство. -/
lemma sum_map_le_sum_map {α : Type _} (L : List α)
    (f g : α → Q) (h : ∀ x ∈ L, f x ≤ g x) :
    ((L.map f).sum) ≤ ((L.map g).sum) := by
  classical
  induction L with
  | nil => simp
  | cons x xs ih =>
      have hx : f x ≤ g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y ≤ g y := by
        intro y hy
        exact h y (by simp [hy])
      have ih' := ih hxs
      simpa [List.map_cons, List.sum_cons, add_comm, add_left_comm, add_assoc]
        using add_le_add hx ih'

lemma foldl_select_sum_aux {α : Type _} (L : List α) (f : α → Q)
    (P : α → Prop) [DecidablePred P] (acc : Q) :
    (L.foldl (fun acc x => if P x then acc + f x else acc) acc)
      = acc + ((L.map fun x => if P x then f x else (0 : Q)).sum) := by
  classical
  induction L generalizing acc with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : P x
      · have := ih (acc := acc + f x)
        simp [hx, ih, add_comm, add_left_comm, add_assoc]
      · have := ih (acc := acc)
        simp [hx, ih]

lemma foldl_select_sum {α : Type _} (L : List α) (f : α → Q) (P : α → Prop)
    [DecidablePred P] :
    (L.foldl (fun acc x => if P x then acc + f x else acc) 0)
      = ((L.map fun x => if P x then f x else (0 : Q)).sum) := by
  simpa using (foldl_select_sum_aux (L := L) (f := f) (P := P) (acc := (0 : Q)))

lemma if_add_else (b : Bool) (a x : Q) :
    (if b then a + x else a) = a + (if b then x else 0) := by
  cases b <;> simp

/--
Сумма по списку с «усечённой» функцией (`if P x then f x else 0`) совпадает с
суммой по отфильтрованному списку.  Это удобная форма для переписывания
вероятностных выражений через явное множество «плохих» ограничений.-/
  lemma sum_map_filter_eq {α : Type _} (L : List α) (f : α → Q)
      (P : α → Prop) [DecidablePred P] :
      ((L.map fun x => if P x then f x else (0 : Q)).sum)
        = ((L.filter P).map f).sum := by
    classical
    induction L with
    | nil => simp
    | cons x xs ih =>
        by_cases hx : P x
        · simp [hx, ih]
        · simp [hx, ih]

/--
Состояние литерала относительно маски ограничения.
-/
@[simp] def literalStatus {n : Nat} (ρ : Restriction n)
    (ℓ : Literal n) : LiteralStatus :=
  match ρ.mask ℓ.idx with
  | none      => LiteralStatus.unassigned
  | some b    => if b = ℓ.value then LiteralStatus.satisfied
                  else LiteralStatus.falsified

lemma literalStatus_eq_satisfied {n : Nat} {ρ : Restriction n}
    {ℓ : Literal n} :
    ρ.literalStatus ℓ = LiteralStatus.satisfied ↔ ρ.mask ℓ.idx = some ℓ.value := by
  classical
  unfold literalStatus
  cases hmask : ρ.mask ℓ.idx with
  | none => simp [hmask]
  | some b =>
      by_cases hb : b = ℓ.value
      · subst hb; simp [hmask]
      · have hb' : b ≠ ℓ.value := hb
        simp [hmask, hb, hb']

lemma literalStatus_eq_unassigned {n : Nat} {ρ : Restriction n}
    {ℓ : Literal n} :
    ρ.literalStatus ℓ = LiteralStatus.unassigned ↔ ρ.mask ℓ.idx = none := by
  classical
  unfold literalStatus
  cases hmask : ρ.mask ℓ.idx with
  | none => simp [hmask]
  | some b =>
      by_cases hb : b = ℓ.value
      · simp [hmask, hb]
      · simp [hmask, hb]

lemma literalStatus_eq_falsified {n : Nat} {ρ : Restriction n}
    {ℓ : Literal n} :
    ρ.literalStatus ℓ = LiteralStatus.falsified ↔
      ∃ b : Bool, ρ.mask ℓ.idx = some b ∧ b ≠ ℓ.value := by
  classical
  unfold literalStatus
  cases hmask : ρ.mask ℓ.idx with
  | none => simp [hmask]
  | some b =>
      by_cases hb : b = ℓ.value
      · simp [hmask, hb]
      · constructor
        · intro _
          exact ⟨b, rfl, hb⟩
        · rintro ⟨b', hb', hbneq⟩
          have hb_eq' : some b = some b' := by
            simpa [hmask] using hb'
          have hb_eq : b = b' := Option.some.inj hb_eq'
          have hbne : b ≠ ℓ.value := by
            simpa [hb_eq] using hbneq
          simpa [hmask, hbne]

/--
Если ограничение объявило литерал удовлетворённым, то после `override` он
действительно вычисляется в `true`.
-/
lemma literalStatus_eval_override_true {n : Nat} {ρ : Restriction n}
    {ℓ : Literal n} {x : BitVec n}
    (h : ρ.literalStatus ℓ = LiteralStatus.satisfied) :
    Literal.eval ℓ (ρ.override x) = true := by
  classical
  obtain hmask : ρ.mask ℓ.idx = some ℓ.value :=
    (literalStatus_eq_satisfied (ρ := ρ) (ℓ := ℓ)).1 h
  unfold Literal.eval
  simp [Restriction.override, hmask]

/--
Если литерал помечен как ложный, то после применения `override` он остаётся
ложным.
-/
lemma literalStatus_eval_override_false {n : Nat} {ρ : Restriction n}
    {ℓ : Literal n} {x : BitVec n}
    (h : ρ.literalStatus ℓ = LiteralStatus.falsified) :
    Literal.eval ℓ (ρ.override x) = false := by
  classical
  obtain ⟨b, hmask, hb⟩ :=
    (literalStatus_eq_falsified (ρ := ρ) (ℓ := ℓ)).1 h
  unfold Literal.eval
  simp [Restriction.override, hmask, hb]

/-- Список литералов, оставшихся свободными после применения ограничения. -/
@[simp] def freeLiterals {n : Nat} (ρ : Restriction n) (C : CnfClause n) :
    List (Literal n) :=
  C.literals.filter
    (fun ℓ => decide (ρ.literalStatus ℓ = LiteralStatus.unassigned))

lemma mem_freeLiterals {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    {ℓ : Literal n} :
    ℓ ∈ ρ.freeLiterals C ↔ ℓ ∈ C.literals ∧
      ρ.literalStatus ℓ = LiteralStatus.unassigned := by
  classical
  unfold freeLiterals
  constructor
  · intro hmem
    have h := List.mem_filter.mp hmem
    exact ⟨h.1, (decide_eq_true_iff
      (p := ρ.literalStatus ℓ = LiteralStatus.unassigned)).1 h.2⟩
  · intro hmem
    obtain ⟨hC, hstatus⟩ := hmem
    refine List.mem_filter.mpr ?_
    exact ⟨hC, (decide_eq_true_iff
      (p := ρ.literalStatus ℓ = LiteralStatus.unassigned)).2 hstatus⟩

/-- Список `freeLiterals` пуст тогда и только тогда, когда в клаузе не осталось свободных литералов. -/
lemma freeLiterals_eq_nil_iff {n : Nat} {ρ : Restriction n}
    {C : CnfClause n} :
    ρ.freeLiterals C = [] ↔
      ∀ ℓ ∈ C.literals, ρ.literalStatus ℓ ≠ LiteralStatus.unassigned := by
  classical
  constructor
  · intro hfree ℓ hℓ hstatus
    have hmem : ℓ ∈ ρ.freeLiterals C :=
      (mem_freeLiterals (ρ := ρ) (C := C) (ℓ := ℓ)).2 ⟨hℓ, hstatus⟩
    have heq := congrArg (fun l => ℓ ∈ l) hfree
    have hnil : ℓ ∈ ([] : List (Literal n)) := Eq.mp heq hmem
    cases hnil
  · intro hnone
    classical
    cases hfree : ρ.freeLiterals C with
    | nil => simpa [hfree]
    | cons ℓ₀ free =>
        have heq := congrArg (fun l => ℓ₀ ∈ l) hfree.symm
        have hmem : ℓ₀ ∈ ρ.freeLiterals C :=
          Eq.mp heq (List.mem_cons_self (l := free) (a := ℓ₀))
        obtain ⟨hℓC, hstatus⟩ :=
          (mem_freeLiterals (ρ := ρ) (C := C) (ℓ := ℓ₀)).1 hmem
        exact False.elim ((hnone ℓ₀ hℓC) hstatus)

structure ClausePendingWitness {n : Nat}
    (ρ : Restriction n) (C : CnfClause n) where
  free : List (Literal n)
  subset : ∀ ℓ ∈ free, ℓ ∈ C.literals
  unassigned : ∀ ℓ ∈ free, ρ.literalStatus ℓ = LiteralStatus.unassigned
  nonempty : free ≠ []
  noSatisfied : ∀ ℓ ∈ C.literals, ρ.literalStatus ℓ ≠ LiteralStatus.satisfied
  deriving Repr

inductive ClauseStatus {n : Nat} (ρ : Restriction n) (C : CnfClause n)
  | satisfied
  | falsified
  | pending (w : ClausePendingWitness ρ C)
  deriving Repr

@[simp] def clauseStatus {n : Nat} (ρ : Restriction n) (C : CnfClause n) :
    ClauseStatus ρ C :=
  if hsat : ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.satisfied then
    ClauseStatus.satisfied
  else
    let free := ρ.freeLiterals C
    if hfree : free = [] then
      ClauseStatus.falsified
    else
      ClauseStatus.pending
        { free := free
          , subset := by
              intro ℓ hℓ
              have := (mem_freeLiterals (ρ := ρ) (C := C) (ℓ := ℓ)).1 hℓ
              exact this.1
          , unassigned := by
              intro ℓ hℓ
              have := (mem_freeLiterals (ρ := ρ) (C := C) (ℓ := ℓ)).1 hℓ
              exact this.2
          , nonempty := by
              simpa using hfree
          , noSatisfied := by
              intro ℓ hℓ hstat
              exact hsat ⟨ℓ, hℓ, hstat⟩ }

lemma ClausePendingWitness.exists_unassigned
    {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    (w : ClausePendingWitness ρ C) :
    ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.unassigned := by
  classical
  obtain ⟨ℓ, freeTail, hfree⟩ := List.exists_cons_of_ne_nil w.nonempty
  have hℓmem : ℓ ∈ w.free := by
    simpa [hfree] using List.mem_cons_self ℓ freeTail
  exact ⟨ℓ, w.subset _ hℓmem, w.unassigned _ hℓmem⟩

lemma clauseStatus_pending_exists_literal {n : Nat} {ρ : Restriction n}
    {C : CnfClause n} {w : ClausePendingWitness ρ C} :
    ρ.clauseStatus C = ClauseStatus.pending w →
      ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.unassigned := by
  intro _; exact ClausePendingWitness.exists_unassigned w

end Restriction

namespace CNF

/-- Вероятность (по `𝓡_p`) того, что глубина PDT после ограничения больше `t`. -/
@[simp] def failureProbability
    {n w : Nat} (F : CNF n w) (p : Q) (t : Nat) : Q :=
  ((Restriction.enumerate n).foldl
    (fun acc ρ =>
      if Restriction.hasDecisionTreeOfDepth ρ F.eval t = false then
        acc + ρ.weight p
      else
        acc)
    0)

/--
Множество (список) «плохих» ограничений, на которых глубина PDT превышает
`t`.  Мы реализуем его через фильтрацию полного перечисления ограничений.
-/
@[simp] def failureSet {n w : Nat} (F : CNF n w) (t : Nat) :
    List (Restriction n) :=
  (Restriction.enumerate n).filter
    (fun ρ => Restriction.hasDecisionTreeOfDepth ρ F.eval t = false)

lemma mem_failureSet {n w : Nat} {F : CNF n w} {t : Nat} {ρ : Restriction n} :
    ρ ∈ F.failureSet t ↔
      ρ ∈ Restriction.enumerate n ∧
        Restriction.hasDecisionTreeOfDepth ρ F.eval t = false := by
  classical
  unfold failureSet
  constructor
  · intro hρ
    obtain ⟨hmem, hbool⟩ := List.mem_filter.mp hρ
    have hfail : Restriction.hasDecisionTreeOfDepth ρ F.eval t = false := by
      have := of_decide_eq_true (p :=
        Restriction.hasDecisionTreeOfDepth ρ F.eval t = false) hbool
      exact this
    exact ⟨hmem, hfail⟩
  · intro hρ
    rcases hρ with ⟨hmem, hfail⟩
    have hbool : decide (Restriction.hasDecisionTreeOfDepth ρ F.eval t = false)
        = true := by
      exact (decide_eq_true_iff
        (p := Restriction.hasDecisionTreeOfDepth ρ F.eval t = false)).2 hfail
    exact List.mem_filter.mpr ⟨hmem, hbool⟩

/--
Переписываем определение `failureProbability` как сумму по всем ограничениям,
где вклад равен весу ограничения или нулю в зависимости от того, провалилась ли
проверка глубины.
-/
lemma failureProbability_eq_sum
    {n w : Nat} (F : CNF n w) (p : Q) (t : Nat) :
    failureProbability F p t =
      ((Restriction.enumerate n).map
        (fun ρ =>
          if Restriction.hasDecisionTreeOfDepth ρ F.eval t = false then
            ρ.weight p
          else
            0)).sum := by
  classical
  unfold failureProbability
  simpa using
    Restriction.foldl_select_sum (L := Restriction.enumerate n)
      (f := fun ρ => ρ.weight p)
      (P := fun ρ => Restriction.hasDecisionTreeOfDepth ρ F.eval t = false)

/--
Вероятность неудачи — это сумма весов по множеству «плохих» ограничений.
-/
lemma failureProbability_eq_failureSet_sum
    {n w : Nat} (F : CNF n w) (p : Q) (t : Nat) :
    failureProbability F p t =
      ((F.failureSet t).map fun ρ => ρ.weight p).sum := by
  classical
  have hsum := failureProbability_eq_sum (F := F) (p := p) (t := t)
  have hfilter := Restriction.sum_map_filter_eq
    (L := Restriction.enumerate n)
    (f := fun ρ => ρ.weight p)
    (P := fun ρ => Restriction.hasDecisionTreeOfDepth ρ F.eval t = false)
  calc
    failureProbability F p t
        = ((Restriction.enumerate n).map
            (fun ρ =>
              if Restriction.hasDecisionTreeOfDepth ρ F.eval t = false then
                ρ.weight p
              else
                0)).sum := hsum
    _ = (((Restriction.enumerate n).filter
            (fun ρ =>
              Restriction.hasDecisionTreeOfDepth ρ F.eval t = false)).map
              (fun ρ => ρ.weight p)).sum := by
            simpa using hfilter
    _ = ((F.failureSet t).map fun ρ => ρ.weight p).sum := by
            simpa [failureSet]

/--
Вероятность неудачи не превосходит полной массы распределения случайных
ограничений `𝓡_p`.
-/
lemma failureProbability_le_totalWeight
    {n w : Nat} (F : CNF n w) {p : Q} (t : Nat)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    failureProbability F p t ≤ Restriction.totalWeight n p := by
  classical
  have hpointwise : ∀ ρ ∈ Restriction.enumerate n,
      (if Restriction.hasDecisionTreeOfDepth ρ F.eval t = false then
        ρ.weight p
      else
        0)
        ≤ ρ.weight p := by
    intro ρ hρ
    by_cases hfail : Restriction.hasDecisionTreeOfDepth ρ F.eval t = false
    · simp [hfail]
    · have hnonneg : 0 ≤ ρ.weight p :=
        Restriction.weight_nonneg (ρ := ρ) hp₀ hp₁
      simpa [hfail] using hnonneg
  have hsum :=
    Restriction.sum_map_le_sum_map (Restriction.enumerate n)
      (fun ρ =>
        if Restriction.hasDecisionTreeOfDepth ρ F.eval t = false then
          ρ.weight p
        else
          0)
      (fun ρ => ρ.weight p) hpointwise
  have hf := failureProbability_eq_sum (F := F) (p := p) (t := t)
  have ht : ((Restriction.enumerate n).map fun ρ => ρ.weight p).sum
      = Restriction.totalWeight n p := by rfl
  -- После подстановки определений получаем требуемое неравенство.
  calc
    failureProbability F p t
        = ((Restriction.enumerate n).map
            (fun ρ =>
              if Restriction.hasDecisionTreeOfDepth ρ F.eval t = false then
                ρ.weight p
              else
                0)).sum := hf
    _ ≤ ((Restriction.enumerate n).map fun ρ => ρ.weight p).sum := hsum
    _ = Restriction.totalWeight n p := ht

/-- Вероятность неудачи не может быть отрицательной: каждый вклад неотрицателен. -/
lemma failureProbability_nonneg
    {n w : Nat} (F : CNF n w) {p : Q} (t : Nat)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ failureProbability F p t := by
  classical
  have hsum := failureProbability_eq_sum (F := F) (p := p) (t := t)
  -- Все слагаемые в явной сумме неотрицательны.
  have hterms :
      ∀ ρ ∈ Restriction.enumerate n,
        0 ≤
          (if Restriction.hasDecisionTreeOfDepth ρ F.eval t = false then
            ρ.weight p
          else
            0) := by
    intro ρ _
    by_cases hfail : Restriction.hasDecisionTreeOfDepth ρ F.eval t = false
    · have hnonneg : 0 ≤ ρ.weight p :=
        Restriction.weight_nonneg (ρ := ρ) hp₀ hp₁
      simpa [hfail]
    · simp [hfail]
  have hlist :
      0 ≤ ((Restriction.enumerate n).map
        (fun ρ =>
          if Restriction.hasDecisionTreeOfDepth ρ F.eval t = false then
            ρ.weight p
          else
            0)).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
    exact hterms ρ hρ
  -- Переписываем цель через эту сумму и применяем результат выше.
  refine hsum.symm ▸ ?_
  exact hlist

/-- Вероятность неудачи всегда ≤ 1 при стандартных ограничениях на `p`. -/
lemma failureProbability_le_one
    {n w : Nat} (F : CNF n w) {p : Q} (t : Nat)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    failureProbability F p t ≤ 1 := by
  have hle :=
    failureProbability_le_totalWeight (F := F) (p := p) (t := t) hp₀ hp₁
  have htotal := Restriction.totalWeight_eq_one n p
  rwa [htotal] at hle

end CNF

end Core
end Pnp3
