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
import Mathlib.Tactic

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
Размер подкуба выражается через число фиксированных координат.  Формально:
существует `t ≤ n` (количество зафиксированных позиций), такое что число точек
подкуба равно `2^(n - t)`.  Пока оставляем это утверждение в виде аксиомы —
реальное доказательство можно импортировать из `mathlib` или перенести из
предыдущей версии проекта.
-/
axiom subcube_card_pow {n : Nat} (β : Subcube n) :
  ∃ t : Nat, t ≤ n ∧
    Fintype.card {x : BitVec n // mem β x} = Nat.pow 2 (n - t)

end Core
end Pnp3
