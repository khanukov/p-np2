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

end Core
end Pnp3
