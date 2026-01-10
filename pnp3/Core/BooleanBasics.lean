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
      simp [List.flatMap_cons, List.map_cons,
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
    -- Приводим булеву проверку из определения `memB` к каноничному виду.
    have hi' : x i = b := by
      -- Приводим булеву проверку из определения `memB` к равенству значений.
      have htmp := hi
      simp [hib] at htmp
      exact htmp
    exact hi'
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
  -- Переписываем определение `mem` и применяем булеву характеристику.
  change memB β x = true ↔ ∀ i : Fin n, ∀ b : Bool, β i = some b → x i = b
  exact memB_eq_true_iff (β := β) (x := x)

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
        -- Сначала вычисляем явный результат присваивания.
        have hassignβ :
            Subcube.assign β i b =
              some (fun j => if j = i then some b else β j) := by
          simp [Subcube.assign, hβ]
        exact Eq.subst (motive := fun t => t = some γ) hassignβ hassign
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
            -- После подстановки `β i = none` получаем противоречие.
            have : False := by
              have hnoneEq :=
                Eq.subst (motive := fun t => t = some c) hβ hj
              cases hnoneEq
            exact False.elim this
          · have hif : (if j = i then some b else β j) = β j := by
              simp [hji]
            have htmp : (if j = i then some b else β j) = some c :=
              Eq.trans hif hj
            exact hγ' j c htmp
        have hβmem : mem β x :=
          (mem_iff (β := β) (x := x)).2 hβprop
        have hi : x i = b := by
          have : (if i = i then some b else β i) = some b := by simp
          have hinst := hγ' i b this
          exact hinst
        exact ⟨hβmem, hi⟩
      · intro hx
        rcases hx with ⟨hβmem, hib⟩
        have hβ' := (mem_iff (β := β) (x := x)).1 hβmem
        refine
          (mem_iff (β := fun j => if j = i then some b else β j) (x := x)).2 ?_
        intro j c hj
        by_cases hji : j = i
        · subst hji
          have hj' := hj
          -- После подстановки `j = i` сокращаем условие до равенства значений.
          simp at hj'
          have hb' : b = c := hj'
          have : c = b := hb'.symm
          simp [this, hib]
        · have : β j = some c := by
            -- Условие напрямую переписывается, когда `j ≠ i`.
            have htmp := hj
            simp [hji] at htmp
            exact htmp
          exact hβ' j c this
  | some bOld =>
      -- Координата уже фиксирована. Возможны два случая: согласие или конфликт.
      have hb' : b = bOld := by
        by_contra hbneq
        have hnone : Subcube.assign β i b = none := by
          simp [Subcube.assign, hβ, hbneq]
        have hcontra : none = some γ :=
          Eq.subst (motive := fun t => t = some γ) hnone hassign
        cases hcontra
      have hγ : γ = β := by
        have hassign' : Subcube.assign β i b = some β := by
          simp [Subcube.assign, hβ, hb']
        have hsome : some γ = some β := hassign.symm.trans hassign'
        exact (Option.some.inj hsome.symm).symm
      constructor
      · intro hγmem
        have hβmem : mem β x := by
          -- Используем равенство `γ = β` для переноса принадлежности.
          exact Eq.subst (motive := fun δ => mem δ x) hγ hγmem
        have hprop := (mem_iff (β := β) (x := x)).1 hβmem
        have hi : x i = bOld := hprop i bOld hβ
        have hi' : x i = b := by
          -- Переписываем значение через равенство `b = bOld`.
          exact hi.trans hb'.symm
        exact ⟨hβmem, hi'⟩
      · intro hx
        -- Опять переносим принадлежность через равенство `γ = β`.
        exact Eq.subst (motive := fun δ => mem δ x) hγ.symm hx.1

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
        -- Единственный результат: присваивание ничего не меняет.
        have htmp := hassign
        simp [Subcube.assignMany] at htmp
        exact htmp
      subst hγ
      simp
  | cons ub rest ih =>
      -- Разбираем первое присваивание и рекурсивно применяем гипотезу индукции.
      rcases ub with ⟨i, b⟩
      dsimp [Subcube.assignMany] at hassign
      cases hstep : Subcube.assign β i b with
      | none =>
          -- Конфликт невозможен, ведь результат объявлен как `some γ`.
          have hnone :
              Subcube.assignMany β (⟨i, b⟩ :: rest) = none := by
            simp [Subcube.assignMany, hstep]
          have hcontr :=
            Eq.subst (motive := fun t => t = some γ) hnone hassign
          cases hcontr
      | some β' =>
          have hrest : Subcube.assignMany β' rest = some γ := by
            have htmp := hassign
            simp [hstep] at htmp
            exact htmp
          have htail := ih (β := β') (γ := γ) hrest
          -- Эквивалентность для первого шага: принадлежность β' ↔ (β ∧ нужный бит).
          have hhead :=
            (mem_assign_iff (β := β) (γ := β') (i := i) (b := b)
              (x := x) hstep)
          -- Склеиваем два эквивалента и приводим результат к компактному виду.
          have hcombined :
              mem γ x ↔ (mem β x ∧ x i = b) ∧ ∀ u ∈ rest, x u.1 = u.2 := by
            constructor
            · intro hγmem
              have htail' := htail.mp hγmem
              rcases htail' with ⟨hβ', hrestProp⟩
              have hβmem := hhead.mp hβ'
              exact ⟨hβmem, hrestProp⟩
            · intro hgoal
              rcases hgoal with ⟨⟨hβmem, hib⟩, hrestProp⟩
              have hβ' := hhead.mpr ⟨hβmem, hib⟩
              exact htail.mpr ⟨hβ', hrestProp⟩
          -- Завершаем преобразование, переписывая условие на список.
          constructor
          · intro hγmem
            have hparts := hcombined.mp hγmem
            rcases hparts with ⟨⟨hβmem, hib⟩, hrestProp⟩
            refine ⟨hβmem, ?_⟩
            intro u hu
            have hunion := List.mem_cons.mp hu
            rcases hunion with hheadEq | htailMem
            · -- Для первого элемента списка получаем нужный бит напрямую.
              cases hheadEq
              simp [hib]
            · exact hrestProp u htailMem
          · intro hgoal
            rcases hgoal with ⟨hβmem, hlist⟩
            have hib : x i = b := by
              have hmem : ⟨i, b⟩ ∈ (⟨i, b⟩ :: rest) := by
                simp
              have hheadCase := hlist ⟨i, b⟩ hmem
              change x i = b at hheadCase
              exact hheadCase
            have hrestProp : ∀ u ∈ rest, x u.1 = u.2 := by
              intro u hu
              have hcase := hlist u (List.mem_cons.mpr (Or.inr hu))
              exact hcase
            have hcombined' : (mem β x ∧ x i = b) ∧ ∀ u ∈ rest, x u.1 = u.2 :=
              ⟨⟨hβmem, hib⟩, hrestProp⟩
            exact hcombined.mpr hcombined'


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
    · left; subst hγ; exact hx
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
    have : β ∈ R.dedup := hβ
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
            (covered_iff (Rset := R) x).mpr hcase
          exact (hcov this).elim
    have hfalse' : coveredB (R.dedup) x = false := by
      cases hcase : coveredB (R.dedup) x with
      | false => rfl
      | true =>
          have : covered (R.dedup) x :=
            (covered_iff (Rset := R.dedup) x).mpr hcase
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
          | false => simp
          | true => cases hb hcase
      have hfalse₂ : coveredB R₂ x = false := by
        by_cases hb : coveredB R₂ x = true
        · have hx := (covered_iff (Rset := R₂) x).mpr hb
          exact (hcov' hx).elim
        · cases hcase : coveredB R₂ x with
          | false => simp
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
  · have hβ' : β ∈ R₁.toFinset := List.mem_toFinset.mpr hβ
    have hβ'' : β ∈ R₂.toFinset := by
      -- Переносим членство через равенство множеств.
      exact h ▸ hβ'
    exact List.mem_toFinset.mp hβ''
  · have hβ' : β ∈ R₂.toFinset := List.mem_toFinset.mpr hβ
    have hβ'' : β ∈ R₁.toFinset := by
      -- Обратное направление равенства множеств.
      exact h.symm ▸ hβ'
    exact List.mem_toFinset.mp hβ''

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
    · intro hx; cases hx
  have hmismatch : mismatches = 0 := by
    -- После упрощения фильтра остаётся пустое множество, чья мощность равна нулю.
    simp [mismatches, hfilter]
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
        -- Совмещая два описания `β i`, получаем невозможное равенство `some b = none`.
        have hcontr : some b = none := by
          exact hb ▸ hnone
        cases hcontr
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
      -- После подстановки `h` декодер возвращает соответствующий бит.
      simp [decodeFun, h]
    have decode_eval_some (f : FreeIndex → Bool) (i : Fin n)
        {b : Bool} (h : β i = some b) : decodeFun f i = b := by
      have hne : β i ≠ none := by
        intro hnone; simp [hnone] at h
      have hval : Classical.choose (exists_of_ne_none (i := i) hne) = b := by
        have : some (Classical.choose (exists_of_ne_none (i := i) hne)) = some b := by
          -- `simp` по `h` уже раскрывает нужное равенство; дополнительных фактов не нужно.
          simp [h]
        exact Option.some.inj this
      -- После подстановки `h` остаётся заменить выбранный элемент на `b`.
      -- `simp` сводит цель к равенству выбранного значения с `b`.
      simpa [decodeFun, h] using hval
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
      simp
    have hfreeIndex_card : Fintype.card FreeIndex = n - t := by
      simp [hfree_card, hfree_count]
    have hfinal :
        Fintype.card {x : BitVec n // mem β x} = 2 ^ (n - t) := by
      calc
        Fintype.card {x : BitVec n // mem β x}
            = Fintype.card (FreeIndex → Bool) := hcube_card
        _ = 2 ^ Fintype.card FreeIndex := hfun_card
        _ = 2 ^ (n - t) := by simp [hfreeIndex_card]

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
    Literal.mk ℓ.idx ℓ.value = ℓ := by
  cases ℓ
  rfl

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
  simp [List.any_eq_false]

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
  simp [List.all_eq_false]

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
  simp [List.all_eq_false]

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
  simp [List.any_eq_false]

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

-- Для подсчётов удобно иметь `Fintype`-инстанс для всех рестрикций.
instance (n : Nat) : Fintype (Restriction n) := by
  classical
  refine Fintype.ofEquiv (Subcube n) ?_
  refine
    { toFun := fun mask => { mask := mask }
      invFun := Restriction.mask
      left_inv := by intro mask; rfl
      right_inv := by intro ρ; rfl }

-- Кардинал всех рестрикций равен `3^n`, поскольку каждая координата имеет три
-- варианта (`*`, `0`, `1`).  Это пригодится при комбинаторных подсчётах
-- вероятности в Switching Lemma.
lemma card_restriction (n : Nat) : Fintype.card (Restriction n) = 3 ^ n := by
  classical
  -- Сводим к `Subcube n = Fin n → Option Bool`.
  let e : Restriction n ≃ Subcube n :=
    { toFun := Restriction.mask
      invFun := fun mask => { mask := mask }
      left_inv := by intro ρ; rfl
      right_inv := by intro mask; rfl }
  -- Кардинал функции равен `|Option Bool|^n = 3^n`.
  have hcard : Fintype.card (Subcube n) = 3 ^ n := by
    -- `simp` разворачивает `Subcube` в пространство функций и считает кардинал.
    simp [Subcube]
  simpa [hcard] using (Fintype.card_congr e)


/-- Полностью свободное ограничение. -/
@[simp] def free (n : Nat) : Restriction n :=
  { mask := fun _ => none }

/-- Три варианта для каждой координаты: `*`, `0`, `1`. -/
@[simp] def optionChoices : List (Option Bool) := [none, some false, some true]

/--
Множество зафиксированных координат рестрикции.

Мы используем фильтрацию по `Option.isSome`: координата принадлежит `fixedPositions`,
если соответствующий бит подкуба задан явно.
-/
@[simp] def fixedPositions (ρ : Restriction n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => (ρ.mask i).isSome)

/--
Множество свободных координат рестрикции.

Это комплементарное множество к `fixedPositions`: координата свободна тогда и
только тогда, когда в маске стоит `none`.
-/
@[simp] def freePositions (ρ : Restriction n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => (ρ.mask i).isNone)

/-- Число зафиксированных координат. -/
@[simp] def fixedCount (ρ : Restriction n) : Nat :=
  ρ.fixedPositions.card

/-- Характеризация принадлежности `fixedPositions`. -/
@[simp] lemma mem_fixedPositions {ρ : Restriction n} {i : Fin n} :
    i ∈ ρ.fixedPositions ↔ (ρ.mask i).isSome := by
  classical
  simp [fixedPositions]

/-- Характеризация принадлежности `freePositions`. -/
@[simp] lemma mem_freePositions {ρ : Restriction n} {i : Fin n} :
    i ∈ ρ.freePositions ↔ (ρ.mask i).isNone := by
  classical
  simp [freePositions]

@[ext] lemma ext {ρ σ : Restriction n} (h : ∀ i, ρ.mask i = σ.mask i) : ρ = σ := by
  cases ρ with
  | mk ρmask =>
      cases σ with
      | mk σmask =>
          have hmask : ρmask = σmask := funext h
          cases hmask
          rfl

/--
Построить рестрикцию с заранее заданным множеством свободных координат.

Мы передаём функцию, которая назначает значения **только** на фиксированной
части (дополнение `free`). На свободных координатах маска всегда `none`.
-/
def restrictionOfFree (free : Finset (Fin n))
    (assign : {i : Fin n // i ∉ free} → Bool) : Restriction n :=
  { mask := fun i =>
      if h : i ∈ free then
        none
      else
        some (assign ⟨i, h⟩) }

lemma restrictionOfFree_mask_of_mem
    (free : Finset (Fin n)) (assign : {i : Fin n // i ∉ free} → Bool)
    {i : Fin n} (hmem : i ∈ free) :
    (restrictionOfFree free assign).mask i = none := by
  simp [restrictionOfFree, hmem]

lemma restrictionOfFree_mask_of_not_mem
    (free : Finset (Fin n)) (assign : {i : Fin n // i ∉ free} → Bool)
    {i : Fin n} (hmem : i ∉ free) :
    (restrictionOfFree free assign).mask i = some (assign ⟨i, hmem⟩) := by
  simp [restrictionOfFree, hmem]

/--
У `restrictionOfFree` множество свободных координат совпадает с `free`.
-/
lemma freePositions_restrictionOfFree
    (free : Finset (Fin n)) (assign : {i : Fin n // i ∉ free} → Bool) :
    (restrictionOfFree free assign).freePositions = free := by
  classical
  ext i
  by_cases hmem : i ∈ free
  · -- На свободных координатах маска равна `none`.
    simp [Restriction.freePositions, restrictionOfFree, hmem]
  · -- Вне `free` маска равна `some`, значит `isNone` ложно.
    simp [Restriction.freePositions, restrictionOfFree, hmem]

/--
Из рестрикции с фиксированным множеством свободных координат извлекаем
значения на фиксированной части.
-/
def assignOfRestriction
    (free : Finset (Fin n)) (ρ : Restriction n)
    (_hfree : ρ.freePositions = free) :
    {i : Fin n // i ∉ free} → Bool :=
  fun i => (ρ.mask i.1).getD false

/--
Эквивалентность между функциями на фиксированной части и рестрикциями с
фиксированным множеством свободных координат.
-/
noncomputable def restrictionOfFreeEquiv
    (free : Finset (Fin n)) :
    ({i : Fin n // i ∉ free} → Bool) ≃
      {ρ : Restriction n // ρ.freePositions = free} :=
  { toFun := fun assign => ⟨restrictionOfFree free assign,
      freePositions_restrictionOfFree free assign⟩
    invFun := fun ρ => assignOfRestriction free ρ.1 ρ.2
    left_inv := by
      intro assign
      funext i
      -- Для фиксированной координаты маска всегда `some`.
      cases i with
      | mk i hmem =>
          simp [assignOfRestriction, restrictionOfFree, hmem]
    right_inv := by
      intro ρ
      apply Subtype.ext
      apply Restriction.ext
      intro i
      by_cases hmem : i ∈ free
      · -- На свободных координатах обе маски равны `none`.
        have hfree : i ∈ ρ.1.freePositions := by
          have hmem' := hmem
          rw [← ρ.2] at hmem'
          exact hmem'
        have hmask : (ρ.1.mask i).isNone :=
          (Restriction.mem_freePositions (ρ := ρ.1) (i := i)).1 hfree
        have hmask' : ρ.1.mask i = none := (Option.isNone_iff_eq_none).1 hmask
        simp [restrictionOfFree, hmem, hmask']
      · -- На фиксированной части извлекаем значение из `ρ`.
        cases h : ρ.1.mask i with
        | none =>
            have hnone : (ρ.1.mask i).isNone := by
              -- Уточняем `isNone` через значение маски.
              simp [h]
            have hmem' : i ∈ ρ.1.freePositions :=
              (Restriction.mem_freePositions (ρ := ρ.1) (i := i)).2 hnone
            have hmem'' : i ∈ free := by
              exact (Eq.ndrec (motive := fun s => i ∈ s) hmem' ρ.2)
            exact (hmem hmem'').elim
        | some b =>
            simp [assignOfRestriction, restrictionOfFree, hmem, h]
  }

/--
Число рестрикций с фиксированным множеством свободных координат.
-/
lemma restrictions_with_freePositions_card
    (free : Finset (Fin n)) :
    Fintype.card {ρ : Restriction n // ρ.freePositions = free}
      = 2 ^ (n - free.card) := by
  classical
  -- Сводим к функциям на дополнении `free`.
  have hcard :
      Fintype.card {ρ : Restriction n // ρ.freePositions = free}
        = Fintype.card ({i : Fin n // i ∉ free} → Bool) :=
    Fintype.card_congr (restrictionOfFreeEquiv free).symm
  have hfun :
      Fintype.card ({i : Fin n // i ∉ free} → Bool)
        = 2 ^ Fintype.card {i : Fin n // i ∉ free} := by
    -- `simp` умеет считать кардинал функции в `Bool`.
    simp
  have hcomp :
      Fintype.card {i : Fin n // i ∉ free} = n - free.card := by
    -- Переписываем через кардинал комплемента `free` в `Fin n`.
    have hsub :
        Fintype.card {i : Fin n // i ∉ free}
          = (Finset.univ.filter fun i => i ∉ free).card := by
      simpa using (Fintype.card_subtype (p := fun i : Fin n => i ∉ free))
    have hfilter :
        (Finset.univ.filter fun i => i ∉ free) = (Finset.univ \ free) := by
      ext i
      simp [Finset.mem_sdiff]
    have hsdiff :
        (Finset.univ \ free).card = (Finset.univ : Finset (Fin n)).card - free.card := by
      exact Finset.card_sdiff (by simp)
    have huniv : (Finset.univ : Finset (Fin n)).card = n := by
      -- `simp` раскрывает кардинал универсального множества `Fin n`.
      simp
    calc
      Fintype.card {i : Fin n // i ∉ free}
          = (Finset.univ \ free).card := by simpa [hfilter] using hsub
      _ = (Finset.univ : Finset (Fin n)).card - free.card := hsdiff
      _ = n - free.card := by
          -- Подстановка `huniv` и упрощение.
          simp [huniv]
  calc
    Fintype.card {ρ : Restriction n // ρ.freePositions = free}
        = Fintype.card ({i : Fin n // i ∉ free} → Bool) := hcard
    _ = 2 ^ Fintype.card {i : Fin n // i ∉ free} := hfun
    _ = 2 ^ (n - free.card) := by
        -- После подстановки `hcomp` достаточно обычного `simp`.
        simp [hcomp]

/--
Оценка сверху: число зафиксированных координат не превосходит `n`.
Эта лемма будет использоваться при грубых комбинаторных оценках для
числа рестрикций.
-/
lemma fixedCount_le (ρ : Restriction n) : ρ.fixedCount ≤ n := by
  classical
  -- `card` фильтра не превосходит `card` всего множества.
  have hcard :
      ρ.fixedPositions.card ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa [fixedPositions] using
      (Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun i => (ρ.mask i).isSome))
  -- У универсума кардинал равен `n`.
  have huniv : (Finset.univ : Finset (Fin n)).card = n := by
    -- Кардинал `Fin n` равен `n`.
    simp
  simpa [fixedCount, huniv] using hcard

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
  | none =>
      -- При `none` гипотеза `hβ` невозможна.
      have hcontra : (none : Option Bool) = some b := by
        simpa [hρ] using hβ
      cases hcontra
  | some b' =>
      have hb : b' = b := by
        simpa [hρ] using hβ
      -- В ветви `some` достаточно заменить `b'` на `b`.
      simp [hb]

/-- Если `x` удовлетворяет ограничению, `override` не меняет вектор. -/
lemma override_eq_of_mem {ρ : Restriction n} {x : BitVec n}
    (h : mem ρ.mask x) : ρ.override x = x := by
  classical
  funext i
  unfold override
  cases hρ : ρ.mask i with
  | none => rfl
  | some b =>
      -- Передаём явное значение маски, чтобы избежать лишних `simp`.
      have hx := (mem_iff (β := ρ.mask) (x := x)).1 h i b hρ
      simp [hρ, hx]

/-- Совместимость эквивалентна тождественности `override`. -/
lemma compatible_iff_override_eq {ρ : Restriction n} {x : BitVec n} :
    ρ.compatible x = true ↔ ρ.override x = x := by
  constructor
  · intro hcompat
    have hmem : mem ρ.mask x := hcompat
    -- Подставляем доказательство совместимости и упрощаем.
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

/--
  Сбрасываем координату `i` в состояние «звезда».  Эта операция понадобится
  при обратной реконструкции исходного ограничения из закодированного
  свидетеля switching-леммы: мы будем восстанавливать исходные звёзды,
  последовательно отменяя ранее сделанные присваивания.
-/
@[simp] def unassign (ρ : Restriction n) (i : Fin n) : Restriction n :=
  ⟨fun j => if j = i then none else ρ.mask j⟩

@[simp] lemma unassign_mask (ρ : Restriction n) (i : Fin n) (j : Fin n) :
    (ρ.unassign i).mask j = if j = i then none else ρ.mask j := by
  rfl

/-- Если координата `i` уже свободна, то операция `unassign` ничего не
  меняет. -/
lemma unassign_of_free {ρ : Restriction n} {i : Fin n}
    (hfree : ρ.mask i = none) :
    ρ.unassign i = ρ := by
  cases' ρ with mask
  apply congrArg Restriction.mk
  funext j
  classical
  change (if j = i then none else mask j) = mask j
  by_cases hj : j = i
  · cases hj
    have hmask : mask i = none := hfree
    simp [hmask]
  · simp [hj]


/--
  Присваивание свободной координаты, а затем её явное освобождение возвращает
  исходное ограничение.  Важный шаг при доказательстве инъективности
  кодирования «плохих» ограничений.
-/
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

/--
  Присваивание свободной координаты, а затем её явное освобождение возвращает
  исходное ограничение.  Важный шаг при доказательстве инъективности
  кодирования «плохих» ограничений.
-/
lemma unassign_assign_of_free {ρ : Restriction n} {i : Fin n} {b : Bool}
    {ρ' : Restriction n} (hassign : ρ.assign i b = some ρ')
    (hfree : ρ.mask i = none) :
    ρ'.unassign i = ρ := by
  classical
  cases' ρ with mask
  cases' ρ' with mask'
  have hmask :=
    assign_mask_eq (ρ := ⟨mask⟩) (ρ' := ⟨mask'⟩) (i := i) (b := b) hassign
  apply congrArg Restriction.mk
  funext j
  have hmask_i : mask i = none := hfree
  have hmask_j := hmask j
  change (if j = i then none else mask' j) = mask j
  by_cases hj : j = i
  · cases hj
    have hβ : mask' i = some b := by
      simpa [if_pos rfl] using hmask_j
    have hgoal : (if i = i then none else mask' i) = mask i := by
      have hmask_i_free : mask i = none := hmask_i
      simp [hβ, hmask_i_free]
    exact hgoal
  · have hβ : mask' j = mask j := by
      have hIf : (if j = i then some b else mask j) = mask j := by
        simp [hj]
      exact Eq.trans hmask_j hIf
    have hgoal : (if j = i then none else mask' j) = mask j := by
      simp [hj, hβ]
    exact hgoal

lemma mask_eq_some_of_not_none {ρ : Restriction n} {i : Fin n}
    (h : ρ.mask i ≠ none) : ∃ b : Bool, ρ.mask i = some b := by
  cases hmask : ρ.mask i with
  | none => cases h <| by simpa [hmask]
  | some b => exact ⟨b, rfl⟩

/-- Список свободных координат (там, где маска равна `none`). -/
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

/-- Число свободных координат. -/
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

/--
Свободные координаты как `Finset`: `freePositions` совпадает с
`freeIndicesList.toFinset`.

Мы сознательно доказываем через поэлементное равенство: membership в `Finset`
редуцируется к `mask i = none` (для списка) и к `Option.isNone` (для `Finset`),
после чего используется `Option.isNone_iff_eq_none`.
-/
lemma freePositions_eq_toFinset_freeIndicesList (ρ : Restriction n) :
    ρ.freeIndicesList.toFinset = ρ.freePositions := by
  classical
  ext i
  -- Сводим обе стороны к утверждению о значении маски.
  constructor
  · intro hi
    -- Левая часть: `i` в `freeIndicesList` ↔ `mask i = none`.
    have hmask : ρ.mask i = none :=
      (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).1 (by
        -- В `Finset` membership означает membership в исходном списке.
        simpa using hi)
    -- Переводим `mask i = none` в `isNone` и возвращаемся к `freePositions`.
    exact (Restriction.mem_freePositions (ρ := ρ) (i := i)).2
      ((Option.isNone_iff_eq_none).2 hmask)
  · intro hi
    -- Правая часть: `i` в `freePositions` ↔ `mask i` равно `none`.
    have hmask : ρ.mask i = none := by
      -- В `freePositions` membership эквивалентен `isNone`.
      have hnone : (ρ.mask i).isNone := (Restriction.mem_freePositions (ρ := ρ) (i := i)).1 hi
      exact (Option.isNone_iff_eq_none).1 hnone
    -- Возвращаемся к membership в списке и затем в `Finset`.
    have hmem : i ∈ ρ.freeIndicesList :=
      (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).2 hmask
    simpa using hmem

/--
Число свободных координат, выраженное через `Finset.card`.

Это удобная связка между списковым `freeCount` и `freePositions`.
-/
lemma freePositions_card_eq_freeCount (ρ : Restriction n) :
    ρ.freePositions.card = ρ.freeCount := by
  classical
  -- `freeIndicesList` не содержит повторов, поэтому `toFinset.card` равен длине списка.
  have hnodup := freeIndicesList_nodup (ρ := ρ)
  have hcard : ρ.freeIndicesList.toFinset.card = ρ.freeIndicesList.length := by
    simpa [List.dedup_eq_self.2 hnodup] using
      (List.card_toFinset ρ.freeIndicesList)
  -- Явно переписываем `freePositions` в сторону `freeIndicesList.toFinset`,
  -- чтобы не зависеть от направления `simp`.
  have hpos : ρ.freePositions = ρ.freeIndicesList.toFinset := by
    simpa using (freePositions_eq_toFinset_freeIndicesList (ρ := ρ)).symm
  -- Финализируем через длину списка.
  calc
    ρ.freePositions.card = ρ.freeIndicesList.toFinset.card := by
      rw [hpos]
    _ = ρ.freeIndicesList.length := hcard
    _ = ρ.freeCount := rfl

/--
Число рестрикций, оставляющих ровно `s` свободных координат.
-/
lemma restrictions_with_freeCount_card
    (s : Nat) :
    Fintype.card {ρ : Restriction n // ρ.freeCount = s}
      = Nat.choose n s * 2 ^ (n - s) := by
  classical
  -- Переформулируем через `freePositions.card = s`.
  have hpos :
      Fintype.card {ρ : Restriction n // ρ.freeCount = s}
        = Fintype.card {ρ : Restriction n // ρ.freePositions.card = s} := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun ρ => ⟨ρ.1, by simpa [freePositions_card_eq_freeCount] using ρ.2⟩
        invFun := fun ρ => ⟨ρ.1, by simpa [freePositions_card_eq_freeCount] using ρ.2⟩
        left_inv := by intro ρ; rfl
        right_inv := by intro ρ; rfl }
  -- Разбиваем по выбору множества свободных координат размера `s`.
  let FreeSet := {free : Finset (Fin n) // free.card = s}
  have hsplit :
      Fintype.card {ρ : Restriction n // ρ.freePositions.card = s}
        = Fintype.card (Σ free : FreeSet, {ρ : Restriction n // ρ.freePositions = free.1}) := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun ρ =>
          ⟨⟨ρ.1.freePositions, by simpa using ρ.2⟩, ⟨ρ.1, rfl⟩⟩
        invFun := fun ρ =>
          ⟨ρ.2.1, by
            have hcard' :
                ρ.2.1.freePositions.card = ρ.1.1.card := by
              simpa using congrArg Finset.card ρ.2.2
            exact hcard'.trans ρ.1.2⟩
        left_inv := by intro ρ; rfl
        right_inv := by
          intro ρ
          cases ρ with
          | mk free rest =>
              cases rest with
              | mk ρ hfree =>
                  cases free with
                  | mk free hcard =>
                      cases hfree
                      rfl }
  -- Кардинал сигмы: сумма по всем `free`.
  have hsum :
      Fintype.card (Σ free : FreeSet, {ρ : Restriction n // ρ.freePositions = free.1})
        = ∑ free : FreeSet, Fintype.card {ρ : Restriction n // ρ.freePositions = free.1} := by
    simpa using (Fintype.card_sigma (α := FreeSet)
      (β := fun free => {ρ : Restriction n // ρ.freePositions = free.1}))
  -- Число множеств размера `s` равно биному.
  have hfree_card :
      Fintype.card FreeSet = Nat.choose n s := by
    have hcard :
        Fintype.card FreeSet
          = (Finset.univ.filter fun free : Finset (Fin n) => free.card = s).card := by
      simpa [FreeSet] using
        (Fintype.card_subtype (p := fun free : Finset (Fin n) => free.card = s))
    have hfilter :
        (Finset.univ.filter fun free : Finset (Fin n) => free.card = s)
          = (Finset.univ : Finset (Fin n)).powersetCard s := by
      ext free
      simp [Finset.mem_powersetCard]
    calc
      Fintype.card FreeSet
          = (Finset.univ.filter fun free : Finset (Fin n) => free.card = s).card := hcard
      _ = ((Finset.univ : Finset (Fin n)).powersetCard s).card := by simpa [hfilter]
      _ = Nat.choose n s := by
          simpa [Finset.card_univ] using
            (Finset.card_powersetCard (n := s) (s := (Finset.univ : Finset (Fin n))))
  -- Теперь собираем всё вместе.
  calc
    Fintype.card {ρ : Restriction n // ρ.freeCount = s}
        = Fintype.card {ρ : Restriction n // ρ.freePositions.card = s} := hpos
    _ = Fintype.card (Σ free : FreeSet, {ρ : Restriction n // ρ.freePositions = free.1}) := hsplit
    _ = ∑ free : FreeSet, Fintype.card {ρ : Restriction n // ρ.freePositions = free.1} := hsum
    _ = ∑ _free : FreeSet, 2 ^ (n - s) := by
          -- Для каждого `free` с `free.card = s` кардинал одинаковый.
          refine Finset.sum_congr rfl ?_
          intro free _hmem
          have hcard : Fintype.card {ρ : Restriction n // ρ.freePositions = free.1}
              = 2 ^ (n - free.1.card) := restrictions_with_freePositions_card (free := free.1)
          simpa [free.2] using hcard
    _ = Fintype.card FreeSet * 2 ^ (n - s) := by
          simpa using (Finset.sum_const (2 ^ (n - s)) (s := (Finset.univ : Finset FreeSet)))
    _ = Nat.choose n s * 2 ^ (n - s) := by
          simpa [hfree_card]

/--
Финитное множество рестрикций с ровно `s` свободными координатами.

Это удобная обёртка для работы в стиле `R_s` (равномерное распределение по
рестрикциям с фиксированным числом свободных координат), которая позволит
обходиться без вероятностного формализма в multi‑switching.
-/
@[simp] def restrictionsWithFreeCount (s : Nat) : Finset (Restriction n) :=
  (Finset.univ : Finset (Restriction n)).filter (fun ρ => ρ.freeCount = s)

@[simp] lemma mem_restrictionsWithFreeCount {ρ : Restriction n} {s : Nat} :
    ρ ∈ restrictionsWithFreeCount (n := n) s ↔ ρ.freeCount = s := by
  classical
  simp [restrictionsWithFreeCount]

/--
Кардинал `restrictionsWithFreeCount` совпадает с формулой из
`restrictions_with_freeCount_card`.
-/
lemma restrictionsWithFreeCount_card (s : Nat) :
    (restrictionsWithFreeCount (n := n) s).card
      = Nat.choose n s * 2 ^ (n - s) := by
  classical
  have hcard :
      (restrictionsWithFreeCount (n := n) s).card
        = Fintype.card {ρ : Restriction n // ρ.freeCount = s} := by
    simpa [restrictionsWithFreeCount] using
      (Fintype.card_subtype (p := fun ρ : Restriction n => ρ.freeCount = s)).symm
  calc
    (restrictionsWithFreeCount (n := n) s).card
        = Fintype.card {ρ : Restriction n // ρ.freeCount = s} := hcard
    _ = Nat.choose n s * 2 ^ (n - s) := restrictions_with_freeCount_card (n := n) (s := s)

/-- Кардинал `R_s` положителен, если `s ≤ n`. -/
lemma restrictionsWithFreeCount_card_pos {s : Nat} (hs : s ≤ n) :
    0 < (restrictionsWithFreeCount (n := n) s).card := by
  -- Используем явную формулу `|R_s| = C(n,s) * 2^(n-s)`.
  have hchoose : 0 < Nat.choose n s := Nat.choose_pos hs
  have hpow : 0 < 2 ^ (n - s) := by
    exact Nat.pow_pos (by decide : 0 < (2 : Nat))
  have hmul : 0 < Nat.choose n s * 2 ^ (n - s) := Nat.mul_pos hchoose hpow
  -- Переписываем по лемме `restrictionsWithFreeCount_card`.
  have hcard := restrictionsWithFreeCount_card (n := n) (s := s)
  -- Явно переписываем по равенству кардинала, избегая агрессивного `simp`.
  exact hcard ▸ hmul

/-- `R_s` непусто при `s ≤ n`. -/
lemma restrictionsWithFreeCount_nonempty {s : Nat} (hs : s ≤ n) :
    (restrictionsWithFreeCount (n := n) s).Nonempty := by
  classical
  -- Положительный кардинал эквивалентен непустоте финитного множества.
  exact Finset.card_pos.mp (restrictionsWithFreeCount_card_pos (n := n) (s := s) hs)

/--
Комбинаторная лемма: если `s ⊆ t` и кардинал `s` строго меньше `t`,
то в `t` обязательно есть элемент, не принадлежащий `s`.

Эта форма удобно применяется к множеству "плохих" рестрикций внутри
`restrictionsWithFreeCount`: из строгой оценки на кардинал сразу следует
существование "хорошей" рестрикции.
-/
lemma exists_not_mem_of_subset_card_lt {α : Type} [DecidableEq α]
    {s t : Finset α} (hsub : s ⊆ t) (hcard : s.card < t.card) :
    ∃ x ∈ t, x ∉ s := by
  classical
  by_contra h
  have hsubset : t ⊆ s := by
    intro x hx
    by_contra hxnot
    exact h ⟨x, hx, hxnot⟩
  have hcard_le : t.card ≤ s.card := by
    simpa using (Finset.card_le_card hsubset)
  have hcard_eq : s.card = t.card := by
    apply le_antisymm
    · simpa using (Finset.card_le_card hsub)
    · exact hcard_le
  have : s.card < s.card := by simpa [hcard_eq] using hcard
  exact (lt_irrefl _ this)

lemma fixedPositions_disjoint_freePositions (ρ : Restriction n) :
    Disjoint ρ.fixedPositions ρ.freePositions := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro i hi_fixed hi_free
  have hs : (ρ.mask i).isSome := (mem_fixedPositions (ρ := ρ) (i := i)).1 hi_fixed
  have hn : (ρ.mask i).isNone := (mem_freePositions (ρ := ρ) (i := i)).1 hi_free
  cases h : ρ.mask i with
  | none =>
      -- `isSome` противоречит `mask i = none`.
      have : False := by
        simpa [Option.isSome, Option.isNone, h] using hs
      exact this
  | some b =>
      -- `isNone` противоречит `mask i = some b`.
      have : False := by
        simpa [Option.isSome, Option.isNone, h] using hn
      exact this

lemma fixed_union_free (ρ : Restriction n) :
    ρ.fixedPositions ∪ ρ.freePositions = (Finset.univ : Finset (Fin n)) := by
  classical
  ext i
  by_cases h : ρ.mask i = none
  · simp [fixedPositions, freePositions, h]
  · have hs : (ρ.mask i).isSome := by
      cases hmask : ρ.mask i with
      | none =>
          cases h (by simp [hmask])
      | some b =>
          simp [hmask]
    simp [fixedPositions, freePositions, h, hs]

/--
Разбиение координат на фиксированные и свободные:
`fixedCount + freeCount = n`.

Это базовая комбинаторная формула для подсчёта рестрикций.
-/
lemma fixedCount_add_freeCount (ρ : Restriction n) :
    ρ.fixedCount + ρ.freeCount = n := by
  classical
  -- Используем стандартное разбиение через `filter`.
  -- Здесь `p` выбирает фиксированные координаты (`isSome`), а `¬ p`
  -- выбирает свободные (`isNone`).
  have hcard :=
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => (ρ.mask i).isSome)
  have hneg :
      (Finset.univ : Finset (Fin n)).filter (fun i => ¬ (ρ.mask i).isSome)
        = ρ.freePositions := by
    ext i
    -- `¬ isSome` эквивалентно `isNone`, а у `freePositions` именно эта фильтрация.
    cases h : ρ.mask i <;> simp [freePositions, h]
  have hfixed :
      (Finset.univ : Finset (Fin n)).filter (fun i => (ρ.mask i).isSome)
        = ρ.fixedPositions := by
    ext i
    simp [fixedPositions]
  -- Избавляемся от `simp` с большим числом переписок, чтобы не упираться
  -- в лимит глубины.
  have hcard' := hcard
  -- Переписываем фильтры через `fixedPositions`/`freePositions`.
  rw [hfixed, hneg] at hcard'
  -- Приводим к `fixedCount` и `freePositions.card`.
  have hcard'' : ρ.fixedCount + ρ.freePositions.card = (Finset.univ : Finset (Fin n)).card := by
    simpa [fixedCount] using hcard'
  -- Кардинал `Finset.univ` равен `n` для `Fin n`.
  have huniv : (Finset.univ : Finset (Fin n)).card = n := by
    simpa using (Finset.card_univ (α := Fin n))
  have hcard_final : ρ.fixedCount + ρ.freePositions.card = n := hcard''.trans huniv
  simpa [freePositions_card_eq_freeCount] using hcard_final

lemma assign_some_of_mem_freeIndicesList {ρ : Restriction n} {i : Fin n}
    {b : Bool} (hmem : i ∈ ρ.freeIndicesList) :
    ∃ ρ' : Restriction n, ρ.assign i b = some ρ' := by
  classical
  have hmask : ρ.mask i = none := (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).1 hmem
  refine ⟨⟨fun j => if j = i then some b else ρ.mask j⟩, ?_⟩
  simp [Restriction.assign, Subcube.assign, hmask]

/-!
  Фиксация свободной координаты уменьшает число свободных позиций ровно на
  единицу: новый список свободных индексов получается фильтрацией старого по
  условию `≠ i`.
-/
lemma freeCount_assign_of_mem {ρ : Restriction n} {i : Fin n}
    {b : Bool} {ρ' : Restriction n}
    (hmem : i ∈ ρ.freeIndicesList)
    (hassign : ρ.assign i b = some ρ') :
    ρ'.freeCount = ρ.freeCount - 1 := by
  classical
  have hmask := assign_mask_eq (ρ := ρ) (ρ' := ρ') (i := i) (b := b) hassign
  have hmask_i : ρ'.mask i = some b := by
    have := hmask i
    simp at this
    exact this
  have hmask_fun :
      (fun j => decide (ρ'.mask j = none))
        = fun j => decide (ρ.mask j = none) && decide (j ≠ i) := by
    funext j
    have hmask_j := hmask j
    by_cases hij : j = i
    · subst hij
      simp [hmask_i]
    · have : ρ'.mask j = ρ.mask j := by
        simp [hmask_j, hij]
      simp [this, hij]
  have hfilter_eq :
      ρ'.freeIndicesList =
        (List.finRange n).filter
          (fun j => decide (ρ.mask j = none) && decide (j ≠ i)) := by
    unfold Restriction.freeIndicesList
    exact congrArg (fun g => (List.finRange n).filter g) hmask_fun
  have hfinset_eq :
      (Finset.univ.filter fun j => ρ'.mask j = none) =
        (Finset.univ.filter fun j => ρ.mask j = none).erase i := by
    apply Finset.ext
    intro j
    have hmask_j := hmask j
    by_cases hij : j = i
    · subst hij
      simp [Finset.mem_filter, Finset.mem_erase, hmask_i]
    · simp [Finset.mem_filter, Finset.mem_erase, hmask_j, hij]
  have hmask_none : ρ.mask i = none :=
    (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).1 hmem
  have hi_mem_set : i ∈ (Finset.univ.filter fun j => ρ.mask j = none) := by
    simp [Finset.mem_filter, hmask_none]
  have hcard_eq :
      (Finset.univ.filter fun j => ρ'.mask j = none).card + 1 =
        (Finset.univ.filter fun j => ρ.mask j = none).card := by
    have hcard := Finset.card_erase_add_one hi_mem_set
    have hcard' :
        ((Finset.univ.filter fun j => ρ.mask j = none).erase i).card + 1 =
          (Finset.univ.filter fun j => ρ.mask j = none).card := hcard
    have hcard'' := hcard'
    rw [← hfinset_eq] at hcard''
    exact hcard''
  have hcount_formula :
      ∀ σ : Restriction n,
        σ.freeCount =
          (Finset.univ.filter fun j => σ.mask j = none).card := by
    intro σ
    unfold Restriction.freeCount Restriction.freeIndicesList
    set L := (List.finRange n).filter (fun j => decide (σ.mask j = none)) with hL
    have hsub : L.Sublist (List.finRange n) := by
      simpa [hL] using List.filter_sublist
        (l := List.finRange n) (p := fun j => decide (σ.mask j = none))
    have hnodup : L.Nodup :=
      List.Sublist.nodup hsub (List.nodup_finRange n)
    have hcard := List.card_toFinset L
    have hdedup : L.dedup = L := (List.dedup_eq_self).2 hnodup
    have hlen_to_card : L.length = L.toFinset.card := by
      have hlen_dedup : L.dedup.length = L.length :=
        congrArg List.length hdedup
      have hcard' : L.toFinset.card = L.length := Eq.trans hcard hlen_dedup
      exact hcard'.symm
    have hfilter_toFinset :=
      List.toFinset_filter (List.finRange n)
        (fun j => decide (σ.mask j = none))
    have hfinrange := List.toFinset_finRange n
    have hfinset_card :
        L.toFinset =
          (Finset.univ.filter fun j => σ.mask j = none) := by
      simpa [hL, hfilter_toFinset, hfinrange]
    have hlen :=
      calc
        L.length = L.toFinset.card := hlen_to_card
        _ = (Finset.univ.filter fun j => σ.mask j = none).card := by
              simp [hfinset_card]
    have hlen' := hlen
    simp [hL] at hlen'
    exact hlen'
  have hcount_eq := hcount_formula ρ
  have hcount_eq' := hcount_formula ρ'
  have hsucc_eq : Nat.succ ρ'.freeCount = ρ.freeCount := by
    have htmp := hcard_eq
    simp [Nat.succ_eq_add_one, hcount_eq, hcount_eq'] at htmp
    exact htmp
  have hpred := congrArg Nat.pred hsucc_eq
  have hfinal := hpred
  simp [Nat.pred_eq_sub_one] at hfinal
  exact hfinal

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

/--
  Вес ограничения после `unassign` отличается ровно в коэффициент
  `\frac{2p}{1-p}`. Остальные множители совпадают покоординатно, поскольку
  операция затрагивает только выбранную позицию `i`.
-/
lemma weight_unassign_mul (ρ : Restriction n) (i : Fin n) (p : Q)
    {b : Bool} (hmask : ρ.mask i = some b) (hp : p ≠ 1) :
    Restriction.weight (ρ.unassign i) p
      = ((2 * p) / (1 - p)) * Restriction.weight ρ p := by
  classical
  let F : Option Bool → Q :=
    fun
    | none => p
    | some _ => ((1 : Q) - p) / 2
  have hmem : (i : Fin n) ∈ (Finset.univ : Finset (Fin n)) := by
    exact Finset.mem_univ i
  have hunassign_prod :=
    (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => F ((ρ.unassign i).mask j))
      (a := i) hmem).symm
  have hρ_prod :=
    (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => F (ρ.mask j))
      (a := i) hmem).symm
  have hmask_eq :
      ∀ j ∈ Finset.univ.erase i,
        (ρ.unassign i).mask j = ρ.mask j := by
    intro j hj
    obtain ⟨hji, _⟩ := Finset.mem_erase.mp hj
    have hneq : j ≠ i := hji
    simp [Restriction.unassign_mask, hneq]
  have htail :
      (∏ j ∈ Finset.univ.erase i,
        F ((ρ.unassign i).mask j))
        = ∏ j ∈ Finset.univ.erase i,
            F (ρ.mask j) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hmask_eq' := hmask_eq j hj
    have hcongr := congrArg F hmask_eq'
    simpa [F] using hcongr
  have hρ_weight : Restriction.weight ρ p
      = F (ρ.mask i)
          * ∏ j ∈ Finset.univ.erase i,
              F (ρ.mask j) := by
    simpa [Restriction.weight, F]
      using hρ_prod
  have hunassign_weight : Restriction.weight (ρ.unassign i) p
      = F ((ρ.unassign i).mask i)
          * ∏ j ∈ Finset.univ.erase i,
              F ((ρ.unassign i).mask j) := by
    simpa [Restriction.weight, F]
      using hunassign_prod
  have hdenom : 1 - p ≠ 0 := by
    exact sub_ne_zero.mpr ((ne_comm).mp hp)
  have hcoeff : ((2 * p) / (1 - p)) * ((1 - p) / 2) = p := by
    have htwo : (2 : Q) ≠ 0 := by
      norm_num
    -- Умножаем обе части на общий знаменатель и сводим к полиному.
    have hzero :
        ((2 * p) / (1 - p)) * ((1 - p) / 2) - p = 0 := by
      field_simp [hdenom, htwo]
    exact sub_eq_zero.mp hzero
  have hmain_F : ((2 * p) / (1 - p))
        * (F (ρ.mask i)
            * ∏ j ∈ Finset.univ.erase i, F (ρ.mask j))
        = p * ∏ j ∈ Finset.univ.erase i, F (ρ.mask j) := by
    have hFi : F (ρ.mask i) = ((1 - p) / 2) := by
      simp [F, hmask]
    have hscaled := congrArg
      (fun x => x * ∏ j ∈ Finset.univ.erase i, F (ρ.mask j)) hcoeff
    calc
      ((2 * p) / (1 - p))
          * (F (ρ.mask i)
              * ∏ j ∈ Finset.univ.erase i, F (ρ.mask j))
          = ((2 * p) / (1 - p))
              * (((1 - p) / 2)
                  * ∏ j ∈ Finset.univ.erase i, F (ρ.mask j)) := by
                    simp [hFi]
      _ = (((2 * p) / (1 - p)) * ((1 - p) / 2))
              * ∏ j ∈ Finset.univ.erase i, F (ρ.mask j) := by
                    simp [mul_left_comm, mul_assoc]
      _ = p * ∏ j ∈ Finset.univ.erase i, F (ρ.mask j) := by
                    exact hscaled
  have hscaled_weight : ((2 * p) / (1 - p)) * Restriction.weight ρ p
      = p * ∏ j ∈ Finset.univ.erase i,
          F (ρ.mask j) := by
    have htmp := hmain_F
    simp [← hρ_weight, mul_left_comm, mul_assoc] at htmp
    exact htmp
  have hunassign_mask : (ρ.unassign i).mask i = none := by simp
  have hstep1 : F ((ρ.unassign i).mask i)
      * ∏ j ∈ Finset.univ.erase i, F ((ρ.unassign i).mask j)
        = p * ∏ j ∈ Finset.univ.erase i, F ((ρ.unassign i).mask j) := by
    simp [F, hunassign_mask]
  have hstep2 : ∏ j ∈ Finset.univ.erase i, F ((ρ.unassign i).mask j)
      = ∏ j ∈ Finset.univ.erase i, F (ρ.mask j) := htail
  calc
    Restriction.weight (ρ.unassign i) p
        = F ((ρ.unassign i).mask i)
            * ∏ j ∈ Finset.univ.erase i,
                F ((ρ.unassign i).mask j) := hunassign_weight
    _ = p * ∏ j ∈ Finset.univ.erase i,
            F ((ρ.unassign i).mask j) := hstep1
    _ = p * ∏ j ∈ Finset.univ.erase i,
            F (ρ.mask j) := by
          have htmp := congrArg (fun x => p * x) hstep2
          exact htmp
    _ = ((2 * p) / (1 - p)) * Restriction.weight ρ p :=
          hscaled_weight.symm

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
Сумма постоянной функции по списку: полезна для подсчёта длин `flatMap`.
-/
lemma sum_map_const_nat {α : Type _} (c : Nat) :
    ∀ L : List α, (L.map (fun _ => c)).sum = c * L.length
  | [] => by simp
  | _ :: L => by
      -- На шаге индукции приводим сумму к `c + c * |L|`.
      simp [sum_map_const_nat c L, Nat.mul_add, Nat.add_mul, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc]

/--
Число всех ограничений размера `n` равно `3^n`.

Эта оценка используется в комбинаторных подсчётах: на каждом шаге
к маске добавляется ровно три продолжения (`*`, `0`, `1`).
-/
lemma enumerate_length : ∀ n, (Restriction.enumerate n).length = 3 ^ n
  | 0 => by
      simp [Restriction.enumerate]
  | Nat.succ n => by
      have ih := enumerate_length n
      have hsum :
          ((Restriction.enumerate n).map (fun _ => 3)).sum
            = 3 * (Restriction.enumerate n).length := by
        simpa using
          (sum_map_const_nat (α := Restriction n) (c := 3)
            (L := Restriction.enumerate n))
      calc
        (Restriction.enumerate (Nat.succ n)).length
            = ((Restriction.enumerate n).map (fun _ => 3)).sum := by
                -- Каждая маска даёт ровно три продолжения.
                simp [Restriction.enumerate, List.length_flatMap]
        _ = 3 * (Restriction.enumerate n).length := hsum
        _ = 3 * 3 ^ n := by simpa [ih]
        _ = 3 ^ (Nat.succ n) := by
              simp [pow_succ, Nat.mul_comm]

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
              exact hfree
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
    classical
    have hmem : ℓ ∈ ℓ :: freeTail := List.mem_cons_self (a := ℓ) (l := freeTail)
    have := congrArg (fun l => ℓ ∈ l) hfree
    exact Eq.mpr this hmem
  exact ⟨ℓ, w.subset _ hℓmem, w.unassigned _ hℓmem⟩

lemma clauseStatus_pending_exists_literal {n : Nat} {ρ : Restriction n}
    {C : CnfClause n} {w : ClausePendingWitness ρ C} :
    ρ.clauseStatus C = ClauseStatus.pending w →
      ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.unassigned := by
  intro _; exact ClausePendingWitness.exists_unassigned w

lemma ClausePendingWitness.mask_idx_eq_none {n : Nat}
    {ρ : Restriction n} {C : CnfClause n}
    {w : ClausePendingWitness ρ C} {ℓ : Literal n}
    (hℓ : ℓ ∈ w.free) : ρ.mask ℓ.idx = none := by
  classical
  have hstatus := w.unassigned ℓ hℓ
  exact (literalStatus_eq_unassigned (ρ := ρ) (ℓ := ℓ)).1 hstatus

lemma ClausePendingWitness.literal_idx_mem_freeIndicesList {n : Nat}
    {ρ : Restriction n} {C : CnfClause n}
    {w : ClausePendingWitness ρ C} {ℓ : Literal n}
    (hℓ : ℓ ∈ w.free) : ℓ.idx ∈ ρ.freeIndicesList := by
  classical
  have hmask := ClausePendingWitness.mask_idx_eq_none
    (ρ := ρ) (C := C) (w := w) (ℓ := ℓ) hℓ
  exact (Restriction.mem_freeIndicesList (ρ := ρ) (i := ℓ.idx)).2 hmask

/--
`PendingClauseSelection` описывает первую «живую» (pending) клаузу в списке
`clauses`.  Мы сохраняем явное разбиение списка на префикс удовлетворённых
клауз, саму живую клаузу и оставшийся хвост, а также свидетеля её незавершённости.
-/
structure PendingClauseSelection {n : Nat}
    (ρ : Restriction n) (clauses : List (CnfClause n)) where
  /-- Список клауз до первой «живой» клаузы.  Все элементы здесь удовлетворены.
  -/
  leadingClauses : List (CnfClause n)
  /-- Первая клауза, статус которой — `pending`. -/
  clause : CnfClause n
  /-- Хвост после выбранной клаузы. -/
  suffix : List (CnfClause n)
  /-- Свидетель того, что выбранная клауза действительно «живая». -/
  witness : ClausePendingWitness ρ clause
  /-- Каждая клауза в префиксе удовлетворена текущим ограничением. -/
  leadingSatisfied : ∀ C ∈ leadingClauses, ρ.clauseStatus C = ClauseStatus.satisfied
  /-- Статус выбранной клаузы равен `pending` с указанным свидетелем. -/
  pendingStatusEq : ρ.clauseStatus clause = ClauseStatus.pending witness
  /-- Полное восстановление исходного списка клауз. -/
  clausesDecomposition : clauses = leadingClauses ++ clause :: suffix
  deriving Repr

/--
Поиск первой «живой» клаузы в списке.  Возвращает разбиение списка и свидетеля,
если такая клауза существует; иначе возвращает `none`.  Если встречается
фальсифицированная клауза, функция немедленно завершает поиск, поскольку формула
уже обращается в `false`.
-/
def firstPendingClause?
    {n : Nat} (ρ : Restriction n) :
    ∀ clauses : List (CnfClause n),
      Option (PendingClauseSelection (ρ := ρ) clauses)
  | [] => none
  | C :: rest =>
      match hstatus : ρ.clauseStatus C with
      | ClauseStatus.pending w =>
          some {
            leadingClauses := [],
            clause := C,
            suffix := rest,
            witness := w,
            leadingSatisfied := by
              intro C' hmem
              have : C' ∈ ([] : List (CnfClause n)) := hmem
              cases this
            pendingStatusEq := hstatus,
            clausesDecomposition := rfl }
      | ClauseStatus.satisfied =>
          match firstPendingClause? (ρ := ρ) rest with
          | none => none
          | some selection =>
              some {
                leadingClauses := C :: selection.leadingClauses,
                clause := selection.clause,
                suffix := selection.suffix,
                witness := selection.witness,
                leadingSatisfied := by
                  intro D hmem
                  obtain h | h := List.mem_cons.mp hmem
                  · subst h
                    exact hstatus
                  · exact selection.leadingSatisfied D h
                pendingStatusEq := selection.pendingStatusEq,
                clausesDecomposition := by
                  have hrest : rest =
                      selection.leadingClauses ++ selection.clause :: selection.suffix :=
                      selection.clausesDecomposition
                  have : C :: rest =
                      (C :: selection.leadingClauses) ++ selection.clause :: selection.suffix := by
                      simp [List.cons_append, hrest]
                  exact this }
      | ClauseStatus.falsified => none

end Restriction

namespace ClausePendingWitness

variable {n : Nat} {ρ : Restriction n} {C : CnfClause n}

/--
Выбор конкретного свободного литерала и значения, в которое он был поставлен
на рассматриваемой ветви канонического решающего дерева.  Индекс указывает на
позицию литерала в списке `w.free`, фиксируя тем самым «сохранённый» литерал,
а поле `value` — на значение переменной вдоль ветви.
-/
structure Selection (w : Restriction.ClausePendingWitness ρ C) where
  /-- Позиция выбранного литерала в списке `w.free`. -/
  index : Fin w.free.length
  /-- Значение переменной на ветви, используемой при кодировании. -/
  value : Bool
  deriving Repr

namespace Selection

variable {w : Restriction.ClausePendingWitness ρ C}

/-- Выбранный литерал из списка `w.free`. -/
@[simp] def literal (choice : Selection w) : Literal n :=
  w.free.get choice.index

lemma literal_mem_free (choice : Selection w) :
    choice.literal ∈ w.free := by
  classical
  dsimp [Selection.literal]
  exact List.get_mem (l := w.free) choice.index

lemma mask_idx_eq_none (choice : Selection w) :
    ρ.mask choice.literal.idx = none :=
  Restriction.ClausePendingWitness.mask_idx_eq_none
    (ρ := ρ) (C := C) (w := w) (ℓ := choice.literal)
    (literal_mem_free (choice := choice))

lemma literal_idx_mem_freeIndicesList (choice : Selection w) :
    choice.literal.idx ∈ ρ.freeIndicesList :=
  Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
    (ρ := ρ) (C := C) (w := w) (ℓ := choice.literal)
    (literal_mem_free (choice := choice))

/--
Результат успешного присваивания выбранного литерала.  Мы явно возвращаем как
новое ограничение, так и свидетельство того, что `Restriction.assign` вернул
`some`.
-/
noncomputable def assignResult (choice : Selection w) :
    {ρ' : Restriction n //
      ρ.assign choice.literal.idx choice.value = some ρ'} := by
  classical
  have hmem := literal_idx_mem_freeIndicesList (choice := choice)
  have hassign :=
    Restriction.assign_some_of_mem_freeIndicesList
      (ρ := ρ) (i := choice.literal.idx) (b := choice.value) hmem
  refine ⟨Classical.choose hassign, ?_⟩
  exact Classical.choose_spec hassign

/-- Новое ограничение после фиксации выбранного литерала. -/
noncomputable def nextRestriction (choice : Selection w) : Restriction n :=
  (assignResult (ρ := ρ) (C := C) (w := w) choice).1

@[simp] lemma assign_eq (choice : Selection w) :
    ρ.assign choice.literal.idx choice.value = some (nextRestriction choice) := by
  classical
  have hassign := (assignResult (ρ := ρ) (C := C) (w := w) choice).2
  dsimp [nextRestriction] at hassign
  exact hassign

/--
  В новой маске выбранная координата фиксирована значением `choice.value`.
-/
lemma mask_idx_eq_some (choice : Selection w) :
    (nextRestriction choice).mask choice.literal.idx = some choice.value := by
  classical
  have hassign := Selection.assign_eq
    (ρ := ρ) (C := C) (w := w) (choice := choice)
  have hmask := Restriction.assign_mask_eq (ρ := ρ)
    (ρ' := nextRestriction (ρ := ρ) (C := C) (w := w) choice)
    (i := choice.literal.idx) (b := choice.value) hassign
    choice.literal.idx
  have hgoal : (if choice.literal.idx = choice.literal.idx then some choice.value
      else ρ.mask choice.literal.idx) = some choice.value := by
    simp
  exact Eq.trans hmask hgoal

/--
  Остальные координаты маски не изменяются.
-/
lemma mask_idx_eq_of_ne (choice : Selection w) {j : Fin n}
    (hne : j ≠ choice.literal.idx) :
    (nextRestriction choice).mask j = ρ.mask j := by
  classical
  have hassign := Selection.assign_eq
    (ρ := ρ) (C := C) (w := w) (choice := choice)
  have hmask := Restriction.assign_mask_eq (ρ := ρ)
    (ρ' := nextRestriction (ρ := ρ) (C := C) (w := w) choice)
    (i := choice.literal.idx) (b := choice.value) hassign j
  have hgoal : (if j = choice.literal.idx then some choice.value
        else ρ.mask j) = ρ.mask j := if_neg hne
  exact Eq.trans hmask hgoal

/--
  Число свободных координат в новом ограничении уменьшается на единицу.
-/
lemma freeCount_nextRestriction (choice : Selection w) :
    (nextRestriction choice).freeCount = ρ.freeCount - 1 := by
  classical
  have hassign := Selection.assign_eq
    (ρ := ρ) (C := C) (w := w) (choice := choice)
  have hmem := literal_idx_mem_freeIndicesList (ρ := ρ) (C := C) (w := w)
    (choice := choice)
  have hcount := Restriction.freeCount_assign_of_mem (ρ := ρ)
    (ρ' := nextRestriction (ρ := ρ) (C := C) (w := w) choice)
    (i := choice.literal.idx) (b := choice.value) hmem hassign
  exact hcount

/--
  Операция `unassign` восстанавливает исходное ограничение: мы сразу
  возвращаем «звёздочку» на выбранной координате.
-/
lemma unassign_nextRestriction (choice : Selection w) :
    (nextRestriction choice).unassign choice.literal.idx = ρ := by
  classical
  have hassign := Selection.assign_eq
    (ρ := ρ) (C := C) (w := w) (choice := choice)
  have hfree := mask_idx_eq_none (ρ := ρ) (C := C) (w := w) (choice := choice)
  exact Restriction.unassign_assign_of_free (ρ := ρ)
    (ρ' := nextRestriction (ρ := ρ) (C := C) (w := w) choice)
    (i := choice.literal.idx) (b := choice.value) hassign hfree

/--
  После присваивания выбранная координата перестаёт быть свободной.
-/
lemma not_mem_freeIndicesList_nextRestriction (choice : Selection w) :
    choice.literal.idx ∉ (nextRestriction choice).freeIndicesList := by
  classical
  intro hmem
  have hmask_none :=
    (Restriction.mem_freeIndicesList
      (ρ := nextRestriction (ρ := ρ) (C := C) (w := w) choice)
      (i := choice.literal.idx)).1 hmem
  have hmask_some := mask_idx_eq_some (ρ := ρ) (C := C) (w := w) (choice := choice)
  have hcontr : some choice.value = (none : Option Bool) :=
    Eq.trans (Eq.symm hmask_some) hmask_none
  cases hcontr


end Selection

end ClausePendingWitness

/--
`SelectionTrace clauses ρ t` фиксирует последовательность из `t` шагов
канонического ветвления для списка клауз `clauses`, начиная с ограничения `ρ`.
Каждый шаг хранит выбранную «живую» клаузу, конкретный литерал внутри неё и
оставшийся хвост трассы, построенный уже для обновлённого ограничения.
-/
inductive SelectionTrace {n : Nat} (clauses : List (CnfClause n))
    : Restriction n → Nat → Type
  | nil {ρ : Restriction n} : SelectionTrace clauses ρ 0
  | cons {ρ : Restriction n}
      (selection : Restriction.PendingClauseSelection (ρ := ρ) clauses)
      (choice : ClausePendingWitness.Selection selection.witness)
      {t : Nat}
      (rest : SelectionTrace clauses
          (ClausePendingWitness.Selection.nextRestriction
            (ρ := ρ)
            (C := selection.clause)
            (w := selection.witness)
            (choice := choice)) t) :
      SelectionTrace clauses ρ (Nat.succ t)

namespace SelectionTrace

variable {n : Nat} {clauses : List (CnfClause n)}

/-- Множитель `\frac{2p}{1-p}`, возникающий при восстановлении звёзд. -/
@[simp] def branchFactor (p : Q) : Q := (2 * p) / (1 - p)

/--
Итоговое ограничение после применения всей трассы.  Для пустой трассы оно
совпадает с исходным `ρ`, а для непустой — с ограничением на последнем шаге.
-/
@[simp] noncomputable def finalRestriction {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) : Restriction n :=
  match trace with
  | SelectionTrace.nil => ρ
  | SelectionTrace.cons _ _ rest => finalRestriction rest

/--
Список зафиксированных пар (индекс, значение) вдоль трассы.  Порядок соответствует
порядку появления шагов.
-/
@[simp] noncomputable def assignedBitFixes {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) : List (BitFix n) :=
  match trace with
  | SelectionTrace.nil => []
  | SelectionTrace.cons _ choice rest =>
      (choice.literal.idx, choice.value) :: assignedBitFixes rest

/--
Список позиций выбранных литералов внутри соответствующих клауз.  Порядок
совпадает с порядком шагов трассы и будет использоваться в штрих-коде.
-/
@[simp] noncomputable def literalPositions {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) : List Nat :=
  match trace with
  | SelectionTrace.nil => []
  | SelectionTrace.cons _ choice rest =>
      choice.index.1 :: literalPositions rest

/--
Длина списка `assignedBitFixes` совпадает с числом шагов трассы.
-/
lemma assignedBitFixes_length {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) :
    (assignedBitFixes trace).length = t := by
  induction trace with
  | nil =>
      simp [assignedBitFixes]
  | @cons ρ selection choice t rest ih =>
      simp [assignedBitFixes, ih]

/--
Длина списка позиций также равна длине трассы.
-/
lemma literalPositions_length {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) :
    (literalPositions trace).length = t := by
  induction trace with
  | nil =>
      simp [literalPositions]
  | @cons ρ selection choice t rest ih =>
      simp [literalPositions, ih]

/--
Последовательное восстановление исходного ограничения: разбираем список фиксаций
с конца и вызываем `unassign` на каждой записанной координате.
-/
@[simp] def reconstructRestriction (ρ : Restriction n)
    : List (BitFix n) → Restriction n
  | [] => ρ
  | fix :: rest =>
      (reconstructRestriction ρ rest).unassign fix.1

/--
Применяя `reconstructRestriction` к итоговому ограничению и списку фиксаций,
возвращаемся к исходной маске `ρ`.
-/
lemma reconstruct_eq_original {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) :
    reconstructRestriction (finalRestriction trace)
        (assignedBitFixes trace) = ρ := by
  induction trace with
  | nil =>
      simp [assignedBitFixes, reconstructRestriction]
  | @cons ρ selection choice t rest ih =>
      have hnext := ih
      have hstep :
          reconstructRestriction
              (finalRestriction (SelectionTrace.cons selection choice rest))
              (assignedBitFixes (SelectionTrace.cons selection choice rest))
            =
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ)
                (C := selection.clause)
                (w := selection.witness)
                (choice := choice)).unassign choice.literal.idx := by
        simp [assignedBitFixes, reconstructRestriction, finalRestriction, hnext]
      have hundo :=
        ClausePendingWitness.Selection.unassign_nextRestriction
          (ρ := ρ)
          (C := selection.clause)
          (w := selection.witness)
          (choice := choice)
      exact Eq.trans hstep hundo

/--
Структура штрих-кода: финальное ограничение, пары (индекс, значение) и позиции
выбранных литералов.  Эти данные позволяют восстановить исходное ограничение и
служат для последующего подсчёта количества «плохих» ограничений.
-/
structure Barcode (n : Nat) where
  /-- Окончательное ограничение после применения всех шагов трассы. -/
  finalRestriction : Restriction n
  /-- Пары (индекс, значение) в порядке появления вдоль трассы. -/
  assignedFixes : List (BitFix n)
  /-- Номера выбранных литералов в соответствующих клаузах. -/
  literalPositions : List Nat
  deriving Repr

/--
Кодирование трассы: собираем итоговое ограничение, список фиксаций и позиции
литералов.  Эти данные образуют «штрих-код» ветви канонического разбора.
-/
@[simp] noncomputable def encode {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) : Barcode n :=
  { finalRestriction := finalRestriction trace
    , assignedFixes := assignedBitFixes trace
    , literalPositions := literalPositions trace }

/--
Декодирование штрих-кода: последовательное применение `unassign` восстанавливает
исходное ограничение.
-/
@[simp] noncomputable def decode {n : Nat} (code : Barcode n) : Restriction n :=
  reconstructRestriction (ρ := code.finalRestriction) code.assignedFixes

/--
Длина списка фиксаций в коде равна длине трассы, породившей этот код.
-/
lemma encode_assignedFixes_length {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) :
    (encode trace).assignedFixes.length = t := by
  change (assignedBitFixes trace).length = t
  exact assignedBitFixes_length (trace := trace)

/--
Длина списка позиций в коде совпадает с длиной исходной трассы.
-/
lemma encode_literalPositions_length {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) :
    (encode trace).literalPositions.length = t := by
  change (literalPositions trace).length = t
  exact literalPositions_length (trace := trace)

/--
Декодирование штрих-кода, полученного из трассы, возвращает исходное ограничение.
-/
lemma decode_encode {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) :
    decode (encode trace) = ρ := by
  change
    reconstructRestriction (finalRestriction trace)
      (assignedBitFixes trace) = ρ
  exact reconstruct_eq_original (trace := trace)

/--
  Вес исходного ограничения выражается через вес финальной маски и фактор
  `(branchFactor p)^t`, где `t` — длина трассы.
-/
lemma weight_eq_branchFactor_pow {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) (p : Q) (hp : p ≠ 1) :
    Restriction.weight (ρ := ρ) (p := p) = (branchFactor p) ^ t
      * Restriction.weight (ρ := finalRestriction trace) (p := p) := by
  classical
  induction trace with
  | nil =>
      simp [branchFactor]
  | @cons ρ selection choice t rest ih =>
      -- Обозначим промежуточное ограничение после текущего шага.
      let σ := ClausePendingWitness.Selection.nextRestriction
        (ρ := ρ)
        (C := selection.clause)
        (w := selection.witness)
        (choice := choice)
      have hmask_raw :=
        ClausePendingWitness.Selection.mask_idx_eq_some
          (ρ := ρ)
          (C := selection.clause)
          (w := selection.witness)
          (choice := choice)
      -- Сопоставляем веса `ρ` и `σ`.
      have hunassign :=
        ClausePendingWitness.Selection.unassign_nextRestriction
          (ρ := ρ)
          (C := selection.clause)
          (w := selection.witness)
          (choice := choice)
      have hmaskσ : σ.mask choice.literal.idx = some choice.value := by
        have htmp := hmask_raw
        simp [σ] at htmp
        exact htmp
      have hmul_raw :
          Restriction.weight
              (ρ := σ.unassign choice.literal.idx) (p := p)
            = ((2 * p) / (1 - p))
              * Restriction.weight (ρ := σ) (p := p) :=
        Restriction.weight_unassign_mul
          (ρ := σ)
          (i := choice.literal.idx)
          (p := p)
          (b := choice.value)
          (hmask := hmaskσ)
          (hp := hp)
      have hratio_raw : Restriction.weight (ρ := ρ) (p := p)
          = ((2 * p) / (1 - p)) * Restriction.weight (ρ := σ) (p := p) := by
        have hcongr := congrArg
          (fun τ => Restriction.weight (ρ := τ) (p := p)) hunassign
        exact Eq.trans (Eq.symm hcongr) hmul_raw
      have hratio : Restriction.weight (ρ := ρ) (p := p)
          = branchFactor p * Restriction.weight (ρ := σ) (p := p) := by
        have hrewrite :
            ((2 * p) / (1 - p)) * Restriction.weight (ρ := σ) (p := p)
              = branchFactor p * Restriction.weight (ρ := σ) (p := p) := by
          change ((2 * p) / (1 - p)) * Restriction.weight (ρ := σ) (p := p)
              = ((2 * p) / (1 - p)) * Restriction.weight (ρ := σ) (p := p)
          simp [branchFactor]
        exact hratio_raw.trans hrewrite
      -- Индуктивное выражение для веса `σ`.
      have hrec_raw := ih
      have hrec : Restriction.weight (ρ := σ) (p := p)
          = (branchFactor p) ^ t
            * Restriction.weight (ρ := finalRestriction rest) (p := p) := by
        have htmp := hrec_raw
        simp [σ] at htmp
        exact htmp
      -- Преобразуем результирующую формулу.
      have hfinal :
          finalRestriction (SelectionTrace.cons selection choice rest)
            = finalRestriction rest := rfl
      have hweight_swap := congrArg
        (fun τ => Restriction.weight (ρ := τ) (p := p)) hfinal.symm
      have hpow := (pow_succ (branchFactor p) t).symm
      calc
        Restriction.weight (ρ := ρ) (p := p)
            = branchFactor p * Restriction.weight (ρ := σ) (p := p) := hratio
        _ = branchFactor p *
              ((branchFactor p) ^ t
                * Restriction.weight (ρ := finalRestriction rest) (p := p)) := by
              -- заменяем вес `σ` по индуктивному предположению
              rw [hrec]
        _ = (branchFactor p) ^ (Nat.succ t)
              * Restriction.weight
                  (ρ := finalRestriction
                    (SelectionTrace.cons selection choice rest))
                  (p := p) := by
              -- аккуратно сворачиваем множители
              calc
                branchFactor p *
                    ((branchFactor p) ^ t
                      * Restriction.weight (ρ := finalRestriction rest) (p := p))
                    = (branchFactor p * (branchFactor p) ^ t)
                        * Restriction.weight (ρ := finalRestriction rest) (p := p) :=
                      (mul_assoc (branchFactor p) ((branchFactor p) ^ t)
                        (Restriction.weight (ρ := finalRestriction rest) (p := p))).symm
                _ = ((branchFactor p) ^ t * branchFactor p)
                        * Restriction.weight (ρ := finalRestriction rest) (p := p) := by
                      refine congrArg
                        (fun x =>
                          x * Restriction.weight (ρ := finalRestriction rest) (p := p))
                        ?_
                      exact mul_comm (branchFactor p) ((branchFactor p) ^ t)
                _ = (branchFactor p) ^ (Nat.succ t)
                        * Restriction.weight (ρ := finalRestriction rest) (p := p) := by
                      refine congrArg
                        (fun x =>
                          x * Restriction.weight (ρ := finalRestriction rest) (p := p))
                        hpow
                _ = (branchFactor p) ^ (Nat.succ t)
                        * Restriction.weight
                            (ρ := finalRestriction
                              (SelectionTrace.cons selection choice rest))
                            (p := p) := by
                      refine congrArg
                        (fun w => (branchFactor p) ^ (Nat.succ t) * w)
                        hweight_swap

/--
  Переписываем формулу выше непосредственно для закодированного ограничения.
-/
lemma decode_encode_weight {ρ : Restriction n} {t : Nat}
    (trace : SelectionTrace clauses ρ t) (p : Q) (hp : p ≠ 1) :
    Restriction.weight (ρ := decode (encode trace)) (p := p)
      = (branchFactor p) ^ t
      * Restriction.weight (ρ := finalRestriction trace) (p := p) := by
  have hdecode := decode_encode (trace := trace)
  have hrewrite := congrArg
    (fun τ => Restriction.weight (ρ := τ) (p := p)) hdecode
  have hbase := weight_eq_branchFactor_pow
    (trace := trace) (p := p) (hp := hp)
  exact Eq.trans hrewrite hbase

end SelectionTrace

namespace CNF

/--
Путь канонического разветвления для КНФ.  Конструкция хранит последовательность
шагов, на каждом из которых выбирается первая «живая» клауза и конкретный
свободный литерал внутри неё.  Хвостовой путь строится относительно полученного
после присваивания ограничения.
-/
inductive CanonicalTrace {n w : Nat} (F : CNF n w) :
    Restriction n → Nat → Type
  | nil {ρ : Restriction n} : CanonicalTrace (F := F) ρ 0
  | cons {ρ : Restriction n} {t : Nat}
      (selection : Restriction.PendingClauseSelection
        (ρ := ρ) F.clauses)
      (choice : ClausePendingWitness.Selection selection.witness)
      (tail : CanonicalTrace (F := F)
        (ClausePendingWitness.Selection.nextRestriction
          (ρ := ρ) (C := selection.clause) (w := selection.witness) choice)
        t) :
      CanonicalTrace (F := F) ρ (Nat.succ t)

namespace CanonicalTrace

variable {n w : Nat} {F : CNF n w}

/--
Преобразование канонической трассы в универсальную `SelectionTrace`.  Мы просто
забываем о принадлежности к конкретной формуле и используем ранее определённую
структуру, parametrized только списком клауз. -/
@[simp] noncomputable def toSelectionTrace {ρ : Restriction n} {t : Nat}
    (trace : CanonicalTrace (F := F) ρ t) :
    SelectionTrace F.clauses ρ t :=
  match trace with
  | CanonicalTrace.nil => SelectionTrace.nil
  | CanonicalTrace.cons selection choice tail =>
      SelectionTrace.cons selection choice
        (toSelectionTrace (trace := tail))

/--
Полученный штрих-код: используем универсальное кодирование `SelectionTrace`
для трассы, ассоциированной с текущей канонической ветвью. -/
@[simp] noncomputable def barcode {ρ : Restriction n} {t : Nat}
    (trace : CanonicalTrace (F := F) ρ t) : SelectionTrace.Barcode n :=
  SelectionTrace.encode (clauses := F.clauses)
    (trace := toSelectionTrace (trace := trace))

/-- Длина списка присваиваний в штрих-коде равна длине исходной трассы. -/
lemma barcode_assignedFixes_length {ρ : Restriction n} {t : Nat}
    (trace : CanonicalTrace (F := F) ρ t) :
    (barcode (trace := trace)).assignedFixes.length = t := by
  simpa using
    (SelectionTrace.encode_assignedFixes_length
      (clauses := F.clauses)
      (trace := toSelectionTrace (trace := trace)))

/-- Аналогично для списка позиций литералов. -/
lemma barcode_literalPositions_length {ρ : Restriction n} {t : Nat}
    (trace : CanonicalTrace (F := F) ρ t) :
    (barcode (trace := trace)).literalPositions.length = t := by
  simpa using
    (SelectionTrace.encode_literalPositions_length
      (clauses := F.clauses)
      (trace := toSelectionTrace (trace := trace)))

/-- Декодирование штрих-кода возвращает исходное ограничение. -/
lemma decode_barcode {ρ : Restriction n} {t : Nat}
    (trace : CanonicalTrace (F := F) ρ t) :
    SelectionTrace.decode (barcode (trace := trace)) = ρ := by
  simpa using
    (SelectionTrace.decode_encode
      (clauses := F.clauses)
      (trace := toSelectionTrace (trace := trace)))

/-- Итоговое ограничение после применения всех шагов пути. -/

noncomputable def finalRestriction :
    {ρ : Restriction n} → {t : Nat} →
      CanonicalTrace (F := F) ρ t → Restriction n
  | ρ, _, CanonicalTrace.nil => ρ
  | _, _, CanonicalTrace.cons _ _ tail => finalRestriction tail

/--
Список индексов переменных, которые фиксируются вдоль пути, в том порядке, в
котором происходят присваивания.
-/
noncomputable def indicesList :
    {ρ : Restriction n} → {t : Nat} →
      CanonicalTrace (F := F) ρ t → List (Fin n)
  | _, _, CanonicalTrace.nil => []
  | _, _, CanonicalTrace.cons _ choice tail =>
      choice.literal.idx :: indicesList tail

/--
Список значений, в которые устанавливаются выбранные переменные.  Порядок
совпадает с порядком `indicesList`.
-/
noncomputable def valuesList :
    {ρ : Restriction n} → {t : Nat} →
      CanonicalTrace (F := F) ρ t → List Bool
  | _, _, CanonicalTrace.nil => []
  | _, _, CanonicalTrace.cons _ choice tail =>
      choice.value :: valuesList tail

/--
Список внутренних позиций выбранных литералов внутри соответствующих клауз.
Эти значения пригодятся для дальнейшего кодирования сведений о ветви.
-/
noncomputable def positionList :
    {ρ : Restriction n} → {t : Nat} →
      CanonicalTrace (F := F) ρ t → List Nat
  | _, _, CanonicalTrace.nil => []
  | _, _, CanonicalTrace.cons _ choice tail =>
      choice.index.1 :: positionList tail

@[simp] lemma indicesList_length :
    ∀ {ρ : Restriction n} {t : Nat}
      (trace : CanonicalTrace (F := F) ρ t),
        (indicesList trace).length = t
  | _, _, CanonicalTrace.nil => by
      simp [indicesList]
  | ρ, Nat.succ t, CanonicalTrace.cons selection choice tail => by
      have htail := indicesList_length (trace := tail)
      calc
        (indicesList (CanonicalTrace.cons selection choice tail)).length
            = (choice.literal.idx :: indicesList tail).length := rfl
        _ = Nat.succ (indicesList tail).length := by
            simp
        _ = Nat.succ t := by
            exact congrArg Nat.succ htail

@[simp] lemma valuesList_length :
    ∀ {ρ : Restriction n} {t : Nat}
      (trace : CanonicalTrace (F := F) ρ t),
        (valuesList trace).length = t
  | _, _, CanonicalTrace.nil => by
      simp [valuesList]
  | ρ, Nat.succ t, CanonicalTrace.cons selection choice tail => by
      have htail := valuesList_length (trace := tail)
      calc
        (valuesList (CanonicalTrace.cons selection choice tail)).length
            = (choice.value :: valuesList tail).length := rfl
        _ = Nat.succ (valuesList tail).length := by
            simp
        _ = Nat.succ t := by
            exact congrArg Nat.succ htail

@[simp] lemma positionList_length :
    ∀ {ρ : Restriction n} {t : Nat}
      (trace : CanonicalTrace (F := F) ρ t),
        (positionList trace).length = t
  | _, _, CanonicalTrace.nil => by
      simp [positionList]
  | ρ, Nat.succ t, CanonicalTrace.cons selection choice tail => by
      have htail := positionList_length (trace := tail)
      calc
        (positionList (CanonicalTrace.cons selection choice tail)).length
            = (choice.index.1 :: positionList tail).length := rfl
        _ = Nat.succ (positionList tail).length := by
            simp
        _ = Nat.succ t := by
            exact congrArg Nat.succ htail

lemma foldr_unassign_eq_start :
    ∀ {ρ : Restriction n} {t : Nat}
      (trace : CanonicalTrace (F := F) ρ t),
        (indicesList trace).foldr
          (fun idx acc => acc.unassign idx)
          (finalRestriction trace)
          = ρ
  | ρ, _, CanonicalTrace.nil => by
      simp [indicesList, finalRestriction]
  | ρ, Nat.succ t, CanonicalTrace.cons selection choice tail => by
      have htail :=
        foldr_unassign_eq_start (trace := tail)
      have hcalc :
          (indicesList (CanonicalTrace.cons selection choice tail)).foldr
              (fun idx acc => acc.unassign idx)
              (finalRestriction (CanonicalTrace.cons selection choice tail))
            = ((indicesList tail).foldr
                  (fun idx acc => acc.unassign idx)
                  (finalRestriction tail)).unassign choice.literal.idx := by
          simp [indicesList, finalRestriction]
      have hrewrite :=
        congrArg (fun σ => σ.unassign choice.literal.idx) htail
      have hunassign :=
        ClausePendingWitness.Selection.unassign_nextRestriction
          (ρ := ρ) (C := selection.clause) (w := selection.witness)
          (choice := choice)
      calc
        (indicesList (CanonicalTrace.cons selection choice tail)).foldr
            (fun idx acc => acc.unassign idx)
            (finalRestriction (CanonicalTrace.cons selection choice tail))
          = ((indicesList tail).foldr
                (fun idx acc => acc.unassign idx)
                (finalRestriction tail)).unassign choice.literal.idx := hcalc
        _ = ((ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := selection.witness) choice).unassign
                choice.literal.idx) := hrewrite
        _ = ρ := hunassign

end CanonicalTrace

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
