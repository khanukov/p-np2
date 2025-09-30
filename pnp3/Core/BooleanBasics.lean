/-
  pnp3/Core/BooleanBasics.lean

  Базовые определения для SAL:
  - BitVec n  := Fin n → Bool
  - Subcube n := Fin n → Option Bool   (some b = фиксированный бит, none = свободно)
  - memB      : булева принадлежность x подкубу β
  - coveredB  : индикатор "x покрыт объединением подкубов"
  - errU      : ошибка аппроксимации по равномерному распределению (через полный перебор)
-/
import Std.Data.List.Basic
import Std.Tactic

namespace PnP3.Core

abbrev Q := Rat
abbrev BitVec (n : Nat) := Fin n → Bool
abbrev Subcube (n : Nat) := Fin n → Option Bool

/-- Bool → Nat (true ↦ 1, false ↦ 0). -/
@[inline] def b2n (b : Bool) : Nat := if b then 1 else 0

@[simp] lemma b2n_true : b2n true = 1 := by simp [b2n]

@[simp] lemma b2n_false : b2n false = 0 := by simp [b2n]

/-- "xor" для Bool (без зависимостей). -/
@[inline] def boolXor (a b : Bool) : Bool := if a = b then false else true

@[simp] lemma boolXor_self (a : Bool) : boolXor a a = false := by
  simp [boolXor]

@[simp] lemma boolXor_false_right (a : Bool) : boolXor a false = a := by
  by_cases h : a = false
  · simpa [boolXor, h]
  · have : a = true := by cases a <;> simp_all
    simpa [boolXor, this]

@[simp] lemma boolXor_false_left (a : Bool) : boolXor false a = a := by
  by_cases h : a = false
  · simpa [boolXor, h]
  · have : a = true := by cases a <;> simp_all
    simpa [boolXor, this]

/-- Булева принадлежность точки x подкубу β. -/
def memB {n : Nat} (β : Subcube n) (x : BitVec n) : Bool :=
  (List.range n).all (fun i =>
    match β ⟨i, by decide⟩ with
    | none    => true
    | some b  => if x ⟨i, by decide⟩ = b then true else false)

/-- Индикатор покрытия x объединением подкубов из списка Rset. -/
def coveredB {n : Nat} (Rset : List (Subcube n)) (x : BitVec n) : Bool :=
  Rset.any (fun β => memB β x)

@[simp] lemma coveredB_nil {n : Nat} (x : BitVec n) :
    coveredB ([] : List (Subcube n)) x = false := by
  simp [coveredB]

/-- Построить BitVec длины n из числа k (по двоичным битам). -/
def vecOfNat (n : Nat) (k : Nat) : BitVec n :=
  fun i => Nat.testBit k i.val

/-- Полный список всех BitVec длины n. -/
def allBitVec (n : Nat) : List (BitVec n) :=
  (List.range (Nat.pow 2 n)).map (vecOfNat n)

/-- Ошибка аппроксимации: доля входов, где f(x) ≠ coveredB Rset x. -/
def errU {n : Nat} (f : BitVec n → Bool) (Rset : List (Subcube n)) : Q :=
  let xs := allBitVec n
  let mismatches : Nat :=
    xs.foldl (fun acc x => acc + b2n (boolXor (f x) (coveredB Rset x))) 0
  ((mismatches : Int) : Q) / ((Nat.pow 2 n : Int) : Q)

/--
`foldl` с добавлением функции, всюду равной нулю, возвращает исходный аккумулятор.
Этот технический лемматик используется при подсчёте ошибок: если на каждом
входе `f` совпадает с аппроксимацией, то суммарное число несовпадений нулевое.
-/
private lemma foldl_add_eq_self {α : Type _} (g : α → Nat)
    (hg : ∀ x, g x = 0) :
    ∀ (xs : List α) (a : Nat),
      xs.foldl (fun acc x => acc + g x) a = a := by
  intro xs
  induction xs with
  | nil => intro a; simp
  | cons x xs ih =>
      intro a
      have hx : g x = 0 := hg x
      have := ih (a + g x)
      simpa [List.foldl, hx] using this

/-- Если функция `f` совпадает с покрытием `coveredB`, то ошибка аппроксимации
равна нулю. -/
lemma errU_eq_zero_of_agree {n : Nat}
    (f : BitVec n → Bool) (Rset : List (Subcube n))
    (h : ∀ x, f x = coveredB Rset x) :
    errU f Rset = 0 := by
  unfold errU
  set xs := allBitVec n
  set mismatches :=
    xs.foldl (fun acc x => acc + b2n (boolXor (f x) (coveredB Rset x))) 0
  have hg : ∀ x, b2n (boolXor (f x) (coveredB Rset x)) = 0 := by
    intro x
    have hx : f x = coveredB Rset x := h x
    have hxor : boolXor (f x) (coveredB Rset x) = false := by
      simp [boolXor, hx]
    simpa [hxor]
  have hfold := foldl_add_eq_self
    (fun x => b2n (boolXor (f x) (coveredB Rset x))) hg xs 0
  have hmismatch : mismatches = 0 := by simpa [mismatches] using hfold
  simp [mismatches, hmismatch]

/-- Частный случай: пустой набор подкубов идеально аппроксимирует константный
нуль. -/
@[simp] lemma errU_false_nil {n : Nat} :
    errU (fun (_ : BitVec n) => false) ([] : List (Subcube n)) = 0 := by
  apply errU_eq_zero_of_agree
  intro x
  simp

/-- Вспомогательный факт: размер подкуба с k фиксированными битами равен 2^(n-k).
    (Используется далее для вероятностных оценок; доказательство можно добавить позже.) -/
axiom subcube_card_pow {n : Nat} (β : Subcube n) :
  True  -- placeholder; при необходимости позже заменим на реальное утверждение

end PnP3.Core
