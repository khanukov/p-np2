/-
  pnp3/Core/SubcubeExtras.lean

  Дополнительные леммы для работы с подкубами (Subcube).
  Расширяют функциональность из BooleanBasics.lean.
-/
import Core.BooleanBasics

namespace Pnp3
namespace Core

/-! ## Дополнительные свойства Subcube.assign -/

/-- Присваивание сохраняет значение, если оно уже установлено -/
lemma Subcube.assign_idempotent {n : Nat} (β : Subcube n) (i : Fin n) (b : Bool)
    (h : β i = some b) :
    Subcube.assign β i b = some β := by
  unfold Subcube.assign
  simp [h]

/-! ## Свойства assignMany -/

/-- assignMany для пустого списка - identity -/
@[simp]
lemma Subcube.assignMany_nil_eq {n : Nat} (β : Subcube n) :
    Subcube.assignMany β [] = some β := rfl

/-- assignMany ассоциативна -/
lemma Subcube.assignMany_append {n : Nat} (β : Subcube n) (l1 l2 : List (BitFix n)) :
    Subcube.assignMany β (l1 ++ l2) =
    (Subcube.assignMany β l1).bind (fun β' => Subcube.assignMany β' l2) := by
  induction l1 generalizing β with
  | nil => simp [Subcube.assignMany]
  | cons head tail ih =>
    simp [Subcube.assignMany]
    cases hassign : Subcube.assign β head.1 head.2 with
    | none => simp
    | some β' =>
      simp
      exact ih β'

/-! ## Подсчет зафиксированных битов -/

/-- Количество зафиксированных битов в подкубе -/
def Subcube.fixedCount {n : Nat} (β : Subcube n) : Nat :=
  (List.finRange n).countP (fun i => (β i).isSome)

/-- Количество свободных битов -/
def Subcube.freeCount {n : Nat} (β : Subcube n) : Nat :=
  n - Subcube.fixedCount β

/-- Общее количество битов = зафиксированные + свободные -/
lemma Subcube.fixedCount_add_freeCount {n : Nat} (β : Subcube n) :
    Subcube.fixedCount β + Subcube.freeCount β = n := by
  unfold Subcube.freeCount
  have h : Subcube.fixedCount β ≤ n := by
    unfold Subcube.fixedCount
    have : List.countP (fun i => (β i).isSome) (List.finRange n) ≤ (List.finRange n).length :=
      List.countP_le_length
    simp at this
    exact this
  omega

/-- Пустой подкуб (все биты свободны) имеет 0 зафиксированных битов -/
lemma Subcube.fixedCount_empty {n : Nat} :
    Subcube.fixedCount (fun (_ : Fin n) => none) = 0 := by
  unfold Subcube.fixedCount
  have h : ∀ i ∈ List.finRange n, ¬((none : Option Bool).isSome = true) := by
    intro i _
    simp
  rw [List.countP_eq_zero]
  exact h

/-- Полностью зафиксированный подкуб имеет n зафиксированных битов -/
lemma Subcube.fixedCount_full {n : Nat} (x : BitVec n) :
    Subcube.fixedCount (fun i => some (x i)) = n := by
  unfold Subcube.fixedCount
  have h : ∀ i ∈ List.finRange n, ((fun i => some (x i)) i).isSome = true := by
    intro i _
    simp
  simp [h]

/-! ## Совместимость подкубов -/

/-- Два подкуба совместимы, если не противоречат друг другу -/
def Subcube.compatible {n : Nat} (β₁ β₂ : Subcube n) : Prop :=
  ∀ i, match β₁ i, β₂ i with
       | some b₁, some b₂ => b₁ = b₂
       | _, _ => True

/-- Совместимость рефлексивна -/
lemma Subcube.compatible_refl {n : Nat} (β : Subcube n) :
    Subcube.compatible β β := by
  intro i
  cases hβ : β i <;> simp

/-- Совместимость симметрична -/
lemma Subcube.compatible_symm {n : Nat} {β₁ β₂ : Subcube n}
    (h : Subcube.compatible β₁ β₂) :
    Subcube.compatible β₂ β₁ := by
  intro i
  have hi := h i
  cases hβ1 : β₁ i <;> cases hβ2 : β₂ i
  · trivial
  · trivial
  · trivial
  · rw [hβ1, hβ2] at hi
    exact hi.symm

/- Совместимость транзитивна (только когда средний подкуб не создает "пробелов")

   Примечание: Полная транзитивность требует более сильного определения compatible.
   Текущее определение не транзитивно в случае (some, none, some).
   Для практического применения рассмотрим усиление определения или
   добавление дополнительных условий.

lemma Subcube.compatible_trans {n : Nat} {β₁ β₂ β₃ : Subcube n}
    (h12 : Subcube.compatible β₁ β₂)
    (h23 : Subcube.compatible β₂ β₃) :
    Subcube.compatible β₁ β₃ := by
  sorry  -- Unprovable: case (some val₁, none, some val₃) cannot prove val₁ = val₃
-/

end Core
end Pnp3
