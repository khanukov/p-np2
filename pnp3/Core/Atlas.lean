/-
  pnp3/Core/Atlas.lean

  Атлас = общий словарь подкубов + допустимая ошибка ε.
  Предикат WorksFor: для каждого f из семейства есть поднабор словаря, аппроксимирующий f с ошибкой ≤ ε.
-/
import Mathlib.Data.List.Basic
import Core.BooleanBasics
import Core.PDT

namespace Pnp3
namespace Core

structure Atlas (n : Nat) where
  dict    : List (Subcube n)
  epsilon : Q
deriving Repr

/-- Подмножество (как предикат) списка: каждый элемент xs присутствует в ys. -/
def listSubset {α} [DecidableEq α] (xs ys : List α) : Prop :=
  ∀ a, xs.contains a = true → ys.contains a = true

/-- Преобразуем членство в списке в равносильное утверждение про `contains`. -/
lemma contains_of_mem {α} [DecidableEq α] {xs : List α} {a : α}
    (ha : a ∈ xs) : xs.contains a = true := by
  classical
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
      by_cases hba : a = b
      · subst hba; simp
      · have hmem : a ∈ xs := by
          simpa [List.mem_cons, hba] using ha
        have hcontains : xs.contains a = true := ih hmem
        simpa [List.contains_cons, hba, hcontains]

/-- Обратное направление: `contains = true` означает обычное членство. -/
lemma mem_of_contains {α} [DecidableEq α] {xs : List α} {a : α}
    (ha : xs.contains a = true) : a ∈ xs := by
  classical
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
      by_cases hba : a = b
      · subst hba; simpa using List.mem_cons_self b xs
      · have htail : xs.contains a = true := by
          simpa [List.contains_cons, hba] using ha
        have hmem := ih htail
        simpa [List.mem_cons, hba] using hmem

/-- Пустой список содержится в любом другом. -/
lemma listSubset_nil {α} [DecidableEq α] (ys : List α) :
    listSubset ([] : List α) ys := by
  intro a ha
  simp at ha

/-- Рефлексивность: любой список является подсписком самого себя. -/
lemma listSubset_refl {α} [DecidableEq α] (xs : List α) :
    listSubset xs xs := by
  intro a ha; simpa using ha

/-- Транзитивность отношения `listSubset`. -/
lemma listSubset_trans {α} [DecidableEq α]
    {xs ys zs : List α} (hxy : listSubset xs ys) (hyz : listSubset ys zs) :
    listSubset xs zs := by
  intro a ha
  exact hyz _ (hxy _ ha)

/-- Из соотношения `listSubset xs ys` следует включение по обычному членству. -/
lemma listSubset.mem {α} [DecidableEq α]
    {xs ys : List α} (h : listSubset xs ys) {a : α} (ha : a ∈ xs) :
    a ∈ ys := by
  classical
  have hcontains : xs.contains a = true := contains_of_mem (xs := xs) ha
  have hcontains' := h a hcontains
  exact mem_of_contains (xs := ys) hcontains'


/-- Добавление элемента, уже содержащегося в `ys`, сохраняет отношение `listSubset`. -/
lemma listSubset_cons_of_mem {α} [DecidableEq α]
    {xs ys : List α} {a : α}
    (ha : ys.contains a = true) (h : listSubset xs ys) :
    listSubset (a :: xs) ys := by
  intro b hb
  classical
  by_cases hba : b = a
  · subst hba; simpa using ha
  · have hb' : xs.contains b = true := by
      simpa [List.contains_cons, hba] using hb
    exact h _ hb'

/-- Атлас "работает" для семейства F:
    для каждого f ∈ F существует подсписок R_f ⊆ dict, такой что errU f R_f ≤ ε. -/
def WorksFor {n : Nat}
    (A : Atlas n) (F : List (BitVec n → Bool)) : Prop :=
  ∀ f, f ∈ F →
    ∃ (Rf : List (Subcube n)),
      listSubset Rf A.dict ∧
      errU f Rf ≤ A.epsilon

/-- Атлас, построенный из PDT: словарь = листья PDT. -/
def Atlas.ofPDT {n : Nat} (t : PDT n) (ε : Q) : Atlas n :=
  { dict := PDT.leaves t, epsilon := ε }

end Core
end Pnp3
