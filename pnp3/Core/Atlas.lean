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
