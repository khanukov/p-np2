/-
  pnp3/Core/Atlas.lean

  Атлас = общий словарь подкубов + допустимая ошибка ε.
  Предикат WorksFor: для каждого f из семейства есть поднабор словаря, аппроксимирующий f с ошибкой ≤ ε.
-/
import Std.Data.List.Basic
import PnP3.Core.BooleanBasics
import PnP3.Core.PDT

namespace PnP3.Core

open PnP3.Core

structure Atlas (n : Nat) where
  dict    : List (Subcube n)
  epsilon : Q
deriving Repr

/-- Подмножество (как предикат) списка: каждый элемент xs присутствует в ys. -/
def listSubset {α} [DecidableEq α] (xs ys : List α) : Prop :=
  ∀ a, xs.contains a = true → ys.contains a = true

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

end PnP3.Core
