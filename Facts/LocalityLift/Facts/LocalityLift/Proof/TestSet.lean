import Mathlib.Data.Finset.Card
import Facts.LocalityLift.Interface.Parameters
import Facts.LocalityLift.Proof.Arithmetic

/-!
# Канонический тест-набор для конструктивного свидетеля

Пока доказательство locality lift не построено полностью, удобно иметь
стандартный маленький тест-набор, удовлетворяющий требуемым численным
ограничениям.  Его можно использовать как временную заглушку и в качестве
базовой проверки арифметики.  Ниже мы фиксируем такой набор: однотонный
вектор из нулей (его достаточно для демонстрации `|T| ≤ polylogBudget`).
-/

namespace Facts
namespace LocalityLift

open Finset

/-- Нулевой битовый вектор длины `n`. -/
def zeroVector (n : Nat) : BitVec n := fun _ => false

@[simp] lemma zeroVector_apply {n : Nat} (i : Fin n) : zeroVector n i = false := rfl

/-- Стандартный тест-набор: одна точка `0…0`.  Его мощность равна `1`, что
    немедленно удовлетворяет полилогарифмической границе. -/
def defaultTestSet (p : GapMCSPParams) : Finset (BitVec (inputLen p)) :=
  {zeroVector (inputLen p)}

@[simp] lemma mem_defaultTestSet {p : GapMCSPParams}
    (x : BitVec (inputLen p)) : x ∈ defaultTestSet p ↔ x = zeroVector (inputLen p) := by
  classical
  constructor
  · intro hx
    have : x ∈ ({zeroVector (inputLen p)} : Finset (BitVec (inputLen p))) := hx
    simpa [defaultTestSet] using this
  · intro hx
    subst hx
    simp [defaultTestSet]

@[simp] lemma card_defaultTestSet (p : GapMCSPParams) :
    (defaultTestSet p).card = 1 := by
  classical
  simp [defaultTestSet]

/-- Мощность стандартного тест-набора не превышает полилогарифмический бюджет. -/
lemma card_defaultTestSet_le_polylog (p : GapMCSPParams) :
    (defaultTestSet p).card ≤ polylogBudget (inputLen p) := by
  classical
  simpa [card_defaultTestSet] using one_le_polylogBudget (inputLen p)

end LocalityLift
end Facts
