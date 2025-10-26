import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Facts.LocalityLift.Interface.Parameters

/-!
# Числовые вспомогательные факты для оценки параметров локализации

В этом модуле собираем базовые леммы про `polylogBudget`.  Они потребуются при
конструктивном построении тест-набора и локального решателя.  Сейчас нам нужны
минимальные утверждения: положительность бюджета и удобная форма неравенств.
-/

namespace Facts
namespace LocalityLift

/--
  Базовая оценка: `log₂ (N + 1) + 1 ≥ 1` для любого натурального `N`.
  Используем тот факт, что `log₂` возвращает натуральное число и потому не
  может быть отрицательным.
-/
lemma log2_succ_le_base (N : Nat) : 1 ≤ Nat.log2 (N + 1) + 1 := by
  exact Nat.succ_le_succ (Nat.zero_le _)

/--
  Полилогарифмический бюджет не меньше единицы.  Это позволит выбирать
  непустой тест-набор и ограничивать локальность числом `1` без нарушения
  неравенств.
-/
private lemma pow_ge_one (a k : Nat) (ha : 1 ≤ a) : 1 ≤ a ^ k := by
  induction k with
  | zero => simpa [Nat.pow_zero]
  | succ k ih =>
      have hmul : 1 ≤ a * a ^ k := by
        simpa [Nat.mul_comm, Nat.mul_one, Nat.one_mul]
          using Nat.mul_le_mul ha ih
      simpa [Nat.pow_succ, Nat.mul_comm] using hmul

lemma one_le_polylogBudget (N : Nat) : 1 ≤ polylogBudget N := by
  have := pow_ge_one (Nat.log2 (N + 1) + 1) 4 (log2_succ_le_base N)
  simpa [polylogBudget] using this

end LocalityLift
end Facts
