import Mathlib.Data.Set.Basic

/-!
  pnp3/Complexity/Promise.lean

  Базовые определения для promise-задач и корректности решателей.

  Задачи вроде GapMCSP естественным образом задаются в promise-форме: мы
  фиксируем множество YES-инстансов и множество NO-инстансов и требуем, чтобы
  решатель отвечал правильно хотя бы на них.  Вне `Yes ∪ No` поведение
  решателя не ограничивается.
-/

namespace Pnp3
namespace Complexity

/-- Promise-задача: фиксируем множества YES и NO. -/
structure PromiseProblem (α : Type) :=
  (Yes : Set α)
  (No : Set α)
  (disjoint : Disjoint Yes No)

/--
  Решатель корректен для promise-задачи, если он принимает все YES-инстансы
  и отклоняет все NO-инстансы.
-/
def SolvesPromise {α : Type} (P : PromiseProblem α) (decide : α → Bool) : Prop :=
  (∀ x, x ∈ P.Yes → decide x = true) ∧
  (∀ x, x ∈ P.No → decide x = false)

end Complexity
end Pnp3
