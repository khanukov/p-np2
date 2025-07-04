import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Finset

namespace BoolFunc
variable {n : ℕ}

/-- Если `x,y` совпадают на `support f`, то `f x = f y`. —/
lemma eval_eq_of_agree_on_support
    {f : BFunc n} {x y : Point n}
    (h : ∀ i, i ∈ support f → x i = y i) :
    f x = f y := by
  classical
  -- В противном случае найдётся координата, на которой значения различны.
  by_contra hneq
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ y i := by
    by_cases hxy : x = y
    · simpa [hxy] using hneq
    · push_neg at hxy; exact hxy
  have hisupp : i ∈ support f := by
    -- используем определение support
    unfold support
    simp [hi, Finset.mem_filter]
  have : x i = y i := h i hisupp
  exact hi this

/-- Всякая нетривиальная функция принимает `true` где‑то. —/
lemma exists_true_on_support {f : BFunc n} (h : support f ≠ ∅) :
    ∃ x, f x = true := by
  classical
  -- перебираем все точки, ищем, где функция 0 ⇒ flip i меняет на 1
  by_contra hnone
  push_neg at hnone
  have : support f = ∅ := by
    -- ни на одной точке нельзя изменить бит, значит support пуст
    ext i; simp [support, hnone]
  exact h this

end BoolFunc
