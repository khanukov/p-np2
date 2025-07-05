import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Finset

namespace BoolFunc
variable {n : ℕ}

/-/-- If `x` and `y` agree on `support f`, then `f x = f y`. -/
lemma eval_eq_of_agree_on_support
    {f : BFunc n} {x y : Point n}
    (h : ∀ i, i ∈ support f → x i = y i) :
    f x = f y := by
  classical
  -- Otherwise there exists a coordinate where the values differ.
  by_contra hneq
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ y i := by
    by_cases hxy : x = y
    · simpa [hxy] using hneq
    · push_neg at hxy; exact hxy
  have hisupp : i ∈ support f := by
    -- use the definition of `support`
    unfold support
    simp [hi, Finset.mem_filter]
  have : x i = y i := h i hisupp
  exact hi this

/-/-- Every non-trivial function evaluates to `true` at some point. -/
lemma exists_true_on_support {f : BFunc n} (h : support f ≠ ∅) :
    ∃ x, f x = true := by
  classical
  -- iterate over all points, looking for one where flipping a bit changes the
  -- value from `0` to `1`
  by_contra hnone
  push_neg at hnone
  have : support f = ∅ := by
    -- if no bit can be flipped on any point, the support is empty
    ext i; simp [support, hnone]
  exact h this

end BoolFunc
