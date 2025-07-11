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
  rcases Finset.nonempty_iff_ne_empty.2 h with ⟨i, hi⟩
  rcases mem_support_iff.mp hi with ⟨x, hx⟩
  cases hfx : f x
  · have : f (Point.update x i (!x i)) = true := by
      have hneq := hx
      simp [hfx] at hneq
      cases hupdate : f (Point.update x i (!x i)) with
      | true => simpa [hupdate]
      | false =>
          have : False := by simpa [hupdate] using hneq
          contradiction
    exact ⟨Point.update x i (!x i), this⟩
  · exact ⟨x, by simpa [hfx]⟩

end BoolFunc
