import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Finset

namespace BoolFunc
variable {n : ℕ}

/-- If a coordinate is not in the `support` of `f`, updating that coordinate does
not change the value of `f`. -/
lemma eval_update_not_support {f : BFunc n} {i : Fin n}
    (hi : i ∉ support f) (x : Point n) (b : Bool) :
    f x = f (Point.update x i b) := by
  classical
  have hxne : ¬ ∃ z, f z ≠ f (Point.update z i (! z i)) := by
    simp [mem_support_iff] at hi
    exact hi
  have hxall : ∀ z : Point n, f z = f (Point.update z i (! z i)) :=
    not_exists.mp hxne
  have hx := hxall x
  by_cases hb : b = x i
  · subst hb; simp
  · have hb' : b = ! x i := by
      cases x i <;> cases b
      · contradiction
      · simp [hb]
      · simp [hb]
      · contradiction
    simpa [hb'] using hx

/-/-- If `x` and `y` agree on `support f`, then `f x = f y`. -/
lemma eval_eq_of_agree_on_support
    {f : BFunc n} {x y : Point n}
    (h : ∀ i, i ∈ support f → x i = y i) :
    f x = f y := by
  classical
  -- Otherwise there exists a coordinate where the values differ.
  by_contra hneq
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ y i := by
    classical
    have hxy' : ¬ ∀ j, x j = y j := by
      intro hxy
      apply hneq
      funext j; exact hxy j
    simpa [not_forall] using hxy'
  have hisupp : i ∈ support f := by
    -- use the definition of `support`
    unfold support
    simp [Finset.mem_filter] at *
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
