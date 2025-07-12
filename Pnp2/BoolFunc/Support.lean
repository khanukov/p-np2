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
  -- `hi` means flipping coordinate `i` never changes the value.
  -- from `hi` we obtain that flipping `i` never changes the value
  classical
  have hxall_ne : ∀ z : Point n, ¬ f z ≠ f (Point.update z i (!z i)) :=
    not_exists.mp (by simpa [mem_support_iff] using hi)
  have hx : f x = f (Point.update x i (!x i)) := by
    by_cases hx' : f x = f (Point.update x i (!x i))
    · exact hx'
    · exfalso; exact (hxall_ne x) (by simpa [hx'] )
  by_cases hbi : b = x i
  · subst hbi; simp
  · have hb : b = !x i := by
      cases x i <;> cases b <;> simp [hbi] at *
    simpa [hb] using hx

/-/-- If `x` and `y` agree on `support f`, then `f x = f y`. -/
lemma eval_eq_of_agree_on_support
    {f : BFunc n} {x y : Point n}
    (h : ∀ i, i ∈ support f → x i = y i) :
    f x = f y := by
  classical
  -- Otherwise there exists a coordinate where the values differ.
  by_contra hneq
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ y i := by
    -- contraposition: from `x ≠ y` get `¬ ∀ i, x i = y i`
    have hxy' : ¬ ∀ j, x j = y j := by
      intro H; apply hneq; funext j; exact H j
    -- extract an index on which they differ
    contrapose! hxy'
    intro hdiff; exact hdiff.2
  have hisupp : i ∈ support f := by
    -- unfold the definition of `support` and simplify
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
