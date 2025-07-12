import Mathlib.Data.Finset.Basic
import Pnp.BoolFunc

open Finset

namespace BoolFunc
variable {n : ℕ}

/-- If a coordinate is not in the `support` of `f`, updating that coordinate does
not change the value of `f`. -/
lemma eval_update_not_support {f : BFunc n} {i : Fin n}
    (hi : i ∉ support f) (x : Point n) (b : Bool) :
    f x = f (Point.update x i b) := by
  classical
  have hxall : ∀ z : Point n, f z = f (Point.update z i (!z i)) := by
    simpa [mem_support_iff] using hi
  have hx := hxall x
  by_cases hb : b = x i
  · subst hb
    have hupdate : Point.update x i (x i) = x := by
      funext j; by_cases hj : j = i <;> simp [Point.update, hj]
    simp [hupdate]
  · have hb' : b = !x i := by
      cases hxi : x i <;> cases hbv : b <;> simp [hxi, hbv] at *
    simpa [hb'] using hx

/-- Every non-trivial function evaluates to `true` at some point. -/
lemma exists_true_on_support {f : BFunc n} (h : support f ≠ ∅) :
    ∃ x, f x = true := by
  classical
  rcases Finset.nonempty_iff_ne_empty.2 h with ⟨i, hi⟩
  rcases mem_support_iff.mp hi with ⟨x, hx⟩
  cases hxfx : f x
  · -- if `f x = false`, the witness from `mem_support_iff` shows
    -- that flipping coordinate `i` yields `true`.
    have : f (Point.update x i (!x i)) = true := by
      -- otherwise we contradict `hx`
      cases hupdate : f (Point.update x i (!x i)) with
      | true => simpa [hupdate]
      | false =>
          have := hx
          simp [hxfx, hupdate] at this
    exact ⟨Point.update x i (!x i), this⟩
  · -- otherwise `x` itself evaluates to `true`
    exact ⟨x, by simpa [hxfx]⟩

end BoolFunc
