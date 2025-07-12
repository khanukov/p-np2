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
    simp [hb'] at hx
    exact hx

/-- Every non-trivial function evaluates to `true` at some point. -/
lemma exists_true_on_support {f : BFunc n} (h : support f ≠ ∅) :
    ∃ x, f x = true := by
  classical
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h
  obtain ⟨x, hx⟩ := mem_support_iff.mp hi
  by_cases hfx : f x = true
  · exact ⟨x, hfx⟩
  · cases hupd : f (Point.update x i (!x i))
    · simp [hfx, hupd] at hx
      contradiction
    · exact ⟨Point.update x i (!x i), hupd⟩

end BoolFunc
