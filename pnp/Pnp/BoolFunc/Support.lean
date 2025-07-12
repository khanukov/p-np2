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

end BoolFunc
