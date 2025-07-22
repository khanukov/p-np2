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
  have hxall : ∀ z : Point n, f z = f (Point.update z i (!z i)) := by
    simp [mem_support_iff] at hi
    exact hi
  have hx := hxall x
  by_cases hb : b = x i
  · subst hb
    have hupdate : Point.update x i (x i) = x := by
      funext j; by_cases hj : j = i <;> simp [Point.update, hj]
    simp [hupdate]
  · have hb' : b = !x i := by
      cases hxi : x i <;> cases hbv : b <;> simp [hxi, hbv] at *
    simp [hb'.symm] at hx
    exact hx

/-- Every non-trivial function evaluates to `true` at some point. -/
lemma exists_true_on_support {f : BFunc n} (h : support f ≠ ∅) :
    ∃ x, f x = true := by
  classical
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h
  obtain ⟨x, hx⟩ := mem_support_iff.mp hi
  by_cases hfx : f x = true
  · exact ⟨x, hfx⟩
  · have hxne : f (Point.update x i (!x i)) ≠ f x := by simpa using hx.symm
    cases hupdate : f (Point.update x i (!x i)) with
    | false =>
        have : False := by
          simp [hfx, hupdate] at hxne
        contradiction
    | true =>
        exact ⟨Point.update x i (!x i), by simp [hupdate]⟩

@[simp] lemma support_const_false (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  classical
  ext i
  simp [support]

@[simp] lemma support_const_true (n : ℕ) :
    support (fun _ : Point n => true) = (∅ : Finset (Fin n)) := by
  classical
  ext i
  simp [support]

end BoolFunc
