import Mathlib.Data.Finset.Basic
import Pnp.BoolFunc

open Finset

namespace Pnp.BoolFunc

variable {n : ℕ}

/-- If a coordinate is not in the `support` of `f`, updating that coordinate does
not change the value of `f`. -/
theorem eval_update_not_support {f : BFunc n} {i : Fin n} (hi : i ∉ support f)
    (x : Point n) (b : Bool) :
    f x = f (x.update i b) := by
  classical
  have eq_all : ∀ z, f z = f (z.update i (!z i)) := by
    intro z
    have : ¬ ∃ z, f z ≠ f (z.update i (!z i)) := by
      simpa [mem_support_iff, not_exists] using hi
    simp [this]
  by_cases hb : b = x i
  · simp [hb]
  ·
    have : b = ! x i := by
      cases x i <;> cases b <;> simp [hb]
    calc
      f x = f (x.update i (!x i)) := eq_all x
      _ = f (x.update i b) := by simp [this]

/-- If `x` and `y` agree on `support f`, then `f x = f y`. -/
theorem eval_eq_of_agree_on_support {f : BFunc n} {x y : Point n}
    (h : ∀ i ∈ support f, x i = y i) :
    f x = f y := by
  classical
  let toFix := (Finset.univ : Finset (Fin n)) \ support f
  have : f x = (toFix.fold (fun z p => p.update z (y z)) x) := by
    induction toFix using Finset.induction_on with
    | empty =>
        simp [Finset.fold_empty]
    | @insert i s hi ih =>
        simp [Finset.fold_insert hi]
        have hi' : i ∉ support f := by simp [Finset.mem_diff, hi]
        have := eval_update_not_support hi' x (y i)
        simp [this] at ih
        calc
          f x = f (x.update i (y i)) := by simpa using this
          _ = f (s.fold (fun z p => p.update z (y z)) (x.update i (y i))) := by
                simpa using ih
  simpa using this

/-- Every non-trivial function evaluates to `true` at some point. -/
theorem exists_true_on_support {f : BFunc n} (h : support f ≠ ∅) :
    ∃ x, f x = true := by
  classical
  rcases Finset.nonempty_iff_ne_empty.1 h with ⟨i, hi⟩
  rcases mem_support_iff.1 hi with ⟨x, hf⟩
  by_cases hfx : f x = true
  · exact ⟨x, hfx⟩
  ·
    have : f (x.update i (!x i)) = true := by
      simp [hfx] at hf
      cases hf_update : f (x.update i (!x i)) <;> simp_all at hf
    exact ⟨x.update i (!x i), this⟩

end Pnp.BoolFunc
