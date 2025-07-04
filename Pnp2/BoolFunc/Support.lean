import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Pnp2.BoolFunc

open Finset

namespace BoolFunc

variable {n : ℕ}

/--
If two points agree on every coordinate in the *support* of `f`,
then `f` takes the same value on these points.
-/
lemma eval_eq_of_agree_on_support
    {f : BFunc n} {x y : Point n}
    (h : ∀ i, i ∈ support f → x i = y i) :
    f x = f y := by
  classical
  by_contra hneq
  have hxy : ∃ i : Fin n, x i ≠ y i := by
    by_cases hxy' : x = y
    · have : f x = f y := by simpa [hxy'] using rfl
      exact (hneq this).elim
    · push_neg at hxy'
      exact hxy'
  rcases hxy with ⟨i, hi⟩
  have hi_supp : i ∈ support f := by
    unfold BoolFunc.support
    simp [Finset.mem_filter, hi]
  have : x i = y i := h i hi_supp
  exact hi this

/--
Flipping bits outside the support of `f` keeps its value.
-/
lemma flip_outside_support (f : BFunc n) (x : Point n) {i : Fin n}
    (hi : i ∉ support f) :
    f x = f (Point.update x i (!x i)) := by
  classical
  have hagree : ∀ j, j ∈ support f → x j = (Point.update x i (!x i)) j := by
    intro j hj
    by_cases hji : j = i
    · subst hji; exact (hi hj).elim
    · simp [Point.update, hji]
  simpa using
    (eval_eq_of_agree_on_support (f := f) (x := x) (y := Point.update x i (!x i)) hagree)



/--
If `support f ⊆ S` and `x` and `y` agree on all coordinates in `S`,
then `f` takes the same value on `x` and `y`.
-/
lemma eval_eq_of_agree_on_superset {f : BFunc n} {S : Finset (Fin n)}
    {x y : Point n}
    (hSup : support f ⊆ S) (h : ∀ i, i ∈ S → x i = y i) :
    f x = f y :=
  eval_eq_of_agree_on_support (x:=x) (y:=y) (fun i hi => h i (hSup hi))

end BoolFunc
