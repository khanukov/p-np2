import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Pnp2.BoolFunc
import Pnp2.Agreement

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

/-
  A non-constant Boolean function takes the value `true` somewhere.
-/
lemma exists_point_true (f : BFunc n) (h : support f ≠ ∅) :
    ∃ x : Point n, f x = true := by
  classical
  by_contra hfalse
  push_neg at hfalse
  have hsupp : support f = ∅ := by
    ext i; constructor
    · intro hi
      rcases mem_support_iff.mp hi with ⟨x, hx⟩
      have hx1 := hfalse x
      have hx2 := hfalse (Point.update x i (!x i))
      simp [hx1, hx2] at hx
    · intro hi; cases hi
  exact h hsupp

/--
  If `K ⊆ support f` then fixing the coordinates in `K`
  leaves `f` *constant* on the resulting subcube.
-/
lemma constant_on_subcube (f : BFunc n)
    {K : Finset (Fin n)} (hK : K ⊆ support f) :
    ∀ {x₀ : Point n} {x y : Point n},
      x ∈ Agreement.Subcube.fromPoint x₀ K →
      y ∈ Agreement.Subcube.fromPoint x₀ K →
      f x = f y := by
  intro x₀ x y hx hy
  classical
  apply eval_eq_of_agree_on_support (f := f) (x := x) (y := y)
  intro i hi
  have hiK : i ∈ K := hK hi
  have hx_i : x i = x₀ i := hx i hiK
  have hy_i : y i = x₀ i := hy i hiK
  simpa [Agreement.Subcube.fromPoint, hx_i, hy_i] using congrArg id (show x i = y i from by
    trans x₀ i <;> assumption)

end BoolFunc

export BoolFunc (exists_point_true constant_on_subcube)
