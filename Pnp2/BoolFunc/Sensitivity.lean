import Pnp2.BoolFunc
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold

open Finset

namespace BoolFunc

variable {n : ℕ} [Fintype (Point n)]

/-- `sensitivityAt f x` is the number of coordinates on which flipping the
    input changes the value of `f`. -/
def sensitivityAt (f : BFunc n) (x : Point n) : ℕ :=
  (Finset.univ.filter fun i => f (Point.update x i (!x i)) ≠ f x).card

/-- The (block) sensitivity of a Boolean function.  We take the maximum of
    `sensitivityAt` over all points of the cube. -/
def sensitivity (f : BFunc n) : ℕ :=
  (Finset.univ.sup fun x => sensitivityAt f x)

lemma sensitivityAt_le (f : BFunc n) (x : Point n) :
    sensitivityAt f x ≤ sensitivity f :=
  by
    classical
    have hx : x ∈ (Finset.univ : Finset (Point n)) := by simp
    exact Finset.le_sup (s := Finset.univ) hx

/-!
The next lemma states that freezing one input bit cannot increase the
sensitivity of a Boolean function.  It will be useful when constructing
decision trees: at each branching step we restrict all functions in the
family by fixing a coordinate and need to maintain the global sensitivity
bound.
-/

lemma sensitivity_restrictCoord_le (f : BFunc n) (i : Fin n) (b : Bool) :
    sensitivity (BFunc.restrictCoord f i b) ≤ sensitivity f := by
  classical
  -- Expand both sensitivities as suprema of `sensitivityAt`.
  unfold sensitivity
  -- To prove the supremum inequality we bound each `sensitivityAt` value
  -- of the restricted function by the corresponding value of `f` at the
  -- updated point where coordinate `i` is fixed to `b`.
  refine Finset.sup_le ?_;
  intro x hx
  -- Consider the point `x'` obtained from `x` by fixing the `i`-th bit.
  let x' : Point n := Point.update x i b
  have hsub :
      (Finset.univ.filter
        fun j : Fin n =>
          BFunc.restrictCoord f i b (Point.update x j (!x j)) ≠
            BFunc.restrictCoord f i b x).card ≤
      (Finset.univ.filter
        fun j : Fin n =>
          f (Point.update x' j (!x' j)) ≠ f x').card := by
    -- Show that the set counted on the left is a subset of the one on the right.
    refine Finset.card_le_of_subset ?subset
    intro j hj
    have hjmem : j ∈ Finset.univ := by simp
    have hjcond := (Finset.mem_filter.mp hj).2
    have hj' : j ≠ i := by
      -- Flipping the fixed coordinate does not change the restricted function.
      by_contra hji
      subst hji
      simp [BFunc.restrictCoord] at hjcond
    -- Rewrite the condition using commutativity of distinct updates.
    have hupdate : Point.update (Point.update x j (!x j)) i b =
        Point.update x' j (!x j) := by
      by_cases hij : j = i
      · contradiction
      · funext k
        by_cases hk : k = j
        · subst hk; simp [Point.update, hij]
        · by_cases hk' : k = i
          · subst hk'; simp [Point.update]
          · simp [Point.update, hk, hk', hij]
    -- Now express the difference of restricted function values via `f`.
    have hjcond' : f (Point.update x' j (!x j)) ≠ f x' := by
      simpa [BFunc.restrictCoord, hupdate] using hjcond
    -- Convert the negated equality to membership in the filter set on the right.
    have hxj : j ∈
        Finset.univ.filter
          (fun j : Fin n => f (Point.update x' j (!x' j)) ≠ f x') := by
      have hxj' : j ∈ Finset.univ := by simp
      have hneq : f (Point.update x' j (!x' j)) ≠ f x' := by
        simpa [Point.update, hj'] using hjcond'
      exact Finset.mem_filter.mpr ⟨hxj', hneq⟩
    exact hxj
  -- Conclude using the subset bound and the definition of `sensitivityAt`.
  have hsens_at :=
    calc
      sensitivityAt (BFunc.restrictCoord f i b) x =
          (Finset.univ.filter
            fun j : Fin n =>
              BFunc.restrictCoord f i b (Point.update x j (!x j)) ≠
                BFunc.restrictCoord f i b x).card := rfl
      _ ≤ (Finset.univ.filter
            fun j : Fin n => f (Point.update x' j (!x' j)) ≠ f x').card := hsub
  have hsens_at_f :
      (Finset.univ.filter
          fun j : Fin n => f (Point.update x' j (!x' j)) ≠ f x').card ≤
        sensitivity f := by
    -- This is exactly `sensitivityAt_le` for the point `x'`.
    have := sensitivityAt_le (f := f) (x := x')
    simpa [sensitivity, sensitivityAt] using this
  exact le_trans hsens_at hsens_at_f

end BoolFunc

