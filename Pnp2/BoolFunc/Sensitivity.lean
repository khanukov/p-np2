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

/-! ### Sensitivity and restrictions -/

@[simp] lemma sensitivityAt_restrict_le (f : BFunc n) (j : Fin n)
    (b : Bool) (x : Point n) :
    sensitivityAt (f.restrictCoord j b) x ≤
      sensitivityAt f (Point.update x j b) := by
  classical
  -- Unfold both `sensitivityAt` sets.
  simp [sensitivityAt, BFunc.restrictCoord] at *
  -- Define the original and restricted index sets.
  set z := Point.update x j b with hz
  have hz_i (i : Fin n) (hij : i ≠ j) :
      Point.update (Point.update x i (!x i)) j b =
        Point.update z i (!z i) := by
    have := Point.update_swap (x := x) hij (!x i) b
    simpa [hz, hij] using this
  have hsubset :
      (Finset.univ.filter fun i =>
          f (Point.update (Point.update x i (!x i)) j b) ≠ f z) ⊆
        Finset.univ.filter fun i => f (Point.update z i (!z i)) ≠ f z := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiu, hi⟩
    by_cases hij : i = j
    · -- Updates on the fixed coordinate `j` cancel out and cannot contribute.
      subst hij
      have hpoint : Point.update (Point.update x i (!x i)) i b = Point.update x i b := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [Point.update]
        · simp [Point.update, hk]
      have hcontr : f (Point.update x i b) ≠ f (Point.update x i b) := by
        simpa [hz, hpoint] using hi
      exact (hcontr rfl).elim
    · -- For `i ≠ j` we use the swap lemma to rewrite the update order.
      have hi' : f (Point.update z i (!z i)) ≠ f z := by
        simpa [hz_i i hij, hz, hij] using hi
      exact Finset.mem_filter.mpr ⟨by simpa, hi'⟩
  -- The subset relation yields the desired card inequality.
  have hcard := Finset.card_le_card hsubset
  simpa [hz] using hcard

lemma sensitivity_restrictCoord_le (f : BFunc n) (j : Fin n) (b : Bool) :
    sensitivity (f.restrictCoord j b) ≤ sensitivity f := by
  classical
  unfold sensitivity
  refine Finset.sup_le ?_
  intro x hx
  have hx' := sensitivityAt_le (f := f) (x := Point.update x j b)
  exact le_trans (sensitivityAt_restrict_le (f := f) (j := j) (b := b) (x := x)) hx'

/-!
Fixing one coordinate of every function in a family cannot increase
sensitivity.  This convenience lemma will be useful for the recursive
construction of a decision tree: restricting the family to `i = b`
keeps all sensitivities below the original bound.
 -/
lemma sensitivity_family_restrict_le (F : Family n) (i : Fin n) (b : Bool)
    {s : ℕ} (hF : ∀ f ∈ F, sensitivity f ≤ s) :
    ∀ g ∈ F.restrict i b, sensitivity g ≤ s := by
  intro g hg
  classical
  -- Unfold membership in the restricted family.  It is implemented via
  -- `Finset.image`, so we obtain an original function `f ∈ F` with
  -- `g = f.restrictCoord i b`.
  rcases Finset.mem_image.mp hg with ⟨f, hfF, rfl⟩
  -- Apply the single-function lemma and the assumption `hF`.
  exact le_trans (sensitivity_restrictCoord_le (f := f) (j := i) (b := b))
    (hF f hfF)

end BoolFunc

