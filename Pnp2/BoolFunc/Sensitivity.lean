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

/- ### Sensitivity and restrictions -/

set_option linter.unnecessarySimpa false in
set_option linter.unusedSectionVars false in
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
    simpa [hz, hij] using Point.update_swap (x := x) hij (!x i) b
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
      have hcontr : False := by
        simpa [hz, hpoint] using hi
      exact hcontr.elim
    · -- For `i ≠ j` we use the swap lemma to rewrite the update order.
      have hi' : f (Point.update z i (!z i)) ≠ f z := by
        simpa [hz_i i hij, hz, hij] using hi
      exact Finset.mem_filter.mpr ⟨by simp, hi'⟩
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

/--
If a Boolean function has positive sensitivity, then there exists a coordinate
whose value change flips the function on some input.  This lemma extracts such
a witness and will be useful for constructing decision trees.
-/
lemma exists_sensitive_coord (f : BFunc n) (hpos : 0 < sensitivity f) :
    ∃ i : Fin n, ∃ x : Point n, f x ≠ f (Point.update x i (!x i)) := by
  classical
  -- Expand the definition of sensitivity.  The assumption `hpos` shows that the
  -- maximum of `sensitivityAt f x` over all points `x` is positive, so some
  -- particular point must witness positive sensitivity.
  have h :=
    (Finset.lt_sup_iff (s := (Finset.univ : Finset (Point n)))
      (f := fun x => sensitivityAt f x) (a := 0)).1
      (by simpa [sensitivity] using hpos)
  rcases h with ⟨x, -, hxpos⟩
  -- A positive `sensitivityAt` value means the set of sensitive coordinates at `x`
  -- is nonempty.  Convert this statement into an explicit index.
  have hxpos' :
      0 < (Finset.univ.filter fun i => f (Point.update x i (!x i)) ≠ f x).card :=
    by simpa [sensitivityAt] using hxpos
  have hxnonempty :
      (Finset.univ.filter fun i => f (Point.update x i (!x i)) ≠ f x).Nonempty :=
    Finset.card_pos.mp hxpos'
  rcases hxnonempty with ⟨i, hi⟩
  -- `hi` certifies that flipping the `i`‑th bit changes the output of `f`.
  refine ⟨i, x, ?_⟩
  simpa using ((Finset.mem_filter.mp hi).2).symm

/-!
If at least one function in a family has positive sensitivity, then the family
contains a function together with an input and coordinate witnessing this
sensitivity.  This is a light wrapper around `exists_sensitive_coord` that also
returns the membership proof for convenience.
-/
set_option linter.unusedSectionVars false in
lemma exists_family_sensitive_coord (F : Family n) [Fintype (Point n)]
    (h : ∃ f ∈ F, 0 < sensitivity f) :
    ∃ i : Fin n, ∃ f ∈ F, ∃ x : Point n,
      f x ≠ f (Point.update x i (!x i)) := by
  classical
  rcases h with ⟨f, hfF, hpos⟩
  rcases exists_sensitive_coord (f := f) hpos with ⟨i, x, hx⟩
  exact ⟨i, f, hfF, x, hx⟩

@[simp] lemma sensitivity_const (n : ℕ) (b : Bool) [Fintype (Point n)] :
    sensitivity (fun _ : Point n => b) = 0 := by
  classical
  have hxle : (Finset.univ.sup fun x : Point n => sensitivityAt (fun _ : Point n => b) x) ≤ 0 := by
    refine Finset.sup_le ?_; intro x hx
    simp [sensitivityAt]
  have hxge : 0 ≤ (Finset.univ.sup fun x : Point n => sensitivityAt (fun _ : Point n => b) x) := by
    exact Nat.zero_le _
  have hx : (Finset.univ.sup fun x : Point n => sensitivityAt (fun _ : Point n => b) x) = 0 := le_antisymm hxle hxge
  simpa [sensitivity] using hx


end BoolFunc

