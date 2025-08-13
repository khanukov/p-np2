import Pnp2.BoolFunc
import Pnp2.BoolFunc.Support
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold

open Finset

-- Silence routine linter warnings during development.
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

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

/--
`coordSensitivity f i` counts the number of inputs where flipping the `i`‑th
bit changes the value of `f`.  This refined notion is useful for tracking which
coordinates remain "active" during recursive constructions.
-/
def coordSensitivity (f : BFunc n) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun x : Point n =>
      f x ≠ f (Point.update x i (!x i))).card

lemma coordSensitivity_eq_zero_iff (f : BFunc n) (i : Fin n) :
    coordSensitivity f i = 0 ↔
      ∀ x : Point n, f x = f (Point.update x i (!x i)) := by
  classical
  unfold coordSensitivity
  constructor
  · intro h x
    have hempty :
        (Finset.univ.filter fun y : Point n =>
          f y ≠ f (Point.update y i (!y i))) = (∅ : Finset (Point n)) :=
      Finset.card_eq_zero.mp h
    by_contra hx
    have hxmem : x ∈
        (Finset.univ.filter fun y : Point n =>
          f y ≠ f (Point.update y i (!y i))) := by
      simpa [hx]
    simpa [hempty] using hxmem
  · intro hx
    have hempty :
        (Finset.univ.filter fun y : Point n =>
          f y ≠ f (Point.update y i (!y i))) = (∅ : Finset (Point n)) := by
      apply Finset.eq_empty_of_forall_not_mem
      intro x hxmem
      rcases Finset.mem_filter.mp hxmem with ⟨-, hxneq⟩
      have := hx x
      exact hxneq (by simpa using this)
    simpa [hempty]

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

/-- After fixing coordinate `i` the resulting function no longer depends on
`i`; the coordinate sensitivity along `i` is therefore zero. -/
lemma coordSensitivity_restrict_self_zero (f : BFunc n) (i : Fin n) (b : Bool) :
    coordSensitivity (f.restrictCoord i b) i = 0 := by
  classical
  apply (coordSensitivity_eq_zero_iff (f := f.restrictCoord i b) (i := i)).2
  intro x
  have : Point.update (Point.update x i (!x i)) i b = Point.update x i b := by
    funext k; by_cases hk : k = i <;> simp [Point.update, hk]
  simp [BFunc.restrictCoord, this]

/--
Restricting a function on an unrelated coordinate preserves zero sensitivity on
`j`.  In particular, if flipping `j` never changes `f`, the same remains true
after fixing any coordinate `i`.
-/
lemma coordSensitivity_restrict_eq_zero (f : BFunc n) (i j : Fin n) (b : Bool)
    (h : coordSensitivity f j = 0) :
    coordSensitivity (f.restrictCoord i b) j = 0 := by
  classical
  have h' := (coordSensitivity_eq_zero_iff (f := f) (i := j)).1 h
  by_cases hji : j = i
  ·
    subst hji
    have hzero := coordSensitivity_restrict_self_zero (f := f) (i := j) (b := b)
    simpa using hzero
  · apply (coordSensitivity_eq_zero_iff
        (f := f.restrictCoord i b) (i := j)).2
    intro x
    have hx := h' (Point.update x i b)
    have hx' : f (Point.update x i b) =
        f (Point.update (Point.update x j (!x j)) i b) := by
      simpa [Point.update, hji] using hx
    simpa [BFunc.restrictCoord] using hx'

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

/--
`sensitiveCoord F i` means that some function in the family `F` changes value
when the `i`‑th bit of the input is flipped. -/
def sensitiveCoord (F : Family n) (i : Fin n) : Prop :=
  ∃ f ∈ F, ∃ x : Point n, f x ≠ f (Point.update x i (!x i))

/--
If a Boolean function has zero sensitivity, then its essential `support` is
empty.  Any coordinate belonging to the support would witness positive
sensitivity, contradicting the assumption.
-/
lemma support_eq_empty_of_sensitivity_zero (f : BFunc n)
    (h : sensitivity f = 0) :
    support f = (∅ : Finset (Fin n)) := by
  classical
  -- Show that no coordinate can belong to the support.
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rcases mem_support_iff.mp hi with ⟨x, hx⟩
  -- The witness `x` certifies that flipping `i` changes the value of `f`.
  have hxpos' :
      0 < (Finset.univ.filter fun j => f (Point.update x j (!x j)) ≠ f x).card := by
    have hiuniv : i ∈ (Finset.univ : Finset (Fin n)) := by simp
    have hmem : i ∈
        Finset.univ.filter fun j => f (Point.update x j (!x j)) ≠ f x :=
      Finset.mem_filter.mpr ⟨hiuniv, by simpa using hx.symm⟩
    exact Finset.card_pos.mpr ⟨i, hmem⟩
  have hAtpos : 0 < sensitivityAt f x := by
    simpa [sensitivityAt] using hxpos'
  have hle : sensitivityAt f x ≤ sensitivity f :=
    sensitivityAt_le (f := f) (x := x)
  have hpos : 0 < sensitivity f := lt_of_lt_of_le hAtpos hle
  have : False := by simpa [h] using hpos
  exact this.elim

/--
For a non‑constant family without identically false members, there exists a
function, input, and sensitive coordinate witnessing positive sensitivity.
This lemma combines `support_eq_empty_of_sensitivity_zero` with the helper
`exists_family_sensitive_coord`.
-/
lemma non_constant_family_has_sensitive_coord (F : Family n)
    (hconst : ¬ ∃ b, ∀ f ∈ F, ∀ x, f x = b)
    (htrue : ∀ f ∈ F, ∃ x, f x = true) :
    ∃ i : Fin n, ∃ f ∈ F, ∃ x : Point n,
      f x ≠ f (Point.update x i (!x i)) := by
  classical
  -- First show that some function has positive sensitivity.
  have hpos : ∃ f ∈ F, 0 < sensitivity f := by
    classical
    by_contra h
    -- Then every function would have zero sensitivity and hence be constant.
    have hzero : ∀ f ∈ F, sensitivity f = 0 := by
      intro f hf
      by_contra hf0
      have hposf : 0 < sensitivity f := Nat.pos_of_ne_zero hf0
      exact h ⟨f, hf, hposf⟩
    -- Using the `true` witness, deduce that each function is constantly `true`.
    have hconst' : ∀ f ∈ F, ∀ x, f x = true := by
      intro f hf x
      obtain ⟨x₀, hx₀⟩ := htrue f hf
      have hsupp :=
        support_eq_empty_of_sensitivity_zero (f := f) (h := hzero f hf)
      have hagree : ∀ i ∈ support f, x i = x₀ i := by
        intro i hi
        have : i ∈ (∅ : Finset (Fin n)) := by simpa [hsupp] using hi
        cases this
      have hval : f x = f x₀ :=
        eval_eq_of_agree_on_support (f := f) (x := x) (y := x₀) hagree
      simp [hval, hx₀]
    -- Thus the whole family would be constantly `true`, contradicting `hconst`.
    have hcontr : False :=
      hconst ⟨true, hconst'⟩
    exact hcontr.elim
  -- Apply the existing lemma to extract the sensitive coordinate.
  rcases exists_family_sensitive_coord (F := F) hpos with
    ⟨i, f, hfF, x, hx⟩
  exact ⟨i, f, hfF, x, hx⟩

/--
If a family is not constant and all coordinates outside `A` are known to be
insensitive, then the sensitive coordinate guaranteed by
`non_constant_family_has_sensitive_coord` must lie inside `A`.
-/
lemma exists_sensitive_coord_in_A (F : Family n) (A : Finset (Fin n))
    (hNonConst : ¬ ∃ b, ∀ f ∈ F, ∀ x, f x = b)
    (htrue : ∀ f ∈ F, ∃ x, f x = true)
    (hA : ∀ j ∉ A, ∀ f ∈ F, coordSensitivity f j = 0) :
    ∃ i ∈ A, sensitiveCoord F i := by
  classical
  rcases non_constant_family_has_sensitive_coord (F := F) (hconst := hNonConst)
      (htrue := htrue) with ⟨i, f, hfF, x, hx⟩
  have hiA : i ∈ A := by
    by_contra hnot
    have hzero := hA i hnot f hfF
    have hcontr :=
      (coordSensitivity_eq_zero_iff (f := f) (i := i)).1 hzero x
    exact hx hcontr
  exact ⟨i, hiA, f, hfF, x, hx⟩

/-!
The project originally conjectured the following statement: if a family has a
function witnessing sensitivity on coordinate `i`, then two distinct members of
the family must coincide after restricting `i` to some Boolean value.  During
development we found a counterexample (`F = {id, not}` on one bit), so the claim
is **false** as stated.  A corrected version will require additional
assumptions, and the precise formulation remains open.  The placeholder lemma
has therefore been removed to keep the code base consistent.
-/

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

