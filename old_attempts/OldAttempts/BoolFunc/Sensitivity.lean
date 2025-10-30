import OldAttempts.BoolFunc
import OldAttempts.BoolFunc.Support
import OldAttempts.Agreement
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
open Agreement
open scoped BigOperators

-- Silence routine linter warnings during development.
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

namespace BoolFunc

variable {n : ℕ} [Fintype (Point n)]

/-- `sensitivityAt f x` is the number of coordinates on which flipping the
    input changes the value of `f`. -/
def sensitivityAt (f : BFunc n) (x : Point n) : ℕ :=
  (Finset.univ.filter fun i => f (Point.update x i (!x i)) ≠ f x).card

/--
`insensitiveCoordsAt f x` collects all coordinates whose individual bit flip
does not change the value of `f` at the input `x`.  This set will later be used
to identify large subcubes on which the function stays constant.  Note that the
definition mirrors `sensitivityAt`: the sensitive coordinates correspond to the
complement of this set inside `Finset.univ`.
-/
def insensitiveCoordsAt (f : BFunc n) (x : Point n) : Finset (Fin n) :=
  (Finset.univ.filter fun i => f (Point.update x i (!x i)) = f x)

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
      apply Finset.eq_empty_of_forall_notMem
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

/--
The supremum defining `sensitivity` is attained on the finite Boolean cube.
Equivalently, some point achieves the maximal local sensitivity.
-/
lemma exists_argmax_sensitivityAt (f : BFunc n) :
    ∃ x : Point n, sensitivityAt f x = sensitivity f := by
  classical
  -- `Finset.univ` of points is nonempty, allowing us to use `exists_mem_eq_sup`.
  have hne : (Finset.univ : Finset (Point n)).Nonempty := by
    simpa using
      (Finset.univ_nonempty : (Finset.univ : Finset (Point n)).Nonempty)
  -- Extract a point where the supremum is realised.
  obtain ⟨x, -, hx⟩ :=
    Finset.exists_mem_eq_sup
      (s := (Finset.univ : Finset (Point n)))
      (h := hne) (f := fun x => sensitivityAt f x)
  -- Reinterpret the equality in terms of `sensitivity`.
  refine ⟨x, ?_⟩
  simpa [sensitivity] using hx.symm

/--
The sets of sensitive and insensitive coordinates at `x` partition all
coordinates.  Consequently their cardinalities add up to the dimension `n`.
-/
lemma insensitiveCoordsAt_card_add (f : BFunc n) (x : Point n) :
    (insensitiveCoordsAt f x).card + sensitivityAt f x = n := by
  classical
  -- Apply the general partition lemma to the equality predicate.
  simpa [insensitiveCoordsAt, sensitivityAt, Finset.card_univ,
      Classical.decEq] using
    (filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun i : Fin n => f (Point.update x i (!x i)) = f x))

/--
Rewriting the previous lemma gives an explicit formula for the number of
locally insensitive coordinates at `x`.
-/
lemma insensitiveCoordsAt_card_eq (f : BFunc n) (x : Point n) :
    (insensitiveCoordsAt f x).card = n - sensitivityAt f x := by
  classical
  have h := insensitiveCoordsAt_card_add (f := f) (x := x)
  have h' := congrArg (fun t => t - sensitivityAt f x) h
  -- The left-hand side simplifies via `Nat.add_sub_cancel`.
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'

/--
If the local sensitivity at `x` is bounded by `s`, then at least `n - s`
coordinates are locally insensitive.
-/
lemma insensitiveCoordsAt_card_ge (f : BFunc n) (x : Point n) {s : ℕ}
    (hs : sensitivityAt f x ≤ s) :
    n - s ≤ (insensitiveCoordsAt f x).card := by
  classical
  have hcard := insensitiveCoordsAt_card_eq (f := f) (x := x)
  have h := Nat.sub_le_sub_left hs n
  simpa [hcard] using h

/--
A global sensitivity bound immediately yields the same lower bound for every
point `x` on the cube.
-/
lemma insensitiveCoordsAt_card_ge_of_global (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (x : Point n) :
    n - s ≤ (insensitiveCoordsAt f x).card := by
  have hsx : sensitivityAt f x ≤ s :=
    le_trans (sensitivityAt_le (f := f) (x := x)) hs
  exact insensitiveCoordsAt_card_ge (f := f) (x := x) (hs := hsx)

/--
Given a global sensitivity bound `s`, every point admits a concrete finite
subset of locally insensitive coordinates of size at least `n - s`.  This
strengthens the eventual target bound `n / (2*s)`.
-/
lemma exists_insensitiveCoordsAt_card_eq (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (x : Point n) :
    ∃ A ⊆ insensitiveCoordsAt f x, A.card = n - s := by
  classical
  have hcard : n - s ≤ (insensitiveCoordsAt f x).card :=
    insensitiveCoordsAt_card_ge_of_global (f := f) (hs := hs) (x := x)
  exact Finset.exists_subset_card_eq (s := insensitiveCoordsAt f x)
    (n := n - s) hcard

/--
Given a global sensitivity bound `s`, every point admits a concrete finite
subset of locally insensitive coordinates of size at least `n - s`.  This
strengthens the eventual target bound `n / (2*s)`.
-/
lemma exists_large_insensitiveCoordsAt (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (x : Point n) :
    ∃ A : Finset (Fin n), n - s ≤ A.card ∧ A ⊆ insensitiveCoordsAt f x := by
  classical
  obtain ⟨A, hAsub, hAcard⟩ :=
    exists_insensitiveCoordsAt_card_eq (f := f) (hs := hs) (x := x)
  refine ⟨A, ?_, hAsub⟩
  simpa [hAcard]

/--
For positive `s` the weaker bound `n / (2*s)` is always dominated by `n - s`.
This numeric fact lets us trade the exact count of insensitive coordinates for a
coarser estimate that will be convenient in later asymptotic bounds.-/
lemma div_two_mul_le_sub (n s : ℕ) (hs : 0 < s) :
    n / (2 * s) ≤ n - s := by
  classical
  -- Split into the cases `n ≤ s` and `s < n`.
  by_cases hns : n ≤ s
  · -- If `n ≤ s`, division yields `0` and the right hand side also truncates to `0`.
    have hslt : s < 2 * s := by
      have h12 : (1 : ℕ) < 2 := by decide
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using (Nat.mul_lt_mul_of_pos_right h12 hs)
    have hlt : n < 2 * s := lt_of_le_of_lt hns hslt
    have hdiv : n / (2 * s) = 0 := Nat.div_eq_of_lt hlt
    have hsub : n - s = 0 := Nat.sub_eq_zero_of_le hns
    simpa [hdiv, hsub]
  · -- In the interesting case `s < n` we show `n ≤ (n - s) * (2*s)` and conclude.
    have hlt : s < n := lt_of_not_ge hns
    -- Set `t = n - s` (> 0).
    set t := n - s with htdef
    have ht_pos : 0 < t := Nat.sub_pos_of_lt hlt
    -- `t ≤ s*t` since `s ≥ 1`.
    have h1 : t ≤ s * t := by
      have : 1 ≤ s := Nat.succ_le_of_lt hs
      have := Nat.mul_le_mul_right t this
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    -- Likewise `s ≤ s*t` since `t ≥ 1`.
    have h2 : s ≤ s * t := by
      have : 1 ≤ t := Nat.succ_le_of_lt ht_pos
      have := Nat.mul_le_mul_left s this
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    -- Add the two inequalities and rearrange the algebraic expression.
    have hsum : s + t ≤ s * t + s * t := add_le_add h2 h1
    have hsum' : s + t ≤ t * (s + s) := by
      simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm,
        Nat.right_distrib, Nat.mul_left_comm, Nat.mul_assoc] using hsum
    have hsum'' : s + t ≤ (n - s) * (2 * s) := by
      simpa [htdef, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum'
    have hn_eq : n = s + t := by
      have : s ≤ n := Nat.le_of_lt hlt
      have := Nat.add_sub_of_le this
      simpa [htdef, Nat.add_comm] using this.symm
    have hle : n ≤ (2 * s) * (n - s) := by
      simpa [hn_eq, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum''
    -- The division inequality follows from `Nat.div_le_of_le_mul`.
    exact Nat.div_le_of_le_mul hle

/--
From a global sensitivity bound `s > 0` we can extract at least `n / (2*s)`
locally insensitive coordinates at any point of the cube.
-/
lemma exists_insensitiveCoordsAt_card_ge_div (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (hspos : 0 < s) (x : Point n) :
    ∃ A : Finset (Fin n), n / (2 * s) ≤ A.card ∧ A ⊆ insensitiveCoordsAt f x := by
  classical
  -- Obtain the stronger bound `|A| ≥ n - s` and weaken it using the numeric lemma.
  obtain ⟨A, hAcard, hAsub⟩ :=
    exists_large_insensitiveCoordsAt (f := f) (hs := hs) (x := x)
  refine ⟨A, ?_, hAsub⟩
  have hineq : n / (2 * s) ≤ n - s := div_two_mul_le_sub n s hspos
  exact le_trans hineq hAcard

/--
From the existential version we immediately deduce a direct lower bound on the
cardinality of the full set `insensitiveCoordsAt f x`.
-/
lemma insensitiveCoordsAt_card_ge_div (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (hspos : 0 < s) (x : Point n) :
    n / (2 * s) ≤ (insensitiveCoordsAt f x).card := by
  classical
  obtain ⟨A, hAcard, hAsub⟩ :=
    exists_insensitiveCoordsAt_card_ge_div (f := f) (hs := hs)
      (hspos := hspos) (x := x)
  exact le_trans hAcard (Finset.card_le_card hAsub)

/--
Selecting a subset of *exactly* `n / (2*s)` locally insensitive coordinates.
This refines `exists_insensitiveCoordsAt_card_ge_div` by choosing a subset of
the desired size out of the larger set guaranteed there.
-/
lemma exists_insensitiveCoordsAt_card_eq_div (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (hspos : 0 < s) (x : Point n) :
    ∃ A ⊆ insensitiveCoordsAt f x, A.card = n / (2 * s) := by
  classical
  have hbound :=
    insensitiveCoordsAt_card_ge_div (f := f) (hs := hs) (hspos := hspos) (x := x)
  exact Finset.exists_subset_card_eq
    (s := insensitiveCoordsAt f x) (n := n / (2 * s)) hbound

/- ### Total sensitivity across the cube -/

/--
Summing the local sensitivities over all vertices of the Boolean cube is
bounded by the number of vertices times a global sensitivity bound `s`.
This estimate will later feed into probabilistic arguments about random
restrictions.-/
lemma sum_sensitivityAt_le (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) :
    (∑ x : Point n, sensitivityAt f x) ≤ Fintype.card (Point n) * s := by
  classical
  have hforall : ∀ x ∈ (Finset.univ : Finset (Point n)), sensitivityAt f x ≤ s := by
    intro x _; exact le_trans (sensitivityAt_le (f := f) (x := x)) hs
  simpa [Finset.card_univ] using
    Finset.sum_le_card_nsmul
      (s := (Finset.univ : Finset (Point n)))
      (f := fun x => sensitivityAt f x) (n := s) hforall

/--
Counting sensitive edges two ways shows that the sum of all coordinate
sensitivities equals the sum of pointwise sensitivities over the Boolean cube.
-/
lemma sum_coordSensitivity_eq_sum_sensitivityAt (f : BFunc n) :
    (∑ i : Fin n, coordSensitivity f i)
      = ∑ x : Point n, sensitivityAt f x := by
  classical
  have h₁ :
      (∑ i : Fin n, coordSensitivity f i)
        = ∑ i : Fin n, ∑ x : Point n,
            if f x ≠ f (Point.update x i (! x i)) then 1 else 0 := by
    simp [coordSensitivity, Finset.card_filter]
  calc
    (∑ i : Fin n, coordSensitivity f i)
        = ∑ i : Fin n, ∑ x : Point n,
            if f x ≠ f (Point.update x i (! x i)) then 1 else 0 := h₁
    _ = ∑ x : Point n, ∑ i : Fin n,
            if f x ≠ f (Point.update x i (! x i)) then 1 else 0 := by
            simpa using Finset.sum_comm
    _ = ∑ x : Point n, sensitivityAt f x := by
            simp [sensitivityAt, Finset.card_filter, ne_comm]

/--
The total coordinate sensitivity inherits the same upper bound as the sum of
pointwise sensitivities.
-/
lemma sum_coordSensitivity_le (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) :
    (∑ i : Fin n, coordSensitivity f i)
      ≤ Fintype.card (Point n) * s := by
  classical
  simpa [sum_coordSensitivity_eq_sum_sensitivityAt (f := f)] using
    sum_sensitivityAt_le (f := f) (hs := hs)

/- ### Globally insensitive coordinates -/

/--
`insensitiveCoords f` collects all coordinates that `f` completely ignores:
flipping such an index in any input never changes the value of `f`.
-/
def insensitiveCoords (f : BFunc n) : Finset (Fin n) :=
  (Finset.univ.filter fun i : Fin n => coordSensitivity f i = 0)

@[simp] lemma mem_insensitiveCoords (f : BFunc n) (i : Fin n) :
    i ∈ insensitiveCoords f ↔ coordSensitivity f i = 0 := by
  classical
  simp [insensitiveCoords]

/--
Globally insensitive coordinates are locally insensitive at every point.
-/
lemma insensitiveCoords_subset_insensitiveCoordsAt (f : BFunc n) (x : Point n) :
    insensitiveCoords f ⊆ insensitiveCoordsAt f x := by
  classical
  intro i hi
  have hzero := (mem_insensitiveCoords (f := f) (i := i)).1 hi
  have hins := (coordSensitivity_eq_zero_iff (f := f) (i := i)).1 hzero
  have hx := hins x
  have hx' : f (Point.update x i (!x i)) = f x := by
    simpa using hx.symm
  exact Finset.mem_filter.mpr ⟨by simp, hx'⟩

lemma insensitiveCoords_card_le (f : BFunc n) (x : Point n) :
    (insensitiveCoords f).card ≤ (insensitiveCoordsAt f x).card := by
  classical
  exact Finset.card_le_card (insensitiveCoords_subset_insensitiveCoordsAt (f := f) (x := x))


/--
Flipping any finite set of globally insensitive coordinates leaves the function
unchanged.  The equality holds for every input simultaneously, making it a
convenient tool for reasoning about multiple bit flips at once.
-/
lemma eval_flip_subset_insensitiveCoords (f : BFunc n)
    {S : Finset (Fin n)} (hS : S ⊆ insensitiveCoords f) :
    ∀ x : Point n, f (Point.flip x S) = f x := by
  classical
  revert hS
  refine Finset.induction_on S ?base ?step
  · intro _ x; simp
  · intro i S hiS hrec hsubset x
    -- Separate out the newly inserted coordinate `i`.
    have hS' : S ⊆ insensitiveCoords f := by
      intro j hj; exact hsubset (by simp [hj])
    have hi : i ∈ insensitiveCoords f := hsubset (by simp)
    -- Flipping the remaining set after `i` keeps the value.
    have htail := hrec hS' (Point.flip x ({i} : Finset (Fin n)))
    -- Flipping `i` alone keeps the value as well.
    have hall :=
      (coordSensitivity_eq_zero_iff (f := f) (i := i)).1
        ((mem_insensitiveCoords (f := f) (i := i)).1 hi)
    have hhead : f (Point.flip x ({i} : Finset (Fin n))) = f x := by
      simpa using (hall x).symm
    -- Reassociate the full flip as first toggling `i` and then `S`.
    have hdecomp :=
      Point.flip_insert (x := x) (S := S) (i := i) (hi := hiS)
    -- Combine the three pieces.
    have : f (Point.flip x (insert i S)) = f (Point.flip x ({i} : Finset _)) := by
      simpa [hdecomp] using htail
    exact this.trans hhead

@[simp] lemma eval_flip_subset_insensitiveCoords' (f : BFunc n) (x : Point n)
    {S : Finset (Fin n)} (hS : S ⊆ insensitiveCoords f) :
    f (Point.flip x S) = f x :=
  (eval_flip_subset_insensitiveCoords (f := f) (S := S) (hS := hS)) x

@[simp] lemma eval_flip_subset_insensitiveCoords_symm (f : BFunc n) (x : Point n)
    {S : Finset (Fin n)} (hS : S ⊆ insensitiveCoords f) :
    f x = f (Point.flip x S) := by
  simpa using (eval_flip_subset_insensitiveCoords' (f := f) (x := x) (S := S)
      (hS := hS)).symm

/-- If two points differ only on globally insensitive coordinates, then the
Boolean function takes the same value on both. -/
lemma eval_eq_of_eq_on_compl_insensitive (f : BFunc n)
    {A : Finset (Fin n)} (hA : A ⊆ insensitiveCoords f)
    {x y : Point n} (hy : ∀ i ∉ A, y i = x i) :
    f y = f x := by
  classical
  -- Flip precisely the coordinates where `x` and `y` disagree; the set of such
  -- indices is a subset of the globally insensitive ones, so the previous lemma
  -- applies.
  have hflip :=
    eval_flip_subset_insensitiveCoords' (f := f) (x := x)
      (S := A.filter fun i => y i ≠ x i)
      (hS := by
        intro i hi
        exact hA (by
          -- membership in the filtered set implies membership in `A`
          exact (Finset.mem_filter.mp hi).1))
  -- Re-express `y` via a flip of `x` over the disagreement set.
  have : Point.flip x (A.filter fun i => y i ≠ x i) = y :=
    Point.flip_eq_of_eq_on_compl (x := x) (y := y) (A := A) hy
  simpa [this] using hflip

/--
Coordinates outside the essential `support` are precisely the globally
insensitive ones.  This characterisation will make it convenient to switch
between the two viewpoints.
-/
@[simp] lemma mem_insensitiveCoords_iff_not_mem_support
    (f : BFunc n) (i : Fin n) :
    i ∈ insensitiveCoords f ↔ i ∉ support f := by
  classical
  constructor
  · intro hi
    have hzero := (mem_insensitiveCoords (f := f) (i := i)).1 hi
    -- Translate the numerical condition `coordSensitivity f i = 0` to
    -- the semantic statement that flipping `i` never changes `f`.
    have hins :=
      (coordSensitivity_eq_zero_iff (f := f) (i := i)).1 hzero
    -- The absence of any witness of change means `i` cannot belong to
    -- the essential support.
    refine fun hmem => ?_
    rcases (mem_support_iff (f := f) (i := i)).1 hmem with ⟨x, hx⟩
    exact hx (by simpa using hins x)
  · intro hi
    -- If `i` is not in the support, every flip of `i` leaves `f`
    -- unchanged.  Converting this fact via `coordSensitivity` yields
    -- membership in `insensitiveCoords`.
    have hins : ∀ x : Point n, f x = f (Point.update x i (!x i)) := by
      intro x
      have hnot : ¬ f x ≠ f (Point.update x i (!x i)) := by
        intro hx
        have : i ∈ support f :=
          (mem_support_iff (f := f) (i := i)).2 ⟨x, by simpa [hx]⟩
        exact hi this
      simpa using not_not.mp hnot
    have hzero := (coordSensitivity_eq_zero_iff (f := f) (i := i)).2 hins
    exact (mem_insensitiveCoords (f := f) (i := i)).2 hzero

/--
A coordinate belongs to the essential `support` exactly when flipping it
changes the function somewhere, i.e. when its coordinate sensitivity is
non‑zero.
-/
@[simp] lemma mem_support_iff_coordSensitivity_ne_zero
    (f : BFunc n) (i : Fin n) :
    i ∈ support f ↔ coordSensitivity f i ≠ 0 := by
  classical
  constructor
  · intro hi
    have hnot : i ∉ insensitiveCoords f := by
      intro hmem
      have hns :=
        (mem_insensitiveCoords_iff_not_mem_support (f := f) (i := i)).1 hmem
      exact hns hi
    -- A zero coordinate sensitivity would contradict the above.
    by_contra hzero
    have hmem : i ∈ insensitiveCoords f :=
      (mem_insensitiveCoords (f := f) (i := i)).2 hzero
    exact hnot hmem
  · intro hne
    by_contra hns
    have hins : i ∈ insensitiveCoords f :=
      (mem_insensitiveCoords_iff_not_mem_support (f := f) (i := i)).2 hns
    have hzero := (mem_insensitiveCoords (f := f) (i := i)).1 hins
    exact hne hzero

/-- Membership in the global `support` forces positive coordinate sensitivity. -/
lemma coordSensitivity_pos_of_mem_support (f : BFunc n) (i : Fin n)
    (hi : i ∈ support f) : 0 < coordSensitivity f i := by
  have hne := (mem_support_iff_coordSensitivity_ne_zero (f := f) (i := i)).1 hi
  exact Nat.pos_of_ne_zero hne

/--
A coordinate belonging to the `support` contributes at least two to the
total coordinate sensitivity.  Flipping such an index changes the value of
`f` on both endpoints of the corresponding cube edge, yielding two distinct
witnesses in the defining set for `coordSensitivity`.
-/
lemma two_le_coordSensitivity_of_mem_support (f : BFunc n) (i : Fin n)
    (hi : i ∈ support f) : 2 ≤ coordSensitivity f i := by
  classical
  -- Extract a point `x` witnessing the dependence on coordinate `i`.
  rcases (mem_support_iff (f := f) (i := i)).1 hi with ⟨x, hx⟩
  -- Consider both endpoints of the sensitive edge along `i`.
  let y := Point.update x i (! x i)
  have hxmem : x ∈
      (Finset.univ.filter fun z : Point n =>
        f z ≠ f (Point.update z i (! z i))) := by
    simpa [hx]
  have hymem : y ∈
      (Finset.univ.filter fun z : Point n =>
        f z ≠ f (Point.update z i (! z i))) := by
    have hupdate : (x.update i !x i).update i (x i) = x := by
      funext j; by_cases hj : j = i <;> simp [Point.update, hj]
    have hneq : f y ≠ f ((x.update i !x i).update i (x i)) := by
      simpa [y, hupdate] using ne_comm.mp hx
    have hneq' : f y ≠ f (y.update i (!y i)) := by
      simpa [y] using hneq
    refine Finset.mem_filter.mpr ?_
    exact ⟨by simp [y], hneq'⟩
  -- The two endpoints form a size-two subset of the full set.
  have hsubset : ({x, y} : Finset (Point n)) ⊆
      (Finset.univ.filter fun z : Point n =>
        f z ≠ f (Point.update z i (! z i))) := by
    intro z hz; rcases Finset.mem_insert.mp hz with hz | hz
    · simpa [hz] using hxmem
    · have hz' : z = y := by simpa [Finset.mem_singleton] using hz
      simpa [hz'] using hymem
  have hcard := Finset.card_le_card hsubset
  have hxy : x ≠ y := by
    intro h; have : x i = y i := congrArg (fun t => t i) h
    have : x i = ! x i := by simpa [y] using this
    cases hxbool : x i <;> simp [hxbool] at this
  have hpair : ({x, y} : Finset (Point n)).card = 2 := by
    simp [y, hxy]
  -- Translate back to `coordSensitivity`.
  have htwo : 2 ≤
      (Finset.univ.filter fun z : Point n =>
        f z ≠ f (Point.update z i (! z i))).card := by
    simpa [hpair] using hcard
  simpa [coordSensitivity] using htwo

/--
The essential `support` forms the complement of `insensitiveCoords`.
-/
lemma support_eq_univ_sdiff_insensitiveCoords (f : BFunc n) :
    support f = (Finset.univ \ insensitiveCoords f) := by
  classical
  ext i
  by_cases hi : i ∈ support f
  · -- Membership in the support precludes global insensitivity.
    have hnot : i ∉ insensitiveCoords f := by
      intro hmem
      have hns :=
        (mem_insensitiveCoords_iff_not_mem_support (f := f) (i := i)).1 hmem
      exact hns hi
    simp [Finset.mem_sdiff, hi, hnot]
  · -- Outside the support, the coordinate is globally insensitive.
    have hins : i ∈ insensitiveCoords f :=
      (mem_insensitiveCoords_iff_not_mem_support (f := f) (i := i)).2 hi
    simp [Finset.mem_sdiff, hi, hins]

/--
The counts of globally insensitive coordinates and the support add up to the
dimension `n`.
-/
lemma insensitiveCoords_card_add_support_card (f : BFunc n) :
    (insensitiveCoords f).card + (support f).card = n := by
  classical
  -- Partition `Finset.univ` into the insensitive coordinates and their
  -- complement.  The partition lemma immediately gives the desired sum.
  -- The complement of `insensitiveCoords f` has cardinality
  -- `n - (insensitiveCoords f).card`.
  have hcompl := Finset.card_compl (s := insensitiveCoords f)
  have hsupport : (support f).card = n - (insensitiveCoords f).card := by
    simpa [support_eq_univ_sdiff_insensitiveCoords, Finset.card_univ] using hcompl
  -- Rearranging finishes the proof.
  have hle : (insensitiveCoords f).card ≤ n := by
    simpa [Finset.card_univ] using (Finset.card_le_univ (s := insensitiveCoords f))
  have hsum := Nat.add_sub_of_le hle
  simpa [hsupport, Nat.add_comm] using hsum

/--
If the `support` misses some coordinate, then there exists a globally
insensitive index.  This provides a concrete direction along which `f`
never changes.
-/
lemma exists_insensitiveCoord_of_support_card_lt (f : BFunc n)
    (h : (support f).card < n) :
    ∃ i : Fin n, i ∈ insensitiveCoords f := by
  classical
  -- Translate the cardinality relation into an explicit formula for
  -- `|insensitiveCoords f|`.
  have hcard := insensitiveCoords_card_add_support_card (f := f)
  -- Rearrange `|insensitive| + |support| = n` to express the size of the
  -- insensitive coordinates.
  have hins : (insensitiveCoords f).card = n - (support f).card := by
    -- Subtract `|support|` from both sides of the equality.
    have h := congrArg (fun t => t - (support f).card) hcard
    -- The left-hand side simplifies using `Nat.add_sub_cancel`.
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  -- The hypothesis `|support| < n` ensures at least one insensitive coordinate.
  have hpos : 0 < (insensitiveCoords f).card := by
    have : 0 < n - (support f).card := Nat.sub_pos_of_lt h
    simpa [hins] using this
  -- Extract a witness from the positive cardinality.
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, hi⟩

/--
The subcube obtained by freezing the `support` of `f` has dimension equal to
the number of globally insensitive coordinates.  Intuitively, every coordinate
outside the support remains free because `f` never reads it.
-/
lemma supportSubcube_dim_eq_insensitiveCoords_card (f : BFunc n) (x : Point n) :
    (supportSubcube (f := f) (x := x)).dimension = (insensitiveCoords f).card := by
  classical
  -- Rewrite the dimension using the definition of `supportSubcube`.
  have hdim := supportSubcube_dim (f := f) (x := x)
  -- Express `n - |support|` as `|insensitiveCoords|` using the previous lemma.
  have hle : (support f).card ≤ n := by
    simpa [Finset.card_univ] using (Finset.card_le_univ (s := support f))
  -- Use the cardinality relation `|insensitive| + |support| = n` to rewrite.
  have hn : n = (insensitiveCoords f).card + (support f).card := by
    -- Symmetrise and commute the sum to match the `Nat.add_sub_cancel` pattern.
    simpa [Nat.add_comm] using
      (insensitiveCoords_card_add_support_card (f := f)).symm
  -- Subtracting `|support|` from both sides yields `|insensitive|`.
  have h : n - (support f).card = (insensitiveCoords f).card := by
    simpa [hn] using
      Nat.add_sub_cancel (insensitiveCoords f).card (support f).card
  simpa [hdim] using h

/- ### Subcubes from local insensitivity -/

/--
`insensitiveSubcubeAt f x` freezes every coordinate that is *sensitive* at the
point `x`, allowing the locally insensitive ones to vary freely.  By
construction this subcube always contains `supportSubcube f x`, but it may be
larger whenever `x` has additional coordinates where `f` does not react to
single-bit flips.
-/
noncomputable def insensitiveSubcubeAt (f : BFunc n) (x : Point n) : Subcube n where
  idx := Finset.univ \ insensitiveCoordsAt f x
  val := fun i _ => x i

@[simp] lemma mem_insensitiveSubcubeAt {f : BFunc n} {x y : Point n} :
    (y ∈ₛ insensitiveSubcubeAt f x) ↔
      ∀ i ∈ Finset.univ \ insensitiveCoordsAt f x, y i = x i := by
  rfl

/-- Flipping any subset of coordinates locally insensitive at `x` stays inside
`insensitiveSubcubeAt f x`. -/
@[simp] lemma flip_mem_insensitiveSubcubeAt (f : BFunc n) (x : Point n)
    {S : Finset (Fin n)} (hS : S ⊆ insensitiveCoordsAt f x) :
    Point.flip x S ∈ₛ insensitiveSubcubeAt f x := by
  classical
  -- Membership requires equality on all *sensitive* coordinates.
  refine (mem_insensitiveSubcubeAt (f := f) (x := x) (y := Point.flip x S)).2 ?_
  intro i hi
  have hnot : i ∉ insensitiveCoordsAt f x := (Finset.mem_sdiff.mp hi).2
  have hi' : i ∉ S := fun hSi => hnot (hS hSi)
  -- With `i ∉ S` the flipped point agrees with `x` on `i`.
  simpa [Point.flip_apply_not_mem hi']

/--
`insensitiveSubcubeAt` can be described purely by the set of locally
insensitive coordinates: a mass flip of a finite set `S` stays inside the
subcube exactly when no sensitive coordinate is flipped.
-/
@[simp] lemma flip_mem_insensitiveSubcubeAt_iff (f : BFunc n) (x : Point n)
    {S : Finset (Fin n)} :
    (Point.flip x S ∈ₛ insensitiveSubcubeAt f x)
      ↔ S ⊆ insensitiveCoordsAt f x := by
  classical
  constructor
  · intro h i hiS
    -- If flipping `i` were to leave the subcube, it would contradict the
    -- membership assumption.
    by_contra hnot
    -- `i` lies in the complement of `insensitiveCoordsAt f x`.
    have hiCompl : i ∈ Finset.univ \ insensitiveCoordsAt f x := by
      have : i ∈ (Finset.univ : Finset (Fin n)) := by simp
      exact Finset.mem_sdiff.mpr ⟨this, hnot⟩
    -- Membership in the subcube asserts equality with `x` on `i`.
    have hmem :=
      (mem_insensitiveSubcubeAt (f := f) (x := x)
        (y := Point.flip x S)).1 h i hiCompl
    -- But flipping a listed coordinate toggles the bit, a contradiction.
    have hflip : Point.flip x S i = !x i := by
      simpa [Point.flip_apply_mem hiS]
    cases hxi : x i with
    | false =>
        have : False := by simpa [hxi, hflip] using hmem
        cases this
    | true =>
        have : False := by simpa [hxi, hflip] using hmem
        cases this
  · intro hS
    exact flip_mem_insensitiveSubcubeAt (f := f) (x := x) (S := S) (hS := hS)

/-- The base point always belongs to its `insensitiveSubcubeAt`. -/
@[simp] lemma mem_insensitiveSubcubeAt_self (f : BFunc n) (x : Point n) :
    x ∈ₛ insensitiveSubcubeAt f x := by
  classical
  have : (∅ : Finset (Fin n)) ⊆ insensitiveCoordsAt f x := by simp
  simpa [Point.flip_empty] using
    (flip_mem_insensitiveSubcubeAt (f := f) (x := x) (S := ∅) (hS := this))

/-- The dimension of `insensitiveSubcubeAt` counts exactly the locally
insensitive coordinates at the base point `x`. -/
lemma insensitiveSubcubeAt_dim (f : BFunc n) (x : Point n) :
    (insensitiveSubcubeAt f x).dimension = (insensitiveCoordsAt f x).card := by
  classical
  -- The coordinates outside `insensitiveCoordsAt` are precisely the locally
  -- sensitive ones, whose number is `sensitivityAt f x`.
  have hcompl_card :
      (Finset.univ \ insensitiveCoordsAt f x).card = sensitivityAt f x := by
    have hcompl :
        (Finset.univ \ insensitiveCoordsAt f x) =
          Finset.univ.filter (fun i =>
            f (Point.update x i (!x i)) ≠ f x) := by
      ext i
      have : i ∈ (Finset.univ : Finset (Fin n)) := by simp
      by_cases hi : f (Point.update x i (!x i)) = f x
      · simp [insensitiveCoordsAt, hi, this]
      · simp [insensitiveCoordsAt, hi, this]
    simpa [hcompl, sensitivityAt]
  -- Rewrite the dimension via the complement cardinality and use the previous
  -- equality together with `insensitiveCoordsAt_card_eq`.
  have hdim : (insensitiveSubcubeAt f x).dimension = n - sensitivityAt f x := by
    simp [insensitiveSubcubeAt, Subcube.dimension, hcompl_card]
  have hrev := (insensitiveCoordsAt_card_eq (f := f) (x := x)).symm
  simpa [hdim]
    using hrev

/-- If the local sensitivity at `x` is bounded by `s`, the subcube freezing all
sensitive coordinates at `x` has dimension at least `n - s`. -/
lemma insensitiveSubcubeAt_dim_ge (f : BFunc n) (x : Point n) {s : ℕ}
    (hs : sensitivityAt f x ≤ s) :
    n - s ≤ (insensitiveSubcubeAt f x).dimension := by
  classical
  -- Translate the statement to cardinalities via `insensitiveSubcubeAt_dim`.
  have hcard := insensitiveCoordsAt_card_ge (f := f) (x := x) (hs := hs)
  simpa [insensitiveSubcubeAt_dim (f := f) (x := x)] using hcard

/-- A global sensitivity bound immediately gives the same lower dimension bound
for `insensitiveSubcubeAt` at every point. -/
lemma insensitiveSubcubeAt_dim_ge_of_global (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (x : Point n) :
    n - s ≤ (insensitiveSubcubeAt f x).dimension :=
  by
    -- Apply the local version to each point using `sensitivityAt_le`.
    have hsx : sensitivityAt f x ≤ s :=
      le_trans (sensitivityAt_le (f := f) (x := x)) hs
    exact insensitiveSubcubeAt_dim_ge (f := f) (x := x) (hs := hsx)

/--
From a global sensitivity bound `s > 0` we also obtain the coarser dimension
estimate `n / (2*s)` for `insensitiveSubcubeAt`.
-/
lemma insensitiveSubcubeAt_dim_ge_div (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (hspos : 0 < s) (x : Point n) :
    n / (2 * s) ≤ (insensitiveSubcubeAt f x).dimension := by
  classical
  have hcard :
      n / (2 * s) ≤ (insensitiveCoordsAt f x).card :=
    insensitiveCoordsAt_card_ge_div (f := f) (hs := hs)
      (hspos := hspos) (x := x)
  simpa [insensitiveSubcubeAt_dim (f := f) (x := x)] using hcard

/--
When the local sensitivity at `x` vanishes, every coordinate is locally
insensitive at that point.  Hence `insensitiveCoordsAt f x` equals the entire
index set `univ`.
-/
lemma insensitiveCoordsAt_eq_univ_of_sensitivityAt_zero (f : BFunc n)
    (x : Point n) (h : sensitivityAt f x = 0) :
    insensitiveCoordsAt f x = (Finset.univ : Finset (Fin n)) := by
  classical
  -- The set of sensitive coordinates at `x` is empty.
  have hcard :
      (Finset.univ.filter fun i : Fin n => f (Point.update x i (!x i)) ≠ f x).card
        = 0 := by simpa [sensitivityAt] using h
  have hempty :
      (Finset.univ.filter fun i : Fin n => f (Point.update x i (!x i)) ≠ f x)
        = (∅ : Finset (Fin n)) := Finset.card_eq_zero.mp hcard
  -- Any index in `univ` is therefore locally insensitive.
  refine Finset.eq_univ_of_forall ?_
  intro i
  have hiuniv : i ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hnotmem : i ∉ Finset.univ.filter
      (fun j : Fin n => f (Point.update x j (!x j)) ≠ f x) := by
    simpa [hempty] using (Finset.not_mem_empty (i := i))
  have hmem_equiv :
      i ∈ Finset.univ.filter (fun j : Fin n => f (Point.update x j (!x j)) ≠ f x)
        ↔ f (Point.update x i (!x i)) ≠ f x := by
    constructor
    · intro hmem; exact (Finset.mem_filter.mp hmem).2
    · intro hne; exact Finset.mem_filter.mpr ⟨hiuniv, hne⟩
  have hneq : ¬ f (Point.update x i (!x i)) ≠ f x :=
    (not_congr hmem_equiv).1 hnotmem
  have heq : f (Point.update x i (!x i)) = f x := not_not.mp hneq
  exact Finset.mem_filter.mpr ⟨hiuniv, heq⟩

/--
If the local sensitivity at `x` is zero, the subcube freezing the sensitive
coordinates is the whole cube and thus has dimension `n`.
-/
lemma insensitiveSubcubeAt_dim_eq_n_of_sensitivityAt_zero (f : BFunc n)
    (x : Point n) (h : sensitivityAt f x = 0) :
    (insensitiveSubcubeAt f x).dimension = n := by
  classical
  have hset :=
    insensitiveCoordsAt_eq_univ_of_sensitivityAt_zero (f := f) (x := x) (h := h)
  simpa [insensitiveSubcubeAt_dim (f := f) (x := x), hset]

/-- All coordinates that are locally sensitive at `x` must lie in the global
`support` of `f`.  Indeed, any globally insensitive coordinate is insensitive at
every point. -/
lemma sensitiveCoordsAt_subset_support (f : BFunc n) (x : Point n) :
    (Finset.univ \ insensitiveCoordsAt f x) ⊆ support f := by
  classical
  intro i hi
  rcases Finset.mem_sdiff.mp hi with ⟨-, hi⟩
  by_contra hnot
  have hins : i ∈ insensitiveCoords f :=
    (mem_insensitiveCoords_iff_not_mem_support (f := f) (i := i)).2 hnot
  have hi' :=
    insensitiveCoords_subset_insensitiveCoordsAt (f := f) (x := x) hins
  exact hi hi'

/-- Every point of `supportSubcube f x` also lies in the larger subcube that
freezes only the coordinates sensitive at `x`. -/
lemma supportSubcube_subset_insensitiveSubcubeAt (f : BFunc n) (x : Point n)
    {y : Point n} (hy : y ∈ₛ supportSubcube f x) :
    y ∈ₛ insensitiveSubcubeAt f x := by
  classical
  -- The membership condition for `supportSubcube` grants equality on `support`.
  have hsupport :=
    (mem_supportSubcube (f := f) (x := x) (y := y)).1 hy
  -- To show membership in `insensitiveSubcubeAt`, it suffices to check equality
  -- on the smaller set `univ \ insensitiveCoordsAt f x`.
  refine (mem_insensitiveSubcubeAt (f := f) (x := x) (y := y)).2 ?_
  intro i hi
  have hi' : i ∈ support f := (sensitiveCoordsAt_subset_support (f := f) (x := x)) hi
  exact hsupport i hi'

/-- Consequently, the dimension of `supportSubcube` is bounded above by the
dimension of `insensitiveSubcubeAt` since the latter allows at least as many
free coordinates. -/
lemma supportSubcube_dim_le_insensitiveSubcubeAt_dim (f : BFunc n)
    (x : Point n) :
    (supportSubcube f x).dimension ≤ (insensitiveSubcubeAt f x).dimension := by
  classical
  -- Translate dimensions to cardinalities of insensitive coordinate sets.
  have h := insensitiveCoords_card_le (f := f) (x := x)
  have hsupp := supportSubcube_dim_eq_insensitiveCoords_card (f := f) (x := x)
  have hins := insensitiveSubcubeAt_dim (f := f) (x := x)
  simpa [hsupp, hins] using h

/--
Any subcube that is monochromatic for `f` and contains a point `x` must lie
inside `insensitiveSubcubeAt f x`.  Thus every element of such a subcube
agrees with `x` on all locally sensitive coordinates.-/
lemma monochromaticSubcube_subset_insensitiveSubcubeAt (f : BFunc n)
    {R : Subcube n} (x : Point n) (hxR : x ∈ₛ R)
    (hmono : Subcube.monochromaticFor R f) {y : Point n}
    (hy : y ∈ₛ R) :
    y ∈ₛ insensitiveSubcubeAt f x := by
  classical
  -- Membership requires agreement with `x` on all sensitive coordinates.
  refine (mem_insensitiveSubcubeAt (f := f) (x := x) (y := y)).2 ?_
  intro i hi
  have hins : i ∉ insensitiveCoordsAt f x := (Finset.mem_sdiff.mp hi).2
  -- Suppose `y` disagrees with `x` on `i`; we derive a contradiction.
  by_contra hneq
  -- Then `i` cannot be fixed by `R`.
  have hiidx : i ∉ R.idx := by
    intro hi'
    have hx := hxR i hi'
    have hy' := hy i hi'
    exact hneq (hy'.trans hx.symm)
  -- Flipping `i` from `x` stays within the subcube.
  have hxflip : Point.flip x ({i} : Finset (Fin n)) ∈ₛ R := by
    intro j hj
    have hji : j ≠ i := by
      intro hji; exact hiidx (hji ▸ hj)
    have hxj := hxR j hj
    simp [Point.flip, hji, hxj]
  -- Monochromaticity equates the function values of `x` and the flipped point.
  rcases hmono with ⟨b, hb⟩
  have hxval : f x = b := hb hxR
  have hflipval := hb (x := Point.flip x ({i} : Finset (Fin n))) hxflip
  have heq : f (Point.flip x ({i} : Finset (Fin n))) = f x := by
    simpa [hxval, Point.flip_singleton] using hflipval
  -- But sensitivity at `x` forbids this equality.
  have hne : f (Point.flip x ({i} : Finset (Fin n))) ≠ f x := by
    have : f (Point.update x i (! x i)) ≠ f x := by
      intro h
      apply hins
      have hiuniv : i ∈ (Finset.univ : Finset (Fin n)) := by simp
      exact Finset.mem_filter.2 ⟨hiuniv, h⟩
    simpa [Point.flip_singleton] using this
  exact hne heq

/--
The dimension of any monochromatic subcube through `x` is bounded above by the
dimension of `insensitiveSubcubeAt f x`, since all its free coordinates must be
locally insensitive at `x`.-/
lemma monochromaticSubcube_dim_le_insensitiveSubcubeAt_dim (f : BFunc n)
    {R : Subcube n} (x : Point n) (hxR : x ∈ₛ R)
    (hmono : Subcube.monochromaticFor R f) :
    R.dimension ≤ (insensitiveSubcubeAt f x).dimension := by
  classical
  -- The free coordinates of `R` are locally insensitive at `x`.
  have hsubset : (Finset.univ \ R.idx) ⊆ insensitiveCoordsAt f x := by
    intro j hj
    have hjnot : j ∉ R.idx := (Finset.mem_sdiff.mp hj).2
    -- Flipping a free coordinate remains inside `R`.
    have hjflip : Point.flip x ({j} : Finset (Fin n)) ∈ₛ R := by
      intro i hi
      have hji : i ≠ j := by
        intro h; exact hjnot (h ▸ hi)
      have hxi := hxR i hi
      simp [Point.flip, hji, hxi]
    -- Consequently the flip lies in `insensitiveSubcubeAt`.
    have hins' :=
      monochromaticSubcube_subset_insensitiveSubcubeAt (f := f)
        (R := R) (x := x) (hxR := hxR) (hmono := hmono)
        (y := Point.flip x ({j} : Finset (Fin n))) (hy := hjflip)
    -- Extract the membership as a subset condition on coordinates.
    have :=
      (flip_mem_insensitiveSubcubeAt_iff (f := f) (x := x)
        (S := ({j} : Finset (Fin n)))).1 hins'
    simpa using this
  -- Compare cardinalities to translate the subset relation to dimensions.
  have hcard := Finset.card_le_card hsubset
  -- Rewrite both dimensions via cardinalities of free coordinates.
  have hdimR : R.dimension = (Finset.univ \ R.idx).card := by
    have hsdiff :
        (Finset.univ \ R.idx).card
          = (Finset.univ : Finset (Fin n)).card - R.idx.card :=
      Finset.card_sdiff (Finset.subset_univ R.idx)
    have : (Finset.univ \ R.idx).card = n - R.idx.card := by
      simpa [Finset.card_univ] using hsdiff
    simpa [Subcube.dimension, this]
  have hinsdim := insensitiveSubcubeAt_dim (f := f) (x := x)
  simpa [hdimR, hinsdim] using hcard

/-- Flipping coordinates outside the fixed index set of a subcube keeps the
point inside that subcube. -/
@[simp] lemma flip_mem_subcube (R : Subcube n) (x : Point n)
    (hx : x ∈ₛ R) {S : Finset (Fin n)}
    (hS : S ⊆ Finset.univ \ R.idx) :
    Point.flip x S ∈ₛ R := by
  classical
  intro i hi
  -- A coordinate from `R.idx` cannot appear in the flipped set `S`.
  have hnot : i ∉ Finset.univ \ R.idx := by
    intro hmem
    exact (Finset.mem_sdiff.mp hmem).2 hi
  have hiS : i ∉ S := fun hmem => hnot (hS hmem)
  -- Hence the flipped point agrees with `x` on `i`, and `x` already satisfies
  -- the defining equation of `R`.
  have hx_eq : x i = R.val i hi := hx i hi
  have hflip : Point.flip x S i = x i := by
    simpa [Point.flip_apply_not_mem hiS]
  simpa [hflip, hx_eq]

/-- Inside a monochromatic subcube `R`, flipping any subset of its free
coordinates leaves the function value unchanged. -/
lemma eval_flip_subset_of_monochromatic (f : BFunc n) {R : Subcube n}
    (x : Point n) (hx : x ∈ₛ R)
    (hmono : Subcube.monochromaticFor R f)
    {S : Finset (Fin n)} (hS : S ⊆ Finset.univ \ R.idx) :
    f (Point.flip x S) = f x := by
  classical
  -- The flipped point remains within `R`.
  have hmem : Point.flip x S ∈ₛ R :=
    flip_mem_subcube (R := R) (x := x) (hx := hx) (S := S) (hS := hS)
  -- Monochromaticity equates the function values.
  rcases hmono with ⟨b, hb⟩
  have hxval : f x = b := hb hx
  have hflipval : f (Point.flip x S) = b := hb hmem
  simpa [hxval] using hflipval

/--
Points within a monochromatic subcube all evaluate to the same Boolean value.
This specialises `eval_flip_subset_of_monochromatic` to two arbitrary members
of the subcube.
-/
lemma eval_eq_of_mem_of_monochromatic (f : BFunc n) {R : Subcube n}
    (hmono : Subcube.monochromaticFor R f) {x y : Point n}
    (hx : x ∈ₛ R) (hy : y ∈ₛ R) : f x = f y := by
  classical
  rcases hmono with ⟨c, hc⟩
  have hx' : f x = c := hc hx
  have hy' : f y = c := hc hy
  exact hx'.trans hy'.symm

/-- From a monochromatic subcube we can extract an explicit set of coordinates
that is insensitive to flips around the base point.  The set consists of all
free coordinates of the subcube and its size equals the subcube's dimension. -/
lemma insensitive_subset_of_monochromatic_subcube (f : BFunc n)
    {R : Subcube n} (x : Point n) (hx : x ∈ₛ R)
    (hmono : Subcube.monochromaticFor R f) :
    ∃ A : Finset (Fin n), R.dimension = A.card ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A →
        f (Point.flip x T) = f x := by
  classical
  -- Take the set of all free coordinates of `R`.
  let A := Finset.univ \ R.idx
  have hAcard' : A.card = n - R.idx.card := by
    -- Cardinality of the complement of `R.idx` inside the universe.
    simpa [A, Finset.card_univ]
      using Finset.card_sdiff (Finset.subset_univ R.idx)
  have hdim : R.dimension = n - R.idx.card := by
    simp [Subcube.dimension]
  refine ⟨A, ?_, ?_⟩
  · -- The size of `A` matches the dimension of `R`.
    simpa [hdim, hAcard']
  · intro T hT
    -- Flipping any subset of `A` preserves membership in `R` and hence the
    -- function value.
    have hsubset : T ⊆ Finset.univ \ R.idx := by
      simpa [A] using hT
    exact
      eval_flip_subset_of_monochromatic (f := f) (R := R)
        (x := x) (hx := hx) (hmono := hmono)
        (S := T) (hS := hsubset)

/--
From a monochromatic subcube whose dimension dominates a numerical bound `k`, we
can extract an explicit set of at least `k` coordinates around the base point on
which the Boolean function is insensitive to simultaneous flips.  This is a
convenient wrapper around `insensitive_subset_of_monochromatic_subcube` that
tracks only a lower bound on the dimension instead of the exact equality. -/
lemma exists_large_insensitive_subset_of_monochromatic_subcube (f : BFunc n)
    {R : Subcube n} {x : Point n} (hx : x ∈ₛ R)
    (hmono : Subcube.monochromaticFor R f) {k : ℕ}
    (hk : k ≤ R.dimension) :
    ∃ A : Finset (Fin n), k ≤ A.card ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  -- Obtain the full set of free coordinates provided by the previous lemma.
  obtain ⟨A, hdim, hflip⟩ :=
    insensitive_subset_of_monochromatic_subcube (f := f) (R := R)
      (x := x) (hx := hx) (hmono := hmono)
  -- Translate the dimension lower bound into a cardinality statement.
  have hcard : k ≤ A.card := by
    simpa [hdim] using hk
  exact ⟨A, hcard, hflip⟩

/--
Extracts an insensitive set of coordinates from a monochromatic subcube and
records explicitly that every coordinate in the set is locally insensitive at
the base point.  This variant packages the subset condition
`A ⊆ insensitiveCoordsAt f x` which is often convenient when composing with
lemmas about local insensitive regions.
-/
lemma exists_large_insensitive_subset_of_monochromatic_subcube_subset_insensitiveCoordsAt
    (f : BFunc n) {R : Subcube n} {x : Point n} (hx : x ∈ₛ R)
    (hmono : Subcube.monochromaticFor R f) {k : ℕ}
    (hk : k ≤ R.dimension) :
    ∃ A : Finset (Fin n), k ≤ A.card ∧
      A ⊆ insensitiveCoordsAt f x ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  -- Start with the insensitive set given by the previous lemma.
  obtain ⟨A, hAcard, hAflip⟩ :=
    exists_large_insensitive_subset_of_monochromatic_subcube
      (f := f) (R := R) (x := x) (hx := hx) (hmono := hmono) (hk := hk)
  -- Every element of `A` is locally insensitive because singletons preserve
  -- the function value.
  have hAsub : A ⊆ insensitiveCoordsAt f x := by
    intro i hiA
    -- Apply the flip invariance to the singleton `{i}`.
    have hflip_single : f (Point.flip x {i}) = f x := by
      have hsubset : ({i} : Finset (Fin n)) ⊆ A := by
        intro j hj
        -- `j` can only be `i` in this singleton, yielding membership in `A`.
        have hj_eq : j = i := by simpa [Finset.mem_singleton] using hj
        simpa [hj_eq] using hiA
      simpa using hAflip (T := {i}) hsubset
    -- Rewrite the flip in terms of `update` to match the definition.
    have hflip_single' : f (x.update i (!x i)) = f x := by
      simpa [Point.flip] using hflip_single
    -- Conclude that `i` is insensitive at `x` via the definition.
    have : i ∈ insensitiveCoordsAt f x := by
      simp [insensitiveCoordsAt, Finset.mem_filter, hflip_single']
    exact this
  -- Assemble the result with the strengthened subset information.
  refine ⟨A, hAcard, hAsub, ?_⟩
  intro T hT
  exact hAflip hT

/--
Flipping a subset of globally insensitive coordinates keeps a point inside the
subcube determined by the `support`.
-/
@[simp] lemma flip_mem_supportSubcube (f : BFunc n) (x : Point n)
    {S : Finset (Fin n)} (hS : S ⊆ insensitiveCoords f) :
    Point.flip x S ∈ₛ supportSubcube f x := by
  classical
  -- Membership requires agreement with `x` on all support coordinates.
  refine (mem_supportSubcube (f := f) (x := x) (y := Point.flip x S)).2 ?_
  intro i hi
  have : i ∉ S := by
    have hnot : i ∉ insensitiveCoords f := by
      intro hins
      have hmem :=
        (mem_insensitiveCoords_iff_not_mem_support (f := f) (i := i)).1 hins
      exact hmem hi
    exact fun hmem => hnot (hS hmem)
  simpa [Point.flip, this] 

/--
Membership of a flipped point in `supportSubcube f x` precisely asserts that
the flipped coordinates come from the globally insensitive set.
-/
@[simp] lemma flip_mem_supportSubcube_iff (f : BFunc n) (x : Point n)
    {S : Finset (Fin n)} :
    (Point.flip x S ∈ₛ supportSubcube f x) ↔ S ⊆ insensitiveCoords f := by
  classical
  constructor
  · intro hmem
    intro i hiS
    -- If `i` belonged to the support, flipping it would violate membership.
    have hi_flip : Point.flip x S i = !x i := by simp [Point.flip, hiS]
    have hi_ne : Point.flip x S i ≠ x i := by
      cases hxi : x i <;> simp [hi_flip, hxi]
    have hsupport :=
      (mem_supportSubcube (f := f) (x := x) (y := Point.flip x S)).1 hmem
    have : i ∉ support f := by
      intro hi
      have := hsupport i hi
      exact hi_ne this
    exact
      (mem_insensitiveCoords_iff_not_mem_support (f := f) (i := i)).2 this
  · intro hS
    exact flip_mem_supportSubcube (f := f) (x := x) (S := S) hS

@[simp] lemma mem_supportSubcube_self (f : BFunc n) (x : Point n) :
    x ∈ₛ supportSubcube f x := by
  classical
  -- Membership demands agreement with `x` on all support coordinates,
  -- which holds trivially for `x` itself.
  refine (mem_supportSubcube (f := f) (x := x) (y := x)).2 ?_
  intro i hi
  rfl

/--
The subcube that freezes every support coordinate around a reference point
`x` is monochromatic for `f`.
-/
lemma supportSubcube_monochromaticFor (f : BFunc n) (x : Point n) :
    Subcube.monochromaticFor (supportSubcube f x) f := by
  classical
  refine ⟨f x, ?_⟩
  intro y hy
  simpa using
    (supportSubcube_monochromatic (f := f) (x := x) (y := y) hy)

/- ### Support bounds via coordinate sensitivity -/

lemma support_card_le_sum_coordSensitivity (f : BFunc n) :
    (support f).card ≤ ∑ i : Fin n, coordSensitivity f i := by
  classical
  -- Each support coordinate contributes at least one to the total sensitivity.
  have hforall : ∀ i ∈ support f, 1 ≤ coordSensitivity f i := by
    intro i hi
    have hne :=
      (mem_support_iff_coordSensitivity_ne_zero (f := f) (i := i)).1 hi
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
  have hcard_le :
      (support f).card ≤ ∑ i ∈ support f, coordSensitivity f i := by
    -- Compare the two sums coordinatewise using `hforall`.
    have hsum_le :
        ∑ i ∈ support f, (1 : ℕ) ≤ ∑ i ∈ support f, coordSensitivity f i :=
      Finset.sum_le_sum (by intro i hi; exact hforall i hi)
    simpa using hsum_le
  -- Extending the sum to all coordinates can only increase its value.
  have hsubset :
      (∑ i ∈ support f, coordSensitivity f i)
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), coordSensitivity f i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _)
      (by intro i hi hnot; exact Nat.zero_le _)
  exact le_trans hcard_le hsubset

lemma support_card_le (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) :
    (support f).card ≤ Fintype.card (Point n) * s := by
  have hsum := support_card_le_sum_coordSensitivity (f := f)
  have htotal := sum_coordSensitivity_le (f := f) (hs := hs)
  exact le_trans hsum htotal

/--
If the sensitivity of `f` is bounded by `s`, then at least
`n - Fintype.card (Point n) * s` coordinates are globally insensitive.
Intuitively, the function can depend on at most `2^n * s` coordinates, so the
remaining directions are ignored everywhere.
-/
lemma insensitiveCoords_card_ge_of_global (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) :
    n - Fintype.card (Point n) * s ≤ (insensitiveCoords f).card := by
  classical
  -- Bound the size of the support via the total coordinate sensitivity.
  have hupper : (support f).card ≤ Fintype.card (Point n) * s :=
    support_card_le (f := f) (hs := hs)
  -- Express the number of globally insensitive coordinates through the
  -- complement of the support.
  have hsum := insensitiveCoords_card_add_support_card (f := f)
  have hins : (insensitiveCoords f).card = n - (support f).card := by
    have := congrArg (fun t => t - (support f).card) hsum
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  -- Subtract the support bound from `n` and rewrite via the above identity.
  have hineq :
      n - Fintype.card (Point n) * s ≤ n - (support f).card :=
    Nat.sub_le_sub_left hupper _
  simpa [hins] using hineq

/--
From the previous bound we can extract an explicit set of globally insensitive
coordinates with that cardinality.
-/
lemma exists_insensitiveCoords_card_eq_of_global (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) :
    ∃ A ⊆ insensitiveCoords f,
      A.card = n - Fintype.card (Point n) * s := by
  classical
  have hcard :
      n - Fintype.card (Point n) * s ≤ (insensitiveCoords f).card :=
    insensitiveCoords_card_ge_of_global (f := f) (hs := hs)
  exact Finset.exists_subset_card_eq (s := insensitiveCoords f)
    (n := n - Fintype.card (Point n) * s) hcard

/--
Given a global sensitivity bound, the `supportSubcube` around any point has
large dimension.  This subcube fixes every coordinate on which `f` may depend,
so its dimension counts the globally insensitive directions. -/
lemma supportSubcube_dim_ge_of_global (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (x : Point n) :
    n - Fintype.card (Point n) * s ≤ (supportSubcube f x).dimension := by
  classical
  -- The dimension equals the number of globally insensitive coordinates.
  have hdim := supportSubcube_dim_eq_insensitiveCoords_card (f := f) (x := x)
  -- Bound the cardinality of `insensitiveCoords f` via the sensitivity cap.
  have hcard := insensitiveCoords_card_ge_of_global (f := f) (hs := hs)
  -- Rewrite the inequality through the dimension equality.
  simpa [hdim] using hcard

/--
Starting from any collection of globally insensitive coordinates `A`, we can
build a subcube around a reference point `x` where the Boolean function `f`
remains constant.  The resulting subcube varies exactly on the coordinates in
`A` and therefore has dimension `|A|`.-/
lemma monochromaticSubcube_of_insensitive_subset (f : BFunc n)
    {A : Finset (Fin n)} (hA : A ⊆ insensitiveCoords f) (x : Point n) :
    ∃ R : Subcube n,
      (x ∈ₛ R) ∧ Subcube.monochromaticFor R f ∧ R.dimension = A.card := by
  classical
  -- Freeze all coordinates outside `A` to their values in `x`.
  let I := (Finset.univ \ A)
  let R := Agreement.Subcube.fromPoint x I
  have hxmem : x ∈ₛ R := by
    -- The reference point always belongs to its own subcube.
    simp [R]
  have hmono : Subcube.monochromaticFor R f := by
    refine ⟨f x, ?_⟩
    intro y hy
    -- Coordinates where `y` differs from `x` form a finite set `T`.
    let T := Finset.univ.filter fun i : Fin n => y i ≠ x i
    have hTyx : T ⊆ A := by
      -- Membership in `R` forces agreement on `I = univ \ A`.
      have hy' := (Agreement.fromPoint_mem (x := x) (I := I)).1 hy
      intro i hiT
      have hy_ne : y i ≠ x i := (Finset.mem_filter.mp hiT).2
      have hi_notI : i ∉ I := by
        intro hiI; exact hy_ne (hy' i hiI)
      -- Translate `i ∉ (univ \ A)` to `i ∈ A`.
      have hi_univ : i ∈ (Finset.univ : Finset (Fin n)) := by simp
      have hcontr : ¬ (i ∈ (Finset.univ : Finset (Fin n)) ∧ i ∉ A) := by
        simpa [I, Finset.mem_sdiff] using hi_notI
      have : ¬ i ∉ A := fun hnotA => hcontr ⟨hi_univ, hnotA⟩
      exact Classical.not_not.mp this
    -- Express `y` as flipping `x` on the coordinates `T`.
    have hy_eq : y = Point.flip x T := by
      funext i; by_cases hiT : i ∈ T
      · have hy_ne : y i ≠ x i := (Finset.mem_filter.mp hiT).2
        cases hx : x i <;> cases hyi : y i <;>
          simp [Point.flip, T, hiT, hx, hyi] at hy_ne ⊢
      · have hy_eq' : y i = x i := by
          have : y i ≠ x i → False := by
            intro hy_ne; exact hiT (Finset.mem_filter.mpr ⟨by simp, hy_ne⟩)
          have : ¬ y i ≠ x i := by intro hy_ne; exact this hy_ne
          exact Classical.not_not.mp this
        simp [Point.flip, T, hiT, hy_eq']
    -- `T` consists of globally insensitive coordinates, so flipping it leaves `f` unchanged.
    have hTins : T ⊆ insensitiveCoords f := fun i hi => hA (hTyx hi)
    simpa [hy_eq] using
      (eval_flip_subset_insensitiveCoords' (f := f) (x := x)
        (S := T) (hS := hTins))
  -- Compute the dimension of `R` from the size of `A`.
  have hIcard : I.card = n - A.card := by
    have hAuniv : A ⊆ (Finset.univ : Finset (Fin n)) := by intro i hi; simp
    simpa [I, Finset.card_univ] using
      Finset.card_sdiff (s := A) (t := (Finset.univ : Finset (Fin n))) hAuniv
  have hdim : R.dimension = A.card := by
    have hdim' : R.dimension = n - I.card := by
      simpa [R] using (Agreement.dimension_fromPoint (x := x) (I := I))
    have hAle : A.card ≤ n := by
      simpa [Finset.card_univ] using (Finset.card_le_univ (s := A))
    have : n - (n - A.card) = A.card := Nat.sub_sub_self hAle
    simpa [hIcard, hdim', this]
  exact ⟨R, hxmem, hmono, hdim⟩

/--
If a set of coordinates `A` leaves the function `f` unchanged whenever the
input agrees with `x` outside `A`, then the points obtained by varying only the
bits of `A` form a monochromatic subcube.  The subcube has dimension `|A|` and
is anchored at the reference point `x`.
-/
lemma monochromaticSubcube_of_pointwise (f : BFunc n) (x : Point n)
    {A : Finset (Fin n)}
    (hA : ∀ ⦃y : Point n⦄, (∀ i ∉ A, y i = x i) → f y = f x) :
    ∃ R : Subcube n, (x ∈ₛ R) ∧ Subcube.monochromaticFor R f ∧
      R.dimension = A.card := by
  classical
  -- Freeze all coordinates outside `A` to the values in `x`.
  let R : Subcube n := Agreement.Subcube.fromPoint x (Finset.univ \ A)
  have hx : x ∈ₛ R := by
    -- The reference point obviously lies in the constructed subcube.
    simp [R]
  -- Points inside `R` agree with `x` on the complement of `A`.
  have hmono : Subcube.monochromaticFor R f := by
    refine ⟨f x, ?_⟩
    intro y hy
    have hy' := (Agreement.fromPoint_mem (x := x) (I := Finset.univ \ A)).1 hy
    -- Convert membership information into agreement outside `A`.
    have hy_eq : ∀ i ∉ A, y i = x i := by
      intro i hi
      have hi' : i ∈ Finset.univ \ A := by
        simpa [Finset.mem_sdiff, hi]
      exact hy' i hi'
    -- Apply the invariance hypothesis to conclude.
    simpa [hy_eq] using hA (y := y) hy_eq
  -- Compute the dimension: `idx` fixes exactly the complement of `A`.
  have hdim : R.dimension = A.card := by
    have hAuniv : A ⊆ (Finset.univ : Finset (Fin n)) := by
      intro i hi; simp
    have hcard : (Finset.univ \ A).card = n - A.card := by
      simpa [Finset.card_univ] using
        Finset.card_sdiff (s := A) (t := (Finset.univ : Finset (Fin n))) hAuniv
    -- Translate the dimension formula via the index size.
    have : R.dimension = n - (Finset.univ \ A).card := by
      simpa [R] using
        (Agreement.dimension_fromPoint (x := x) (I := Finset.univ \ A))
    have hAle : A.card ≤ n := by
      simpa [Finset.card_univ] using (Finset.card_le_univ (s := A))
    have hsub : n - (n - A.card) = A.card := Nat.sub_sub_self hAle
    simpa [hcard, this, hsub]
  exact ⟨R, hx, hmono, hdim⟩

/--
Given a global sensitivity bound, every point lies in a "monochromatic"
subcube obtained by freely varying a large set of globally insensitive
coordinates.  While this cardinality bound `n - 2^n * s` is weaker than the
conjectured `n / (2*s)` estimate, it provides a constructive witness that will
be sufficient for subsequent refactorings of the decision-tree argument.
-/
lemma exists_large_insensitive_subset (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (x : Point n) :
    ∃ A : Finset (Fin n),
      n - Fintype.card (Point n) * s ≤ A.card ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  -- Extract a concrete subset of globally insensitive coordinates of the
  -- desired size.  Flipping any subset of these coordinates leaves `f`
  -- unchanged everywhere by `eval_flip_subset_insensitiveCoords`.
  obtain ⟨A, hAsub, hAcard⟩ :=
    exists_insensitiveCoords_card_eq_of_global (f := f) (hs := hs)
  refine ⟨A, ?_, ?_⟩
  · -- The cardinality inequality follows from the exact count above.
    simpa [hAcard]
  · -- Any subset `T` of `A` consists of globally insensitive coordinates.
    intro T hT
    have hTins : T ⊆ insensitiveCoords f := fun i hi => hAsub (hT hi)
    simpa using
      (eval_flip_subset_insensitiveCoords' (f := f) (x := x)
        (S := T) (hS := hTins))

/-- A pointwise reformulation of `exists_large_insensitive_subset` that avoids
explicit flip sets.  Any point agreeing with `x` outside the chosen set `A`
evaluates to the same function value. -/
lemma exists_large_insensitive_subset_pointwise (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (x : Point n) :
    ∃ A : Finset (Fin n),
      n - Fintype.card (Point n) * s ≤ A.card ∧
      ∀ ⦃y : Point n⦄, (∀ i ∉ A, y i = x i) → f y = f x := by
  classical
  obtain ⟨A, hAcard, hAflip⟩ :=
    exists_large_insensitive_subset (f := f) (hs := hs) (x := x)
  refine ⟨A, hAcard, ?_⟩
  intro y hy
  -- Express `y` as a flip of `x` over the coordinates where they differ.
  have hy_eq :
      Point.flip x (A.filter fun i => y i ≠ x i) = y :=
    Point.flip_eq_of_eq_on_compl (x := x) (y := y) (A := A) hy
  have hTsub : (A.filter fun i => y i ≠ x i) ⊆ A :=
    Finset.filter_subset _ _
  -- Apply the flip-based version to this disagreement set.
  have := hAflip (T := A.filter fun i => y i ≠ x i) hTsub
  simpa [hy_eq] using this

/--
In regimes where the coarse global bound already forces at least
`n / (2*s)` globally insensitive coordinates, we can upgrade
`exists_large_insensitive_subset` to meet the desired lower bound.  This
lemma is a temporary stepping stone towards the conjectured unconditional
`n / (2*s)` estimate.
-/
lemma exists_large_insensitive_subset_div_of_small (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hsmall : Fintype.card (Point n) * s ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ A : Finset (Fin n),
      n / (2 * s) ≤ A.card ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  -- Extract the globally insensitive coordinates and compare cardinalities.
  obtain ⟨A, hAcard, hAflip⟩ :=
    exists_large_insensitive_subset (f := f) (hs := hs) (x := x)
  refine ⟨A, ?_, hAflip⟩
  -- First show `n / (2*s)` is bounded by `n - 2^n * s` via the assumption `hsmall`.
  have hineq : n / (2 * s) ≤ n - Fintype.card (Point n) * s := by
    -- Translate `hsmall : 2^n * s ≤ n - n/(2*s)` into an additive inequality.
    -- Adding `n / (2*s)` to both sides gives the claim through `Nat.le_sub_of_add_le`.
    -- Convert the hypothesis `hsmall` into an inequality of the form
    -- `a + b ≤ n` required by `Nat.le_sub_of_add_le`.
    have hsum := Nat.add_le_add_right hsmall (n / (2 * s))
    have hdivle : n / (2 * s) ≤ n := Nat.div_le_self _ _
    have hcancel : n - n / (2 * s) + n / (2 * s) = n :=
      Nat.sub_add_cancel hdivle
    have hsum' : Fintype.card (Point n) * s + n / (2 * s) ≤ n := by
      simpa [hcancel, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
    have hsum'' : n / (2 * s) + Fintype.card (Point n) * s ≤ n := by
      simpa [Nat.add_comm] using hsum'
    exact Nat.le_sub_of_add_le (a := n / (2 * s))
      (b := Fintype.card (Point n) * s) hsum''
  -- Combine with the cardinality bound from `exists_large_insensitive_subset`.
  exact le_trans hineq hAcard

/--
When the coarse inequality `2^n * s ≤ n - n/(2*s)` holds, the large insensitive
set from `exists_large_insensitive_subset_div_of_small` yields a sizeable
monochromatic subcube around any reference point.  This strengthens
`exists_large_monochromatic_subcube` under the numeric assumption and will serve
as a preparatory step towards the general `n/(2*s)` bound without extra
constraints.-/
lemma exists_large_monochromatic_subcube_div_of_small (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hsmall : Fintype.card (Point n) * s ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ R : Subcube n,
      (x ∈ₛ R) ∧ Subcube.monochromaticFor R f ∧
      n / (2 * s) ≤ R.dimension := by
  classical
  -- Obtain the large flip‑invariant set `A` and turn it into a subcube.
  obtain ⟨A, hAcard, hAflip⟩ :=
    exists_large_insensitive_subset_div_of_small (f := f) (s := s)
      (hs := hs) (hsmall := hsmall) (x := x)
  -- Freeze the complement of `A` to the values of `x`.
  let R : Subcube n := { idx := Finset.univ \ A, val := fun i _ => x i }
  have hxR : x ∈ₛ R := by
    intro i hi
    simp [R] at hi
    simpa [R]
  -- Any point in `R` differs from `x` only on `A`, hence evaluates identically.
  have hmono : Subcube.monochromaticFor R f := by
    refine ⟨f x, ?_⟩
    intro y hy
    -- Express `y` as a flip of `x` on a subset of `A`.
    have hyagree : ∀ i ∉ A, y i = x i := by
      intro i hiA
      have hi : i ∈ Finset.univ \ A := by
        simp [Finset.mem_sdiff, hiA]
      exact hy i hi
    have hy_eq : Point.flip x (A.filter fun i => y i ≠ x i) = y :=
      Point.flip_eq_of_eq_on_compl (x := x) (y := y) (A := A) hyagree
    have hTsub : (A.filter fun i => y i ≠ x i) ⊆ A :=
      Finset.filter_subset _ _
    have := hAflip (T := A.filter fun i => y i ≠ x i) hTsub
    simpa [hy_eq]
  -- Translate the cardinality bound on `A` to the dimension of `R`.
  have hdim_card : R.dimension = A.card := by
    have hidx : R.idx.card = n - A.card := by
      have := Finset.card_sdiff (Finset.subset_univ A)
      simpa [R] using this
    have hdim0 : R.dimension = n - (n - A.card) := by
      simpa [Subcube.dimension, R, hidx]
    have hA_le_n : A.card ≤ n := by
      simpa using
        (Finset.card_le_univ (s := A) : A.card ≤ Fintype.card (Fin n))
    have hsub : n - (n - A.card) = A.card := Nat.sub_sub_self hA_le_n
    simpa [hsub] using hdim0
  have hdim : n / (2 * s) ≤ R.dimension := by
    simpa [hdim_card] using hAcard
  exact ⟨R, hxR, hmono, hdim⟩

/--
If the essential `support` of a Boolean function is small, we can directly
extract a large set of globally insensitive coordinates.  The bound `n - m`
describes how many variables remain freely flippable whenever the support has
size at most `m`.

This lemma provides a convenient bridge between combinatorial information about
the `support` and the flip-invariance guarantee required later in the
construction of low-sensitivity covers.
-/
lemma exists_large_insensitive_subset_of_support_le (f : BFunc n)
    {m : ℕ} (hsupp : (support f).card ≤ m) (x : Point n) :
    ∃ A : Finset (Fin n),
      n - m ≤ A.card ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  -- Use all globally insensitive coordinates as the candidate set.
  refine ⟨insensitiveCoords f, ?_, ?_⟩
  · -- Convert the support bound into a lower bound on the complement.
    have hins : (insensitiveCoords f).card = n - (support f).card := by
      -- Rearrange the equality `|insensitive| + |support| = n`.
      have hsum := insensitiveCoords_card_add_support_card (f := f)
      -- Subtract `|support|` from both sides.
      have := congrArg (fun t => t - (support f).card) hsum
      -- Simplify the resulting expression.
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this
    -- Comparing with `m` yields the desired inequality.
    have hineq : n - m ≤ n - (support f).card :=
      Nat.sub_le_sub_left hsupp _
    simpa [hins] using hineq
  · -- Flipping coordinates outside the support leaves `f` unchanged.
    intro T hT
    have hTins : T ⊆ insensitiveCoords f := hT
    simpa using
      (eval_flip_subset_insensitiveCoords' (f := f) (x := x)
        (S := T) (hS := hTins))

/--
A specialised variant of `exists_large_insensitive_subset_of_support_le` that
expresses the lower bound using the familiar `n / (2*s)` quantity.  Supplying a
numerical `support` estimate in this form will often be easier in applications.
-/
lemma exists_large_insensitive_subset_div_of_support (f : BFunc n) {s : ℕ}
    (hsupp : (support f).card ≤ n - n / (2 * s)) (x : Point n) :
    ∃ A : Finset (Fin n),
      n / (2 * s) ≤ A.card ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  -- Instantiate the previous lemma with `m = n - n/(2*s)`.
  obtain ⟨A, hAcard, hAflip⟩ :=
    exists_large_insensitive_subset_of_support_le (f := f)
      (m := n - n / (2 * s)) (hsupp := hsupp) (x := x)
  -- Rewrite the resulting lower bound into the desired form.
  have hdiv : n / (2 * s) ≤ n := Nat.div_le_self _ _
  have hrewrite : n - (n - n / (2 * s)) = n / (2 * s) :=
    Nat.sub_sub_self hdiv
  have hbound : n / (2 * s) ≤ A.card := by
    simpa [hrewrite] using hAcard
  exact ⟨A, hbound, hAflip⟩

/--
A pointwise variant of `exists_large_insensitive_subset_div_of_support`.  Any
point agreeing with the reference input `x` outside the extracted set `A`
evaluates to the same function value.
-/
lemma exists_large_insensitive_subset_pointwise_div_of_support
    (f : BFunc n) {s : ℕ}
    (hsupp : (support f).card ≤ n - n / (2 * s)) (x : Point n) :
    ∃ A : Finset (Fin n),
      n / (2 * s) ≤ A.card ∧
      ∀ ⦃y : Point n⦄, (∀ i ∉ A, y i = x i) → f y = f x := by
  classical
  -- Extract the insensitive set using the flip-based lemma.
  obtain ⟨A, hAcard, hAflip⟩ :=
    exists_large_insensitive_subset_div_of_support (f := f) (s := s)
      (hsupp := hsupp) (x := x)
  refine ⟨A, hAcard, ?_⟩
  intro y hy
  -- Express `y` as a flip of `x` over the coordinates where they differ.
  have hy_eq :
      Point.flip x (A.filter fun i => y i ≠ x i) = y :=
    Point.flip_eq_of_eq_on_compl (x := x) (y := y) (A := A) hy
  have hsub : (A.filter fun i => y i ≠ x i) ⊆ A :=
    Finset.filter_subset _ _
  -- Apply the flip invariance to this disagreement set.
  simpa [hy_eq] using hAflip (T := A.filter fun i => y i ≠ x i) hsub

/--
Combines the two routes to a large insensitive set.  If either the coarse
inequality `2^n * s ≤ n - n/(2*s)` holds or the essential `support` of `f`
is bounded by `n - n/(2*s)`, there exists a subset of at least `n/(2*s)`
coordinates around the point `x` on which simultaneous flips leave the
function value unchanged.
-/
lemma exists_large_insensitive_subset_div (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hbound :
        Fintype.card (Point n) * s ≤ n - n / (2 * s) ∨
        (support f).card ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ A : Finset (Fin n), n / (2 * s) ≤ A.card ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  cases hbound with
  | inl hsmall =>
      exact
        exists_large_insensitive_subset_div_of_small (f := f) (s := s)
          (hs := hs) (hsmall := hsmall) (x := x)
  | inr hsupp =>
      exact
        exists_large_insensitive_subset_div_of_support (f := f) (s := s)
          (hsupp := hsupp) (x := x)

/--
Pointwise version of `exists_large_insensitive_subset_div`.  Any point that
agrees with `x` outside the produced set takes the same value of `f`.
-/
lemma exists_large_insensitive_subset_pointwise_div (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hbound :
        Fintype.card (Point n) * s ≤ n - n / (2 * s) ∨
        (support f).card ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ A : Finset (Fin n), n / (2 * s) ≤ A.card ∧
      ∀ ⦃y : Point n⦄, (∀ i ∉ A, y i = x i) → f y = f x := by
  classical
  obtain ⟨A, hAcard, hAflip⟩ :=
    exists_large_insensitive_subset_div (f := f) (s := s)
      (hs := hs) (hbound := hbound) (x := x)
  refine ⟨A, hAcard, ?_⟩
  intro y hy
  -- Express `y` as a flip of `x` on the disagreement set.
  have hy_eq :
      Point.flip x (A.filter fun i => y i ≠ x i) = y :=
    Point.flip_eq_of_eq_on_compl (x := x) (y := y) (A := A) hy
  have hsub : (A.filter fun i => y i ≠ x i) ⊆ A :=
    Finset.filter_subset _ _
  simpa [hy_eq] using hAflip (T := A.filter fun i => y i ≠ x i) hsub

/--
From the combined insensitive-set lemma we obtain a monochromatic subcube of
dimension at least `n/(2*s)` whenever one of the numeric side conditions holds.
-/
lemma exists_large_monochromatic_subcube_div (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hbound :
        Fintype.card (Point n) * s ≤ n - n / (2 * s) ∨
        (support f).card ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ R : Subcube n, (x ∈ₛ R) ∧ Subcube.monochromaticFor R f ∧
      n / (2 * s) ≤ R.dimension := by
  classical
  obtain ⟨A, hAcard, hApoint⟩ :=
    exists_large_insensitive_subset_pointwise_div (f := f) (s := s)
      (hs := hs) (hbound := hbound) (x := x)
  obtain ⟨R, hxR, hmono, hdim⟩ :=
    monochromaticSubcube_of_pointwise (f := f) (x := x) (A := A)
      (hA := hApoint)
  refine ⟨R, hxR, hmono, ?_⟩
  simpa [hdim] using hAcard

/--
The `n/(2*s)`-dimensional subcube obtained above lies entirely inside the
local `insensitiveSubcubeAt` of the base point.  This ensures that subsequent
flips remain within the region where the set of sensitive coordinates is
frozen.-/
lemma exists_large_monochromatic_subcube_div_subset_insensitiveSubcubeAt
    (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hbound :
        Fintype.card (Point n) * s ≤ n - n / (2 * s) ∨
        (support f).card ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ R : Subcube n,
      (x ∈ₛ R) ∧
      Subcube.monochromaticFor R f ∧
      n / (2 * s) ≤ R.dimension ∧
      (∀ y : Point n, (y ∈ₛ R) → y ∈ₛ insensitiveSubcubeAt f x) := by
  classical
  obtain ⟨R, hxR, hmono, hdim⟩ :=
    exists_large_monochromatic_subcube_div (f := f) (s := s)
      (hs := hs) (hbound := hbound) (x := x)
  have hsub :
      ∀ y : Point n, (y ∈ₛ R) → y ∈ₛ insensitiveSubcubeAt f x := by
    intro y hy
    exact monochromaticSubcube_subset_insensitiveSubcubeAt
      (f := f) (R := R) (x := x) (hxR := hxR) (hmono := hmono)
      (y := y) (hy := hy)
  exact ⟨R, hxR, hmono, hdim, hsub⟩

/--
Combining the nested subcube construction with the subset version of
`exists_large_insensitive_subset_of_monochromatic_subcube` yields a concrete set
of locally insensitive coordinates inside `insensitiveCoordsAt f x` whose size
meets the `n/(2*s)` bound.  Flipping any subset of this set leaves the function
value at `x` unchanged.
-/
lemma exists_large_insensitive_subset_div_subset_insensitiveCoordsAt
    (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hbound :
        Fintype.card (Point n) * s ≤ n - n / (2 * s) ∨
        (support f).card ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ A : Finset (Fin n),
      n / (2 * s) ≤ A.card ∧
      A ⊆ insensitiveCoordsAt f x ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  -- Obtain the large monochromatic subcube that sits inside the local
  -- insensitive region around `x`.
  obtain ⟨R, hxR, hmono, hdim, _⟩ :=
    exists_large_monochromatic_subcube_div_subset_insensitiveSubcubeAt
      (f := f) (s := s) (hs := hs) (hbound := hbound) (x := x)
  -- Extract the free coordinates as an insensitive set.
  obtain ⟨A, hAcard, hAsub, hAflip⟩ :=
    exists_large_insensitive_subset_of_monochromatic_subcube_subset_insensitiveCoordsAt
      (f := f) (R := R) (x := x) (hx := hxR) (hmono := hmono)
      (hk := hdim)
  exact ⟨A, hAcard, hAsub, hAflip⟩

/--
Pointwise reformulation of
`exists_large_insensitive_subset_div_subset_insensitiveCoordsAt`.  Any point
that agrees with `x` outside the extracted set `A` yields the same function
value.
-/
lemma exists_large_insensitive_subset_pointwise_div_subset_insensitiveCoordsAt
    (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hbound :
        Fintype.card (Point n) * s ≤ n - n / (2 * s) ∨
        (support f).card ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ A : Finset (Fin n),
      n / (2 * s) ≤ A.card ∧
      A ⊆ insensitiveCoordsAt f x ∧
      ∀ ⦃y : Point n⦄, (∀ i ∉ A, y i = x i) → f y = f x := by
  classical
  obtain ⟨A, hAcard, hAsub, hAflip⟩ :=
    exists_large_insensitive_subset_div_subset_insensitiveCoordsAt
      (f := f) (s := s) (hs := hs) (hbound := hbound) (x := x)
  refine ⟨A, hAcard, hAsub, ?_⟩
  intro y hy
  -- Represent `y` as a flip over the coordinates where it differs from `x`.
  have hy_eq :
      Point.flip x (A.filter fun i => y i ≠ x i) = y :=
    Point.flip_eq_of_eq_on_compl (x := x) (y := y) (A := A) hy
  have hsubset : (A.filter fun i => y i ≠ x i) ⊆ A :=
    Finset.filter_subset _ _
  -- Apply the flip-based invariance.
  simpa [hy_eq] using hAflip (T := A.filter fun i => y i ≠ x i) hsubset

/--
Combining the pointwise variant with `monochromaticSubcube_of_pointwise` yields a
monochromatic subcube whose free coordinates lie inside
`insensitiveCoordsAt f x`.  The subcube has dimension at least `n/(2*s)` and can
be freely flipped along locally insensitive directions.
-/
lemma exists_large_monochromatic_subcube_div_subset_insensitiveCoordsAt
    (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hbound :
        Fintype.card (Point n) * s ≤ n - n / (2 * s) ∨
        (support f).card ≤ n - n / (2 * s))
    (x : Point n) :
    ∃ R : Subcube n,
      (x ∈ₛ R) ∧
      Subcube.monochromaticFor R f ∧
      n / (2 * s) ≤ R.dimension ∧
      (Finset.univ \ R.idx) ⊆ insensitiveCoordsAt f x := by
  classical
  -- Extract a large locally insensitive set with pointwise invariance.
  obtain ⟨A, hAcard, hAsub, hApoint⟩ :=
    exists_large_insensitive_subset_pointwise_div_subset_insensitiveCoordsAt
      (f := f) (s := s) (hs := hs) (hbound := hbound) (x := x)
  -- Build the subcube that varies exactly on the coordinates in `A`.
  let R : Subcube n := Agreement.Subcube.fromPoint x (Finset.univ \ A)
  have hxR : x ∈ₛ R := by
    -- The reference point obviously belongs to this subcube.
    simp [R]
  have hmono : Subcube.monochromaticFor R f := by
    refine ⟨f x, ?_⟩
    intro y hy
    -- Points in `R` coincide with `x` outside `A`.
    have hy' := (Agreement.fromPoint_mem (x := x) (I := Finset.univ \ A)).1 hy
    have hy_eq : ∀ i ∉ A, y i = x i := by
      intro i hi
      have hi' : i ∈ Finset.univ \ A := by simpa [Finset.mem_sdiff, hi]
      exact hy' i hi'
    simpa [hy_eq] using hApoint (y := y) hy_eq
  -- Compute the dimension of the constructed subcube.
  have hcard : (Finset.univ \ A).card = n - A.card := by
    simpa [Finset.card_univ] using (Finset.card_compl (s := A))
  have hA_le : A.card ≤ n := by
    simpa [Finset.card_univ] using (Finset.card_le_univ A)
  have hdim : R.dimension = A.card := by
    have hsub' : n - (n - A.card) = A.card := Nat.sub_sub_self hA_le
    have hsub : n - (Finset.univ \ A).card = A.card := by
      simpa [hcard] using hsub'
    simpa [R, Subcube.dimension] using hsub
  -- Translate the cardinality bound to the subcube dimension.
  have hdim_ge : n / (2 * s) ≤ R.dimension := by
    simpa [hdim] using hAcard
  -- Free coordinates of `R` are contained in `A` and thus locally insensitive.
  have hfree_subset : (Finset.univ \ R.idx) ⊆ insensitiveCoordsAt f x := by
    intro i hi
    -- Extract membership information from the set difference.
    have hi_not : i ∉ R.idx := (Finset.mem_sdiff.mp hi).2
    -- Since `R.idx = univ \ A`, absence from `R.idx` forces membership in `A`.
    have hiA : i ∈ A := by
      have hi_univ : i ∈ (Finset.univ : Finset (Fin n)) := by simp
      by_contra hnotA
      have hmem : i ∈ R.idx := by
        -- If `i ∉ A` then `i` would belong to `R.idx = univ \ A`.
        dsimp [R]
        exact Finset.mem_sdiff.mpr ⟨hi_univ, hnotA⟩
      exact hi_not hmem
    -- Membership in `A` implies local insensitivity via `hAsub`.
    exact hAsub hiA
  exact ⟨R, hxR, hmono, hdim_ge, hfree_subset⟩

/--
A bound on the size of the essential `support` immediately forces many
globally insensitive coordinates.  This numerical corollary will be
useful when converting combinatorial information about the `support`
into explicit flip-invariant sets.
-/
lemma insensitiveCoords_card_ge_div_of_support (f : BFunc n) {s : ℕ}
    (hsupp : (support f).card ≤ n - n / (2 * s)) :
    n / (2 * s) ≤ (insensitiveCoords f).card := by
  classical
  -- Turn the assumption into an additive inequality.
  have hsupp_plus : (support f).card + n / (2 * s) ≤ n := by
    have := Nat.add_le_add_right hsupp (n / (2 * s))
    have hdivle : n / (2 * s) ≤ n := Nat.div_le_self _ _
    have hcancel : n - n / (2 * s) + n / (2 * s) = n :=
      Nat.sub_add_cancel hdivle
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hcancel] using this
  have hsupp_plus' : n / (2 * s) + (support f).card ≤ n := by
    simpa [Nat.add_comm] using hsupp_plus
  -- Remove the support contribution from both sides.
  have hineq : n / (2 * s) ≤ n - (support f).card :=
    Nat.le_sub_of_add_le hsupp_plus'
  -- Express the number of insensitive coordinates via the support.
  have hins : (insensitiveCoords f).card = n - (support f).card := by
    have hsum := insensitiveCoords_card_add_support_card (f := f)
    have := congrArg (fun t => t - (support f).card) hsum
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  -- Combine the two inequalities.
  simpa [hins] using hineq

/--
Combining the global sensitivity bound with the coarse numerical condition
`2^n * s ≤ n - n/(2*s)` directly yields many globally insensitive coordinates.
This lemma ties the rough sensitivity estimate to the refined `n/(2*s)`
bound via the general support-based corollary above.
-/
lemma insensitiveCoords_card_ge_div_of_small (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hsmall : Fintype.card (Point n) * s ≤ n - n / (2 * s)) :
    n / (2 * s) ≤ (insensitiveCoords f).card := by
  classical
  -- First bound the size of the support using the sensitivity estimate.
  have hsupp := support_card_le (f := f) (hs := hs)
  have hsupp' : (support f).card ≤ n - n / (2 * s) :=
    hsupp.trans hsmall
  -- Apply the support-based insensitive coordinate bound.
  exact
    insensitiveCoords_card_ge_div_of_support (f := f) (s := s)
      (hsupp := hsupp')

/--
Combines the two numeric routes to many globally insensitive coordinates.  If
either the coarse inequality `2^n * s ≤ n - n/(2*s)` holds or the size of the
`support` is bounded by `n - n/(2*s)`, then at least `n/(2*s)` coordinates are
globally insensitive.
-/
lemma insensitiveCoords_card_ge_div (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s)
    (hbound :
        Fintype.card (Point n) * s ≤ n - n / (2 * s) ∨
        (support f).card ≤ n - n / (2 * s)) :
    n / (2 * s) ≤ (insensitiveCoords f).card := by
  classical
  cases hbound with
  | inl hsmall =>
      exact
        insensitiveCoords_card_ge_div_of_small (f := f) (s := s)
          (hs := hs) (hsmall := hsmall)
  | inr hsupp =>
      exact
        insensitiveCoords_card_ge_div_of_support (f := f) (s := s)
          (hsupp := hsupp)

/--
From a global sensitivity bound we can extract an explicit "large" subcube on
which the Boolean function stays constant.  Starting from the witness
`exists_large_insensitive_subset`, we freeze all coordinates *outside* the
insensitive set `A` to the values of a reference point `x`.  Any point in the
resulting subcube differs from `x` only on `A`, and the previous lemma ensures
those flips do not change `f`.
-/
lemma exists_large_monochromatic_subcube (f : BFunc n) {s : ℕ}
    (hs : sensitivity f ≤ s) (x : Point n) :
    ∃ R : Subcube n,
      (x ∈ₛ R) ∧ Subcube.monochromaticFor R f ∧
      n - Fintype.card (Point n) * s ≤ R.dimension := by
  classical
  obtain ⟨A, hAsub, hAcard⟩ :=
    exists_insensitiveCoords_card_eq_of_global (f := f) (hs := hs)
  obtain ⟨R, hxR, hmono, hdim⟩ :=
    monochromaticSubcube_of_insensitive_subset (f := f)
      (A := A) (hA := hAsub) (x := x)
  refine ⟨R, hxR, hmono, ?_⟩
  have hbound : n - Fintype.card (Point n) * s ≤ A.card := by
    simpa [hAcard]
  simpa [hdim] using hbound

/--
The large monochromatic subcube extracted above can be placed entirely inside
the local `insensitiveSubcubeAt` around the reference point `x`.  This
compatibility will be helpful when recursively extending covers only along
locally insensitive directions.-/
lemma exists_large_monochromatic_subcube_subset_insensitiveSubcubeAt
    (f : BFunc n) {s : ℕ} (hs : sensitivity f ≤ s) (x : Point n) :
    ∃ R : Subcube n,
      (x ∈ₛ R) ∧ Subcube.monochromaticFor R f ∧
      n - Fintype.card (Point n) * s ≤ R.dimension ∧
      (∀ y : Point n, (y ∈ₛ R) → y ∈ₛ insensitiveSubcubeAt f x) := by
  classical
  obtain ⟨R, hxR, hmono, hdim⟩ :=
    exists_large_monochromatic_subcube (f := f) (hs := hs) (x := x)
  have hsub : ∀ y : Point n, (y ∈ₛ R) → y ∈ₛ insensitiveSubcubeAt f x := by
    intro y hy
    exact monochromaticSubcube_subset_insensitiveSubcubeAt
      (f := f) (R := R) (x := x) (hxR := hxR) (hmono := hmono)
      (y := y) (hy := hy)
  exact ⟨R, hxR, hmono, hdim, hsub⟩

/--
Combining the unconditional subcube construction with the subset version of
`exists_large_insensitive_subset_of_monochromatic_subcube` yields a concrete set
of locally insensitive coordinates around `x`.  This set sits inside
`insensitiveCoordsAt f x`, has cardinality at least `n - 2^n · s`, and flipping
any subset of it leaves the value of `f` at `x` unchanged.-/
lemma exists_large_insensitive_subset_subset_insensitiveCoordsAt
    (f : BFunc n) {s : ℕ} (hs : sensitivity f ≤ s) (x : Point n) :
    ∃ A : Finset (Fin n),
      n - Fintype.card (Point n) * s ≤ A.card ∧
      A ⊆ insensitiveCoordsAt f x ∧
      ∀ ⦃T : Finset (Fin n)⦄, T ⊆ A → f (Point.flip x T) = f x := by
  classical
  -- Obtain the large monochromatic subcube in the local insensitive region.
  obtain ⟨R, hxR, hmono, hdim, _⟩ :=
    exists_large_monochromatic_subcube_subset_insensitiveSubcubeAt
      (f := f) (s := s) (hs := hs) (x := x)
  -- Extract the free coordinates as an insensitive set.
  obtain ⟨A, hAcard, hAsub, hAflip⟩ :=
    exists_large_insensitive_subset_of_monochromatic_subcube_subset_insensitiveCoordsAt
      (f := f) (R := R) (x := x) (hx := hxR) (hmono := hmono)
      (k := n - Fintype.card (Point n) * s) (hk := hdim)
  exact ⟨A, hAcard, hAsub, hAflip⟩

/--
Pointwise reformulation of
`exists_large_insensitive_subset_subset_insensitiveCoordsAt`.  Any point that
agrees with `x` outside the extracted set takes the same value of `f`.-/
lemma exists_large_insensitive_subset_pointwise_subset_insensitiveCoordsAt
    (f : BFunc n) {s : ℕ} (hs : sensitivity f ≤ s) (x : Point n) :
    ∃ A : Finset (Fin n),
      n - Fintype.card (Point n) * s ≤ A.card ∧
      A ⊆ insensitiveCoordsAt f x ∧
      ∀ ⦃y : Point n⦄, (∀ i ∉ A, y i = x i) → f y = f x := by
  classical
  obtain ⟨A, hAcard, hAsub, hAflip⟩ :=
    exists_large_insensitive_subset_subset_insensitiveCoordsAt
      (f := f) (s := s) (hs := hs) (x := x)
  refine ⟨A, hAcard, hAsub, ?_⟩
  intro y hy
  -- Represent `y` as a flip of `x` over the coordinates where they differ.
  have hy_eq :
      Point.flip x (A.filter fun i => y i ≠ x i) = y :=
    Point.flip_eq_of_eq_on_compl (x := x) (y := y) (A := A) hy
  have hsubset : (A.filter fun i => y i ≠ x i) ⊆ A :=
    Finset.filter_subset _ _
  -- Apply the flip invariance from the previous lemma.
  simpa [hy_eq] using hAflip
    (T := A.filter fun i => y i ≠ x i) hsubset

/--
From a bound on the size of the essential `support` we can extract a large
monochromatic subcube.  The resulting dimension is expressed via the familiar
quantity `n / (2*s)`, strengthening `exists_large_monochromatic_subcube` under
the additional numeric assumption on the support.
-/
lemma exists_large_monochromatic_subcube_div_of_support
    (f : BFunc n) {s : ℕ}
    (hsupp : (support f).card ≤ n - n / (2 * s)) (x : Point n) :
    ∃ R : Subcube n,
      (x ∈ₛ R) ∧ Subcube.monochromaticFor R f ∧
      n / (2 * s) ≤ R.dimension := by
  classical
  -- Build the subcube from all globally insensitive coordinates.
  have hA : insensitiveCoords f ⊆ insensitiveCoords f := by
    intro i hi; simpa using hi
  obtain ⟨R, hxR, hmono, hdim⟩ :=
    monochromaticSubcube_of_insensitive_subset (f := f)
      (A := insensitiveCoords f) (hA := hA) (x := x)
  -- Relate the support bound to the size of `insensitiveCoords f`.
  have hins :
      (insensitiveCoords f).card = n - (support f).card := by
    have hsum := insensitiveCoords_card_add_support_card (f := f)
    have := congrArg (fun t => t - (support f).card) hsum
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have hsupp_plus : (support f).card + n / (2 * s) ≤ n := by
    have := Nat.add_le_add_right hsupp (n / (2 * s))
    have hdivle : n / (2 * s) ≤ n := Nat.div_le_self _ _
    have hcancel : n - n / (2 * s) + n / (2 * s) = n :=
      Nat.sub_add_cancel hdivle
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hcancel] using this
  have hsupp_plus' : n / (2 * s) + (support f).card ≤ n := by
    simpa [Nat.add_comm] using hsupp_plus
  have hdim_bound :
      n / (2 * s) ≤ (insensitiveCoords f).card := by
    have h := Nat.le_sub_of_add_le hsupp_plus'
    simpa [hins] using h
  -- Transfer the bound to the dimension of `R`.
  refine ⟨R, hxR, hmono, ?_⟩
  simpa [hdim] using hdim_bound

/--
Pointwise variant of `exists_large_monochromatic_subcube_div_of_support`.  It
derives a monochromatic subcube of dimension at least `n / (2*s)` from a bound
on the `support`, using the pointwise insensitive set directly.
-/
lemma exists_large_monochromatic_subcube_pointwise_div_of_support
    (f : BFunc n) {s : ℕ}
    (hsupp : (support f).card ≤ n - n / (2 * s)) (x : Point n) :
    ∃ R : Subcube n,
      (x ∈ₛ R) ∧ Subcube.monochromaticFor R f ∧
      n / (2 * s) ≤ R.dimension := by
  classical
  -- Obtain the pointwise insensitive set and turn it into a subcube.
  obtain ⟨A, hAcard, hApoint⟩ :=
    exists_large_insensitive_subset_pointwise_div_of_support
      (f := f) (s := s) (hsupp := hsupp) (x := x)
  obtain ⟨R, hxR, hmono, hdim⟩ :=
    monochromaticSubcube_of_pointwise (f := f) (x := x)
      (A := A) (hA := hApoint)
  refine ⟨R, hxR, hmono, ?_⟩
  -- Translate the cardinality bound on `A` to the dimension of `R`.
  simpa [hdim] using hAcard

/--
The bound `|insensitiveCoords f| ≥ n / (2*s)` does not hold in full generality.
The following four-variable function has sensitivity `2` yet depends on every
coordinate, so the set of globally insensitive coordinates is empty.
-/
def sensitivityTwoSupportFull : BFunc 4 :=
  fun x => (x 1 && x 2) || (x 3 && x 0)

lemma sensitivityTwoSupportFull_sensitivity :
    sensitivity sensitivityTwoSupportFull = 2 := by
  decide

lemma sensitivityTwoSupportFull_insensitiveCoords :
    insensitiveCoords sensitivityTwoSupportFull = (∅ : Finset (Fin 4)) := by
  decide

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
  ·
    apply (coordSensitivity_eq_zero_iff
      (f := f.restrictCoord i b) (i := j)).2
    intro x
    have hx := h' (Point.update x i b)
    have hx' : f (Point.update x i b) =
        f (Point.update (Point.update x j (!x j)) i b) := by
      simpa [Point.update, hji] using hx
    simpa [BFunc.restrictCoord] using hx'

/-- Fixing several coordinates according to a list of assignments never
increases the overall sensitivity of a Boolean function. -/
lemma sensitivity_restrictAssignments_le (f : BFunc n)
    (p : List (Fin n × Bool)) :
    sensitivity (BFunc.restrictAssignments (f := f) p) ≤ sensitivity f := by
  classical
  induction p generalizing f with
  | nil =>
      simp
  | cons hb tl ih =>
      rcases hb with ⟨i, b⟩
      -- First restrict `i := b`, then apply the inductive hypothesis to the tail.
      have htail := ih (BFunc.restrictCoord f i b)
      -- Combine with the single-coordinate inequality.
      have hsingle := sensitivity_restrictCoord_le (f := f) (j := i) (b := b)
      -- Transitivity yields the final bound.
      simpa [BFunc.restrictAssignments] using htail.trans hsingle

/-- If a coordinate is globally insensitive, further restrictions preserve this
property. -/
lemma coordSensitivity_restrictAssignments_eq_zero (f : BFunc n) (i : Fin n)
    (h : coordSensitivity f i = 0) :
    ∀ p : List (Fin n × Bool),
      coordSensitivity (BFunc.restrictAssignments (f := f) p) i = 0 := by
  classical
  intro p
  induction p generalizing f with
  | nil =>
      simpa
  | cons hb tl ih =>
      rcases hb with ⟨j, b⟩
      -- Propagate the zero-sensitivity witness through the head restriction.
      have h' : coordSensitivity (BFunc.restrictCoord f j b) i = 0 :=
        coordSensitivity_restrict_eq_zero (f := f) (i := j) (j := i) (b := b) h
      -- Apply the inductive hypothesis to the remaining assignments.
      simpa [BFunc.restrictAssignments] using ih (BFunc.restrictCoord f j b) h'

/-- Every coordinate explicitly fixed in a list of assignments becomes
insensitive for the resulting restricted function. -/
lemma coordSensitivity_restrictAssignments_self_zero (f : BFunc n)
    (p : List (Fin n × Bool)) {i : Fin n} {b : Bool}
    (h : (i, b) ∈ p) :
    coordSensitivity (BFunc.restrictAssignments (f := f) p) i = 0 := by
  classical
  induction p generalizing f with
  | nil =>
      cases h
  | cons hb tl ih =>
      rcases hb with ⟨j, c⟩
      have hmem : (i, b) = (j, c) ∨ (i, b) ∈ tl := by
        simpa [List.mem_cons] using h
      cases hmem with
      | inl hhead =>
          -- The head assignment fixes coordinate `j`.
          cases hhead
          have hzero :=
            coordSensitivity_restrict_self_zero (f := f) (i := i) (b := b)
          -- Further restrictions preserve the zero sensitivity on `i`.
          have hprop :=
            coordSensitivity_restrictAssignments_eq_zero
              (f := BFunc.restrictCoord f i b) (i := i)
              (h := hzero) (p := tl)
          simpa [BFunc.restrictAssignments] using hprop
      | inr htail =>
          -- The coordinate appears in the tail; restrict the head and recurse.
          have hrec := ih (BFunc.restrictCoord f j c) htail
          simpa [BFunc.restrictAssignments] using hrec

/--
Fixing a coordinate across an entire family renders that coordinate
insensitive for every restricted function.  Each member of
`F.restrict i b` is obtained by fixing `i := b` in some original
function, and therefore has zero sensitivity on `i` itself.
-/
lemma coordSensitivity_family_restrict_self_zero (F : Family n)
    (i : Fin n) (b : Bool) :
    ∀ g ∈ F.restrict i b, coordSensitivity g i = 0 := by
  classical
  intro g hg
  rcases (Family.mem_restrict).1 hg with ⟨f, hfF, rfl⟩
  simpa using coordSensitivity_restrict_self_zero (f := f) (i := i) (b := b)

/--
If all coordinates outside `A` are insensitive across the family `F`, then the
same property holds for the restricted family `F.restrict i b` with respect to
`A.erase i`.  In other words, fixing a coordinate preserves the invariant that
no function in the family is sensitive outside the allowed coordinate set.
-/
lemma insens_off_A_restrict (F : Family n) (A : Finset (Fin n))
    (hA : ∀ j ∉ A, ∀ f ∈ F, coordSensitivity f j = 0)
    (i : Fin n) (b : Bool) :
    ∀ j ∉ A.erase i, ∀ g ∈ F.restrict i b, coordSensitivity g j = 0 := by
  classical
  intro j hj g hg
  -- Expand membership in the restricted family.
  rcases Finset.mem_image.mp hg with ⟨f, hfF, rfl⟩
  -- Either `j` already lies outside `A` or it equals the fixed coordinate `i`.
  have hjA : j ∉ A ∨ j = i := by
    by_cases hjA : j ∈ A
    · by_cases hji : j = i
      · exact Or.inr hji
      ·
        have : j ∈ A.erase i := by simpa [Finset.mem_erase, hjA, hji]
        exact (False.elim (hj this))
    · exact Or.inl hjA
  -- Handle the two cases separately.
  cases hjA with
  | inl hjA =>
      have hz := hA j hjA f hfF
      simpa using
        (coordSensitivity_restrict_eq_zero (f := f) (i := i) (j := j) (b := b) hz)
    | inr hji =>
        have hzero :=
          coordSensitivity_restrict_self_zero (f := f) (i := i) (b := b)
        simpa [hji] using hzero

/-! ### Support behaviour under restrictions -/

/--
Restricting a Boolean function to `i := b` can only shrink its essential
`support`.  More precisely, every coordinate in `support (f.restrictCoord i b)`
already lies in `support f`, and the fixed coordinate `i` is removed.
-/
lemma support_restrict_subset (f : BFunc n) (i : Fin n) (b : Bool) :
    support (f.restrictCoord i b) ⊆ (support f).erase i := by
  classical
  intro j hj
  -- Membership in `support` corresponds to non‑zero coordinate sensitivity.
  have hcs_ne_zero :=
    (mem_support_iff_coordSensitivity_ne_zero
      (f := f.restrictCoord i b) (i := j)).1 hj
  -- The fixed coordinate `i` cannot appear in the new support.
  have hji : j ≠ i := by
    intro hji
    have hzero := coordSensitivity_restrict_self_zero (f := f) (i := i) (b := b)
    have : coordSensitivity (f.restrictCoord i b) j = 0 := by
      simpa [hji] using hzero
    exact hcs_ne_zero this
  -- Obtain a witness that flipping `j` changes the restricted function.
  rcases (mem_support_iff (f := f.restrictCoord i b) (i := j)).1 hj with ⟨x, hx⟩
  -- Unfold the restriction and swap the order of updates to exhibit a witness
  -- for the original function `f`.
  have hx'' : f (Point.update x i b) ≠
      f (Point.update (Point.update x j (!x j)) i b) := by
    simpa [BFunc.restrictCoord] using hx
  -- Swap the updates on `i` and `j`.
  have hswap :=
    Point.update_swap (x := x) (i := j) (j := i) (h := hji) (!x j) b
  have hx2 : f (Point.update x i b) ≠
      f (Point.update (Point.update x i b) j (!x j)) := by
    simpa [hswap] using hx''
  -- Convert the witness into membership of `j` in the original support.
  have hx2' : f (Point.update x i b) ≠
      f (Point.update (Point.update x i b) j (! (Point.update x i b) j)) := by
    have hx_val : (Point.update x i b) j = x j := by
      simp [Point.update, hji] -- since j ≠ i
    simpa [hx_val] using hx2
  have hjf : j ∈ support f :=
    (mem_support_iff (f := f) (i := j)).2 ⟨Point.update x i b, hx2'⟩
  -- Finally, record `j ≠ i` along with this membership.
  exact Finset.mem_erase.mpr ⟨hji, hjf⟩

/-- The size of the `support` cannot increase after fixing a coordinate. -/
lemma support_card_restrict_le (f : BFunc n) (i : Fin n) (b : Bool) :
    (support (f.restrictCoord i b)).card ≤ (support f).card := by
  classical
  have hsubset :=
    support_restrict_subset (f := f) (i := i) (b := b)
  have hle₁ :
      (support (f.restrictCoord i b)).card ≤ ((support f).erase i).card :=
    Finset.card_le_card hsubset
  have hle₂ : ((support f).erase i).card ≤ (support f).card :=
    Finset.card_le_card (Finset.erase_subset _ _)
  exact le_trans hle₁ hle₂

/--
Restricting a Boolean function on a coordinate that belongs to its `support`
strictly decreases the size of the `support`.
This numerical fact will allow the decision-tree construction to make progress
by removing at least one relevant variable at each step.
-/
lemma support_card_restrict_lt (f : BFunc n) (i : Fin n) (b : Bool)
    (hi : i ∈ support f) :
    (support (f.restrictCoord i b)).card < (support f).card := by
  classical
  -- Any dependency in the restricted function lies outside the fixed index `i`.
  have hsubset :
      support (f.restrictCoord i b) ⊆ (support f).erase i :=
    support_restrict_subset (f := f) (i := i) (b := b)
  -- Hence the size of the new support is bounded by the size of the erased set.
  have hle :
      (support (f.restrictCoord i b)).card ≤ ((support f).erase i).card :=
    Finset.card_le_card hsubset
  -- Adding back the erased element recovers the original support size.
  have hsucc :
      (support (f.restrictCoord i b)).card + 1 ≤ (support f).card := by
    simpa [Finset.card_erase_add_one hi] using Nat.succ_le_succ hle
  -- A quantity whose successor is bounded by `|support f|` is strictly smaller.
  exact Nat.lt_of_succ_le hsucc

/--
Restricting along a list of coordinate assignments cannot introduce new
dependencies.  The resulting `support` is contained in the original one minus
all fixed coordinates.
In particular, every variable that survives the restriction was already
present in the initial `support` and was not among the assigned indices.
-/
lemma support_restrictAssignments_subset
    (p : List (Fin n × Bool)) :
    support (BFunc.restrictAssignments (f := f) p)
      ⊆ support f \ (p.map Prod.fst).toFinset := by
  classical
  induction p generalizing f with
  | nil =>
      intro i hi
      -- No assignments: the support is unchanged and we remove nothing.
      exact Finset.mem_sdiff.mpr ⟨hi, by simp⟩
  | cons a p ih =>
      intro i hi
      rcases a with ⟨j, b⟩
      -- Expand the definition of `restrictAssignments` to expose the tail.
      have hi' : i ∈ support (BFunc.restrictAssignments
            (f := f.restrictCoord j b) p) := by
        simpa [BFunc.restrictAssignments] using hi
      -- Apply the inductive hypothesis to the tail.
      have hmem := ih (f := f.restrictCoord j b) hi'
      have hi_support : i ∈ support (f.restrictCoord j b) :=
        (Finset.mem_sdiff.mp hmem).1
      have hi_notTail : i ∉ (p.map Prod.fst).toFinset :=
        (Finset.mem_sdiff.mp hmem).2
      -- Any dependency of the restricted function comes from the original
      -- support and avoids the fixed coordinate `j`.
      have hi_support' :=
        support_restrict_subset (f := f) (i := j) (b := b) hi_support
      have hi_support_f : i ∈ support f :=
        (Finset.mem_erase.mp hi_support').2
      have hi_ne_j : i ≠ j :=
        (Finset.mem_erase.mp hi_support').1
      -- Combine the information: `i` is not among the assigned indices.
      have hi_notS :
          i ∉ ((List.map Prod.fst ((j, b) :: p)).toFinset) := by
        -- Membership expands to the head index `j` or one from the tail.
        -- Both options contradict `hi_ne_j` and `hi_notTail` respectively.
        simp [List.map, hi_ne_j, hi_notTail]
      -- Package the membership into the final subset relation.
      simpa [List.map] using
        (Finset.mem_sdiff.mpr ⟨hi_support_f, hi_notS⟩)

/--
Fixing several coordinates at once cannot increase the size of the `support`.
This quantitative variant of `support_restrictAssignments_subset` bounds the
cardinality after applying any list of assignments.
-/
lemma support_card_restrictAssignments_le
    (p : List (Fin n × Bool)) :
    (support (BFunc.restrictAssignments (f := f) p)).card
      ≤ (support f).card := by
  classical
  induction p generalizing f with
  | nil =>
      simp
  | cons a p ih =>
      rcases a with ⟨i, b⟩
      -- Apply the inductive hypothesis to the tail and compose with the
      -- single-coordinate estimate.
      have h' :
          (support (BFunc.restrictAssignments (f := f) ((i, b) :: p))).card
            ≤ (support (f.restrictCoord i b)).card := by
        simpa [BFunc.restrictAssignments] using ih (f := f.restrictCoord i b)
      exact h'.trans (support_card_restrict_le (f := f) (i := i) (b := b))

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

/--
Positive sensitivity forces the `support` to be nonempty.
Indeed, any witness to nonzero sensitivity exhibits a coordinate on which the
function depends.
-/
lemma support_nonempty_of_sensitivity_pos (f : BFunc n)
    (hpos : 0 < sensitivity f) : (support f).Nonempty := by
  classical
  rcases exists_sensitive_coord (f := f) hpos with ⟨i, x, hi⟩
  exact ⟨i, (mem_support_iff (f := f) (i := i)).2 ⟨x, hi⟩⟩

/-- A convenient cardinality version of
`support_nonempty_of_sensitivity_pos`. -/
lemma support_card_pos_of_sensitivity_pos (f : BFunc n)
    (hpos : 0 < sensitivity f) : 0 < (support f).card := by
  classical
  have hnonempty := support_nonempty_of_sensitivity_pos (f := f) (hpos := hpos)
  exact Finset.card_pos.mpr hnonempty

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
Constant Boolean functions have zero sensitivity.
-/
@[simp] lemma sensitivity_const (n : ℕ) (b : Bool) [Fintype (Point n)] :
    sensitivity (fun _ : Point n => b) = 0 := by
  classical
  have hxle :
      (Finset.univ.sup fun x : Point n =>
          sensitivityAt (fun _ : Point n => b) x) ≤ 0 := by
    refine Finset.sup_le ?_; intro x hx
    simp [sensitivityAt]
  have hxge : 0 ≤
      (Finset.univ.sup fun x : Point n => sensitivityAt (fun _ : Point n => b) x) :=
    Nat.zero_le _
  have hx :
      (Finset.univ.sup fun x : Point n => sensitivityAt (fun _ : Point n => b) x) = 0 :=
    le_antisymm hxle hxge
  simpa [sensitivity] using hx

/--
If a Boolean function has zero sensitivity, then its essential `support` is
empty.  The proof proceeds by contradiction: assuming a coordinate lies in the
support, we exhibit a point where flipping that coordinate changes the function
value, deriving positive sensitivity and contradicting `h`.
-/
lemma support_eq_empty_of_sensitivity_zero (f : BFunc n)
    (h : sensitivity f = 0) :
    support f = (∅ : Finset (Fin n)) := by
  classical
  -- Show that no coordinate can belong to the support.
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rcases mem_support_iff.mp hi with ⟨x, hx⟩
  -- The point `x` demonstrates that flipping coordinate `i` changes `f`.
  -- This non-trivial change will yield positive sensitivity, contradicting `h`.
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
The sensitivity of a Boolean function vanishes exactly when its essential
`support` is empty.
-/
lemma sensitivity_zero_iff_support_eq_empty (f : BFunc n) :
    sensitivity f = 0 ↔ support f = (∅ : Finset (Fin n)) := by
  constructor
  · intro h; exact support_eq_empty_of_sensitivity_zero (f := f) h
  · intro h
    classical
    -- With empty support the function is constant, hence has zero sensitivity.
    have hconst :
        f = (fun _ : Point n => f (Classical.arbitrary (Point n))) := by
      funext x
      -- Points `x` and `arbitrary` agree on the (empty) support.
      have : ∀ i ∈ support f, x i = (Classical.arbitrary (Point n)) i := by
        intro i; simp [h]
      simpa using
        (eval_eq_of_agree_on_support (f := f) (x := x)
            (y := Classical.arbitrary (Point n)) this)
    -- Constant functions have zero sensitivity.
    have hconst' :
        sensitivity (fun _ : Point n => f (Classical.arbitrary (Point n))) = 0 :=
      sensitivity_const (n := n)
        (b := f (Classical.arbitrary (Point n)))
    have hsens := congrArg (fun g : BFunc n => sensitivity g) hconst
    simpa using hsens.trans hconst'

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

end BoolFunc

