import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Pnp2.BoolFunc

open BoolFunc
open Classical
open Finset

namespace Boolcube

-- Basic objects: points, subcubes and Boolean functions.

variable {n : ℕ}

abbrev Point (n : ℕ) := Fin n → Bool

structure Subcube (n : ℕ) where
  fix : Fin n → Option Bool -- none ⇒ "coordinate is free"
  deriving DecidableEq, Fintype

namespace Subcube

@[simp] def support (C : Subcube n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ (C.fix i).isSome

/-- point `x` lies in `C` iff it matches all fixed coordinates. -/
@[simp] def Mem (C : Subcube n) (x : Point n) : Prop :=
  ∀ i, (C.fix i).elim True fun b ↦ x i = b

@[simp] def dim (C : Subcube n) : ℕ := n - C.support.card

@[simp] def full : Subcube n := ⟨fun _ ↦ none⟩
@[simp] def point (x : Point n) : Subcube n := ⟨fun i ↦ some (x i)⟩

@[simp] lemma mem_full (x : Point n) : (full : Subcube n).Mem x := by
  intro; simp [full]

@[simp] lemma mem_point_iff (x y : Point n) : (point x).Mem y ↔ x = y := by
  constructor
  · intro h; funext i; have hi := h i; simpa [point] using hi.symm
  · intro h i; simp [h, point]

/-- Fix exactly one coordinate. -/
@[simp] def fixOne (i : Fin n) (b : Bool) : Subcube n :=
  ⟨fun j ↦ if j = i then some b else none⟩

@[simp] lemma mem_fixOne_iff {i b x} :
    (fixOne (n := n) i b).Mem x ↔ x i = b := by
  constructor
  · intro h; simpa using h i
  · intro h j; by_cases hj : j = i
    · cases hj; simp [fixOne, h]
    · simp [fixOne, hj]

@[simp] lemma dim_full (n : ℕ) :
    (Subcube.full : Subcube n).dim = n := by
  classical
  simp [Subcube.dim, Subcube.support]

@[simp] lemma dim_point (x : Point n) :
    (Subcube.point (n := n) x).dim = 0 := by
  classical
  simp [Subcube.dim, Subcube.support]

@[simp] lemma dim_fixOne (i : Fin n) (b : Bool) :
    (Subcube.fixOne (n := n) i b).dim = n - 1 := by
  classical
  unfold Subcube.dim Subcube.support Subcube.fixOne
  have hset : Finset.univ.filter (fun j : Fin n => j = i) = ({i} : Finset (Fin n)) := by
    ext j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]
  have hcard : (Finset.univ.filter (fun j : Fin n => j = i)).card = 1 := by
    simp [hset]
  simp [hcard]

/-! ### Enumerating the points of a subcube -/

noncomputable def toFinset (C : Subcube n) : Finset (Point n) := by
  classical
  exact Finset.univ.filter fun x => C.Mem x

@[simp] lemma mem_toFinset {C : Subcube n} {x : Point n} :
    x ∈ toFinset (n := n) C ↔ C.Mem x := by
  classical
  simp [toFinset]

noncomputable def size (C : Subcube n) : ℕ := (toFinset (n := n) C).card

lemma monotonicity {C D : Subcube n}
    (h : ∀ {x : Point n}, C.Mem x → D.Mem x) :
    size (n := n) C ≤ size (n := n) D := by
  classical
  have hsubset : toFinset (n := n) C ⊆ toFinset (n := n) D := by
    intro x hx
    have hxC : C.Mem x := (mem_toFinset (C := C) (x := x)).1 hx
    have hxD : D.Mem x := h hxC
    exact (mem_toFinset (C := D) (x := x)).2 hxD
  simpa [size] using Finset.card_le_card hsubset

/-!  The full subcube enumerates all `2^n` points of the Boolean cube. -/
@[simp] lemma size_full (n : ℕ) :
    size (n := n) (Subcube.full : Subcube n) = 2 ^ n := by
  classical
  simp [size, toFinset]

/-! ### Picking a representative point from a subcube -/

/-
`sample` assigns the fixed coordinates of a subcube and fills all
remaining bits with `false`.  This deterministic choice is handy for
searching a cover: evaluating a Boolean function on `sample C` reveals
the constant colour of `C` when `C` is known to be monochromatic. -/
def sample (C : Subcube n) : Point n :=
  fun i => (C.fix i).getD false

@[simp] lemma sample_mem (C : Subcube n) : C.Mem (sample C) := by
  intro i
  cases h : C.fix i <;> simp [sample, h]


/-!  A single-point subcube has size `1`. -/
@[simp] lemma size_point (x : Point n) :
    size (n := n) (Subcube.point (n := n) x) = 1 := by
  classical
  -- A point subcube contains precisely the point `x`.  We show that
  -- the finite set enumerating its elements is `{x}` and hence has
  -- cardinality `1`.
  have hset : toFinset (n := n) (Subcube.point (n := n) x)
      = ({x} : Finset (Point n)) := by
    classical
    ext y
    constructor
    · intro hy
      -- Membership in the finset implies the point coincides with `x`.
      have hy' : (Subcube.point (n := n) x).Mem y :=
        (mem_toFinset (C := Subcube.point (n := n) x) (x := y)).1 hy
      have : y = x := ((Subcube.mem_point_iff (x := x) (y := y)).1 hy').symm
      simp [this]
    · intro hy
      -- Conversely, membership in `{x}` means `y = x`.
      have hy' : y = x := by simpa using hy
      subst hy'
      simp [mem_toFinset]
  -- With this characterisation the result is immediate.
  -- The cardinality of a singleton set is one.
  have : size (n := n) (Subcube.point (n := n) x)
      = ({x} : Finset (Point n)).card := by
    simpa [size] using congrArg Finset.card hset
  simpa [this]

/-! ### A representative point of a subcube -/

-- |`Subcube.rep R`| picks an arbitrary point inside `R` by assigning
-- `false` to all free coordinates.  This choice is convenient for
-- constructive algorithms that need a concrete witness from each
-- subcube.
/-- Pick a canonical representative point inside `R` by assigning `false`
to all free coordinates. -/
@[simp] def rep (R : Subcube n) : Point n :=
  fun i => (R.fix i).getD false

lemma rep_mem (R : Subcube n) : R.Mem (rep (n := n) R) := by
  -- The representative satisfies all fixed coordinates by construction.
  intro i
  cases h : R.fix i with
  | none =>
      simp [rep, h]
  | some b =>
      simp [rep, h]

/-! ### Free coordinates of a subcube -/

/--
Global set of free coordinates of a subcube.  An index belongs to
`freeCoords` precisely when the subcube leaves it unspecified.  The
definition deliberately mirrors `support` so that the two sets form a
partition of the ambient indices.
-/
def freeCoords (R : Subcube n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (R.fix i).isNone

@[simp] lemma mem_freeCoords {R : Subcube n} {i : Fin n} :
    i ∈ freeCoords (n := n) R ↔ (R.fix i).isNone := by
  classical
  simp [freeCoords]

/--
The fixed coordinates (`support`) and the free ones form a disjoint
partition of all indices.
-/
lemma support_disjoint_freeCoords (R : Subcube n) :
    Disjoint R.support (freeCoords (n := n) R) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro i hiSupport hiFree
  have hiSome : (R.fix i).isSome := by
    have := (Finset.mem_filter.mp hiSupport).2
    simpa [support] using this
  have hiNone : (R.fix i).isNone :=
    (mem_freeCoords (R := R) (i := i)).1 hiFree
  cases h : R.fix i with
  | none =>
      simp [h] at hiSome
  | some b =>
      simp [h] at hiNone

/--
Every coordinate is either fixed or free.
-/
lemma support_union_freeCoords (R : Subcube n) :
    R.support ∪ freeCoords (n := n) R = (Finset.univ : Finset (Fin n)) := by
  classical
  ext i
  cases h : R.fix i with
  | none => simp [support, freeCoords, h]
  | some b => simp [support, freeCoords, h]

/--
Cardinality relationship between fixed and free coordinates.
-/
lemma card_support_add_card_freeCoords (R : Subcube n) :
    R.support.card + (freeCoords (n := n) R).card = n := by
  classical
  have hdisj := support_disjoint_freeCoords (n := n) (R := R)
  have hunion := support_union_freeCoords (n := n) (R := R)
  have hcard := Finset.card_union_of_disjoint (s := R.support)
      (t := R.freeCoords) hdisj
  have huniv_card := congrArg Finset.card hunion
  have huniv : (R.support ∪ R.freeCoords).card = n := by
    simpa [Fintype.card_fin] using huniv_card
  exact hcard.symm.trans huniv

/--
The number of free coordinates equals the dimension of the subcube.
-/
lemma card_freeCoords (R : Subcube n) :
    (freeCoords (n := n) R).card = R.dim := by
  classical
  have hsum := card_support_add_card_freeCoords (n := n) (R := R)
  have hsub := congrArg (fun t => t - R.support.card) hsum
  simpa [Subcube.dim, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsub


end Subcube

abbrev BoolFun (n : ℕ) := Point n → Bool
abbrev Family  (n : ℕ) := Finset (BoolFun n)

/-! ## Coordinate partitions of the Boolean cube

The formal proof of Lemма B-5 repeatedly splits the ambient indices into a
"left" and a "right" block.  The auxiliary definitions below package this
partition together with the basic structural facts (disjointness and
coverage).  Although the subsequent applications target circuit families,
the constructions are purely combinatorial and therefore live in the generic
`Boolcube` namespace.
-/

namespace Coords

/-- The finset of the first `k` coordinates of `Fin n`.  When `k ≥ n` this is
simply the whole set of indices. -/
def left (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => (i : ℕ) < k

/-- The complementary block of coordinates starting at position `k`. -/
def right (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => k ≤ (i : ℕ)

@[simp] lemma mem_left {n k : ℕ} {i : Fin n} :
    i ∈ left n k ↔ (i : ℕ) < k := by
  classical
  simp [left]

@[simp] lemma mem_right {n k : ℕ} {i : Fin n} :
    i ∈ right n k ↔ k ≤ (i : ℕ) := by
  classical
  simp [right]

lemma left_union_right (n k : ℕ) :
    left n k ∪ right n k = (Finset.univ : Finset (Fin n)) := by
  classical
  ext i
  by_cases hi : (i : ℕ) < k
  · have : ¬ k ≤ (i : ℕ) := by exact not_le_of_gt hi
    simp [left, right, hi, this]
  · have hle : k ≤ (i : ℕ) := le_of_not_gt hi
    simp [left, right, hi, hle]

lemma left_disjoint_right (n k : ℕ) :
    Disjoint (left n k) (right n k) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro i hiL hiR
  have hlt : (i : ℕ) < k := by simpa [left] using hiL
  have hge : k ≤ (i : ℕ) := by simpa [right] using hiR
  exact (lt_of_lt_of_le hlt hge).false.elim

/--
The left block contains exactly `min k n` indices.  This explicit cardinality
is repeatedly used to convert combinatorial statements about free coordinates
into quantitative bounds involving the ambient parameters `k` and `n`.
-/
lemma card_left (n k : ℕ) : (left n k).card = min k n := by
  classical
  by_cases hk : k ≤ n
  · -- When `k ≤ n`, the first `k` indices are available inside `Fin n`.
    -- They are enumerated by attaching the range `0,…,k-1` to the finset of
    -- naturals.  The helper `attachFin` takes care of the coercions.
    have hcond : ∀ m ∈ Finset.range k, m < n := by
      intro m hm
      have hm' : m < k := Finset.mem_range.mp hm
      exact lt_of_lt_of_le hm' hk
    have hattach :
        left n k = (Finset.range k).attachFin (n := n) hcond := by
      ext i; constructor
      · intro hi
        have hi' : (i : ℕ) ∈ Finset.range k :=
          Finset.mem_range.mpr ((mem_left (n := n) (k := k) (i := i)).1 hi)
        simpa [left] using (Finset.mem_attachFin (s := Finset.range k)
          (n := n) hcond).2 hi'
      · intro hi
        have hi' : (i : ℕ) ∈ Finset.range k :=
          (Finset.mem_attachFin (s := Finset.range k) (n := n) hcond).1 hi
        exact (mem_left (n := n) (k := k) (i := i)).2 (Finset.mem_range.mp hi')
    have hcard := Finset.card_attachFin (s := Finset.range k) (n := n) hcond
    have hrange : (Finset.range k).card = k := Finset.card_range k
    simpa [hattach, hcard, hrange, Nat.min_eq_left hk]
  · -- When `k ≥ n`, every index of `Fin n` lies in the left block.
    have hk' : n ≤ k := le_of_not_ge hk
    have hleft : left n k = (Finset.univ : Finset (Fin n)) := by
      ext i; constructor
      · intro _; exact Finset.mem_univ _
      · intro _
        exact (mem_left (n := n) (k := k) (i := i)).2
          (lt_of_lt_of_le i.is_lt hk')
    simpa [hleft, Nat.min_eq_right hk', Fintype.card_fin] using
      (Finset.card_univ : _ = Fintype.card (Fin n))

/--
Right blocks complement the left ones: their cardinality is the difference
between `n` and the size of the left block.  This lemma is the workhorse behind
all subsequent bounds on the number of free right coordinates.
-/
lemma card_right (n k : ℕ) : (right n k).card = n - min k n := by
  classical
  have hdisj := left_disjoint_right (n := n) (k := k)
  have hunion := left_union_right (n := n) (k := k)
  have hsum :
      (left n k).card + (right n k).card = n := by
    have hcard_union :=
      (Finset.card_union_of_disjoint (s := left n k) (t := right n k) hdisj).symm
    have hsum' :
        (left n k).card + (right n k).card
          = ((Finset.univ : Finset (Fin n))).card := by
      simpa [hunion, add_comm, add_left_comm, add_assoc] using hcard_union
    simpa using hsum'
  have htarget : min k n + (right n k).card = n := by
    simpa [card_left] using hsum
  have hcanonical : min k n + (n - min k n) = n :=
    Nat.add_sub_of_le (Nat.min_le_right _ _)
  have := htarget.trans hcanonical.symm
  exact Nat.add_left_cancel this

end Coords

namespace Subcube

open Coords

/-- Fixed left coordinates of a subcube. -/
def fixedLeft (R : Subcube n) (k : ℕ) : Finset (Fin n) :=
  R.support.filter fun i => (i : ℕ) < k

/-- Fixed right coordinates of a subcube. -/
def fixedRight (R : Subcube n) (k : ℕ) : Finset (Fin n) :=
  R.support.filter fun i => k ≤ (i : ℕ)

/-- Free left coordinates, i.e. indices in the left block that the subcube
does not fix. -/
def freeLeft (R : Subcube n) (k : ℕ) : Finset (Fin n) :=
  (Coords.left n k).filter fun i => (R.fix i).isNone

/-- Free right coordinates of a subcube. -/
def freeRight (R : Subcube n) (k : ℕ) : Finset (Fin n) :=
  (Coords.right n k).filter fun i => (R.fix i).isNone

@[simp] lemma mem_fixedLeft {R : Subcube n} {k : ℕ} {i : Fin n} :
    i ∈ fixedLeft (n := n) R k ↔ (R.fix i).isSome ∧ (i : ℕ) < k := by
  classical
  simp [fixedLeft, support]

@[simp] lemma mem_fixedRight {R : Subcube n} {k : ℕ} {i : Fin n} :
    i ∈ fixedRight (n := n) R k ↔ (R.fix i).isSome ∧ k ≤ (i : ℕ) := by
  classical
  simp [fixedRight, support]

@[simp] lemma mem_freeLeft {R : Subcube n} {k : ℕ} {i : Fin n} :
    i ∈ freeLeft (n := n) R k ↔ (i : ℕ) < k ∧ (R.fix i).isNone := by
  classical
  simp [freeLeft, Coords.left]

@[simp] lemma mem_freeRight {R : Subcube n} {k : ℕ} {i : Fin n} :
    i ∈ freeRight (n := n) R k ↔ k ≤ (i : ℕ) ∧ (R.fix i).isNone := by
  classical
  simp [freeRight, Coords.right]

/--
Free left coordinates are contained in the global set of free coordinates.
-/
lemma freeLeft_subset_freeCoords (R : Subcube n) (k : ℕ) :
    freeLeft (n := n) R k ⊆ freeCoords (n := n) R := by
  classical
  intro i hi
  have hi' := (mem_freeLeft (R := R) (k := k) (i := i)).1 hi
  exact (mem_freeCoords (R := R) (i := i)).2 hi'.2

/--
Free right coordinates are contained in the global set of free coordinates.
-/
lemma freeRight_subset_freeCoords (R : Subcube n) (k : ℕ) :
    freeRight (n := n) R k ⊆ freeCoords (n := n) R := by
  classical
  intro i hi
  have hi' := (mem_freeRight (R := R) (k := k) (i := i)).1 hi
  exact (mem_freeCoords (R := R) (i := i)).2 hi'.2

/--
The number of free left coordinates is bounded by the global free pool.
-/
lemma card_freeLeft_le_freeCoords (R : Subcube n) (k : ℕ) :
    (freeLeft (n := n) R k).card ≤ (freeCoords (n := n) R).card := by
  classical
  have hsubset := freeLeft_subset_freeCoords (n := n) (R := R) (k := k)
  exact Finset.card_le_card hsubset

/--
The number of free right coordinates is bounded by the global free pool.
-/
lemma card_freeRight_le_freeCoords (R : Subcube n) (k : ℕ) :
    (freeRight (n := n) R k).card ≤ (freeCoords (n := n) R).card := by
  classical
  have hsubset := freeRight_subset_freeCoords (n := n) (R := R) (k := k)
  exact Finset.card_le_card hsubset

lemma fixedLeft_disjoint_freeLeft (R : Subcube n) (k : ℕ) :
    Disjoint (fixedLeft (n := n) R k) (freeLeft (n := n) R k) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro i hiFix hiFree
  cases hfix : R.fix i with
  | none =>
      have hsome : (R.fix i).isSome := (mem_fixedLeft (R := R) (k := k)).1 hiFix |>.1
      simp [hfix] at hsome
  | some b =>
      have hnone : (R.fix i).isNone := (mem_freeLeft (R := R) (k := k)).1 hiFree |>.2
      simp [hfix] at hnone

lemma fixedRight_disjoint_freeRight (R : Subcube n) (k : ℕ) :
    Disjoint (fixedRight (n := n) R k) (freeRight (n := n) R k) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro i hiFix hiFree
  cases hfix : R.fix i with
  | none =>
      have hsome : (R.fix i).isSome := (mem_fixedRight (R := R) (k := k)).1 hiFix |>.1
      simp [hfix] at hsome
  | some b =>
      have hnone : (R.fix i).isNone := (mem_freeRight (R := R) (k := k)).1 hiFree |>.2
      simp [hfix] at hnone

lemma fixedLeft_union_freeLeft (R : Subcube n) (k : ℕ) :
    fixedLeft (n := n) R k ∪ freeLeft (n := n) R k = Coords.left n k := by
  classical
  ext i; by_cases hi : (i : ℕ) < k
  · cases hfix : R.fix i with
    | none =>
        simp [Coords.left, fixedLeft, freeLeft, hi, hfix, support]
    | some b =>
        simp [Coords.left, fixedLeft, freeLeft, hi, hfix, support]
  · have hnot : ¬ i ∈ Coords.left n k := by
      simp [Coords.left, hi]
    simp [Coords.left, fixedLeft, freeLeft, hi, support]

lemma fixedRight_union_freeRight (R : Subcube n) (k : ℕ) :
    fixedRight (n := n) R k ∪ freeRight (n := n) R k = Coords.right n k := by
  classical
  ext i; by_cases hi : k ≤ (i : ℕ)
  · cases hfix : R.fix i with
    | none =>
        simp [Coords.right, fixedRight, freeRight, hi, hfix, support]
    | some b =>
        simp [Coords.right, fixedRight, freeRight, hi, hfix, support]
  · have hnot : ¬ i ∈ Coords.right n k := by
      simp [Coords.right, hi]
    simp [Coords.right, fixedRight, freeRight, hi, support]

lemma card_fixedLeft_add_card_freeLeft (R : Subcube n) (k : ℕ) :
    (fixedLeft (n := n) R k).card + (freeLeft (n := n) R k).card
      = (Coords.left n k).card := by
  classical
  have hdisj := fixedLeft_disjoint_freeLeft (R := R) (k := k)
  have hunion := fixedLeft_union_freeLeft (R := R) (k := k)
  simpa [hunion] using
    (Finset.card_union_of_disjoint (s := fixedLeft (n := n) R k)
      (t := freeLeft (n := n) R k) hdisj).symm

/--
The left block of fixed coordinates is bounded by the size of the block itself.
This estimate is frequently used to control the enumeration complexity on the
left half of the cube.
-/
lemma card_fixedLeft_le_left (R : Subcube n) (k : ℕ) :
    (fixedLeft (n := n) R k).card ≤ (Coords.left n k).card := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  have hi' := (mem_fixedLeft (R := R) (k := k) (i := i)).1 hi
  exact (Coords.mem_left (n := n) (k := k) (i := i)).2 hi'.2

/--
Direct corollary of `card_fixedLeft_le_left`: the number of fixed left
coordinates never exceeds `min k n`.
-/
lemma card_fixedLeft_le (R : Subcube n) (k : ℕ) :
    (fixedLeft (n := n) R k).card ≤ min k n := by
  simpa [Coords.card_left] using card_fixedLeft_le_left (n := n) (R := R) (k := k)

/--
The count of free left coordinates is bounded by the size of the left block.
-/
lemma card_freeLeft_le_left (R : Subcube n) (k : ℕ) :
    (freeLeft (n := n) R k).card ≤ (Coords.left n k).card := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  have hi' := (mem_freeLeft (R := R) (k := k) (i := i)).1 hi
  exact (Coords.mem_left (n := n) (k := k) (i := i)).2 hi'.1

/--
The number of free left coordinates is at most `min k n`.
-/
lemma card_freeLeft_le (R : Subcube n) (k : ℕ) :
    (freeLeft (n := n) R k).card ≤ min k n := by
  simpa [Coords.card_left] using card_freeLeft_le_left (n := n) (R := R) (k := k)

/--
When the left block consists of at most `k` coordinates, free coordinates are
bounded by `k`.  This specialised form will later translate cardinality bounds
into running-time estimates of the enumeration procedure.
-/
lemma card_freeLeft_le_of_le (R : Subcube n) {k : ℕ} (hk : k ≤ n) :
    (freeLeft (n := n) R k).card ≤ k := by
  have := card_freeLeft_le_left (n := n) (R := R) (k := k)
  simpa [Coords.card_left, Nat.min_eq_left hk] using this

/--
From `fixedLeft + freeLeft = left` we deduce the handy identity
`freeLeft = left - fixedLeft`.  It will be instrumental when translating
lower bounds on fixed coordinates into upper bounds on the free ones.
-/
lemma card_freeLeft_eq_left_sub_fixed (R : Subcube n) (k : ℕ) :
    (freeLeft (n := n) R k).card
      = (Coords.left n k).card - (fixedLeft (n := n) R k).card := by
  classical
  have hsum :
      (Coords.left n k).card
        = (fixedLeft (n := n) R k).card + (freeLeft (n := n) R k).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (card_fixedLeft_add_card_freeLeft (n := n) (R := R) (k := k)).symm
  have hcalc := congrArg (fun t => t - (fixedLeft (n := n) R k).card) hsum
  have hfree :
      (fixedLeft (n := n) R k).card + (freeLeft (n := n) R k).card
          - (fixedLeft (n := n) R k).card
        = (freeLeft (n := n) R k).card :=
      Nat.add_sub_cancel_left (fixedLeft (n := n) R k).card (freeLeft (n := n) R k).card
  have : (Coords.left n k).card - (fixedLeft (n := n) R k).card
      = (freeLeft (n := n) R k).card := by
    simpa [hfree] using hcalc
  exact this.symm

lemma card_fixedRight_add_card_freeRight (R : Subcube n) (k : ℕ) :
    (fixedRight (n := n) R k).card + (freeRight (n := n) R k).card
      = (Coords.right n k).card := by
  classical
  have hdisj := fixedRight_disjoint_freeRight (R := R) (k := k)
  have hunion := fixedRight_union_freeRight (R := R) (k := k)
  simpa [hunion] using
    (Finset.card_union_of_disjoint (s := fixedRight (n := n) R k)
      (t := freeRight (n := n) R k) hdisj).symm

/--
Fixed right coordinates form a subset of the right block, hence their
cardinality does not exceed the block size.
-/
lemma card_fixedRight_le_right (R : Subcube n) (k : ℕ) :
    (fixedRight (n := n) R k).card ≤ (Coords.right n k).card := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  have hi' := (mem_fixedRight (R := R) (k := k) (i := i)).1 hi
  exact (Coords.mem_right (n := n) (k := k) (i := i)).2 hi'.2

/--
Right-hand counterpart to `card_fixedLeft_le`: fixed right coordinates are at
most `n - min k n`.
-/
lemma card_fixedRight_le (R : Subcube n) (k : ℕ) :
    (fixedRight (n := n) R k).card ≤ n - min k n := by
  simpa [Coords.card_right] using
    card_fixedRight_le_right (n := n) (R := R) (k := k)

/--
Right-hand analogue of `card_freeLeft_le_of_le`: when `k ≤ n`, the free right
coordinates occupy at most `n - k` slots.
-/
lemma card_freeRight_le_of_le (R : Subcube n) {k : ℕ} (hk : k ≤ n) :
    (freeRight (n := n) R k).card ≤ n - k := by
  classical
  have hsubset :
      (freeRight (n := n) R k) ⊆ Coords.right n k := by
    intro i hi
    have hi' := (mem_freeRight (R := R) (k := k) (i := i)).1 hi
    exact (Coords.mem_right (n := n) (k := k) (i := i)).2 hi'.1
  have hcard := Finset.card_le_card hsubset
  simpa [Coords.card_right, Nat.min_eq_left hk] using hcard

/--
Even without the inequality `k ≤ n`, the number of free right coordinates never
exceeds the size of the right block `n - min k n`.
-/
lemma card_freeRight_le (R : Subcube n) (k : ℕ) :
    (freeRight (n := n) R k).card ≤ n - min k n := by
  classical
  have hsubset : (freeRight (n := n) R k) ⊆ Coords.right n k := by
    intro i hi
    have hi' := (mem_freeRight (R := R) (k := k) (i := i)).1 hi
    exact (Coords.mem_right (n := n) (k := k) (i := i)).2 hi'.1
  have hcard := Finset.card_le_card hsubset
  simpa [Coords.card_right] using hcard

/--
Identity mirroring `card_freeLeft_eq_left_sub_fixed` on the right block.
-/
lemma card_freeRight_eq_right_sub_fixed (R : Subcube n) (k : ℕ) :
    (freeRight (n := n) R k).card
      = (Coords.right n k).card - (fixedRight (n := n) R k).card := by
  classical
  have hsum :
      (Coords.right n k).card
        = (fixedRight (n := n) R k).card + (freeRight (n := n) R k).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (card_fixedRight_add_card_freeRight (n := n) (R := R) (k := k)).symm
  have hcalc := congrArg (fun t => t - (fixedRight (n := n) R k).card) hsum
  have hfree :
      (fixedRight (n := n) R k).card + (freeRight (n := n) R k).card
          - (fixedRight (n := n) R k).card
        = (freeRight (n := n) R k).card :=
      Nat.add_sub_cancel_left (fixedRight (n := n) R k).card (freeRight (n := n) R k).card
  have : (Coords.right n k).card - (fixedRight (n := n) R k).card
      = (freeRight (n := n) R k).card := by
    simpa [hfree] using hcalc
  exact this.symm

end Subcube

/-! ### Slicing families by a coordinate -/

def coordSlice (i : Fin n) (b : Bool) (F : Finset (Point n)) :
    Finset (Point n) :=
  F.filter fun x => x i = b

namespace coordSlice

@[simp] lemma card_le (i : Fin n) (b : Bool) (F : Finset (Point n)) :
    (coordSlice i b F).card ≤ F.card :=
  Finset.card_filter_le _ _

@[simp] lemma disj (i : Fin n) (F : Finset (Point n)) :
    Disjoint (coordSlice i true F) (coordSlice i false F) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro x hxT hxF
  simp [coordSlice] at hxT hxF
  cases hxT.2.symm.trans hxF.2

lemma partition (i : Fin n) (F : Finset (Point n)) :
    (coordSlice i true F).card + (coordSlice i false F).card = F.card := by
  classical
  have hdisj := disj i F
  have hunion : (coordSlice i true F) ∪ (coordSlice i false F) = F := by
    classical
    ext x; cases hx : x i <;> simp [coordSlice, hx]
  simpa [hunion] using
    (Finset.card_union_of_disjoint (s := coordSlice i true F)
      (t := coordSlice i false F) hdisj).symm

end coordSlice

open coordSlice

/-- If a finite set of points contains at least two distinct elements, then some
coordinate splits it into nonempty `true` and `false` slices. -/
lemma exists_coord_slice_both_nonempty (S : Finset (Point n))
    (hS : 1 < S.card) :
    ∃ i : Fin n,
      (coordSlice i true S).Nonempty ∧ (coordSlice i false S).Nonempty := by
  classical
  obtain ⟨x, y, hx, hy, hxy⟩ := (Finset.one_lt_card_iff).mp hS
  have hdiff : ∃ i : Fin n, x i ≠ y i := by
    by_contra h
    have hxyeq : x = y := by
      funext i
      have hi := (not_exists.mp h) i
      simpa using hi
    exact hxy hxyeq
  obtain ⟨i, hi⟩ := hdiff
  cases hx_val : x i <;> cases hy_val : y i
  case true.true =>
    have : x i = y i := by simp [hx_val, hy_val]
    exact (hi this).elim
  case true.false =>
    exact ⟨i, ⟨x, by simp [coordSlice, hx, hx_val]⟩,
              ⟨y, by simp [coordSlice, hy, hy_val]⟩⟩
  case false.true =>
    exact ⟨i, ⟨y, by simp [coordSlice, hy, hy_val]⟩,
              ⟨x, by simp [coordSlice, hx, hx_val]⟩⟩
  case false.false =>
    have : x i = y i := by simp [hx_val, hy_val]
    exact (hi this).elim

/-! ### Cardinal halving for point sets -/

lemma min_slice_le_half {i : Fin n} (F : Finset (Point n)) :
    ∃ b, (coordSlice i b F).card ≤ F.card / 2 := by
  classical
  set ct := (coordSlice i true F).card
  set cf := (coordSlice i false F).card
  have hsum : ct + cf = F.card := coordSlice.partition i F
  have h2min_le : 2 * Nat.min ct cf ≤ F.card := by
    have hmin_le : Nat.min ct cf + Nat.min ct cf ≤ ct + cf :=
      add_le_add (Nat.min_le_left _ _) (Nat.min_le_right _ _)
    have h2min_le_sum : 2 * Nat.min ct cf ≤ ct + cf := by
      simpa [two_mul] using hmin_le
    simpa [ct, cf, hsum, two_mul] using h2min_le_sum
  have hmin_half : Nat.min ct cf ≤ F.card / 2 := by
    have h2min_le' : Nat.min ct cf * 2 ≤ F.card := by
      simpa [two_mul, mul_comm] using h2min_le
    exact (Nat.le_div_iff_mul_le Nat.two_pos).mpr h2min_le'
  by_cases hct_le : ct ≤ cf
  · refine ⟨true, ?_⟩
    have hmin : Nat.min ct cf = ct := Nat.min_eq_left hct_le
    simpa [ct, hmin] using hmin_half
  · refine ⟨false, ?_⟩
    have hcf_le : cf ≤ ct := le_of_not_ge hct_le
    have hmin : Nat.min ct cf = cf := Nat.min_eq_right hcf_le
    simpa [cf, hmin] using hmin_half

lemma half_le_bound (c n : ℕ) (hn : 2 ≤ n) :
    c / 2 ≤ c - c / n := by
  have hdiv_le : c / n ≤ c / 2 := by
    have hmul_le : (c / n) * 2 ≤ c := by
      have hmul := Nat.mul_div_le c n
      have hmul' : (c / n) * n ≤ c := by simpa [mul_comm] using hmul
      have hle : (c / n) * 2 ≤ (c / n) * n := by
        have := Nat.mul_le_mul_left (c / n) hn
        simpa [two_mul] using this
      exact le_trans hle hmul'
    exact (Nat.le_div_iff_mul_le Nat.two_pos).mpr hmul_le
  have hsum : c / 2 + c / n ≤ c := by
    have htmp := Nat.add_le_add_left hdiv_le (c / 2)
    have hhalf : c / 2 + c / 2 ≤ c := by
      simpa [two_mul] using Nat.mul_div_le c 2
    exact htmp.trans hhalf
  exact (Nat.le_sub_iff_add_le (Nat.div_le_self _ _)).mpr hsum

lemma exists_coord_card_drop
    (hn : 2 ≤ n)
    {F : Finset (Point n)} (hF : F.Nonempty) :
    ∃ i : Fin n, ∃ b : Bool,
      (coordSlice i b F).card ≤ F.card - F.card / n := by
  classical
  have hcard_pos : 0 < F.card := Finset.card_pos.mpr hF
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.succ_pos 1) hn
  let i : Fin n := ⟨0, hn_pos⟩
  obtain ⟨b, hb⟩ := min_slice_le_half (n := n) (F := F) (i := i)
  have hbound := half_le_bound F.card n hn
  exact ⟨i, b, hb.trans hbound⟩

namespace Entropy

/-- Collision entropy (uniform measure) – we keep only the logarithmic form. -/
@[simp] noncomputable def H₂ {n} (F : Family n) : ℝ := Real.logb 2 (F.card)

lemma H₂_nonneg {F : Family n} : 0 ≤ H₂ F := by
  classical
  unfold H₂
  by_cases hF : F.card = 0
  · -- `logb` of zero is zero by definition
    simp [hF]
  ·
    have hb : (1 : ℝ) < 2 := by norm_num
    have hx : 1 ≤ (F.card : ℝ) := by
      have hpos : 0 < F.card := Nat.pos_of_ne_zero hF
      exact_mod_cast Nat.succ_le_of_lt hpos
    have := Real.logb_nonneg (b := 2) hb hx
    simpa using this

end Entropy

end Boolcube

namespace Boolcube

/-!  ### 2.  High-level cover structure and recursive constructor -/

structure LabeledCube (n : ℕ) (F : Family n) where
  cube : Subcube n
  bit  : Bool

namespace LabeledCube

/-- A cube that fixes a single coordinate to the given bit. -/
@[simp] def fixOneLabel {n} (i : Fin n) (b : Bool) (F : Family n) :
    LabeledCube n F :=
  { cube := Subcube.fixOne i b
    bit  := b }

/-- A cube obtained from an arbitrary `Subcube`. -/
@[simp] def ofSubcube {n} {F : Family n} (C : Subcube n) (b : Bool) :
    LabeledCube n F :=
  ⟨C, b⟩

end LabeledCube

/-- A *cover* is a finite set of labeled cubes that together cover
all `1`-points of every function in `F`. -/
structure Cover {n : ℕ} (F : Family n) where
  cubes  : Finset (LabeledCube n F)
  cover₁ : ∀ f ∈ F, ∀ x, f x = true → ∃ C ∈ cubes, C.cube.Mem x

/-!
Sunflower step lemma from early drafts (deprecated).
The current development in `cover2.lean` relies directly on the
formalised `Sunflower.sunflower_exists` from `sunflower.lean`, so this
placeholder proof has been removed.  The full cover construction is
postponed in this lightweight version.
-/

end Boolcube
