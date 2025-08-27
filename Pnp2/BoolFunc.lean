/-
bool_func.lean
==============

Foundational definitions for working with Boolean functions on the `n`‑dimensional
Boolean cube `𝔹ⁿ ≃ Fin n → Bool`.

This file is completely *self‑contained* and makes **no assumptions** about later
lemmas (entropy, sunflowers, …).  It provides the basic objects and operations
that all subsequent modules (`entropy.lean`, `sunflower.lean`, `cover2.lean`, …)
re‑use.

Main contents
-------------

* `Point  n`      – a vertex of the Boolean cube `𝔹ⁿ`.
* `BFunc  n`      – a Boolean function `𝔹ⁿ → Bool`.
* `Family n`      – a (finite) family of Boolean functions.
* `Subcube n`     – a (partial) assignment of coordinates, i.e. a rectangular
                    subcube of `𝔹ⁿ`.
* Basic operations:
  * `Point.update`        – replace the value of one coordinate.
  * `BFunc.restrictCoord` – fix one input bit of a Boolean function.
  * `Subcube.mem`         – membership of a point in a subcube.
  * `Subcube.dimension`   – dimension (= number of *free* coordinates).
  * `Subcube.monochromaticFor` / `…ForFamily` – (joint) monochromaticity
    predicates.

The code is *purely definitional* — no theorems are proved here except simple
helper facts that the later files rely on (all proofs are by `simp` /
`aesop`‑style automation).
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

noncomputable section

open Classical
open Finset

namespace BoolFunc

/-- **A point of the Boolean `n`‑cube**.  We represent it as a function
`Fin n → Bool`.  Using `Fin n` (rather than `Nat`) keeps all indices
in‑range by construction. -/
abbrev Point (n : ℕ) : Type := Fin n → Bool

/-- **A Boolean function** on `n` input bits. -/
abbrev BFunc (n : ℕ) : Type := Point n → Bool

/-- The Boolean cube `Point n` has `2^n` vertices. -/
@[simp] lemma card_point (n : ℕ) : Fintype.card (Point n) = 2 ^ n := by
  classical
  simpa [Point, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- A *family* (finite set) of Boolean functions on `n` bits.  We use
`Finset` rather than `Set` so that cardinalities are definable.  Lean does
not have decidable equality for function types by default, so we work in
the classical (`noncomputable`) universe and add an explicit `DecidableEq`
instance via *choice*.  This is sufficient for all counting arguments in the
subsequent modules (no algorithmic use of equality is needed). -/
noncomputable
abbrev Family (n : ℕ) : Type := Finset (BFunc n)

instance {n : ℕ} : DecidableEq (BFunc n) := by
  classical
  exact fun f g =>
    if h : (∀ x, f x = g x) then isTrue (by
      have := funext (fun x => (h x))
      exact this)
    else isFalse (by
      intro hfg; apply h; intro x; rw [hfg])

/-! ### Subcubes (rectangles) -/

/-- A **subcube** (a.k.a. rectangle) of the Boolean cube `𝔹ⁿ`.
It is specified by

* `idx` – a finite set `I ⊆ {0, …, n−1}` of fixed coordinates;
* `val` – for each `i ∈ I`, the Boolean value to which that
          coordinate is frozen.

All other coordinates are *free*. -/
structure Subcube (n : ℕ) where
  idx : Finset (Fin n)
  val : (i : Fin n) → (h : i ∈ idx) → Bool
  deriving DecidableEq

namespace Subcube

variable {n : ℕ}

/-- **Membership** of a point in a subcube. -/
def mem (R : Subcube n) (x : Point n) : Prop :=
  ∀ (i : Fin n) (h : i ∈ R.idx), x i = R.val i h

-- local notation for subcube membership
notation x " ∈ₛ " R => Subcube.mem R x

/-- The *dimension* of a subcube = number of *free* coordinates. -/
def dimension (R : Subcube n) : ℕ :=
  n - R.idx.card

@[simp] lemma mem_of_not_fixed {R : Subcube n} {x : Point n} {i : Fin n}
    (_ : i ∉ R.idx) : R.mem x → True := by
  intro _; trivial

/-- **Monochromaticity for a single function**:
`R` is monochromatic for `f` if `f` is constant on `R`. -/
def monochromaticFor (R : Subcube n) (f : BFunc n) : Prop :=
  ∃ b : Bool, ∀ {x : Point n}, R.mem x → f x = b

/-- **Monochromaticity for a family**: `R` has one fixed colour
shared by *all* functions in `F`. -/
def monochromaticForFamily (R : Subcube n) (F : Family n) : Prop :=
  ∃ b : Bool, ∀ f, f ∈ F → ∀ {x : Point n}, R.mem x → f x = b

/-! ### Extending subcubes by fixing one more coordinate -/

/-- Add a new fixed coordinate `i := b` to a subcube `R`.
The index `i` need not be previously free, but in typical
applications we assume `i ∉ R.idx` so that the resulting
subcube describes a refinement of `R`. -/
def extend (R : Subcube n) (i : Fin n) (b : Bool) : Subcube n :=
  { idx := insert i R.idx
    val := fun j hj =>
      -- Inspect whether `j` is the newly inserted coordinate.
      if hji : j = i then by cases hji; exact b
      else
        -- Otherwise `j` was already fixed in `R`.
        let hj' : j ∈ R.idx := by
          have := Finset.mem_insert.mp hj
          cases this with
          | inl h => exact False.elim (hji h)
          | inr h => exact h
        R.val j hj' }

/-- Membership in the extended subcube equals membership in the
original subcube together with the fixed value on the new coordinate. -/
lemma mem_extend_iff {R : Subcube n} {i : Fin n} {b : Bool}
    {x : Point n} (hi : i ∉ R.idx) :
    (extend R i b).mem x ↔ x i = b ∧ R.mem x := by
  classical
  constructor
  · intro hx
    have hxi : x i = b := by
      have := hx i (by simp [extend])
      simpa [extend] using this
    refine ⟨hxi, ?_⟩
    intro j hj
    have hij : j ≠ i := by
      exact fun hji => hi (by simpa [hji] using hj)
    have hmem := hx j (by
      have : j ∈ insert i R.idx :=
        Finset.mem_insert.mpr (Or.inr hj)
      exact this)
    simpa [extend, hij] using hmem
  · rintro ⟨hxi, hxR⟩ j hj
    by_cases hji : j = i
    · subst hji; simpa [extend, hxi]
    ·
      have hjR : j ∈ R.idx := by
        have := Finset.mem_insert.mp hj
        cases this with
        | inl h => exact False.elim (hji h)
        | inr h => exact h
      have := hxR j hjR
      simpa [extend, hji] using this

/--
"Unfix" a coordinate of a subcube by removing it from the set of
frozen indices.  The resulting subcube agrees with `R` on all other
coordinates and no longer constrains the `i`-th bit.  This operation
is useful when normalising branch covers in the decision-tree
construction: after exploring the branch where `x i = b` we may
"forget" that `i` was fixed inside the subcubes returned by the
recursive call.
-/
def unfix (R : Subcube n) (i : Fin n) : Subcube n :=
  { idx := R.idx.erase i
    val := fun j hj =>
      -- Membership in the erased set provides a proof that `j ≠ i` and
      -- that `j` originally belonged to `R.idx`.
      let hjR : j ∈ R.idx := (Finset.mem_erase.mp hj).2
      R.val j hjR }

/--
Any point belonging to `R` also lies in `R.unfix i` since the latter
imposes only a subset of the original constraints.
-/
lemma mem_unfix_of_mem {R : Subcube n} {i : Fin n} {x : Point n}
    (hx : R.mem x) : (unfix (R := R) i).mem x := by
  intro j hj
  -- Extract the membership proof for `j` from the erased index set.
  have hjR : j ∈ R.idx := (Finset.mem_erase.mp hj).2
  -- `R.unfix i` uses the same Boolean value as `R` on coordinate `j`.
  have := hx j hjR
  simpa [unfix, hjR] using this

@[simp]
lemma idx_unfix (R : Subcube n) (i : Fin n) :
    i ∉ (unfix (R := R) i).idx := by
  classical
  simp [unfix]

end Subcube

/-! ### Basic point and function operations -/

section PointOps

variable {n : ℕ}

/-- **Update** a single coordinate of a point. -/
def Point.update (x : Point n) (i : Fin n) (b : Bool) : Point n :=
  fun j => if j = i then b else x j

@[simp] lemma Point.update_eq (x : Point n) (i : Fin n) (b : Bool) :
    (Point.update x i b) i = b := by
  simp [Point.update]

@[simp] lemma Point.update_neq (x : Point n) {i j : Fin n} (h : j ≠ i) (b : Bool) :
    (Point.update x i b) j = x j := by
  simp [Point.update, h]

@[simp] lemma Point.update_idem (x : Point n) (i : Fin n) (b : Bool) :
    Point.update (Point.update x i b) i b = Point.update x i b := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Point.update]
  · simp [Point.update, hk]

/-! ### Additional point update lemmas -/

@[simp] lemma Point.update_swap (x : Point n) {i j : Fin n} (h : i ≠ j)
    (b1 b2 : Bool) :
    Point.update (Point.update x i b1) j b2 =
      Point.update (Point.update x j b2) i b1 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Point.update, h]
  · by_cases hjk : k = j
    · subst hjk; simp [Point.update, hk]
    · simp [Point.update, hk, hjk]

/-! ### Flipping multiple coordinates -/

/-- `Point.flip x S` negates all coordinates of `x` listed in the finite set `S`. -/
def Point.flip (x : Point n) (S : Finset (Fin n)) : Point n :=
  fun i => if i ∈ S then ! x i else x i

@[simp] lemma Point.flip_apply_mem {x : Point n} {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ S) :
    Point.flip x S i = ! x i := by
  simp [Point.flip, hi]

@[simp] lemma Point.flip_apply_not_mem {x : Point n} {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) :
    Point.flip x S i = x i := by
  simp [Point.flip, hi]

@[simp] lemma Point.flip_empty (x : Point n) :
    Point.flip x (∅ : Finset (Fin n)) = x := by
  funext i; simp [Point.flip]

/-- Flipping a singleton set coincides with updating the corresponding
coordinate. -/
@[simp] lemma Point.flip_singleton (x : Point n) (i : Fin n) :
    Point.flip x ({i} : Finset (Fin n)) = Point.update x i (! x i) := by
  classical
  funext j
  by_cases hji : j = i
  · subst hji; simp [Point.flip, Point.update]
  · simp [Point.flip, Point.update, hji]

/-- Flipping after inserting a fresh coordinate `i` is the same as first
flipping `i` and then the original set. -/
@[simp] lemma Point.flip_insert (x : Point n) {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) :
    Point.flip x (insert i S) = Point.flip (Point.flip x ({i})) S := by
  classical
  funext j
  by_cases hji : j = i
  · subst hji
    simp [Point.flip, Finset.mem_insert, hi]
  · by_cases hjs : j ∈ S
    · simp [Point.flip, Finset.mem_insert, hji, hjs]
    · simp [Point.flip, Finset.mem_insert, hji, hjs]

/-- Flipping the same set twice returns to the original point. -/
@[simp] lemma Point.flip_flip (x : Point n) (S : Finset (Fin n)) :
    Point.flip (Point.flip x S) S = x := by
  classical
  funext i
  by_cases hi : i ∈ S
  · simp [Point.flip, hi]
  · simp [Point.flip, hi]

/-- If two points agree outside a finite set `A`, then flipping exactly the
coordinates where they differ recovers the second point. -/
lemma Point.flip_eq_of_eq_on_compl {x y : Point n} (A : Finset (Fin n))
    (h : ∀ i ∉ A, y i = x i) :
    Point.flip x (A.filter fun i => y i ≠ x i) = y := by
  classical
  funext i
  by_cases hiA : i ∈ A
  · by_cases hneq : y i = x i
    · have hiT : i ∉ A.filter fun j => y j ≠ x j := by
        simp [hiA, hneq]
      simp [Point.flip, hiT, hneq]  -- both sides equal `x i`
    · have hiT : i ∈ A.filter fun j => y j ≠ x j := by
        simp [hiA, hneq]
      -- `y i` must be the negation of `x i`
      have : y i = ! x i := by
        cases hxi : x i <;> cases hyi : y i <;> simp [hxi, hyi] at hneq ⊢
      simp [Point.flip, hiT, this]
  · have hiT : i ∉ A.filter fun j => y j ≠ x j := by
      simp [hiA]
    have : y i = x i := h i hiA
    simp [Point.flip, hiT, this]

/-- **A constant point** with the same Boolean value in every coordinate. -/
def Point.const (n : ℕ) (b : Bool) : Point n := fun _ => b

@[simp] lemma Point.const_apply (n : ℕ) (b : Bool) (i : Fin n) :
    (Point.const n b) i = b := rfl

/-! ### Coordinate support of a point -/

/-- Set of coordinates where the Boolean point `x` evaluates to `true`. -/
def supportPt (x : Point n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

@[simp] lemma mem_supportPt {x : Point n} {i : Fin n} :
    i ∈ supportPt (n := n) x ↔ x i = true := by
  classical
  simp [supportPt]

end PointOps

section Restrict

variable {n : ℕ}

/-- **Restriction of a Boolean function** by *fixing one input bit*.
The resulting function still has arity `n`; it ignores its `j`‑th
argument and uses the constant value `b` instead.  This choice avoids
dimension bookkeeping burden elsewhere. -/
def BFunc.restrictCoord (f : BFunc n) (j : Fin n) (b : Bool) : BFunc n :=
  fun x => f (Point.update x j b)

/-! A few helper lemmas used later. -/

@[simp] lemma restrictCoord_fixed {f : BFunc n} {j : Fin n} {b : Bool}
    {x : Point n} :
    (BFunc.restrictCoord f j b) (Point.update x j b) = f (Point.update x j b) := by
  simp [BFunc.restrictCoord]

@[simp] lemma restrictCoord_agrees
    {f : BFunc n} {j : Fin n} {b : Bool} {x : Point n}
    (h : x j = b) :
    (BFunc.restrictCoord f j b) x = f x := by
  have : Point.update x j b = x := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [Point.update, h]
    · simp [Point.update, hk]
  simp [BFunc.restrictCoord, this]

/-!
Equality of both `0`- and `1`-restrictions forces equality of the original
function.  This simple observation will later allow us to inject a family into
the product of its two coordinate restrictions.
-/
lemma eq_of_restrictCoord_eq {f g : BFunc n} {i : Fin n}
    (h0 : BFunc.restrictCoord f i false = BFunc.restrictCoord g i false)
    (h1 : BFunc.restrictCoord f i true = BFunc.restrictCoord g i true) :
    f = g := by
  classical
  funext x
  cases hxi : x i
  · -- When `x i = false`, the `false`-restriction recovers the value of `f x`.
    have h0' := congrArg (fun h => h x) h0
    have hf := restrictCoord_agrees (f := f) (j := i) (b := false)
      (x := x) (h := hxi)
    have hg := restrictCoord_agrees (f := g) (j := i) (b := false)
      (x := x) (h := hxi)
    simpa [hf, hg] using h0'
  · -- Otherwise use the `true`-restriction.
    have h1' := congrArg (fun h => h x) h1
    have hf := restrictCoord_agrees (f := f) (j := i) (b := true)
      (x := x) (h := hxi)
    have hg := restrictCoord_agrees (f := g) (j := i) (b := true)
      (x := x) (h := hxi)
    simpa [hf, hg] using h1'

/--
The mapping sending a function to the pair of its `0`- and `1`-restrictions on
coordinate `i` is injective.  Knowing how a function behaves on both halves of
the cube uniquely determines the original function.
-/
lemma restrict_pair_injective (i : Fin n) :
    Function.Injective
      (fun f : BFunc n =>
        (BFunc.restrictCoord f i false, BFunc.restrictCoord f i true)) := by
  intro f g hpair
  have h0 : BFunc.restrictCoord f i false = BFunc.restrictCoord g i false :=
    congrArg Prod.fst hpair
  have h1 : BFunc.restrictCoord f i true = BFunc.restrictCoord g i true :=
    congrArg Prod.snd hpair
  exact eq_of_restrictCoord_eq (i := i) h0 h1

/-! ### Restricting by multiple assignments -/

/--
Fix several coordinates of a Boolean function according to a list of
assignments.  Each pair `(i, b)` in the list freezes the `i`‑th coordinate
to the Boolean value `b`.  The function still has arity `n`; internally we
apply `BFunc.restrictCoord` for every entry of the list.-/
def BFunc.restrictAssignments (f : BFunc n) :
    List (Fin n × Bool) → BFunc n
  | [] => f
  | (i, b) :: p => BFunc.restrictAssignments (BFunc.restrictCoord f i b) p

/--
`satisfiesAssignments x p` means that the point `x` agrees with every
coordinate–value pair in the list `p`.
-/
def satisfiesAssignments (x : Point n) :
    List (Fin n × Bool) → Prop
  | [] => True
  | (i, b) :: p => x i = b ∧ satisfiesAssignments x p

@[simp] lemma restrictAssignments_nil (f : BFunc n) :
    BFunc.restrictAssignments (f := f) [] = f := rfl

@[simp] lemma restrictAssignments_cons (f : BFunc n)
    (i : Fin n) (b : Bool) (p : List (Fin n × Bool)) :
    BFunc.restrictAssignments (f := f) ((i, b) :: p) =
      BFunc.restrictAssignments
        (f := BFunc.restrictCoord f i b) p := rfl

@[simp] lemma satisfiesAssignments_nil (x : Point n) :
    satisfiesAssignments x [] := by trivial

lemma satisfiesAssignments_cons {x : Point n} {i : Fin n} {b : Bool}
    {p : List (Fin n × Bool)} :
    satisfiesAssignments x ((i, b) :: p) ↔
      x i = b ∧ satisfiesAssignments x p := Iff.rfl

/--
If a point `x` satisfies all assignments in `p`, restricting `f` by `p`
does not change the value at `x`.
-/
lemma restrictAssignments_agrees {f : BFunc n} {x : Point n}
    {p : List (Fin n × Bool)}
    (h : satisfiesAssignments x p) :
    BFunc.restrictAssignments (f := f) p x = f x := by
  induction p generalizing f with
  | nil =>
      simpa [BFunc.restrictAssignments, satisfiesAssignments] using h
  | cons hb tl ih =>
      rcases hb with ⟨i, b⟩
      rcases h with ⟨hx, hrest⟩
      have := ih (f := BFunc.restrictCoord f i b) hrest
      simpa [BFunc.restrictAssignments, satisfiesAssignments, hx,
        restrictCoord_agrees (f := f) (j := i) (b := b) (x := x) (h := hx)] using this

end Restrict

/-- The set of inputs on which a Boolean function outputs `true`. -/
noncomputable
def ones {n : ℕ} [Fintype (Point n)] (f : BFunc n) : Finset (Point n) :=
  Finset.univ.filter fun x => f x = true

@[simp] lemma mem_ones {n : ℕ} [Fintype (Point n)] {f : BFunc n} {x : Point n} :
    x ∈ ones f ↔ f x = true := by
  classical
  simp [ones]

/-! ### Basic probability on the Boolean cube -/

/-- Probability that a Boolean function outputs `true` under the uniform
distribution. -/
noncomputable def prob {n : ℕ} [Fintype (Point n)] (f : BFunc n) : ℝ :=
  ((ones f).card : ℝ) / (Fintype.card (Point n))

lemma prob_nonneg {n : ℕ} [Fintype (Point n)] (f : BFunc n) :
    0 ≤ prob f := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card (Point n)) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hnum : 0 ≤ ((ones f).card : ℝ) := by exact_mod_cast Nat.zero_le _
  have hden : 0 ≤ (Fintype.card (Point n) : ℝ) := le_of_lt hpos
  simpa [prob] using div_nonneg hnum hden

lemma prob_le_one {n : ℕ} [Fintype (Point n)] (f : BFunc n) :
    prob f ≤ 1 := by
  classical
  have hsubset : (ones f).card ≤ Fintype.card (Point n) := by
    simpa using (Finset.card_le_univ (s := ones f))
  have hnum : ((ones f).card : ℝ) ≤ (Fintype.card (Point n) : ℝ) := by
    exact_mod_cast hsubset
  have hden : 0 ≤ (Fintype.card (Point n) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Point n))
  have h := div_le_one_of_le₀ hnum hden
  simpa [prob] using h

/-- Probability that `f` evaluates to `true` when the `i`-th input bit is fixed
to `false`. -/
noncomputable def prob_restrict_false {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) : ℝ :=
  prob (BFunc.restrictCoord f i false)

/-- Probability that `f` evaluates to `true` when the `i`-th input bit is fixed
to `true`. -/
noncomputable def prob_restrict_true {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) : ℝ :=
  prob (BFunc.restrictCoord f i true)

@[simp] lemma prob_restrict_false_eq_discrete {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) :
    prob_restrict_false f i =
      ((ones (BFunc.restrictCoord f i false)).card : ℝ) /
        (Fintype.card (Point n)) := rfl

@[simp] lemma prob_restrict_true_eq_discrete {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) :
    prob_restrict_true f i =
      ((ones (BFunc.restrictCoord f i true)).card : ℝ) /
        (Fintype.card (Point n)) := rfl

/-- Restrict every function in a family by fixing the `i`‑th input bit to `b`. -/
noncomputable
def Family.restrict {n : ℕ} (F : Family n) (i : Fin n) (b : Bool) : Family n :=
  F.image fun f x => f (Point.update x i b)

namespace Family

variable {n : ℕ}

/-!
`mem_restrict` characterises membership in the restricted family.  A function
`g` lies in `F.restrict i b` iff it arises by restricting some `f ∈ F` on the
`i`‑th coordinate.
-/
@[simp] lemma mem_restrict {F : Family n} {i : Fin n} {b : Bool} {g : BFunc n} :
    g ∈ Family.restrict F i b ↔ ∃ f ∈ F, g = BFunc.restrictCoord f i b := by
  classical
  unfold Family.restrict
  constructor
  · intro hg
    rcases Finset.mem_image.mp hg with ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact Finset.mem_image.mpr ⟨f, hf, rfl⟩

/-!  A convenient elimination rule for membership in a restricted family.  The
`Family.mem_of_mem_restrict` lemma packages the forward direction of
`mem_restrict` so that a witness from the original family can be retrieved
directly. -/
lemma mem_of_mem_restrict {F : Family n} {i : Fin n} {b : Bool} {g : BFunc n}
    (hg : g ∈ Family.restrict F i b) :
    ∃ f ∈ F, g = BFunc.restrictCoord f i b :=
  (mem_restrict (F := F) (i := i) (b := b) (g := g)).1 hg

/-! The restricted family is no larger than the original one since `Finset.image`
never increases cardinalities. -/
lemma card_restrict_le (F : Family n) (i : Fin n) (b : Bool) :
    (Family.restrict F i b).card ≤ F.card := by
  classical
  unfold Family.restrict
  simpa using Finset.card_image_le (s := F) (f := fun f => (fun x => f (Point.update x i b)))

/-! Restriction is monotone with respect to set inclusion of families. -/
lemma restrict_mono {F G : Family n} (h : F ⊆ G) (i : Fin n) (b : Bool) :
    Family.restrict F i b ⊆ Family.restrict G i b := by
  intro g hg
  rcases (mem_restrict.mp hg) with ⟨f, hf, rfl⟩
  exact mem_restrict.mpr ⟨f, h hf, rfl⟩

/-!
The size of the original family is bounded by the product of the sizes of its
two coordinate restrictions.  The proof embeds `F` into the Cartesian product of
`F.restrict i false` and `F.restrict i true` via the injective mapping from
`restrict_pair_injective`.
-/
lemma card_le_mul_card_restrict (F : Family n) (i : Fin n) :
    F.card ≤
      (Family.restrict F i false).card * (Family.restrict F i true).card := by
  classical
  -- Map each function to the pair of its restrictions and use injectivity.
  let pairMap :=
    fun f : BFunc n =>
      (BFunc.restrictCoord f i false, BFunc.restrictCoord f i true)
  have hinj : Function.Injective pairMap :=
    restrict_pair_injective (i := i)
  have hcard_img : (F.image pairMap).card = F.card :=
    Finset.card_image_of_injective (s := F) (f := pairMap) hinj
  -- Every such pair lies in the product of the two restricted families.
  have hsubset : F.image pairMap ⊆
      Finset.product (Family.restrict F i false) (Family.restrict F i true) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨f, hfF, rfl⟩
    refine Finset.mem_product.2 ?_
    constructor <;> exact Finset.mem_image.mpr ⟨f, hfF, rfl⟩
  -- Cardinalities transfer along the subset relation.
  have hcard_le := Finset.card_le_card hsubset
  -- Rewrite the image and product cardinalities to obtain the claim.
  simpa [hcard_img, Finset.card_product] using hcard_le

/--
If two distinct functions from a family become identical after restricting a
coordinate, that branch of the family is strictly smaller.  Intuitively,
restricting collapses `f` and `g` into the same element of the image, so the
resulting family loses at least one member.-/
lemma card_restrict_lt_of_restrict_eq {F : Family n} (i : Fin n) (b : Bool)
    {f g : BFunc n} (hf : f ∈ F) (hg : g ∈ F) (hfg : f ≠ g)
    (heq : BFunc.restrictCoord f i b = BFunc.restrictCoord g i b) :
    (Family.restrict F i b).card < F.card := by
  classical
  -- Removing `f` from the family does not change the restricted image:
  -- `f` and `g` map to the same function, so `g` still covers that value.
  have himg_eq :
      Family.restrict F i b = Family.restrict (Finset.erase F f) i b := by
    -- Compare membership elementwise in both images.
    unfold Family.restrict
    ext h; constructor
    · intro hh
      rcases Finset.mem_image.mp hh with ⟨f', hf', rfl⟩
      by_cases hff' : f' = f
      · -- The image comes from `f`; replace it by `g` from the erased set.
        have hg' : g ∈ Finset.erase F f :=
          Finset.mem_erase.mpr ⟨hfg.symm, hg⟩
        refine Finset.mem_image.mpr ?_
        -- `heq` witnesses that the restricted versions coincide.
        have hrestrict :
            BFunc.restrictCoord g i b = BFunc.restrictCoord f' i b := by
          simpa [hff'] using heq.symm
        exact ⟨g, hg', hrestrict⟩
      · -- Any other element already lies in the erased family.
        have hf'' : f' ∈ Finset.erase F f :=
          Finset.mem_erase.mpr ⟨hff', hf'⟩
        exact Finset.mem_image.mpr ⟨f', hf'', rfl⟩
    · intro hh
      -- Every image from the erased family trivially comes from the original one.
      rcases Finset.mem_image.mp hh with ⟨f', hf', rfl⟩
      have hf'F : f' ∈ F := by
        rcases Finset.mem_erase.mp hf' with ⟨_, hfF⟩; exact hfF
      exact Finset.mem_image.mpr ⟨f', hf'F, rfl⟩
  -- The restricted family therefore has at most `F.erase f` many elements.
  have hle : (Family.restrict F i b).card ≤ (Finset.erase F f).card := by
    simpa [himg_eq] using
      (Family.card_restrict_le (F := Finset.erase F f) (i := i) (b := b))
  -- Removing a member strictly decreases the size of the family.
  have hlt_erase : (Finset.erase F f).card < F.card := by
    -- `card (erase f) = card F - 1`, hence it is strictly smaller than `card F`.
    have hpos : 0 < F.card := Finset.card_pos.mpr ⟨f, hf⟩
    have hcard := Finset.card_erase_of_mem hf
    -- Rephrase the equality `card (erase f) = card F - 1`.
    have hsucc : (Finset.erase F f).card + 1 = F.card := by
      have hsub : F.card - 1 + 1 = F.card :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
      simpa [hcard, Nat.succ_eq_add_one, hsub] using
        congrArg (fun t => t + 1) hcard
    -- The desired inequality follows from `a < a + 1`.
    have hlt' : (Finset.erase F f).card < (Finset.erase F f).card + 1 :=
      Nat.lt_succ_self _
    simpa [hsucc] using hlt'
  exact lt_of_le_of_lt hle hlt_erase

end Family

namespace Subcube

/--
If a subcube `R` is monochromatic for the restricted family `F.restrict i b`
and the coordinate `i` is not yet fixed in `R`, then the subcube obtained by
also fixing `x_i = b` is monochromatic for the original family `F`.
-/
lemma monochromaticForFamily_extend_restrict {n : ℕ} {F : Family n}
    {R : Subcube n} {i : Fin n} {b : Bool} (hi : i ∉ R.idx)
    (hmono : monochromaticForFamily R (Family.restrict F i b)) :
    monochromaticForFamily (extend R i b) F := by
  classical
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f hf x hx
  -- `x` lies in the extended cube, hence in the original one and with `x i = b`.
  have hxR : R.mem x :=
    ((mem_extend_iff (R := R) (i := i) (b := b) (x := x) hi).1 hx).2
  have hxi : x i = b :=
    ((mem_extend_iff (R := R) (i := i) (b := b) (x := x) hi).1 hx).1
  -- the restricted version of `f` belongs to the restricted family
  have hf0 : BFunc.restrictCoord f i b ∈ Family.restrict F i b :=
    (Family.mem_restrict).2 ⟨f, hf, rfl⟩
  -- monochromaticity on `R` transfers to the extended cube using the above facts
  have := hc (BFunc.restrictCoord f i b) hf0 (x := x) hxR
  simpa [restrictCoord_agrees (f := f) (j := i) (b := b) (x := x) hxi] using this

/--
If a subcube `R` is monochromatic for the restriction of a single function `f`
to the branch `xᵢ = b` and `R` does not fix `i`, then the extended subcube with
`xᵢ = b` is monochromatic for `f`.  This is the single‑function counterpart of
`monochromaticForFamily_extend_restrict`.
-/
lemma monochromaticFor_extend_restrict {n : ℕ} {f : BFunc n}
    {R : Subcube n} {i : Fin n} {b : Bool} (hi : i ∉ R.idx)
    (hmono : Subcube.monochromaticFor R (BFunc.restrictCoord f i b)) :
    Subcube.monochromaticFor (Subcube.extend R i b) f := by
  classical
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x hx
  have hxR : R.mem x :=
    ((Subcube.mem_extend_iff (R := R) (i := i) (b := b) (x := x) hi).1 hx).2
  have hxi : x i = b :=
    ((Subcube.mem_extend_iff (R := R) (i := i) (b := b) (x := x) hi).1 hx).1
  have hxval := hc hxR
  simpa [restrictCoord_agrees (f := f) (j := i) (b := b)
            (x := x) hxi] using hxval

end Subcube

/-! ### Essential coordinate support -/

/-- Set of coordinates on which `f` depends essentially.  A coordinate `i`
belongs to `support f` if flipping the `i`‑th bit of some input changes the
output. -/
noncomputable
def support {n : ℕ} (f : BFunc n) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x : Point n, f x ≠ f (Point.update x i (!x i))

@[simp] lemma mem_support_iff {n : ℕ} {f : BFunc n} {i : Fin n} :
    i ∈ support f ↔ ∃ x : Point n, f x ≠ f (Point.update x i (!x i)) := by
  classical
  simp [support]

/-! ### Families of supports -/

namespace Family

variable {n : ℕ}

/-/ The collection of essential supports of all functions in the family. -/
noncomputable
def supports (F : Family n) : Finset (Finset (Fin n)) :=
  F.image support

@[simp] lemma mem_supports {F : Family n} {s : Finset (Fin n)} :
    s ∈ supports F ↔ ∃ f ∈ F, support f = s := by
  classical
  unfold supports
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨f, hf, hfs⟩
    exact ⟨f, hf, hfs⟩
  · rintro ⟨f, hf, rfl⟩
    exact Finset.mem_image.mpr ⟨f, hf, rfl⟩

@[simp] lemma supports_card_le (F : Family n) :
    (supports F).card ≤ F.card := by
  classical
  simpa [supports] using
    (Finset.card_image_le (s := F) (f := support))

end Family

/-! ## Re‑exports to avoid long qualified names downstream -/
export Subcube (mem dimension monochromaticFor monochromaticForFamily)
export Point (update)

end BoolFunc

end
