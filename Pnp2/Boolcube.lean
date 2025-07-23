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


end Subcube

abbrev BoolFun (n : ℕ) := Point n → Bool
abbrev Family  (n : ℕ) := Finset (BoolFun n)

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
The current development in `cover.lean` relies directly on the
formalised `Sunflower.sunflower_exists` from `sunflower.lean`, so this
placeholder proof has been removed.  The full cover construction is
postponed in this lightweight version.
-/

end Boolcube
