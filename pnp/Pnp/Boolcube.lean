import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Pnp.BoolFunc

open BoolFunc

namespace Boolcube

-- Basic objects: points, subcubes and Boolean functions.

variable {n : ℕ}

abbrev Point (n : ℕ) := Fin n → Bool

structure Subcube (n : ℕ) where
  fix : Fin n → Option Bool -- none ⇒ "coordinate is free"

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

/-! ### Cardinal halving for point sets (axiom) -/

axiom exists_coord_card_drop
    (hn : 2 ≤ n)
    {F : Finset (Point n)} (hF : F.Nonempty) :
    ∃ i : Fin n, ∃ b : Bool,
      (coordSlice i b F).card ≤ F.card - F.card / n

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
