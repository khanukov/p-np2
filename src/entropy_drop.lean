/-
  Lemma: exists_coord_card_drop
  Author: Dmitry Khanukov
  This file is self-contained; it compiles against mathlib4 ≥ 4.8.0.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

variable {n : ℕ}

/-- Subfamily of `F` consisting of functions whose value at `i` equals `b`. -/
def coordSlice {n : ℕ}
    (i : Fin n) (b : Bool) (F : Finset (Fin n → Bool)) :
    Finset (Fin n → Bool) :=
  F.filter (fun f ↦ f i = b)

namespace coordSlice

@[simp]
lemma card_le (i : Fin n) (b : Bool) (F : Finset (Fin n → Bool)) :
    (coordSlice i b F).card ≤ F.card := by
  -- Filtering can only remove elements, so the card does not increase.
  exact card_filter_le _ _

@[simp]
lemma disj (i : Fin n) (F : Finset (Fin n → Bool)) :
    Disjoint (coordSlice i true F) (coordSlice i false F) := by
  -- Slices with different bit values are disjoint.
  intro x hxT hxF
  simp [coordSlice] at hxT hxF
  have : (x i) = true ∧ (x i) = false := ⟨hxT.2, hxF.2⟩
  cases this with
  | intro hT hF => cases hT.trans hF

lemma partition (i : Fin n) (F : Finset (Fin n → Bool)) :
    (coordSlice i true F).card + (coordSlice i false F).card = F.card := by
  classical
  have hdisj := disj i F
  -- Filtering by a predicate and its negation partitions the set.
  have hunion : (coordSlice i true F) ∪ (coordSlice i false F) = F := by
    ext f; simp [coordSlice, Bool.decEq_true, Bool.decEq_false]
  have := card_union_of_disjoint (s := coordSlice i true F)
    (t := coordSlice i false F) hdisj
  simpa [hunion] using this

end coordSlice

open coordSlice

/--
**Entropy drop lemma.**
For a nonempty family `F` there exists a coordinate `i` and a bit `b`
such that fixing them reduces the family size by at least `|F|/n`.
-/
lemma exists_coord_card_drop
    (hn : 2 ≤ n)
    {F : Finset (Fin n → Bool)} (hF : F.Nonempty) :
    ∃ i : Fin n, ∃ b : Bool,
      (coordSlice i b F).card ≤ F.card - F.card / n := by
  classical
  -- Assume no such coordinate exists.
  by_contra h
  -- Unpack the negated existential.
  push_neg at h
  -- Pick an arbitrary `i`.
  have hsum (i : Fin n) :
      (coordSlice i true F).card > F.card - F.card / n
    ∧ (coordSlice i false F).card > F.card - F.card / n := h i
  -- Sum the two bounds.
  have hlt : (coordSlice 0 true F).card + (coordSlice 0 false F).card
                > 2 * (F.card - F.card / n) := by
    have hi := hsum 0
    have hadd := add_lt_add_of_lt_of_lt hi.1 hi.2
    simpa [two_mul] using hadd
  have hEq : (coordSlice 0 true F).card + (coordSlice 0 false F).card = F.card :=
    partition 0 F
  -- Substitute into the equality and derive a contradiction.
  have : (F.card : ℝ) > 2 * (F.card - F.card / n) := by
    have hEq' := congrArg (fun k : ℕ => (k : ℝ)) hEq
    have hlt' : ((coordSlice 0 true F).card + (coordSlice 0 false F).card : ℝ)
        > 2 * ((F.card - F.card / n) : ℝ) := by exact_mod_cast hlt
    simpa [hEq'] using hlt'
  -- Compute the right-hand side and compare with the left.
  have rhs_le : 2 * (F.card - F.card / n) ≤ (F.card : ℝ) := by
    have : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    have hdiv : (F.card : ℝ) / n ≤ (F.card : ℝ) / 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpos : (0 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
      exact div_le_div_of_le_of_nonneg hpos this
    nlinarith
  have hcontr := lt_of_lt_of_le this rhs_le
  exact lt_irrefl _ hcontr
