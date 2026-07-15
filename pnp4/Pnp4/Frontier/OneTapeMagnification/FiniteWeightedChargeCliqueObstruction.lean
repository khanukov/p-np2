import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Clique obstructions to positive weighted row charge

A positive Schur weight cannot hide a dense positive subkernel.  This file
records the exact finite obstruction: if every off-diagonal entry on a
nonempty finite set is at least `edgeFloor`, then any positive row-charge
subeigenvector at budget `budget` forces

`(card - 1) * edgeFloor <= budget`.

The proof sums all row inequalities, so it applies to arbitrary positive
weights, not only uniform or residual-mass candidates.  It is an analytic
diagnostic; it does not assert that the mandatory canonical selector contains
such a clique.
-/

noncomputable section

open scoped BigOperators

open DPTWStructuredWeightedCharge

namespace FiniteWeightedChargeCliqueObstruction

/-- A complete positive subkernel has weighted degree at least its
off-diagonal floor times `card - 1`, for every possible positive diagonal
scaling. -/
theorem card_sub_one_mul_edgeFloor_le_budget
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι -> ι -> Rat)
    (weight : ι -> Rat) (edgeFloor budget : Rat)
    (hnonempty : indices.Nonempty)
    (hweight : ∀ index ∈ indices, 0 < weight index)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 <= kernel left right)
    (hoffDiagonalFloor :
      ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right ->
        edgeFloor <= kernel left right)
    (hrow : ∀ left ∈ indices,
      weightedRowCharge indices kernel weight left <=
        budget * weight left) :
    ((indices.card : Rat) - 1) * edgeFloor <= budget := by
  classical
  let totalWeight : Rat := ∑ index ∈ indices, weight index
  have htotalWeight : 0 < totalWeight := by
    obtain ⟨index, hindex⟩ := hnonempty
    have hsingle : weight index <= totalWeight := by
      dsimp [totalWeight]
      exact Finset.single_le_sum
        (fun other hother => le_of_lt (hweight other hother)) hindex
    exact lt_of_lt_of_le (hweight index hindex) hsingle
  have hrowLower (left : ι) (hleft : left ∈ indices) :
      edgeFloor * (totalWeight - weight left) <=
        weightedRowCharge indices kernel weight left := by
    have heraseWeight :
        (∑ right ∈ indices.erase left, weight right) =
          totalWeight - weight left := by
      have hsplit := Finset.sum_erase_add indices weight hleft
      dsimp [totalWeight]
      linarith
    have hoffDiagonal :
        (∑ right ∈ indices.erase left, edgeFloor * weight right) <=
          ∑ right ∈ indices.erase left,
            kernel left right * weight right := by
      apply Finset.sum_le_sum
      intro right hright
      have hright' := (Finset.mem_erase.mp hright)
      exact mul_le_mul_of_nonneg_right
        (hoffDiagonalFloor left hleft right hright'.2 (Ne.symm hright'.1))
        (le_of_lt (hweight right hright'.2))
    have hdiagonal : 0 <= kernel left left * weight left :=
      mul_nonneg (hkernelNonnegative left hleft left hleft)
        (le_of_lt (hweight left hleft))
    calc
      edgeFloor * (totalWeight - weight left) =
          ∑ right ∈ indices.erase left, edgeFloor * weight right := by
            rw [← heraseWeight]
            simp only [Finset.mul_sum]
      _ <= ∑ right ∈ indices.erase left,
          kernel left right * weight right := hoffDiagonal
      _ <= (∑ right ∈ indices.erase left,
          kernel left right * weight right) +
            kernel left left * weight left := le_add_of_nonneg_right hdiagonal
      _ = weightedRowCharge indices kernel weight left := by
        unfold weightedRowCharge
        exact Finset.sum_erase_add indices
          (fun right => kernel left right * weight right) hleft
  have hsumDifference :
      (∑ left ∈ indices,
          edgeFloor * (totalWeight - weight left)) =
        (((indices.card : Rat) - 1) * edgeFloor) * totalWeight := by
    calc
      (∑ left ∈ indices,
          edgeFloor * (totalWeight - weight left)) =
          ∑ left ∈ indices,
            (edgeFloor * totalWeight - edgeFloor * weight left) := by
              apply Finset.sum_congr rfl
              intro left _hleft
              ring
      _ = (indices.card : Rat) * (edgeFloor * totalWeight) -
          edgeFloor * totalWeight := by
            rw [Finset.sum_sub_distrib]
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [← Finset.mul_sum]
      _ = (((indices.card : Rat) - 1) * edgeFloor) * totalWeight := by
        ring
  have hsummed :
      (((indices.card : Rat) - 1) * edgeFloor) * totalWeight <=
        budget * totalWeight := by
    calc
      (((indices.card : Rat) - 1) * edgeFloor) * totalWeight =
          ∑ left ∈ indices,
            edgeFloor * (totalWeight - weight left) := by
        exact hsumDifference.symm
      _ <= ∑ left ∈ indices,
          weightedRowCharge indices kernel weight left := by
        apply Finset.sum_le_sum
        intro left hleft
        exact hrowLower left hleft
      _ <= ∑ left ∈ indices, budget * weight left := by
        apply Finset.sum_le_sum
        intro left hleft
        exact hrow left hleft
      _ = budget * totalWeight := by
        dsimp [totalWeight]
        rw [Finset.mul_sum]
  exact (mul_le_mul_right htotalWeight).mp hsummed

/-- Contrapositive form: if the clique floor already exceeds the budget,
there are no positive weights satisfying every row inequality. -/
theorem no_positive_weight_of_budget_lt_card_sub_one_mul_edgeFloor
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι -> ι -> Rat)
    (edgeFloor budget : Rat)
    (hnonempty : indices.Nonempty)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 <= kernel left right)
    (hoffDiagonalFloor :
      ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right ->
        edgeFloor <= kernel left right)
    (hobstruction : budget < ((indices.card : Rat) - 1) * edgeFloor) :
    ¬ ∃ weight : ι -> Rat,
        (∀ index ∈ indices, 0 < weight index) ∧
        ∀ left ∈ indices,
          weightedRowCharge indices kernel weight left <=
            budget * weight left := by
  rintro ⟨weight, hweight, hrow⟩
  have hnecessary := card_sub_one_mul_edgeFloor_le_budget
    indices kernel weight edgeFloor budget hnonempty hweight
      hkernelNonnegative hoffDiagonalFloor hrow
  exact (not_le_of_gt hobstruction) hnecessary

/-- Ambient-set version.  A positive clique obstructs a row bound even when
the displayed rows sum over a larger active set: all extra kernel terms are
nonnegative. -/
theorem card_sub_one_mul_edgeFloor_le_budget_of_subset
    {ι : Type*} [DecidableEq ι]
    (clique ambient : Finset ι) (kernel : ι -> ι -> Rat)
    (weight : ι -> Rat) (edgeFloor budget : Rat)
    (hnonempty : clique.Nonempty) (hsubset : clique ⊆ ambient)
    (hweight : ∀ index ∈ ambient, 0 < weight index)
    (hkernelNonnegative :
      ∀ left ∈ ambient, ∀ right ∈ ambient, 0 <= kernel left right)
    (hoffDiagonalFloor :
      ∀ left ∈ clique, ∀ right ∈ clique, left ≠ right ->
        edgeFloor <= kernel left right)
    (hrow : ∀ left ∈ ambient,
      weightedRowCharge ambient kernel weight left <=
        budget * weight left) :
    ((clique.card : Rat) - 1) * edgeFloor <= budget := by
  apply card_sub_one_mul_edgeFloor_le_budget
    clique kernel weight edgeFloor budget hnonempty
  · intro index hindex
    exact hweight index (hsubset hindex)
  · intro left hleft right hright
    exact hkernelNonnegative left (hsubset hleft) right (hsubset hright)
  · exact hoffDiagonalFloor
  · intro left hleft
    calc
      weightedRowCharge clique kernel weight left <=
          weightedRowCharge ambient kernel weight left := by
        unfold weightedRowCharge
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun right hright _hnotClique =>
            mul_nonneg
              (hkernelNonnegative left (hsubset hleft) right hright)
              (le_of_lt (hweight right hright)))
      _ <= budget * weight left := hrow left (hsubset hleft)

end FiniteWeightedChargeCliqueObstruction
end

end OneTapeMagnification
end Frontier
end Pnp4
