import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredMaskRank
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Abel transfer for dyadic rank weights

This standalone module isolates the summation-by-parts statement needed to
control variation of the actual inverse-rank mask weight.  It does not assert
the selector-specific tail inequalities supplied as hypotheses below.
-/

namespace FiniteRankWeightAbelVariation

open scoped BigOperators
open DPTWStructuredMaskRank
open FiniteBooleanDualAliasConvolutionTransfer

/-! ## Exact dyadic summation by parts -/

/-- The inverse power of two attached to an integer rank. -/
def dyadicRankWeight (rank : Nat) : ℚ :=
  1 / (2 : ℚ) ^ rank

@[simp]
theorem dyadicRankWeight_zero : dyadicRankWeight 0 = 1 := by
  norm_num [dyadicRankWeight]

theorem dyadicRankWeight_succ (rank : Nat) :
    dyadicRankWeight (rank + 1) = dyadicRankWeight rank / 2 := by
  unfold dyadicRankWeight
  rw [pow_succ]
  ring

theorem dyadicRankWeight_succ_sub (rank : Nat) :
    dyadicRankWeight (rank + 1) - dyadicRankWeight rank =
      -dyadicRankWeight (rank + 1) := by
  rw [dyadicRankWeight_succ]
  ring

/-- Pointwise telescoping of the dyadic weight across `steps` rank
increments. -/
theorem dyadicRankWeight_add_sub_eq_neg_sum_range
    (baseRank steps : Nat) :
    dyadicRankWeight (baseRank + steps) - dyadicRankWeight baseRank =
      -(∑ offset ∈ Finset.range steps,
          dyadicRankWeight (baseRank + offset + 1)) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Finset.sum_range_succ]
      calc
        dyadicRankWeight (baseRank + (steps + 1)) -
            dyadicRankWeight baseRank =
            (dyadicRankWeight ((baseRank + steps) + 1) -
              dyadicRankWeight (baseRank + steps)) +
              (dyadicRankWeight (baseRank + steps) -
                dyadicRankWeight baseRank) := by
          rw [show baseRank + (steps + 1) = (baseRank + steps) + 1 by omega]
          ring
        _ = -dyadicRankWeight ((baseRank + steps) + 1) +
            -(∑ offset ∈ Finset.range steps,
              dyadicRankWeight (baseRank + offset + 1)) := by
          rw [dyadicRankWeight_succ_sub, ih]
        _ = -(∑ offset ∈ Finset.range steps,
              dyadicRankWeight (baseRank + offset + 1) +
            dyadicRankWeight (baseRank + steps + 1)) := by
          ring

/-- Interval form of the dyadic telescoping identity. -/
theorem dyadicRankWeight_sub_eq_neg_sum_Ico
    {baseRank rank : Nat} (hbase : baseRank ≤ rank) :
    dyadicRankWeight rank - dyadicRankWeight baseRank =
      -(∑ level ∈ Finset.Ico baseRank rank,
          dyadicRankWeight (level + 1)) := by
  have hadd : baseRank + (rank - baseRank) = rank := by omega
  have h := dyadicRankWeight_add_sub_eq_neg_sum_range
    baseRank (rank - baseRank)
  rw [hadd] at h
  rw [Finset.sum_Ico_eq_sum_range]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- The signed mass above one strict rank threshold. -/
def strictRankTailSum {Index : Type*} [Fintype Index]
    (rank : Index → Nat) (term : Index → ℚ) (level : Nat) : ℚ :=
  ∑ index : Index, if level < rank index then term index else 0

theorem sum_Ico_rank_eq_sum_Ico_upper_ite
    (f : Nat → ℚ) {baseRank rank upperRank : Nat}
    (hupper : rank ≤ upperRank) :
    (∑ level ∈ Finset.Ico baseRank rank, f level) =
      ∑ level ∈ Finset.Ico baseRank upperRank,
        if level < rank then f level else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext level
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  · intro level hlevel
    rfl

/-- Exact Abel decomposition.  Variation of an inverse-rank weight is a
negative dyadic average of the strict rank-tail sums. -/
theorem dyadicVariation_eq_neg_sum_rankTails
    {Index : Type*} [Fintype Index]
    (rank : Index → Nat) (term : Index → ℚ)
    (baseRank upperRank : Nat)
    (hlower : ∀ index, baseRank ≤ rank index)
    (hupper : ∀ index, rank index ≤ upperRank) :
    (∑ index : Index,
        (dyadicRankWeight (rank index) - dyadicRankWeight baseRank) *
          term index) =
      -(∑ level ∈ Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) *
            strictRankTailSum rank term level) := by
  classical
  calc
    (∑ index : Index,
        (dyadicRankWeight (rank index) - dyadicRankWeight baseRank) *
          term index) =
        ∑ index : Index,
          ∑ level ∈ Finset.Ico baseRank upperRank,
            if level < rank index then
              -(dyadicRankWeight (level + 1) * term index)
            else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      rw [dyadicRankWeight_sub_eq_neg_sum_Ico (hlower index)]
      calc
        (-(∑ level ∈ Finset.Ico baseRank (rank index),
              dyadicRankWeight (level + 1))) * term index =
            ∑ level ∈ Finset.Ico baseRank (rank index),
              -(dyadicRankWeight (level + 1) * term index) := by
          rw [neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
        _ = ∑ level ∈ Finset.Ico baseRank upperRank,
              if level < rank index then
                -(dyadicRankWeight (level + 1) * term index)
              else 0 :=
          sum_Ico_rank_eq_sum_Ico_upper_ite _ (hupper index)
    _ = ∑ level ∈ Finset.Ico baseRank upperRank,
          ∑ index : Index,
            if level < rank index then
              -(dyadicRankWeight (level + 1) * term index)
            else 0 := by
      rw [Finset.sum_comm]
    _ = -(∑ level ∈ Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) *
            strictRankTailSum rank term level) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro level _
      unfold strictRankTailSum
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro index _
      by_cases hlevel : level < rank index <;> simp [hlevel]

theorem dyadicRankWeight_nonneg (rank : Nat) :
    0 ≤ dyadicRankWeight rank := by
  unfold dyadicRankWeight
  positivity

/-- Rank-tail lower bounds are sufficient for an upper bound on the dyadic
weight variation.  The constants are the exact successive weight drops. -/
theorem dyadicVariation_le_weightedTailBudgets
    {Index : Type*} [Fintype Index]
    (rank : Index → Nat) (term : Index → ℚ)
    (baseRank upperRank : Nat)
    (tailBudget : Nat → ℚ)
    (hlower : ∀ index, baseRank ≤ rank index)
    (hupper : ∀ index, rank index ≤ upperRank)
    (htail : ∀ level ∈ Finset.Ico baseRank upperRank,
      -tailBudget level ≤ strictRankTailSum rank term level) :
    (∑ index : Index,
        (dyadicRankWeight (rank index) - dyadicRankWeight baseRank) *
          term index) ≤
      ∑ level ∈ Finset.Ico baseRank upperRank,
        dyadicRankWeight (level + 1) * tailBudget level := by
  rw [dyadicVariation_eq_neg_sum_rankTails
    rank term baseRank upperRank hlower hupper]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro level hlevel
  have hnegTail :
      -strictRankTailSum rank term level ≤ tailBudget level := by
    linarith [htail level hlevel]
  calc
    -(dyadicRankWeight (level + 1) *
        strictRankTailSum rank term level) =
        dyadicRankWeight (level + 1) *
          (-strictRankTailSum rank term level) := by ring
    _ ≤ dyadicRankWeight (level + 1) * tailBudget level :=
      mul_le_mul_of_nonneg_left hnegTail
        (dyadicRankWeight_nonneg (level + 1))

/-- Exact total mass of the dyadic rank drops on a finite interval. -/
theorem sum_dyadicRankWeight_succ_Ico
    {baseRank upperRank : Nat} (hbase : baseRank ≤ upperRank) :
    (∑ level ∈ Finset.Ico baseRank upperRank,
        dyadicRankWeight (level + 1)) =
      dyadicRankWeight baseRank - dyadicRankWeight upperRank := by
  have htelescoping :=
    dyadicRankWeight_sub_eq_neg_sum_Ico hbase
  linarith

/-- Uniform rank-tail control gives the sharp finite geometric constant
`2^{-baseRank} - 2^{-upperRank}`. -/
theorem dyadicVariation_le_uniformTailBudget
    {Index : Type*} [Fintype Index]
    (rank : Index → Nat) (term : Index → ℚ)
    (baseRank upperRank : Nat) (tailBudget : ℚ)
    (hbase : baseRank ≤ upperRank)
    (hlower : ∀ index, baseRank ≤ rank index)
    (hupper : ∀ index, rank index ≤ upperRank)
    (htail : ∀ level ∈ Finset.Ico baseRank upperRank,
      -tailBudget ≤ strictRankTailSum rank term level) :
    (∑ index : Index,
        (dyadicRankWeight (rank index) - dyadicRankWeight baseRank) *
          term index) ≤
      (dyadicRankWeight baseRank - dyadicRankWeight upperRank) *
        tailBudget := by
  calc
    (∑ index : Index,
        (dyadicRankWeight (rank index) - dyadicRankWeight baseRank) *
          term index) ≤
        ∑ level ∈ Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) * tailBudget := by
      exact dyadicVariation_le_weightedTailBudgets
        rank term baseRank upperRank (fun _ => tailBudget)
          hlower hupper htail
    _ = (∑ level ∈ Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1)) * tailBudget := by
      rw [Finset.sum_mul]
    _ = (dyadicRankWeight baseRank - dyadicRankWeight upperRank) *
          tailBudget := by
      rw [sum_dyadicRankWeight_succ_Ico hbase]

/-! ## Actual prefix-constraint rank -/

/-- Adding support points cannot decrease the rank of the structured prefix
constraint map. -/
theorem supportPrefixConstraintRank_mono
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    {small large : Finset (Fin (2 ^ n))} (hsubset : small ⊆ large) :
    supportPrefixConstraintRank n k tailBits hn htail small ≤
      supportPrefixConstraintRank n k tailBits hn htail large := by
  let smallMap := supportPrefixConstraintMap
    n k tailBits hn htail small
  let largeMap := supportPrefixConstraintMap
    n k tailBits hn htail large
  let restrictMap := prefixConstraintRestrictionMap tailBits hsubset
  have hcomp : restrictMap.comp largeMap = smallMap := by
    exact prefixConstraintRestrictionMap_comp
      n k tailBits hn htail hsubset
  have hrank : (restrictMap.comp largeMap).rank ≤ largeMap.rank :=
    LinearMap.rank_comp_le_right largeMap restrictMap
  rw [hcomp] at hrank
  unfold supportPrefixConstraintRank
  change Module.finrank (ZMod 2) (LinearMap.range smallMap) ≤
    Module.finrank (ZMod 2) (LinearMap.range largeMap)
  have hcast :
      (Module.finrank (ZMod 2) (LinearMap.range smallMap) : Cardinal) ≤
        (Module.finrank (ZMod 2) (LinearMap.range largeMap) : Cardinal) := by
    rw [Module.finrank_eq_rank, Module.finrank_eq_rank]
    exact hrank
  exact_mod_cast hcast

end FiniteRankWeightAbelVariation
end OneTapeMagnification
end Frontier
end Pnp4
