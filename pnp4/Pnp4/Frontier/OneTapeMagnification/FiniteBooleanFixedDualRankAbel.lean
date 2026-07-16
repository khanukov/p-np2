import Pnp4.Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fixed-dual idempotent rank Abel decomposition

This module combines three finite identities without adding a quantitative
tail estimate:

* selected and rejected indices partition the unweighted sum;
* an idempotent Boolean-cube function has fixed-dual alias convolution equal
  to its Fourier coefficient at the dual support;
* dyadic rank-weight variation is an exact signed sum of strict rank tails.

The result applies to an arbitrary rank function once uniform lower and upper
rank bounds are supplied.
-/

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteRankWeightAbelVariation

namespace FiniteBooleanFixedDualRankAbel

/-- The selected contribution strictly above one rank threshold. -/
def selectedStrictRankTail
    {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (rank : Index → Nat) (term : Index → Rat)
    (level : Nat) : Rat :=
  strictRankTailSum rank
    (fun index => if selected index then term index else 0) level

/-- The selected contribution whose rank is at most one threshold. -/
def selectedRankAtMostSum
    {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (rank : Index → Nat) (term : Index → Rat)
    (level : Nat) : Rat :=
  selectedSum (fun index => selected index ∧ rank index ≤ level) term

/-- At-most and strict-above rank cuts partition the selected mass exactly. -/
theorem selectedStrictRankTail_add_selectedRankAtMostSum
    {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (rank : Index → Nat) (term : Index → Rat)
    (level : Nat) :
    selectedStrictRankTail selected rank term level +
        selectedRankAtMostSum selected rank term level =
      selectedSum selected term := by
  classical
  unfold selectedStrictRankTail strictRankTailSum selectedRankAtMostSum
    selectedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _hindex
  by_cases hselected : selected index
  · by_cases hrank : rank index ≤ level
    · have hnotStrict : ¬level < rank index := by omega
      simp [hselected, hrank, hnotStrict]
    · have hstrict : level < rank index := by omega
      simp [hselected, hrank, hstrict]
  · simp [hselected]

/-- **Generic exact selected rank-Abel identity.**

If the full unweighted sum is `total`, the constant part of a selected
dyadic rank weight is `2⁻ᵇᵃˢᵉ * total` minus the rejected boundary.
All remaining weight variation is exactly the negative sum of selected strict
rank tails. -/
theorem weightedSelectedSum_dyadicRank_eq_base_mul_total_sub_rejected_sub_strictRankTails
    {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (rank : Index → Nat) (term : Index → Rat)
    (baseRank upperRank : Nat) (total : Rat)
    (hlower : ∀ index, baseRank ≤ rank index)
    (hupper : ∀ index, rank index ≤ upperRank)
    (htotal : (∑ index : Index, term index) = total) :
    weightedSelectedSum selected
        (fun index => dyadicRankWeight (rank index)) term =
      dyadicRankWeight baseRank * total -
        dyadicRankWeight baseRank * rejectedSum selected term -
        ∑ level ∈ Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) *
            selectedStrictRankTail selected rank term level := by
  classical
  have hpartition := selectedSum_add_rejectedSum selected term
  have hselected :
      selectedSum selected term = total - rejectedSum selected term := by
    linarith
  calc
    weightedSelectedSum selected
        (fun index => dyadicRankWeight (rank index)) term =
        dyadicRankWeight baseRank * selectedSum selected term +
          selectedWeightVariation selected
            (fun index => dyadicRankWeight (rank index)) term
              (dyadicRankWeight baseRank) :=
      weightedSelectedSum_eq_base_mul_selectedSum_add_variation
        selected (fun index => dyadicRankWeight (rank index)) term
          (dyadicRankWeight baseRank)
    _ = dyadicRankWeight baseRank *
          (total - rejectedSum selected term) -
        ∑ level ∈ Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) *
            selectedStrictRankTail selected rank term level := by
      rw [hselected,
        selectedWeightVariation_dyadicRank_eq_neg_sum_strictRankTails
          selected rank term baseRank upperRank hlower hupper]
      simp only [selectedStrictRankTail, sub_eq_add_neg]
    _ = dyadicRankWeight baseRank * total -
        dyadicRankWeight baseRank * rejectedSum selected term -
        ∑ level ∈ Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) *
            selectedStrictRankTail selected rank term level := by
      ring

/-- Strict actual-rank tail of the high/high part of one fixed-dual Fourier
alias convolution. -/
def fixedDualHighHighStrictRankTail {n : Nat}
    (coefficients : Finset (Fin n) → Rat)
    (cutoff : Nat) (dual : Finset (Fin n))
    (rank : Finset (Fin n) → Nat) (level : Nat) : Rat :=
  selectedStrictRankTail (highHighAlias cutoff dual) rank
    (aliasProduct coefficients dual) level

/-- The actual-rank-at-most part of one fixed-dual high/high convolution. -/
def fixedDualHighHighRankAtMostSum {n : Nat}
    (coefficients : Finset (Fin n) → Rat)
    (cutoff : Nat) (dual : Finset (Fin n))
    (rank : Finset (Fin n) → Nat) (level : Nat) : Rat :=
  selectedRankAtMostSum (highHighAlias cutoff dual) rank
    (aliasProduct coefficients dual) level

/-- Idempotence identifies the unweighted high/high mass with the endpoint
coefficient minus its complementary low boundary. -/
theorem boolean_fixedDual_highHighAliasSum_eq_coefficient_sub_rejected
    {n : Nat} (f : (Fin n → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input)
    (cutoff : Nat) (dual : Finset (Fin n)) :
    selectedSum (highHighAlias cutoff dual)
        (aliasProduct (coefficient f) dual) =
      coefficient f dual -
        rejectedSum (highHighAlias cutoff dual)
          (aliasProduct (coefficient f) dual) := by
  have hpartition := selectedSum_add_rejectedSum
    (highHighAlias cutoff dual) (aliasProduct (coefficient f) dual)
  have htotal :
      (∑ index : Finset (Fin n),
          aliasProduct (coefficient f) dual index) = coefficient f dual := by
    simpa [aliasProduct] using
      (idempotent_symmDiff_convolution f hidempotent dual)
  linarith

/-- Fixed-dual strict and at-most rank pieces reconstruct the idempotent
endpoint minus the low boundary. -/
theorem boolean_fixedDual_strictRankTail_add_rankAtMost_eq
    {n : Nat} (f : (Fin n → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input)
    (cutoff : Nat) (dual : Finset (Fin n))
    (rank : Finset (Fin n) → Nat) (level : Nat) :
    fixedDualHighHighStrictRankTail
          (coefficient f) cutoff dual rank level +
        fixedDualHighHighRankAtMostSum
          (coefficient f) cutoff dual rank level =
      coefficient f dual -
        rejectedSum (highHighAlias cutoff dual)
          (aliasProduct (coefficient f) dual) := by
  rw [fixedDualHighHighStrictRankTail, fixedDualHighHighRankAtMostSum,
    selectedStrictRankTail_add_selectedRankAtMostSum]
  exact boolean_fixedDual_highHighAliasSum_eq_coefficient_sub_rejected
    f hidempotent cutoff dual

/-- **Fixed-dual idempotent rank-Abel identity.**

For an idempotent Boolean-cube function, the endpoint of the full alias
convolution is its Fourier coefficient at `dual`.  Hence the actual-rank
weighted high/high sum is exactly that endpoint, minus the low boundary and
the signed strict-rank tails. -/
theorem boolean_fixedDual_rankWeightedHighHighAlias_eq
    {n : Nat} (f : (Fin n → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input)
    (cutoff : Nat) (dual : Finset (Fin n))
    (rank : Finset (Fin n) → Nat)
    (baseRank upperRank : Nat)
    (hlower : ∀ frequency, baseRank ≤ rank frequency)
    (hupper : ∀ frequency, rank frequency ≤ upperRank) :
    weightedSelectedSum (highHighAlias cutoff dual)
        (fun frequency => dyadicRankWeight (rank frequency))
        (aliasProduct (coefficient f) dual) =
      dyadicRankWeight baseRank * coefficient f dual -
        dyadicRankWeight baseRank *
          rejectedSum (highHighAlias cutoff dual)
            (aliasProduct (coefficient f) dual) -
        ∑ level ∈ Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) *
            fixedDualHighHighStrictRankTail
              (coefficient f) cutoff dual rank level := by
  apply
    weightedSelectedSum_dyadicRank_eq_base_mul_total_sub_rejected_sub_strictRankTails
      (highHighAlias cutoff dual) rank
        (aliasProduct (coefficient f) dual)
        baseRank upperRank (coefficient f dual) hlower hupper
  simpa [aliasProduct] using
    idempotent_symmDiff_convolution f hidempotent dual

end FiniteBooleanFixedDualRankAbel
end OneTapeMagnification
end Frontier
end Pnp4
