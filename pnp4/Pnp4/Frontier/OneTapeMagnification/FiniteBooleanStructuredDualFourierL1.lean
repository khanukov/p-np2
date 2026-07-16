import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPFourierKernel
import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualRankThresholdBridge

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fourier-L1 packing for structured dual-rank pairs

A distinct structured-dual pair always pays the full mask-rank scale
`2^{-((4m+1) * tailBits)}`.  If the two functions have small Fourier `L1`
norm, this pointwise scale can be summed over *all* dual words at once: every
ordered support pair has a unique symmetric difference, so no dual-code or
Fourier-support cardinality occurs.

Fixed coordinate cylinders have Fourier `L1` norm exactly one.  Consequently
the complete structured distinct-alias form of two such cylinders is bounded
by the full rank scale.  This is the analytic fact used by one fixed pair of
canonical-walk subcubes.  It is not an `L1` packing theorem for a disjoint
family of walk cells; summing the per-cell statement by absolute values can
still lose the number of cells.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredMaskRank
open DPTWStructuredUnbiasedDualCode
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualRankThresholdBridge
open FiniteRankWeightAbelVariation
open FiniteUnambiguousFBDD

namespace FiniteBooleanStructuredDualFourierL1

/-- The finite Walsh spectral `L1` norm. -/
def fourierL1 {N : Nat} (f : (Fin N -> Bool) -> Rat) : Rat :=
  ∑ support : Finset (Fin N), abs (coefficient f support)

/-- A weighted Fourier pair form over an arbitrary finite set of ordered
support pairs. -/
def weightedFourierPairCrossForm {N : Nat}
    (pairs : Finset (Finset (Fin N) × Finset (Fin N)))
    (weight : Finset (Fin N) × Finset (Fin N) -> Rat)
    (leftFunction rightFunction : (Fin N -> Bool) -> Rat) : Rat :=
  ∑ pair ∈ pairs,
    weight pair *
      (coefficient leftFunction pair.1 * coefficient rightFunction pair.2)

/-- Uniformly bounded pair weights sum against the product of the two full
Fourier `L1` norms.  The pair set can be arbitrary; in particular, it can
already contain all structured dual words. -/
theorem abs_weightedFourierPairCrossForm_le_fourierL1_mul
    {N : Nat}
    (pairs : Finset (Finset (Fin N) × Finset (Fin N)))
    (weight : Finset (Fin N) × Finset (Fin N) -> Rat)
    (leftFunction rightFunction : (Fin N -> Bool) -> Rat)
    (scale : Rat) (hscale : 0 <= scale)
    (hweight : ∀ pair ∈ pairs, abs (weight pair) <= scale) :
    abs (weightedFourierPairCrossForm pairs weight
        leftFunction rightFunction) <=
      scale * (fourierL1 leftFunction * fourierL1 rightFunction) := by
  classical
  let pairMass := fun pair : Finset (Fin N) × Finset (Fin N) =>
    abs (coefficient leftFunction pair.1) *
      abs (coefficient rightFunction pair.2)
  have hpairMass : ∀ pair, 0 <= pairMass pair := by
    intro pair
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc
    abs (weightedFourierPairCrossForm pairs weight
        leftFunction rightFunction) <=
        ∑ pair ∈ pairs,
          abs (weight pair *
            (coefficient leftFunction pair.1 *
              coefficient rightFunction pair.2)) := by
      unfold weightedFourierPairCrossForm
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ pair ∈ pairs, scale * pairMass pair := by
      apply Finset.sum_le_sum
      intro pair hpair
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hweight pair hpair)
        (hpairMass pair)
    _ <= ∑ pair : Finset (Fin N) × Finset (Fin N),
        scale * pairMass pair := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ pairs)
        (fun pair _ _ => mul_nonneg hscale (hpairMass pair))
    _ = ∑ leftSupport : Finset (Fin N),
        ∑ rightSupport : Finset (Fin N),
          scale * pairMass (leftSupport, rightSupport) := by
      rw [show
        (Finset.univ :
          Finset (Finset (Fin N) × Finset (Fin N))) =
            Finset.univ.product Finset.univ by
          ext pair
          simp]
      exact Finset.sum_product Finset.univ Finset.univ
        (fun pair => scale * pairMass pair)
    _ = scale * (fourierL1 leftFunction * fourierL1 rightFunction) := by
      unfold fourierL1 pairMass
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro leftSupport _hleftSupport
      rw [Finset.mul_sum]

/-- The complete structured distinct-alias form is bounded by the full
rank scale times the two Fourier `L1` norms.  No sum over dual words remains
on the right-hand side. -/
theorem abs_structuredDualRankDistinctCrossForm_le_fourierL1_mul
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    abs (structuredDualRankDistinctCrossForm
        n m tailBits cutoff hn htail leftFunction rightFunction) <=
      dyadicRankWeight (structuredIndependence m * tailBits) *
        (fourierL1 leftFunction * fourierL1 rightFunction) := by
  classical
  rw [structuredDualRankDistinctCrossForm_eq_pairWeightedSum]
  let weight := fun pair :
      Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) =>
    dyadicRankWeight
      (structuredDualAliasPairRank n m tailBits hn htail pair)
  change abs (weightedFourierPairCrossForm
      (structuredDualAliasPairs n m cutoff hn) weight
        leftFunction rightFunction) <= _
  apply abs_weightedFourierPairCrossForm_le_fourierL1_mul
  · exact dyadicRankWeight_nonneg _
  · intro pair hpair
    have hpairData :=
      (mem_structuredDualAliasPairs_iff n m cutoff hn pair).mp hpair
    have hbound := distinctDualAlias_invPowUnionRank_le
      n m tailBits hn htail pair.1 pair.2 hpairData.2.2.1
        hpairData.2.2.2
    have hnonneg : 0 <= weight pair := by
      exact dyadicRankWeight_nonneg _
    rw [abs_of_nonneg hnonneg]
    simpa [weight, structuredDualAliasPairRank, dyadicRankWeight] using hbound

/-- Fourier `L1` at most one is sufficient for the full dual-word-free rank
bound.  This is the interface used by one fixed pair of subcube cells. -/
theorem abs_structuredDualRankDistinctCrossForm_le_baseWeight_of_fourierL1
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (hleft : fourierL1 leftFunction <= 1)
    (hright : fourierL1 rightFunction <= 1) :
    abs (structuredDualRankDistinctCrossForm
        n m tailBits cutoff hn htail leftFunction rightFunction) <=
      dyadicRankWeight (structuredIndependence m * tailBits) := by
  have hL1nonneg (f : (Fin (2 ^ n) -> Bool) -> Rat) :
      0 <= fourierL1 f := by
    unfold fourierL1
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hproduct : fourierL1 leftFunction * fourierL1 rightFunction <= 1 := by
    nlinarith [hL1nonneg leftFunction, hL1nonneg rightFunction]
  have hscale : 0 <=
      dyadicRankWeight (structuredIndependence m * tailBits) :=
    dyadicRankWeight_nonneg _
  exact (abs_structuredDualRankDistinctCrossForm_le_fourierL1_mul
    n m tailBits cutoff hn htail leftFunction rightFunction).trans
      (by nlinarith)

/-! ## Exact spectral norm of a coordinate cylinder -/

/-- A fixed labelled suffix cylinder has Fourier `L1` norm exactly one. -/
theorem fourierL1_ratFixedLabelledSuffixCylinderIndicator_eq_one
    {n : Nat} {B : FiniteUnambiguousFBDD n} {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (reference : Fin n -> Bool) :
    fourierL1
        (fun input => ratFixedLabelledSuffixCylinderIndicator
          suffixWalk reference input) = 1 := by
  classical
  let cylinder : (Fin n -> Bool) -> Rat := fun input =>
    ratFixedLabelledSuffixCylinderIndicator suffixWalk reference input
  have hcoefficient (support : Finset (Fin n)) :
      abs (coefficient cylinder support) =
        if support ⊆ suffixWalk.queryVars then
          1 / (2 : Rat) ^ suffixWalk.queryVars.card
        else 0 := by
    by_cases hsupport : support ⊆ suffixWalk.queryVars
    · rw [if_pos hsupport]
      exact abs_coefficient_ratFixedLabelledSuffixCylinderIndicator_eq_inv_pow
        suffixWalk reference support hsupport
    · rw [if_neg hsupport]
      have hzero : coefficient cylinder support = 0 :=
        coefficient_eq_zero_of_not_subset_of_dependsOnlyOn
          (ratFixedLabelledSuffixCylinderIndicator_dependsOnlyOn_queryVars
            suffixWalk reference) hsupport
      rw [hzero, abs_zero]
  unfold fourierL1
  change (∑ support : Finset (Fin n), abs (coefficient cylinder support)) = 1
  simp_rw [hcoefficient]
  calc
    (∑ support : Finset (Fin n),
        if support ⊆ suffixWalk.queryVars then
          1 / (2 : Rat) ^ suffixWalk.queryVars.card
        else 0) =
      ∑ support ∈ suffixWalk.queryVars.powerset,
        1 / (2 : Rat) ^ suffixWalk.queryVars.card := by
          rw [← Finset.sum_filter]
          congr 1
          ext support
          simp
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_powerset]
      simp only [nsmul_eq_mul]
      have hpow : (0 : Rat) < (2 : Rat) ^ suffixWalk.queryVars.card := by
        positivity
      field_simp

/-- Two fixed labelled suffix cylinders have a complete structured
distinct-alias correlation bounded by the full rank scale, with no dual-word
or Fourier-support count. -/
theorem abs_structuredDualRankDistinctCrossForm_fixedCylinders_le
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftB rightB : FiniteUnambiguousFBDD (2 ^ n))
    {leftVertex : leftB.Vertex} {rightVertex : rightB.Vertex}
    (leftWalk : leftB.Walk leftVertex leftB.accept)
    (rightWalk : rightB.Walk rightVertex rightB.accept)
    (leftReference rightReference : Fin (2 ^ n) -> Bool) :
    abs (structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
        (fun input => ratFixedLabelledSuffixCylinderIndicator
          leftWalk leftReference input)
        (fun input => ratFixedLabelledSuffixCylinderIndicator
          rightWalk rightReference input)) <=
      dyadicRankWeight (structuredIndependence m * tailBits) := by
  apply abs_structuredDualRankDistinctCrossForm_le_baseWeight_of_fourierL1
  · rw [fourierL1_ratFixedLabelledSuffixCylinderIndicator_eq_one]
  · rw [fourierL1_ratFixedLabelledSuffixCylinderIndicator_eq_one]

end FiniteBooleanStructuredDualFourierL1

end

end OneTapeMagnification
end Frontier
end Pnp4
