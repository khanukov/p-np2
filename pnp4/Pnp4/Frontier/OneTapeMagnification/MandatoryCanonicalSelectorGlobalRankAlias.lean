import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFixedDualRankAbel
import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualCoefficientEndpoint
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorRankAliasAbel

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Global fixed-difference rank decomposition for the mandatory selector

The distinct structured-dual Fourier form is first reindexed by its unique
nonempty difference `W`.  Idempotence then collapses the full unweighted
alias convolution at each `W` to the single coefficient `f̂(W)`.  Summing
over `W` leaves one size-free endpoint and two explicit signed remainders:
the low/high boundary and the strict actual-rank tails.

No estimate on those two remainders is asserted here.  The final selector
theorems isolate an exact equivalent of `DualFarBound` and a sufficient
one-sided remainder inequality whose endpoint costs only one base weight.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteRankWeightAbelVariation
open FiniteBooleanFixedDualRankAbel
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualFixedDifferenceReindex
open FiniteStructuredDualCoefficientEndpoint
open FiniteStructuredDualRankThresholdBridge
open FiniteLayeredQueryProgramFamily
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredRankWeightedDualCorrelation
open MandatoryCanonicalSelectorPairCorrelation

namespace MandatoryCanonicalSelectorGlobalRankAlias

/-- The signed complement of the high/high part, aggregated over all
nonempty structured-dual differences. -/
def structuredDualLowAliasBoundary
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat) : Rat :=
  ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
    rejectedSum (highHighAlias cutoff dual)
      (aliasProduct (coefficient f) dual)

/-- The signed selected mass strictly above one actual-rank threshold,
aggregated over every nonempty structured-dual difference. -/
def structuredDualHighHighStrictRankTail
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) (level : Nat) : Rat :=
  ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
    fixedDualHighHighStrictRankTail (coefficient f) cutoff dual
      (fixedDualAliasUnionRank n m tailBits hn htail dual) level

/-- The complete signed low-boundary plus strict-rank-tail remainder.  It is
subtracted from the Fourier endpoint in the exact global identity below. -/
def structuredDualRankAbelRemainder
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) : Rat :=
  dyadicRankWeight (structuredIndependence m * tailBits) *
      structuredDualLowAliasBoundary n m cutoff hn f +
    ∑ level ∈ Finset.Ico
        (structuredIndependence m * tailBits)
        (structuredIndependence m * n),
      dyadicRankWeight (level + 1) *
        structuredDualHighHighStrictRankTail
          n m tailBits cutoff hn htail f level

/-- Fixed-difference form before the outer sums are collected. -/
theorem structuredRankWeightedDualFarPairCorrelation_eq_sum_fixedDualRankAbel
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f =
      ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
        (dyadicRankWeight (structuredIndependence m * tailBits) *
              coefficient f dual -
            dyadicRankWeight (structuredIndependence m * tailBits) *
              rejectedSum (highHighAlias cutoff dual)
                (aliasProduct (coefficient f) dual) -
            ∑ level ∈ Finset.Ico
                (structuredIndependence m * tailBits)
                (structuredIndependence m * n),
              dyadicRankWeight (level + 1) *
                fixedDualHighHighStrictRankTail (coefficient f) cutoff dual
                  (fixedDualAliasUnionRank
                    n m tailBits hn htail dual) level) := by
  classical
  rw [← structuredDualRankDistinctCrossForm_self_eq_rankWeightedDualFar]
  rw [structuredDualRankDistinctCrossForm_eq_sum_fixedDualRankWeightedHighHigh]
  apply Finset.sum_congr rfl
  intro dual hdual
  have hdual' := (mem_nonemptyStructuredDualSupports n m hn dual).mp hdual
  simpa [fixedDualAliasUnionRank, structuredIndependence] using
    (boolean_fixedDual_rankWeightedHighHighAlias_eq
      f hidempotent cutoff dual
      (fixedDualAliasUnionRank n m tailBits hn htail dual)
      (structuredIndependence m * tailBits)
      (structuredIndependence m * n)
      (fixedDualAliasUnionRank_lower
        n m tailBits hn htail dual hdual'.1 hdual'.2)
      (fixedDualAliasUnionRank_upper n m tailBits hn htail dual))

/-- **Global fixed-difference rank-Abel identity.**

The entire distinct selector-pair form has only one unweighted endpoint:
the sum of `f̂(W)` over nonempty structured-dual `W`.  In particular, no
component-diagonal or selector-cardinality factor remains in this formula. -/
theorem structuredRankWeightedDualFarPairCorrelation_eq_endpoint_sub_remainder
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f =
      dyadicRankWeight (structuredIndependence m * tailBits) *
          nonemptyStructuredDualCoefficientSum n m hn f -
        structuredDualRankAbelRemainder
          n m tailBits cutoff hn htail f := by
  classical
  have hendpoint :
      (∑ dual ∈ nonemptyStructuredDualSupports n m hn,
          dyadicRankWeight (structuredIndependence m * tailBits) *
            coefficient f dual) =
        dyadicRankWeight (structuredIndependence m * tailBits) *
          ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
            coefficient f dual := by
    rw [Finset.mul_sum]
  have hboundary :
      (∑ dual ∈ nonemptyStructuredDualSupports n m hn,
          dyadicRankWeight (structuredIndependence m * tailBits) *
            rejectedSum (highHighAlias cutoff dual)
              (aliasProduct (coefficient f) dual)) =
        dyadicRankWeight (structuredIndependence m * tailBits) *
          ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
            rejectedSum (highHighAlias cutoff dual)
              (aliasProduct (coefficient f) dual) := by
    rw [Finset.mul_sum]
  have htails :
      (∑ dual ∈ nonemptyStructuredDualSupports n m hn,
          ∑ level ∈ Finset.Ico
              (structuredIndependence m * tailBits)
              (structuredIndependence m * n),
            dyadicRankWeight (level + 1) *
              fixedDualHighHighStrictRankTail (coefficient f) cutoff dual
                (fixedDualAliasUnionRank
                  n m tailBits hn htail dual) level) =
        ∑ level ∈ Finset.Ico
            (structuredIndependence m * tailBits)
            (structuredIndependence m * n),
          dyadicRankWeight (level + 1) *
            ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
              fixedDualHighHighStrictRankTail (coefficient f) cutoff dual
                (fixedDualAliasUnionRank
                  n m tailBits hn htail dual) level := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro level _hlevel
    rw [Finset.mul_sum]
  rw [structuredRankWeightedDualFarPairCorrelation_eq_sum_fixedDualRankAbel
    n m tailBits cutoff hn htail f hidempotent]
  unfold nonemptyStructuredDualCoefficientSum
    structuredDualRankAbelRemainder structuredDualLowAliasBoundary
    structuredDualHighHighStrictRankTail
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hendpoint, hboundary, htails]
  ring

/-- Expectation form of the endpoint.  It is the structured-generator bias
of `f`, not a sum paid once per selector component. -/
theorem structuredRankWeightedDualFarPairCorrelation_eq_bias_sub_remainder
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f =
      dyadicRankWeight (structuredIndependence m * tailBits) *
          (FiniteBooleanRestrictionMoment.finiteAverage
              (fun seed : Fin (structuredIndependence m * n) → Bool =>
                f ((structuredUnbiasedPrimitive n m hn).generate seed)) -
            FiniteBooleanRestrictionMoment.finiteAverage f) -
        structuredDualRankAbelRemainder
          n m tailBits cutoff hn htail f := by
  rw [structuredRankWeightedDualFarPairCorrelation_eq_endpoint_sub_remainder
    n m tailBits cutoff hn htail f hidempotent]
  rw [nonemptyStructuredDualCoefficientSum_eq_sub_finiteAverage]

/-- The new strict-tail coordinates and the earlier cumulative-at-most
coordinates are exact complements.  After summing over `W`, their common
total is the global idempotent endpoint minus the low boundary. -/
theorem structuredDualHighHighStrictRankTail_add_atMost_eq_endpoint_sub_low
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input)
    (level : Nat) :
    structuredDualHighHighStrictRankTail
          n m tailBits cutoff hn htail f level +
        structuredDualRankAtMostCrossForm
          n m tailBits cutoff hn htail f f level =
      nonemptyStructuredDualCoefficientSum n m hn f -
        structuredDualLowAliasBoundary n m cutoff hn f := by
  classical
  rw [structuredDualRankAtMostCrossForm_eq_sum_fixedDualRankAtMostHighHigh]
  unfold structuredDualHighHighStrictRankTail
    nonemptyStructuredDualCoefficientSum structuredDualLowAliasBoundary
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro dual _hdual
  simpa [fixedDualHighHighRankAtMostSum, selectedRankAtMostSum,
    fixedDualAliasUnionRank, aliasProduct] using
      (boolean_fixedDual_strictRankTail_add_rankAtMost_eq
        f hidempotent cutoff dual
          (fixedDualAliasUnionRank n m tailBits hn htail dual) level)

/-- Solved form of the preceding complement identity.  This pins the exact
remaining strict-tail quantity to the already audited cumulative-rank form. -/
theorem structuredDualHighHighStrictRankTail_eq_endpoint_sub_low_sub_atMost
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input)
    (level : Nat) :
    structuredDualHighHighStrictRankTail
        n m tailBits cutoff hn htail f level =
      nonemptyStructuredDualCoefficientSum n m hn f -
        structuredDualLowAliasBoundary n m cutoff hn f -
        structuredDualRankAtMostCrossForm
          n m tailBits cutoff hn htail f f level := by
  have hpartition :=
    structuredDualHighHighStrictRankTail_add_atMost_eq_endpoint_sub_low
      n m tailBits cutoff hn htail f hidempotent level
  linarith

/-- A `[0,1]`-valued idempotent function pays at most one base weight at the
global endpoint.  The only remaining one-sided task is the signed Abel
remainder. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_base_sub_remainder
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hidempotent : ∀ input, f input * f input = f input)
    (hnonneg : ∀ input, 0 ≤ f input)
    (hle_one : ∀ input, f input ≤ 1) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      dyadicRankWeight (structuredIndependence m * tailBits) -
        structuredDualRankAbelRemainder
          n m tailBits cutoff hn htail f := by
  rw [structuredRankWeightedDualFarPairCorrelation_eq_endpoint_sub_remainder
    n m tailBits cutoff hn htail f hidempotent]
  have hendpoint := nonemptyStructuredDualCoefficientSum_le_one
    n m hn f hnonneg hle_one
  have hweight := dyadicRankWeight_nonneg
    (structuredIndependence m * tailBits)
  simpa only [mul_one] using
    (sub_le_sub_right
      (mul_le_mul_of_nonneg_left hendpoint hweight)
      (structuredDualRankAbelRemainder
        n m tailBits cutoff hn htail f))

/-- Exact selector-specific reformulation of `DualFarBound`. -/
theorem prefixedMandatoryCanonicalSelector_dualFarBound_iff_globalRankAbel
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    DualFarBound machine n T b m tailBits hn htail rounds ↔
      let f := (prefixedMandatoryCanonicalSelector
        machine n T b rounds).ratAcceptanceIndicator
      let p : Rat := 1 / (2 : Rat) ^ tailBits
      dyadicRankWeight (structuredIndependence m * tailBits) *
          nonemptyStructuredDualCoefficientSum n m hn f -
        structuredDualRankAbelRemainder
          n m tailBits (2 * m) hn htail f ≤
        (1 - p) * p ^ (2 * m) := by
  dsimp only
  let f := (prefixedMandatoryCanonicalSelector
    machine n T b rounds).ratAcceptanceIndicator
  have hidempotent : ∀ input, f input * f input = f input := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  unfold DualFarBound
  rw [DPTWStructuredRankWeightedDualCorrelation.structuredDualFarPairCorrelation_eq_rankWeighted]
  rw [structuredRankWeightedDualFarPairCorrelation_eq_endpoint_sub_remainder
    n m tailBits (2 * m) hn htail f hidempotent]

/-- Concrete size-free sufficient selector-pair lemma.  It replaces the
formerly separate component diagonal by one base weight.  Proving the stated
lower bound on the signed low/tail remainder is sufficient for the actual
small-seed correlation budget. -/
theorem prefixedMandatoryCanonicalSelector_dualFarBound_of_globalRankAbelRemainder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hremainder :
      let f := (prefixedMandatoryCanonicalSelector
        machine n T b rounds).ratAcceptanceIndicator
      let p : Rat := 1 / (2 : Rat) ^ tailBits
      dyadicRankWeight (structuredIndependence m * tailBits) -
          (1 - p) * p ^ (2 * m) ≤
        structuredDualRankAbelRemainder
          n m tailBits (2 * m) hn htail f) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  dsimp only at hremainder
  let f := (prefixedMandatoryCanonicalSelector
    machine n T b rounds).ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  have hidempotent : ∀ input, f input * f input = f input := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have hnonneg : ∀ input, 0 ≤ f input := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have hle_one : ∀ input, f input ≤ 1 := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have hfar :=
    structuredRankWeightedDualFarPairCorrelation_le_base_sub_remainder
      n m tailBits (2 * m) hn htail f hidempotent hnonneg hle_one
  unfold DualFarBound
  rw [DPTWStructuredRankWeightedDualCorrelation.structuredDualFarPairCorrelation_eq_rankWeighted]
  change structuredRankWeightedDualFarPairCorrelation
      n m tailBits (2 * m) hn htail f ≤ (1 - p) * p ^ (2 * m)
  exact hfar.trans (by linarith)

end MandatoryCanonicalSelectorGlobalRankAlias
end

end OneTapeMagnification
end Frontier
end Pnp4
