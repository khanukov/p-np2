import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorGlobalRankAlias
import Pnp4.Frontier.OneTapeMagnification.FiniteVectorClaim18ReverseLCPEnergy

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Reverse-LCP form of the global selector rank-Abel remainder

The exact reverse-LCP telescope computes the structured high-tail second
moment of the actual prefixed mandatory selector.  Subtracting its diagonal
energy leaves precisely the signed dual-far form.  Combining this identity
with the global fixed-difference Abel decomposition rewrites the complete
low-boundary/rank-tail remainder as one endpoint plus diagonal energy minus
the averaged reverse-LCP charges.

No numerical estimate on those signed charges is asserted here.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanRestrictionMoment
open FiniteBooleanFullIndependenceRestriction
open FiniteUnambiguousFBDD
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredRankWeightedDualCorrelation
open FiniteRankWeightAbelVariation
open FiniteStructuredDualCoefficientEndpoint
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorGlobalRankAlias

namespace MandatoryCanonicalSelectorGlobalRankAliasLCP

/-- The exact sum of seed-averaged signed reverse-LCP charges of the actual
prefixed mandatory selector. -/
def mandatorySelectorCanonicalExactLCPChargeAverageSum
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Rat :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  ∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      B.canonicalExactLCPSignedPairCharge (2 * m)
        (D seed.1) (mask seed.2) key)

/-- The reverse-LCP charge sum is exactly the diagonal structured mask energy
plus the signed dual-far form. -/
theorem mandatorySelectorCanonicalExactLCPChargeAverageSum_eq_diagonal_add_dualFar
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let f := (prefixedMandatoryCanonicalSelector
      machine n T b rounds).ratAcceptanceIndicator
    mandatorySelectorCanonicalExactLCPChargeAverageSum
        machine n T b m tailBits hn htail rounds =
      FiniteVectorClaim18.structuredDiagonalMaskEnergy
          n m tailBits hn htail f +
        structuredDualFarPairCorrelation
          n m tailBits (2 * m) hn htail f := by
  dsimp only
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  calc
    mandatorySelectorCanonicalExactLCPChargeAverageSum
        machine n T b m tailBits hn htail rounds =
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (B.normalizedResidualAcceptedModelCount
              (D seed.1) (mask seed.2) -
            FiniteBooleanResidualMass.maskedLowDegreePredictor
              f (2 * m) (D seed.1) (mask seed.2)) ^ 2) := by
      unfold mandatorySelectorCanonicalExactLCPChargeAverageSum
      dsimp only
      exact
        (B.residualDeviation_secondMoment_eq_sum_canonicalExactLCPChargeAverages
          (2 * m) D mask).symm
    _ = finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (FiniteBooleanResidualMass.maskedAverage f
              (D seed.1) (mask seed.2) -
            FiniteBooleanResidualMass.maskedLowDegreePredictor
              f (2 * m) (D seed.1) (mask seed.2)) ^ 2) := by
      apply finiteAverage_congr
      intro seed
      rw [FiniteUnambiguousFBDD.maskedAverage_ratAcceptanceIndicator_eq_residualAcceptedMass,
        B.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount]
    _ = finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
            (maskedInput (D seed.1) (mask seed.2) uniform))) ^ 2) := by
      exact FiniteBooleanResidualMass.deviation_secondMoment_eq_highTailSecondMoment
        f (2 * m) D mask
    _ = FiniteVectorClaim18.structuredDiagonalMaskEnergy
          n m tailBits hn htail f +
        structuredDualFarPairCorrelation
          n m tailBits (2 * m) hn htail f := by
      simpa [FiniteVectorClaim18.structuredDiagonalMaskEnergy] using
        (structured_highTail_restriction_secondMoment_eq_diagonal_add_dual
          n m tailBits hn htail f)

/-- **Exact reverse-LCP form of the global rank-Abel remainder.**

The low/high alias boundary and all strict actual-rank tails together equal
the global structured-dual coefficient endpoint, plus diagonal mask energy,
minus the complete averaged reverse-LCP charge sum. -/
theorem structuredDualRankAbelRemainder_eq_endpoint_add_diagonal_sub_lcp
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let f := (prefixedMandatoryCanonicalSelector
      machine n T b rounds).ratAcceptanceIndicator
    structuredDualRankAbelRemainder
        n m tailBits (2 * m) hn htail f =
      dyadicRankWeight (structuredIndependence m * tailBits) *
          nonemptyStructuredDualCoefficientSum n m hn f +
        FiniteVectorClaim18.structuredDiagonalMaskEnergy
          n m tailBits hn htail f -
        mandatorySelectorCanonicalExactLCPChargeAverageSum
          machine n T b m tailBits hn htail rounds := by
  dsimp only
  let f := (prefixedMandatoryCanonicalSelector
    machine n T b rounds).ratAcceptanceIndicator
  have hidempotent : forall input, f input * f input = f input := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have hglobal :=
    structuredRankWeightedDualFarPairCorrelation_eq_endpoint_sub_remainder
      n m tailBits (2 * m) hn htail f hidempotent
  have hlcp :=
    mandatorySelectorCanonicalExactLCPChargeAverageSum_eq_diagonal_add_dualFar
      machine n T b m tailBits hn htail rounds
  dsimp only at hlcp
  rw [structuredDualFarPairCorrelation_eq_rankWeighted] at hlcp
  linarith

/-- A lower bound on the rank-Abel remainder is exactly an upper bound on
the reverse-LCP charge sum with the corresponding endpoint and diagonal
allowance. -/
theorem le_structuredDualRankAbelRemainder_iff_lcpChargeSum_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) (lowerBound : Rat) :
    let f := (prefixedMandatoryCanonicalSelector
      machine n T b rounds).ratAcceptanceIndicator
    lowerBound <=
        structuredDualRankAbelRemainder
          n m tailBits (2 * m) hn htail f <->
      mandatorySelectorCanonicalExactLCPChargeAverageSum
          machine n T b m tailBits hn htail rounds <=
        dyadicRankWeight (structuredIndependence m * tailBits) *
            nonemptyStructuredDualCoefficientSum n m hn f +
          FiniteVectorClaim18.structuredDiagonalMaskEnergy
            n m tailBits hn htail f - lowerBound := by
  dsimp only
  rw [structuredDualRankAbelRemainder_eq_endpoint_add_diagonal_sub_lcp
    machine n T b m tailBits hn htail rounds]
  constructor <;> intro h <;> linarith

/-- Exact reverse-LCP characterization of the mandatory selector's
`DualFarBound`.  Unlike the residual-mass `L2` relaxation, the right side
retains the actual diagonal energy rather than replacing it by its universal
upper bound. -/
theorem prefixedMandatoryCanonicalSelector_dualFarBound_iff_diagonalAwareLCPBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    DualFarBound machine n T b m tailBits hn htail rounds <->
      let f := (prefixedMandatoryCanonicalSelector
        machine n T b rounds).ratAcceptanceIndicator
      let p : Rat := 1 / (2 : Rat) ^ tailBits
      mandatorySelectorCanonicalExactLCPChargeAverageSum
          machine n T b m tailBits hn htail rounds <=
        FiniteVectorClaim18.structuredDiagonalMaskEnergy
            n m tailBits hn htail f +
          (1 - p) * p ^ (2 * m) := by
  dsimp only
  unfold DualFarBound
  rw [mandatorySelectorCanonicalExactLCPChargeAverageSum_eq_diagonal_add_dualFar
    machine n T b m tailBits hn htail rounds]
  constructor <;> intro h <;> linarith

end MandatoryCanonicalSelectorGlobalRankAliasLCP
end

end OneTapeMagnification
end Frontier
end Pnp4
