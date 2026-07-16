import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorGlobalRankAlias
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorRankDispersion

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Weighted rank-dispersion bridge for the global selector alias

The existing selector dispersion is the maximum strict-intermediate
cumulative actual-rank sum.  Keeping the terminal cumulative sum and both
dyadic endpoint weights gives a sharper sufficient criterion than replacing
every threshold, including the terminal one, by the uniform constant four.

This file proves the exact finite bookkeeping.  It does not bound the
machine-specific dispersion.
-/

noncomputable section

open scoped BigOperators

open FiniteRankWeightAbelVariation
open FiniteStructuredDualRankThresholdBridge
open FiniteStructuredDualCoefficientEndpoint
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredRankWeightedDualCorrelation
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorRankDispersion
open MandatoryCanonicalSelectorGlobalRankAlias

namespace MandatoryCanonicalSelectorGlobalRankAliasDispersion

/-- Exact Abel upper bound retaining the actual terminal cumulative form and
the actual selector strict dispersion with their correct dyadic weights. -/
theorem prefixedMandatoryCanonicalSelector_rankWeightedDualFar_le_terminal_add_dispersion
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let f := (prefixedMandatoryCanonicalSelector
      machine n T b rounds).ratAcceptanceIndicator
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits (2 * m) hn htail f ≤
      dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm
            n m tailBits (2 * m) hn htail f f
              (structuredIndependence m * n) +
        (dyadicRankWeight (structuredIndependence m * tailBits) -
            dyadicRankWeight (structuredIndependence m * n)) *
          selectorStructuredDualRankStrictDispersion
            machine n T b m tailBits hn htail rounds := by
  dsimp only
  let f := (prefixedMandatoryCanonicalSelector
    machine n T b rounds).ratAcceptanceIndicator
  let dispersion := selectorStructuredDualRankStrictDispersion
    machine n T b m tailBits hn htail rounds
  have hbase : structuredIndependence m * tailBits ≤
      structuredIndependence m * n :=
    Nat.mul_le_mul_left (structuredIndependence m) htail
  have hsum :
      (∑ level ∈ Finset.Ico
          (structuredIndependence m * tailBits)
          (structuredIndependence m * n),
        dyadicRankWeight (level + 1) *
          structuredDualRankAtMostCrossForm
            n m tailBits (2 * m) hn htail f f level) ≤
      ∑ level ∈ Finset.Ico
          (structuredIndependence m * tailBits)
          (structuredIndependence m * n),
        dyadicRankWeight (level + 1) * dispersion := by
    apply Finset.sum_le_sum
    intro level hlevel
    have hlevel' := Finset.mem_Ico.mp hlevel
    exact mul_le_mul_of_nonneg_left
      (structuredDualRankAtMostCrossForm_le_selectorStrictDispersion
        machine n T b m tailBits level hn htail rounds
          hlevel'.1 hlevel'.2)
      (dyadicRankWeight_nonneg (level + 1))
  rw [structuredRankWeightedDualFarPairCorrelation_eq_terminal_add_cumulative]
  calc
    dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm
            n m tailBits (2 * m) hn htail f f
              (structuredIndependence m * n) +
        ∑ level ∈ Finset.Ico
            (structuredIndependence m * tailBits)
            (structuredIndependence m * n),
          dyadicRankWeight (level + 1) *
            structuredDualRankAtMostCrossForm
              n m tailBits (2 * m) hn htail f f level ≤
      dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm
            n m tailBits (2 * m) hn htail f f
              (structuredIndependence m * n) +
        ∑ level ∈ Finset.Ico
            (structuredIndependence m * tailBits)
            (structuredIndependence m * n),
          dyadicRankWeight (level + 1) * dispersion :=
      add_le_add_left hsum _
    _ = dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm
            n m tailBits (2 * m) hn htail f f
              (structuredIndependence m * n) +
        (dyadicRankWeight (structuredIndependence m * tailBits) -
            dyadicRankWeight (structuredIndependence m * n)) *
          selectorStructuredDualRankStrictDispersion
            machine n T b m tailBits hn htail rounds := by
      rw [← Finset.sum_mul]
      rw [sum_dyadicRankWeight_succ_Ico hbase]

/-- The corresponding lower bound on the new signed Abel remainder. -/
theorem prefixedMandatoryCanonicalSelector_globalRankAbelRemainder_ge
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let f := (prefixedMandatoryCanonicalSelector
      machine n T b rounds).ratAcceptanceIndicator
    dyadicRankWeight (structuredIndependence m * tailBits) *
          nonemptyStructuredDualCoefficientSum n m hn f -
        (dyadicRankWeight (structuredIndependence m * n) *
            structuredDualRankAtMostCrossForm
              n m tailBits (2 * m) hn htail f f
                (structuredIndependence m * n) +
          (dyadicRankWeight (structuredIndependence m * tailBits) -
              dyadicRankWeight (structuredIndependence m * n)) *
            selectorStructuredDualRankStrictDispersion
              machine n T b m tailBits hn htail rounds) ≤
      structuredDualRankAbelRemainder
        n m tailBits (2 * m) hn htail f := by
  dsimp only
  let f := (prefixedMandatoryCanonicalSelector
    machine n T b rounds).ratAcceptanceIndicator
  have hidempotent : ∀ input, f input * f input = f input := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have hexact :=
    structuredRankWeightedDualFarPairCorrelation_eq_endpoint_sub_remainder
      n m tailBits (2 * m) hn htail f hidempotent
  have hfar :=
    prefixedMandatoryCanonicalSelector_rankWeightedDualFar_le_terminal_add_dispersion
      machine n T b m tailBits hn htail rounds
  dsimp only at hfar
  linarith

/-- Sharpened selector-pair capstone.  It is enough to bound the correctly
weighted actual terminal form plus the actual strict dispersion; no uniform
terminal replacement by four is made. -/
theorem prefixedMandatoryCanonicalSelector_dualFarBound_of_weightedRankDispersion
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hweighted :
      let f := (prefixedMandatoryCanonicalSelector
        machine n T b rounds).ratAcceptanceIndicator
      let p : Rat := 1 / (2 : Rat) ^ tailBits
      dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm
            n m tailBits (2 * m) hn htail f f
              (structuredIndependence m * n) +
        (dyadicRankWeight (structuredIndependence m * tailBits) -
            dyadicRankWeight (structuredIndependence m * n)) *
          selectorStructuredDualRankStrictDispersion
            machine n T b m tailBits hn htail rounds ≤
        (1 - p) * p ^ (2 * m)) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  dsimp only at hweighted
  let f := (prefixedMandatoryCanonicalSelector
    machine n T b rounds).ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  have hfar :=
    prefixedMandatoryCanonicalSelector_rankWeightedDualFar_le_terminal_add_dispersion
      machine n T b m tailBits hn htail rounds
  dsimp only at hfar
  unfold DualFarBound
  rw [DPTWStructuredRankWeightedDualCorrelation.structuredDualFarPairCorrelation_eq_rankWeighted]
  change structuredRankWeightedDualFarPairCorrelation
      n m tailBits (2 * m) hn htail f ≤ (1 - p) * p ^ (2 * m)
  exact hfar.trans hweighted

end MandatoryCanonicalSelectorGlobalRankAliasDispersion
end

end OneTapeMagnification
end Frontier
end Pnp4
