import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation
import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPrefixedFourierFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact Abel decomposition of one prefixed selector-component alias

For a fixed nonzero structured-dual support, the two endpoints `S` and
`S ∆ W` are distinct at every frequency.  Their union-support constraint
rank therefore lies between `(4m + 1) * tailBits` and `(4m + 1) * n`.
Combining the prefix-stable full-alias cancellation with exact dyadic Abel
summation turns the remaining nonconstant weight variation into signed strict
rank tails.  This module proves only the identity; it does not bound those
tails.
-/

open scoped BigOperators symmDiff

open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredMaskRank
open DPTWStructuredUnbiasedDualCode
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteRankWeightAbelVariation
open FiniteSignedReverseLCPSiblingDualRank

namespace FiniteLayeredQueryProgramFamily

/-- Actual structured prefix-constraint rank of the union of a fixed-dual
alias pair `frequency`, `frequency ∆ dual`. -/
noncomputable def fixedDualAliasUnionRank
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (dual frequency : Finset (Fin (2 ^ n))) : Nat :=
  supportPrefixConstraintRank n (structuredIndependence m)
    tailBits hn htail (frequency ∪ (frequency ∆ dual))

/-- A nonempty structured dual forces every fixed-dual alias union to have
rank at least `(4m + 1) * tailBits`. -/
theorem fixedDualAliasUnionRank_lower
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (dual : Finset (Fin (2 ^ n))) (hdualNonempty : dual.Nonempty)
    (hdual : IsStructuredDualSupport n (structuredIndependence m) hn dual)
    (frequency : Finset (Fin (2 ^ n))) :
    (4 * m + 1) * tailBits ≤
      fixedDualAliasUnionRank n m tailBits hn htail dual frequency := by
  have hne : frequency ≠ frequency ∆ dual := by
    apply Finset.symmDiff_nonempty.mp
    simpa only [symmDiff_symmDiff_cancel_left] using hdualNonempty
  have haliasDual :
      IsStructuredDualSupport n (structuredIndependence m) hn
        (frequency ∆ (frequency ∆ dual)) := by
    simpa only [symmDiff_symmDiff_cancel_left] using hdual
  simpa [fixedDualAliasUnionRank, structuredIndependence] using
    (structuredIndependence_mul_tailBits_le_unionRank_of_distinct_dual
      n m tailBits hn htail frequency (frequency ∆ dual) hne haliasDual)

/-- Every fixed-dual alias union rank is at most the full
`(4m + 1) * n` coefficient-space dimension. -/
theorem fixedDualAliasUnionRank_upper
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (dual frequency : Finset (Fin (2 ^ n))) :
    fixedDualAliasUnionRank n m tailBits hn htail dual frequency ≤
      (4 * m + 1) * n := by
  simpa [fixedDualAliasUnionRank, structuredIndependence] using
    (supportPrefixConstraintRank_upperBound
      n (structuredIndependence m) tailBits hn htail
        (frequency ∪ (frequency ∆ dual)))

/-- The selected strict-rank tail for one ordered pair of prefixed canonical
components at the actual high-degree cutoff `2m`. -/
noncomputable def prefixedMandatoryCanonicalBlockProjectionStrictRankTail
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hb : 0 < b)
    (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (dual : Finset (Fin (2 ^ n))) (level : Nat) : Rat :=
  strictRankTailSum
    (fixedDualAliasUnionRank n m tailBits hn htail dual)
    (fun frequency =>
      if highHighAlias (2 * m) dual frequency then
        prefixedMandatoryCanonicalBlockProjectionAliasTerm
          machine (2 ^ n) T b hb rounds left right dual frequency
      else 0)
    level

/-- **Exact actual-rank Abel identity for two distinct prefixed components.**

The constant dyadic weight at the unconditional rank floor moves to the
low-boundary aliases.  The remaining actual rank variation is exactly the
negative dyadic average of strict rank tails between the floor and the full
seed-dimension ceiling.  No absolute values, component-count factor, or
unproved tail estimate occurs. -/
theorem prefixedMandatoryCanonical_distinctBlockProjection_rankWeightedHighHighAlias_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hb : 0 < b)
    (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (hne : left ≠ right)
    (dual : Finset (Fin (2 ^ n))) (hdualNonempty : dual.Nonempty)
    (hdual : IsStructuredDualSupport n (structuredIndependence m) hn dual) :
    weightedSelectedSum (highHighAlias (2 * m) dual)
        (fun frequency =>
          dyadicRankWeight
            (fixedDualAliasUnionRank
              n m tailBits hn htail dual frequency))
        (prefixedMandatoryCanonicalBlockProjectionAliasTerm
          machine (2 ^ n) T b hb rounds left right dual) =
      -dyadicRankWeight ((4 * m + 1) * tailBits) *
          rejectedSum (highHighAlias (2 * m) dual)
            (prefixedMandatoryCanonicalBlockProjectionAliasTerm
              machine (2 ^ n) T b hb rounds left right dual) -
        ∑ level ∈ Finset.Ico
            ((4 * m + 1) * tailBits) ((4 * m + 1) * n),
          dyadicRankWeight (level + 1) *
            prefixedMandatoryCanonicalBlockProjectionStrictRankTail
              machine n T b m tailBits hb hn htail rounds
                left right dual level := by
  classical
  let rank := fixedDualAliasUnionRank n m tailBits hn htail dual
  let term := prefixedMandatoryCanonicalBlockProjectionAliasTerm
    machine (2 ^ n) T b hb rounds left right dual
  let selected := highHighAlias (2 * m) dual
  have hlower : ∀ frequency, (4 * m + 1) * tailBits ≤ rank frequency := by
    intro frequency
    exact fixedDualAliasUnionRank_lower
      n m tailBits hn htail dual hdualNonempty hdual frequency
  have hupper : ∀ frequency, rank frequency ≤ (4 * m + 1) * n := by
    intro frequency
    exact fixedDualAliasUnionRank_upper
      n m tailBits hn htail dual frequency
  have htransfer :=
    prefixedMandatoryCanonical_distinctBlockProjection_weightedHighHighAlias_decomposition
      machine (2 ^ n) T b hb rounds left right hne (2 * m) dual
        (fun frequency => dyadicRankWeight (rank frequency))
        (dyadicRankWeight ((4 * m + 1) * tailBits))
  have habel :=
    selectedWeightVariation_dyadicRank_eq_neg_sum_strictRankTails
      selected rank term ((4 * m + 1) * tailBits) ((4 * m + 1) * n)
        hlower hupper
  rw [habel] at htransfer
  simpa [rank, term, selected,
    prefixedMandatoryCanonicalBlockProjectionStrictRankTail,
    sub_eq_add_neg] using htransfer

end FiniteLayeredQueryProgramFamily

end OneTapeMagnification
end Frontier
end Pnp4
