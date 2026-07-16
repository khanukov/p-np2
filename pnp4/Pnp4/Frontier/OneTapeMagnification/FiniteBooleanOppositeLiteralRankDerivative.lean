import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredMaskRankInsertion
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralCorrelation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Numerical rank derivative for opposite query literals

The exact toggle pairing for opposite query literals leaves, on every bulk
pair, one difference between the actual mask-rank weights of `union` and
`insert coordinate union`.  The one-coordinate rank-increment theorem bounds
that difference by the old weight times
`1 - 2^(-tailBits)`.

This is the concrete local selector-pair correlation gain.  It does not bound
the separately exposed cutoff-boundary pairs or sum over reverse-LCP cells.
-/

noncomputable section

open scoped symmDiff

open FiniteBooleanFourier
open FiniteBooleanDualAliasConvolutionTransfer
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open FiniteRankWeightAbelVariation
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualFixedDifferenceReindex
open FiniteBooleanOppositeLiteralCorrelation
open DPTWStructuredMaskRankInsertion

namespace FiniteBooleanOppositeLiteralRankDerivative

/-- **Local bulk selector-pair correlation lemma.**  For the actual
structured rank weight, an opposite-literal toggle pair which is already in
the strict high/high tail is bounded by the rank-difference upper factor
`1 - 2^(-tailBits)`.  The underlying difference-of-weights identity is exact;
this uniform numerical factor is an upper bound. -/
theorem abs_structuredActualRankOppositeLiteralPair_le_of_bulk
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (W alpha : Finset (Fin (2 ^ n)))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W)
    (hbulk : highHighAlias (2 * m) W alpha) :
    let product :=
      coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
    let union := alpha ∪ (alpha ∆ W)
    abs (oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
          (structuredActualRankWeight n m tailBits hn htail) alpha +
        oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
          (structuredActualRankWeight n m tailBits hn htail)
          (toggleSupport coordinate alpha)) <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
        structuredActualRankWeight n m tailBits hn htail union *
          abs product := by
  dsimp only
  let product :=
    coefficient (falseLiteralPart coordinate a) alpha *
      coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
  let union := alpha ∪ (alpha ∆ W)
  have htoggled := highHighAlias_toggle_of_not_mem
    coordinate (2 * m) W alpha hcoordinateAlpha hcoordinateW hbulk
  rw [structuredActualRankOppositeLiteralPair_eq_insertRankDerivative
    n m tailBits hn htail coordinate a b ha hb W alpha
      hcoordinateAlpha hcoordinateW]
  simp only [hbulk, htoggled, if_true]
  have hbounds := dyadicRankWeight_sub_insert_bounds
    n (structuredIndependence m) tailBits hn htail union coordinate
  let oldWeight := dyadicRankWeight
    (DPTWStructuredMaskRank.supportPrefixConstraintRank n
      (structuredIndependence m) tailBits hn htail union)
  let newWeight := dyadicRankWeight
    (DPTWStructuredMaskRank.supportPrefixConstraintRank n
      (structuredIndependence m) tailBits hn htail
        (insert coordinate union))
  have hnonneg : 0 <= oldWeight - newWeight := by
    simpa [oldWeight, newWeight] using hbounds.1
  have hdrop : oldWeight - newWeight <=
      (1 - 1 / (2 : Rat) ^ tailBits) * oldWeight := by
    simpa [oldWeight, newWeight] using hbounds.2
  change abs (product * (oldWeight - newWeight)) <=
    (1 - 1 / (2 : Rat) ^ tailBits) * oldWeight * abs product
  rw [abs_mul, abs_of_nonneg hnonneg]
  calc
    abs product * (oldWeight - newWeight) <=
        abs product *
          ((1 - 1 / (2 : Rat) ^ tailBits) * oldWeight) :=
      mul_le_mul_of_nonneg_left hdrop (abs_nonneg product)
    _ = (1 - 1 / (2 : Rat) ^ tailBits) * oldWeight *
        abs product := by ring

/-- A nonempty structured dual word supplies the additional saturated
`(4m+1) * tailBits` rank scale.  Thus every bulk opposite-literal pair has
the full local factor `(1-p) * p^(4m+1)` before its Fourier coefficient
product. -/
theorem abs_structuredActualRankOppositeLiteralPair_le_dualScale_of_bulk
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (W alpha : Finset (Fin (2 ^ n)))
    (hW : W ∈ nonemptyStructuredDualSupports n m hn)
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W)
    (hbulk : highHighAlias (2 * m) W alpha) :
    let product :=
      coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
    abs (oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
          (structuredActualRankWeight n m tailBits hn htail) alpha +
        oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
          (structuredActualRankWeight n m tailBits hn htail)
          (toggleSupport coordinate alpha)) <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
        dyadicRankWeight (structuredIndependence m * tailBits) *
          abs product := by
  dsimp only
  let product :=
    coefficient (falseLiteralPart coordinate a) alpha *
      coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
  let union := alpha ∪ (alpha ∆ W)
  have hlocal :=
    abs_structuredActualRankOppositeLiteralPair_le_of_bulk
      n m tailBits hn htail coordinate a b ha hb W alpha
        hcoordinateAlpha hcoordinateW hbulk
  dsimp only at hlocal
  have hW' := (mem_nonemptyStructuredDualSupports n m hn W).mp hW
  have hne : alpha ≠ alpha ∆ W := by
    intro heq
    have h := congrArg (fun support => alpha ∆ support) heq
    have hempty : (∅ : Finset (Fin (2 ^ n))) = W := by
      simpa only [symmDiff_self, symmDiff_symmDiff_cancel_left] using h
    exact hW'.1.ne_empty hempty.symm
  have hdual : IsStructuredDualSupport n (structuredIndependence m) hn
      (alpha ∆ (alpha ∆ W)) := by
    simpa only [symmDiff_symmDiff_cancel_left] using hW'.2
  have hweightRaw := distinctDualAlias_invPowUnionRank_le
    n m tailBits hn htail alpha (alpha ∆ W) hne hdual
  have hweight :
      structuredActualRankWeight n m tailBits hn htail union <=
        dyadicRankWeight (structuredIndependence m * tailBits) := by
    simpa [structuredActualRankWeight, dyadicRankWeight, union] using
      hweightRaw
  have hfactor : 0 <= 1 - 1 / (2 : Rat) ^ tailBits := by
    have hpow : (1 : Rat) <= (2 : Rat) ^ tailBits := by
      exact one_le_pow₀ (by norm_num)
    have hpowPos : (0 : Rat) < (2 : Rat) ^ tailBits := by positivity
    rw [sub_nonneg, div_le_iff₀ hpowPos]
    simpa using hpow
  have hscaled :
      (1 - 1 / (2 : Rat) ^ tailBits) *
            structuredActualRankWeight n m tailBits hn htail union *
          abs product <=
        (1 - 1 / (2 : Rat) ^ tailBits) *
            dyadicRankWeight (structuredIndependence m * tailBits) *
          abs product := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hweight hfactor) (abs_nonneg product)
  exact hlocal.trans hscaled

end FiniteBooleanOppositeLiteralRankDerivative

end

end OneTapeMagnification
end Frontier
end Pnp4
