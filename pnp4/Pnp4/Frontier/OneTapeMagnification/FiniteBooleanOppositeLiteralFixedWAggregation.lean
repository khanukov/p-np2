import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralRankDerivative
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fixed-dual aggregation for opposite query literals

The local opposite-literal rank derivative is stated for one Fourier-support
toggle pair.  This module sums that estimate over all strict high/high pairs
for one fixed dual word `W`.

There are two independent factors of one half.  Young's inequality bounds one
coefficient product by half the sum of its squared coefficients.  Moreover,
for a literal part whose residual function is independent of the queried
coordinate, exactly half of its Fourier energy lies on supports which omit
that coordinate.  Since `coordinate ∉ W`, fixed-dual translation preserves
this coordinate-free half of the cube.  Together these give the exact factor
`1 / 4` in the final fixed-`W` estimate.

This is deliberately not a packing theorem.  It treats one dual word and one
opposite-literal pair.  Summation over dual words, reverse-walk cells, or
different literal pairs requires additional overlap control.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteRankWeightAbelVariation
open FiniteStructuredDualFixedDifferenceReindex
open FiniteBooleanOppositeLiteralCorrelation
open FiniteBooleanOppositeLiteralRankDerivative
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredMaskRank

namespace FiniteBooleanOppositeLiteralFixedWAggregation

/-- Fourier supports which omit the queried coordinate. -/
def coordinateFreeSupports {N : Nat} (coordinate : Fin N) :
    Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N))).filter
    (fun alpha => coordinate ∉ alpha)

/-- Squared Fourier energy on supports which omit the queried coordinate. -/
def coordinateFreeFourierEnergy {N : Nat} (coordinate : Fin N)
    (f : (Fin N -> Bool) -> Rat) : Rat :=
  ∑ alpha in coordinateFreeSupports coordinate,
    (coefficient f alpha) ^ 2

/-- Coordinate-free supports in the strict high/high region for one fixed
dual word. -/
def bulkCoordinateFreeSupports {N : Nat} (coordinate : Fin N)
    (cutoff : Nat) (W : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  (coordinateFreeSupports coordinate).filter
    (fun alpha => highHighAlias cutoff W alpha)

private theorem coordinateFree_sum_sq_eq_half_full
    {N : Nat} (coordinate : Fin N)
    (c : Finset (Fin N) -> Rat)
    (htoggle : ∀ alpha,
      (c (toggleSupport coordinate alpha)) ^ 2 = (c alpha) ^ 2) :
    (∑ alpha in coordinateFreeSupports coordinate, (c alpha) ^ 2) =
      (1 / 2 : Rat) * ∑ alpha : Finset (Fin N), (c alpha) ^ 2 := by
  classical
  let absent := coordinateFreeSupports coordinate
  let present := (Finset.univ : Finset (Finset (Fin N))).filter
    (fun alpha => coordinate ∈ alpha)
  have hreindex :
      (∑ alpha in absent, (c (toggleSupport coordinate alpha)) ^ 2) =
        ∑ alpha in present, (c alpha) ^ 2 := by
    apply Finset.sum_bij (fun alpha _ => toggleSupport coordinate alpha)
    · intro alpha halpha
      have habsent : coordinate ∉ alpha := by
        simpa [absent, coordinateFreeSupports] using halpha
      simp [present, (mem_toggleSupport_self_iff coordinate alpha).2 habsent]
    · intro left hleft right hright heq
      exact (toggleSupportEquiv coordinate).injective heq
    · intro target htarget
      have hpresent : coordinate ∈ target := by
        simpa [present] using htarget
      refine ⟨toggleSupport coordinate target, ?_, ?_⟩
      · have habsent : coordinate ∉ toggleSupport coordinate target := by
          intro hmem
          exact (mem_toggleSupport_self_iff coordinate target).1 hmem hpresent
        simp [absent, coordinateFreeSupports, habsent]
      · exact toggleSupport_toggleSupport coordinate target
    · intro alpha halpha
      rfl
  have hsplit := Finset.sum_filter_not_add_sum_filter
    (Finset.univ : Finset (Finset (Fin N)))
    (fun alpha => coordinate ∈ alpha) (fun alpha => (c alpha) ^ 2)
  have hfull :
      (∑ alpha : Finset (Fin N), (c alpha) ^ 2) =
        2 * ∑ alpha in absent, (c alpha) ^ 2 := by
    calc
      (∑ alpha : Finset (Fin N), (c alpha) ^ 2) =
          (∑ alpha in absent, (c alpha) ^ 2) +
            ∑ alpha in present, (c alpha) ^ 2 := by
        symm
        simpa [absent, present, coordinateFreeSupports] using hsplit
      _ = (∑ alpha in absent, (c alpha) ^ 2) +
            ∑ alpha in absent,
              (c (toggleSupport coordinate alpha)) ^ 2 := by
        rw [hreindex]
      _ = 2 * ∑ alpha in absent, (c alpha) ^ 2 := by
        simp_rw [htoggle]
        ring
  rw [hfull]
  change (∑ alpha in absent, (c alpha) ^ 2) = _
  ring

/-- Exactly half of the squared Fourier energy of a false-literal part lies
on supports which omit the literal coordinate. -/
theorem coordinateFreeFourierEnergy_falseLiteralPart_eq_half
    {N : Nat} (coordinate : Fin N)
    (a : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a) :
    coordinateFreeFourierEnergy coordinate
        (falseLiteralPart coordinate a) =
      (1 / 2 : Rat) *
        ∑ alpha : Finset (Fin N),
          (coefficient (falseLiteralPart coordinate a) alpha) ^ 2 := by
  apply coordinateFree_sum_sq_eq_half_full
  intro alpha
  rw [coefficient_falseLiteralPart_toggle coordinate a ha]

/-- Exactly half of the squared Fourier energy of a true-literal part lies
on supports which omit the literal coordinate. -/
theorem coordinateFreeFourierEnergy_trueLiteralPart_eq_half
    {N : Nat} (coordinate : Fin N)
    (b : (Fin N -> Bool) -> Rat)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b) :
    coordinateFreeFourierEnergy coordinate
        (trueLiteralPart coordinate b) =
      (1 / 2 : Rat) *
        ∑ alpha : Finset (Fin N),
          (coefficient (trueLiteralPart coordinate b) alpha) ^ 2 := by
  apply coordinateFree_sum_sq_eq_half_full
  intro alpha
  rw [coefficient_trueLiteralPart_toggle coordinate b hb]
  ring

/-- Parseval form of the false-literal coordinate-free energy split. -/
theorem coordinateFreeFourierEnergy_falseLiteralPart_eq_half_averageSq
    {N : Nat} (coordinate : Fin N)
    (a : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a) :
    coordinateFreeFourierEnergy coordinate
        (falseLiteralPart coordinate a) =
      (1 / 2 : Rat) * finiteAverage
        (fun input : Fin N -> Bool =>
          (falseLiteralPart coordinate a input) ^ 2) := by
  rw [coordinateFreeFourierEnergy_falseLiteralPart_eq_half coordinate a ha,
    parseval]

/-- Parseval form of the true-literal coordinate-free energy split. -/
theorem coordinateFreeFourierEnergy_trueLiteralPart_eq_half_averageSq
    {N : Nat} (coordinate : Fin N)
    (b : (Fin N -> Bool) -> Rat)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b) :
    coordinateFreeFourierEnergy coordinate
        (trueLiteralPart coordinate b) =
      (1 / 2 : Rat) * finiteAverage
        (fun input : Fin N -> Bool =>
          (trueLiteralPart coordinate b input) ^ 2) := by
  rw [coordinateFreeFourierEnergy_trueLiteralPart_eq_half coordinate b hb,
    parseval]

private def fixedDualToggleEquiv {N : Nat} (W : Finset (Fin N)) :
    Finset (Fin N) ≃ Finset (Fin N) :=
  (symmDiff_left_involutive W).toPerm (fun alpha => alpha ∆ W)

private theorem sum_coordinateFree_symmDiff_eq
    {N : Nat} (coordinate : Fin N) (W : Finset (Fin N))
    (hcoordinateW : coordinate ∉ W)
    (f : Finset (Fin N) -> Rat) :
    (∑ alpha in coordinateFreeSupports coordinate, f (alpha ∆ W)) =
      ∑ alpha in coordinateFreeSupports coordinate, f alpha := by
  classical
  apply Finset.sum_bij (fun alpha _ => alpha ∆ W)
  · intro alpha halpha
    have hcoordinateAlpha : coordinate ∉ alpha := by
      simpa [coordinateFreeSupports] using halpha
    have hcoordinateImage : coordinate ∉ alpha ∆ W := by
      simp only [Finset.mem_symmDiff]
      tauto
    simp [coordinateFreeSupports, hcoordinateImage]
  · intro left hleft right hright heq
    exact (fixedDualToggleEquiv W).injective heq
  · intro target htarget
    have hcoordinateTarget : coordinate ∉ target := by
      simpa [coordinateFreeSupports] using htarget
    have hcoordinatePreimage : coordinate ∉ target ∆ W := by
      simp only [Finset.mem_symmDiff]
      tauto
    refine ⟨target ∆ W, ?_, ?_⟩
    · simp [coordinateFreeSupports, hcoordinatePreimage]
    · exact (fixedDualToggleEquiv W).symm_apply_apply target
  · intro alpha halpha
    rfl

private theorem abs_mul_le_half_add_sq (x y : Rat) :
    abs (x * y) <= (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (abs x - abs y), sq_abs x, sq_abs y]

/-- Sum of all strict high/high opposite-literal toggle pairs for one fixed
dual word `W`.  The transversal contains exactly the supports which omit the
queried coordinate. -/
def structuredActualRankOppositeLiteralBulkFixedWSum
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (W : Finset (Fin (2 ^ n))) : Rat :=
  ∑ alpha in bulkCoordinateFreeSupports coordinate (2 * m) W,
    (oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
        (structuredActualRankWeight n m tailBits hn htail) alpha +
      oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
        (structuredActualRankWeight n m tailBits hn htail)
        (toggleSupport coordinate alpha))

/-- **Fixed-`W` bulk aggregation.**  The local rank-derivative gain sums over
all coordinate-free bulk toggle pairs with no loss depending on the number of
Fourier supports.  The factor `1 / 4` is the product of Young's `1 / 2` and
the exact coordinate-free literal-energy split.

This theorem assumes one nonempty structured dual word `W` with
`coordinate ∉ W`; it does not aggregate over different dual words or walk
cells. -/
theorem abs_structuredActualRankOppositeLiteralBulkFixedWSum_le_fourierEnergy
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (W : Finset (Fin (2 ^ n)))
    (hW : W ∈ nonemptyStructuredDualSupports n m hn)
    (hcoordinateW : coordinate ∉ W) :
    abs (structuredActualRankOppositeLiteralBulkFixedWSum
      n m tailBits hn htail coordinate a b W) <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
          dyadicRankWeight (structuredIndependence m * tailBits) *
        ((1 / 4 : Rat) *
          ((∑ alpha : Finset (Fin (2 ^ n)),
              (coefficient (falseLiteralPart coordinate a) alpha) ^ 2) +
            ∑ alpha : Finset (Fin (2 ^ n)),
              (coefficient (trueLiteralPart coordinate b) alpha) ^ 2)) := by
  classical
  let supports := bulkCoordinateFreeSupports coordinate (2 * m) W
  let falsePart := falseLiteralPart coordinate a
  let truePart := trueLiteralPart coordinate b
  let scale :=
    (1 - 1 / (2 : Rat) ^ tailBits) *
      dyadicRankWeight (structuredIndependence m * tailBits)
  have honeSub : 0 <= 1 - 1 / (2 : Rat) ^ tailBits := by
    have hpow : (1 : Rat) <= (2 : Rat) ^ tailBits := by
      exact one_le_pow₀ (by norm_num)
    have hpowPos : (0 : Rat) < (2 : Rat) ^ tailBits := by positivity
    rw [sub_nonneg, div_le_iff₀ hpowPos]
    simpa using hpow
  have hscale : 0 <= scale := by
    exact mul_nonneg honeSub
      (dyadicRankWeight_nonneg (structuredIndependence m * tailBits))
  have hlocal : ∀ alpha ∈ supports,
      abs (oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
            (structuredActualRankWeight n m tailBits hn htail) alpha +
          oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
            (structuredActualRankWeight n m tailBits hn htail)
            (toggleSupport coordinate alpha)) <=
        scale *
          abs (coefficient falsePart alpha *
            coefficient truePart (alpha ∆ W)) := by
    intro alpha halpha
    have halpha' :
        alpha ∈ coordinateFreeSupports coordinate ∧
          highHighAlias (2 * m) W alpha := by
      simpa [supports, bulkCoordinateFreeSupports] using halpha
    have hcoordinateAlpha : coordinate ∉ alpha := by
      simpa [coordinateFreeSupports] using halpha'.1
    have hbulk : highHighAlias (2 * m) W alpha := by
      exact halpha'.2
    simpa [scale, falsePart, truePart] using
      abs_structuredActualRankOppositeLiteralPair_le_dualScale_of_bulk
        n m tailBits hn htail coordinate a b ha hb W alpha hW
          hcoordinateAlpha hcoordinateW hbulk
  have hsupports : supports ⊆ coordinateFreeSupports coordinate := by
    intro alpha halpha
    have halpha' :
        alpha ∈ coordinateFreeSupports coordinate ∧
          highHighAlias (2 * m) W alpha := by
      simpa [supports, bulkCoordinateFreeSupports] using halpha
    exact halpha'.1
  have hfalseSubset :
      (∑ alpha in supports, (coefficient falsePart alpha) ^ 2) <=
        coordinateFreeFourierEnergy coordinate falsePart := by
    unfold coordinateFreeFourierEnergy
    exact Finset.sum_le_sum_of_subset_of_nonneg hsupports
      (fun alpha halpha hnot => sq_nonneg (coefficient falsePart alpha))
  have htrueSubset :
      (∑ alpha in supports,
          (coefficient truePart (alpha ∆ W)) ^ 2) <=
        coordinateFreeFourierEnergy coordinate truePart := by
    calc
      (∑ alpha in supports,
          (coefficient truePart (alpha ∆ W)) ^ 2) <=
          ∑ alpha in coordinateFreeSupports coordinate,
            (coefficient truePart (alpha ∆ W)) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsupports
          (fun alpha halpha hnot =>
            sq_nonneg (coefficient truePart (alpha ∆ W)))
      _ = ∑ alpha in coordinateFreeSupports coordinate,
            (coefficient truePart alpha) ^ 2 := by
        exact sum_coordinateFree_symmDiff_eq coordinate W hcoordinateW
          (fun alpha => (coefficient truePart alpha) ^ 2)
      _ = coordinateFreeFourierEnergy coordinate truePart := by
        rfl
  have hsumProducts :
      (∑ alpha in supports,
          abs (coefficient falsePart alpha *
            coefficient truePart (alpha ∆ W))) <=
        (1 / 2 : Rat) *
          (coordinateFreeFourierEnergy coordinate falsePart +
            coordinateFreeFourierEnergy coordinate truePart) := by
    calc
      (∑ alpha in supports,
          abs (coefficient falsePart alpha *
            coefficient truePart (alpha ∆ W))) <=
          ∑ alpha in supports,
            (((coefficient falsePart alpha) ^ 2 +
              (coefficient truePart (alpha ∆ W)) ^ 2) / 2) := by
        apply Finset.sum_le_sum
        intro alpha halpha
        exact abs_mul_le_half_add_sq _ _
      _ = (1 / 2 : Rat) *
          ((∑ alpha in supports, (coefficient falsePart alpha) ^ 2) +
            ∑ alpha in supports,
              (coefficient truePart (alpha ∆ W)) ^ 2) := by
        simp_rw [div_eq_mul_inv, add_mul]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        ring
      _ <= (1 / 2 : Rat) *
          (coordinateFreeFourierEnergy coordinate falsePart +
            coordinateFreeFourierEnergy coordinate truePart) := by
        nlinarith
  calc
    abs (structuredActualRankOppositeLiteralBulkFixedWSum
        n m tailBits hn htail coordinate a b W) <=
        ∑ alpha in supports,
          abs (oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
                (structuredActualRankWeight n m tailBits hn htail) alpha +
            oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
              (structuredActualRankWeight n m tailBits hn htail)
              (toggleSupport coordinate alpha)) := by
      unfold structuredActualRankOppositeLiteralBulkFixedWSum
      change abs (∑ alpha in supports, _) <= _
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ alpha in supports,
          scale * abs (coefficient falsePart alpha *
            coefficient truePart (alpha ∆ W)) := by
      apply Finset.sum_le_sum
      intro alpha halpha
      exact hlocal alpha halpha
    _ = scale *
          ∑ alpha in supports,
            abs (coefficient falsePart alpha *
              coefficient truePart (alpha ∆ W)) := by
      rw [Finset.mul_sum]
    _ <= scale * ((1 / 2 : Rat) *
          (coordinateFreeFourierEnergy coordinate falsePart +
            coordinateFreeFourierEnergy coordinate truePart)) := by
      exact mul_le_mul_of_nonneg_left hsumProducts hscale
    _ = (1 - 1 / (2 : Rat) ^ tailBits) *
          dyadicRankWeight (structuredIndependence m * tailBits) *
        ((1 / 4 : Rat) *
          ((∑ alpha : Finset (Fin (2 ^ n)),
              (coefficient (falseLiteralPart coordinate a) alpha) ^ 2) +
            ∑ alpha : Finset (Fin (2 ^ n)),
              (coefficient (trueLiteralPart coordinate b) alpha) ^ 2)) := by
      rw [coordinateFreeFourierEnergy_falseLiteralPart_eq_half
          coordinate a ha,
        coordinateFreeFourierEnergy_trueLiteralPart_eq_half
          coordinate b hb]
      simp only [scale]
      ring

/-- Parseval form of the fixed-`W` bulk aggregation theorem. -/
theorem abs_structuredActualRankOppositeLiteralBulkFixedWSum_le_averageSq
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (W : Finset (Fin (2 ^ n)))
    (hW : W ∈ nonemptyStructuredDualSupports n m hn)
    (hcoordinateW : coordinate ∉ W) :
    abs (structuredActualRankOppositeLiteralBulkFixedWSum
      n m tailBits hn htail coordinate a b W) <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
          dyadicRankWeight (structuredIndependence m * tailBits) *
        ((1 / 4 : Rat) *
          (finiteAverage
              (fun input : Fin (2 ^ n) -> Bool =>
                (falseLiteralPart coordinate a input) ^ 2) +
            finiteAverage
              (fun input : Fin (2 ^ n) -> Bool =>
                (trueLiteralPart coordinate b input) ^ 2))) := by
  simpa only [parseval] using
    abs_structuredActualRankOppositeLiteralBulkFixedWSum_le_fourierEnergy
      n m tailBits hn htail coordinate a b ha hb W hW hcoordinateW

end FiniteBooleanOppositeLiteralFixedWAggregation

end

end OneTapeMagnification
end Frontier
end Pnp4
