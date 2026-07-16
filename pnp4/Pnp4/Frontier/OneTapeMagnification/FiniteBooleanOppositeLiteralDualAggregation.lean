import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralFixedWAggregation
import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualNonzeroSeedCorrelation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Dual-word aggregation for opposite query literals

The fixed-dual bulk estimate is useful only if its outer sum over structured
dual words does not pay their cardinality.  This file gives the exact
semantic aggregation step.  A one-coordinate rank derivative is the
probability that the old union is frozen while the queried coordinate is
live.  Consequently, after averaging the structured mask seed, the complete
outer dual-word bulk is one fixed-mask structured cross-correlation rather
than a triangle-inequality sum over dual words.

The identity by itself does not give the required small numerical bound.  It
replaces dual-word multiplicity by a conditional signed-correlation endpoint;
controlling that endpoint is an operator-norm / selector-packing problem.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteBooleanOppositeLiteralCorrelation
open FiniteBooleanOppositeLiteralFixedWAggregation
open FiniteBooleanPerVertexRestrictionBound
open FiniteStructuredDualFixedDifferenceReindex
open FiniteStructuredDualNonzeroSeedCorrelation
open FiniteStructuredDualRankThresholdBridge
open FiniteSignedReverseLCPSiblingDualRank
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredFullFieldCorrelation
open DPTWStructuredMaskRank

namespace FiniteBooleanOppositeLiteralDualAggregation

/-- Indicator that the queried mask coordinate is live (`true`). -/
def maskLiveIndicator {N : Nat} (coordinate : Fin N)
    (mask : Fin N -> Bool) : Rat :=
  if mask coordinate then 1 else 0

/-- If `coordinate` is absent from `support`, being frozen on `support` and
live at `coordinate` is exactly the loss of survival after inserting the
coordinate. -/
theorem maskLiveIndicator_mul_maskAllZeroIndicator_eq_sub_insert
    {N : Nat} (coordinate : Fin N) (support : Finset (Fin N))
    (hcoordinate : coordinate ∉ support) (mask : Fin N -> Bool) :
    maskLiveIndicator coordinate mask * maskAllZeroIndicator support mask =
      maskAllZeroIndicator support mask -
        maskAllZeroIndicator (insert coordinate support) mask := by
  unfold maskLiveIndicator maskAllZeroIndicator
  cases hvalue : mask coordinate
  · have hinsert :
        (∀ index ∈ insert coordinate support, mask index = false) ↔
          ∀ index ∈ support, mask index = false := by
      constructor
      · intro hall index hindex
        exact hall index (Finset.mem_insert_of_mem hindex)
      · intro hall index hindex
        rcases Finset.mem_insert.mp hindex with rfl | hindex
        · exact hvalue
        · exact hall index hindex
    simp only [Bool.false_eq_true, if_false, zero_mul]
    rw [if_congr hinsert rfl rfl]
    ring
  · have hnotInsert :
        ¬ ∀ index ∈ insert coordinate support, mask index = false := by
      intro hall
      have := hall coordinate (Finset.mem_insert_self coordinate support)
      simp [hvalue] at this
    simp only [if_true, one_mul]
    rw [if_neg hnotInsert]
    ring

/-- Exact structured-mask average of the live-coordinate survival event. -/
theorem finiteAverage_live_mul_maskSurvival_eq_rankWeight_sub_insert
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n)) (support : Finset (Fin (2 ^ n)))
    (hcoordinate : coordinate ∉ support) :
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          let mask :=
            (structuredDyadicPrimitive n m tailBits hn htail).generate seed
          maskLiveIndicator coordinate mask *
            maskAllZeroIndicator support mask) =
      structuredActualRankWeight n m tailBits hn htail support -
        structuredActualRankWeight n m tailBits hn htail
          (insert coordinate support) := by
  rw [show finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          let mask :=
            (structuredDyadicPrimitive n m tailBits hn htail).generate seed
          maskLiveIndicator coordinate mask *
            maskAllZeroIndicator support mask) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          maskAllZeroIndicator support
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed) -
            maskAllZeroIndicator (insert coordinate support)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) by
      apply finiteAverage_congr
      intro seed
      exact maskLiveIndicator_mul_maskAllZeroIndicator_eq_sub_insert
        coordinate support hcoordinate _]
  rw [show finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          maskAllZeroIndicator support
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed) -
            maskAllZeroIndicator (insert coordinate support)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) =
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            maskAllZeroIndicator support
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) -
        finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            maskAllZeroIndicator (insert coordinate support)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) by
      unfold finiteAverage
      rw [Finset.sum_sub_distrib]
      ring,
    structuredDyadicPrimitive_maskSurvival_eq_invPowRank,
    structuredDyadicPrimitive_maskSurvival_eq_invPowRank]
  rfl

/-- The fixed-`W` high/high convolution seen by one concrete mask, oriented
on supports which omit the query coordinate. -/
def oppositeLiteralBulkFixedWAtMask
    {N : Nat} (coordinate : Fin N)
    (a b : (Fin N -> Bool) -> Rat) (cutoff : Nat)
    (W : Finset (Fin N)) (mask : Fin N -> Bool) : Rat :=
  ∑ alpha ∈ bulkCoordinateFreeSupports coordinate cutoff W,
    maskLiveIndicator coordinate mask *
      maskAllZeroIndicator (alpha ∪ (alpha ∆ W)) mask *
        (coefficient (falseLiteralPart coordinate a) alpha *
          coefficient (trueLiteralPart coordinate b) (alpha ∆ W))

/-- Fixed-difference reindexing of one concrete-mask cross-correlation.  This
is the exact character-orthogonality aggregation over all nonzero structured
dual words, with no absolute values and no cardinality factor. -/
theorem structuredDualPairCorrelationAtMask_eq_sum_fixedDual
    (n m cutoff : Nat) (hn : 0 < n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredDualPairCorrelationAtMask n m cutoff hn
        leftFunction rightFunction mask =
      ∑ W ∈ nonemptyStructuredDualSupports n m hn,
        ∑ alpha : Finset (Fin (2 ^ n)),
          if highHighAlias cutoff W alpha then
            maskAllZeroIndicator (alpha ∪ (alpha ∆ W)) mask *
              (coefficient leftFunction alpha *
                coefficient rightFunction (alpha ∆ W))
          else 0 := by
  classical
  unfold structuredDualPairCorrelationAtMask
  let sourceTerm := fun pair :
      Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) =>
    maskAllZeroIndicator (pair.1 ∪ pair.2) mask *
      structuredDualAliasPairCoefficient
        leftFunction rightFunction pair
  let targetTerm := fun pair :
      Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) =>
    maskAllZeroIndicator (pair.2 ∪ (pair.2 ∆ pair.1)) mask *
      (coefficient leftFunction pair.2 *
        coefficient rightFunction (pair.2 ∆ pair.1))
  calc
    (∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
        sourceTerm pair) =
        ∑ pair ∈
            (structuredDualAliasPairs n m cutoff hn).map
              (fixedDifferencePairEquiv (Fin (2 ^ n))).toEmbedding,
          targetTerm pair := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro pair _hpair
      rcases pair with ⟨left, right⟩
      simp [sourceTerm, targetTerm,
        structuredDualAliasPairCoefficient]
    _ = ∑ pair ∈ structuredDualFixedDifferencePairs
          n m cutoff hn, targetTerm pair := by
      rw [structuredDualAliasPairs_map_fixedDifferencePairEquiv]
    _ = ∑ W ∈ nonemptyStructuredDualSupports n m hn,
          ∑ alpha : Finset (Fin (2 ^ n)),
            if highHighAlias cutoff W alpha then
              targetTerm (W, alpha) else 0 := by
      unfold structuredDualFixedDifferencePairs
      rw [Finset.sum_filter]
      exact Finset.sum_product
        (nonemptyStructuredDualSupports n m hn) Finset.univ
          (fun pair =>
            if highHighAlias cutoff pair.1 pair.2 then
              targetTerm pair else 0)
    _ = _ := by
      rfl

/-- The complete fixed-mask bulk, summed over every nonempty structured dual
word which omits the query coordinate. -/
def structuredOppositeLiteralBulkDualSumAtMask
    (n m cutoff : Nat) (hn : 0 < n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  ∑ W ∈ nonemptyStructuredDualSupports n m hn,
    if coordinate ∉ W then
      oppositeLiteralBulkFixedWAtMask coordinate a b cutoff W mask
    else 0

private theorem maskAllZeroIndicator_eq_zero_of_true_mem
    {N : Nat} (coordinate : Fin N) (support : Finset (Fin N))
    (mask : Fin N -> Bool) (hmask : mask coordinate = true)
    (hmem : coordinate ∈ support) :
    maskAllZeroIndicator support mask = 0 := by
  unfold maskAllZeroIndicator
  rw [if_neg]
  intro hall
  have := hall coordinate hmem
  simp [hmask] at this

/-- At a live query coordinate, a fixed dual containing that coordinate has
zero mask-surviving cross-convolution: exactly one endpoint contains it. -/
private theorem fixedDualMaskCrossSum_eq_zero_of_coordinate_mem
    {N cutoff : Nat} (coordinate : Fin N)
    (leftFunction rightFunction : (Fin N -> Bool) -> Rat)
    (W : Finset (Fin N)) (hcoordinateW : coordinate ∈ W)
    (mask : Fin N -> Bool) (hmask : mask coordinate = true) :
    (∑ alpha : Finset (Fin N),
      if highHighAlias cutoff W alpha then
        maskAllZeroIndicator (alpha ∪ (alpha ∆ W)) mask *
          (coefficient leftFunction alpha *
            coefficient rightFunction (alpha ∆ W))
      else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro alpha _halpha
  by_cases hhigh : highHighAlias cutoff W alpha
  · have hmem : coordinate ∈ alpha ∪ (alpha ∆ W) := by
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      tauto
    rw [if_pos hhigh,
      maskAllZeroIndicator_eq_zero_of_true_mem
        coordinate _ mask hmask hmem]
    ring
  · rw [if_neg hhigh]

/-- **Exact outer-dual aggregation.**  Once the mask is fixed, summing every
off-coordinate fixed-`W` bulk is exactly the live-coordinate multiple of the
single structured dual-pair cross-correlation.  Thus the dual-word count has
disappeared before any triangle inequality is taken. -/
theorem structuredOppositeLiteralBulkDualSumAtMask_eq_live_mul_crossCorrelation
    (n m cutoff : Nat) (hn : 0 < n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredOppositeLiteralBulkDualSumAtMask
        n m cutoff hn coordinate a b mask =
      maskLiveIndicator coordinate mask *
        structuredDualPairCorrelationAtMask n m cutoff hn
          (falseLiteralPart coordinate a)
          (trueLiteralPart coordinate b) mask := by
  classical
  rw [structuredDualPairCorrelationAtMask_eq_sum_fixedDual]
  unfold structuredOppositeLiteralBulkDualSumAtMask
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W hW
  by_cases hcoordinateW : coordinate ∈ W
  · rw [if_neg (not_not.mpr hcoordinateW)]
    cases hvalue : mask coordinate
    · simp [maskLiveIndicator, hvalue]
    · rw [fixedDualMaskCrossSum_eq_zero_of_coordinate_mem
          coordinate _ _ W hcoordinateW mask hvalue]
      simp
  · rw [if_pos hcoordinateW]
    unfold oppositeLiteralBulkFixedWAtMask
    rw [Finset.mul_sum]
    cases hvalue : mask coordinate
    · simp [maskLiveIndicator, hvalue]
    · simp only [maskLiveIndicator, hvalue, if_true, one_mul]
      unfold bulkCoordinateFreeSupports coordinateFreeSupports
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro alpha _halpha
      by_cases hcoordinateAlpha : coordinate ∈ alpha
      · have hmem : coordinate ∈ alpha ∪ (alpha ∆ W) :=
          Finset.mem_union_left _ hcoordinateAlpha
        rw [if_neg (not_not.mpr hcoordinateAlpha)]
        by_cases hhigh : highHighAlias cutoff W alpha
        · rw [if_pos hhigh,
            maskAllZeroIndicator_eq_zero_of_true_mem
              coordinate _ mask hvalue hmem]
          ring
        · rw [if_neg hhigh]
      · rw [if_pos hcoordinateAlpha]

/-- One fixed-dual bulk derivative is exactly the structured-mask average of
the corresponding live-coordinate convolution slice. -/
theorem structuredActualRankOppositeLiteralBulkFixedWSum_eq_finiteAverage
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (W : Finset (Fin (2 ^ n))) (hcoordinateW : coordinate ∉ W) :
    structuredActualRankOppositeLiteralBulkFixedWSum
        n m tailBits hn htail coordinate a b W =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          oppositeLiteralBulkFixedWAtMask coordinate a b (2 * m) W
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) := by
  classical
  unfold structuredActualRankOppositeLiteralBulkFixedWSum
    oppositeLiteralBulkFixedWAtMask
  rw [finiteAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro alpha halpha
  have halphaData :
      alpha ∈ coordinateFreeSupports coordinate ∧
        highHighAlias (2 * m) W alpha := by
    simpa [bulkCoordinateFreeSupports] using halpha
  have hcoordinateAlpha : coordinate ∉ alpha := by
    simpa [coordinateFreeSupports] using halphaData.1
  have hcoordinateRight : coordinate ∉ alpha ∆ W := by
    simp only [Finset.mem_symmDiff]
    tauto
  have hcoordinateUnion : coordinate ∉ alpha ∪ (alpha ∆ W) := by
    simp [hcoordinateAlpha, hcoordinateRight]
  rw [structuredActualRankOppositeLiteralPair_eq_insertRankDerivative
    n m tailBits hn htail coordinate a b ha hb W alpha
      hcoordinateAlpha hcoordinateW]
  rw [if_pos halphaData.2]
  let product := coefficient (falseLiteralPart coordinate a) alpha *
    coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
  have haverage :=
    finiteAverage_live_mul_maskSurvival_eq_rankWeight_sub_insert
      n m tailBits hn htail coordinate (alpha ∪ (alpha ∆ W))
        hcoordinateUnion
  change product *
      (structuredActualRankWeight n m tailBits hn htail
          (alpha ∪ (alpha ∆ W)) -
        structuredActualRankWeight n m tailBits hn htail
          (insert coordinate (alpha ∪ (alpha ∆ W)))) = _
  calc
    product *
        (structuredActualRankWeight n m tailBits hn htail
            (alpha ∪ (alpha ∆ W)) -
          structuredActualRankWeight n m tailBits hn htail
            (insert coordinate (alpha ∪ (alpha ∆ W)))) =
        product * finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            let mask :=
              (structuredDyadicPrimitive n m tailBits hn htail).generate seed
            maskLiveIndicator coordinate mask *
              maskAllZeroIndicator (alpha ∪ (alpha ∆ W)) mask) := by
      rw [haverage]
    _ = finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            product *
              (maskLiveIndicator coordinate
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate seed) *
                maskAllZeroIndicator (alpha ∪ (alpha ∆ W))
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate seed))) := by
      rw [finiteAverage_const_mul]
    _ = _ := by
      apply finiteAverage_congr
      intro seed
      dsimp only [product]
      ring

/-- The complete actual-rank bulk derivative, aggregated over all nonempty
structured dual words away from the query coordinate. -/
def structuredActualRankOppositeLiteralBulkDualSum
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat) : Rat :=
  ∑ W ∈ nonemptyStructuredDualSupports n m hn,
    if coordinate ∉ W then
      structuredActualRankOppositeLiteralBulkFixedWSum
        n m tailBits hn htail coordinate a b W
    else 0

/-- **Dual-word-free semantic endpoint.**  The entire off-coordinate bulk
sum is a single structured-mask expectation of one signed fixed-mask cross
correlation.  Exact character orthogonality has absorbed the outer dual-word
sum; no factor involving `nonemptyStructuredDualSupports.card` occurs. -/
theorem structuredActualRankOppositeLiteralBulkDualSum_eq_finiteAverage_crossCorrelation
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b) :
    structuredActualRankOppositeLiteralBulkDualSum
        n m tailBits hn htail coordinate a b =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          let mask :=
            (structuredDyadicPrimitive n m tailBits hn htail).generate seed
          maskLiveIndicator coordinate mask *
            structuredDualPairCorrelationAtMask n m (2 * m) hn
              (falseLiteralPart coordinate a)
              (trueLiteralPart coordinate b) mask) := by
  classical
  unfold structuredActualRankOppositeLiteralBulkDualSum
  calc
    (∑ W ∈ nonemptyStructuredDualSupports n m hn,
        if coordinate ∉ W then
          structuredActualRankOppositeLiteralBulkFixedWSum
            n m tailBits hn htail coordinate a b W
        else 0) =
      ∑ W ∈ nonemptyStructuredDualSupports n m hn,
        finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            if coordinate ∉ W then
              oppositeLiteralBulkFixedWAtMask coordinate a b (2 * m) W
                ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)
            else 0) := by
      apply Finset.sum_congr rfl
      intro W _hW
      by_cases hcoordinateW : coordinate ∉ W
      · rw [if_pos hcoordinateW,
          structuredActualRankOppositeLiteralBulkFixedWSum_eq_finiteAverage
            n m tailBits hn htail coordinate a b ha hb W hcoordinateW]
        apply finiteAverage_congr
        intro seed
        rw [if_pos hcoordinateW]
      · rw [if_neg hcoordinateW]
        have hmem : coordinate ∈ W := not_not.mp hcoordinateW
        simp [finiteAverage, hmem]
    _ = finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          structuredOppositeLiteralBulkDualSumAtMask
            n m (2 * m) hn coordinate a b
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) := by
      unfold structuredOppositeLiteralBulkDualSumAtMask
      exact (finiteAverage_finset_sum
        (nonemptyStructuredDualSupports n m hn)
        (fun W =>
          fun seed : Fin (structuredIndependence m * n) -> Bool =>
            if coordinate ∉ W then
              oppositeLiteralBulkFixedWAtMask coordinate a b (2 * m) W
                ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)
            else 0)).symm
    _ = _ := by
      apply finiteAverage_congr
      intro seed
      exact
        structuredOppositeLiteralBulkDualSumAtMask_eq_live_mul_crossCorrelation
          n m (2 * m) hn coordinate a b
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)

/-! ## Honest size-free endpoint and its numerical loss -/

/-- The concrete-mask structured pair form is symmetric in its two function
arguments. -/
theorem structuredDualPairCorrelationAtMask_symm
    (n m cutoff : Nat) (hn : 0 < n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredDualPairCorrelationAtMask n m cutoff hn
        leftFunction rightFunction mask =
      structuredDualPairCorrelationAtMask n m cutoff hn
        rightFunction leftFunction mask := by
  classical
  unfold structuredDualPairCorrelationAtMask
    structuredDualAliasPairCoefficient
  apply Finset.sum_bij (fun pair _ => (pair.2, pair.1))
  · intro pair hpair
    rw [mem_structuredDualAliasPairs_iff] at hpair ⊢
    refine ⟨hpair.2.1, hpair.1, Ne.symm hpair.2.2.1, ?_⟩
    simpa [symmDiff_comm] using hpair.2.2.2
  · intro left _hleft right _hright heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro target htarget
    refine ⟨(target.2, target.1), ?_, ?_⟩
    · rw [mem_structuredDualAliasPairs_iff] at htarget ⊢
      refine ⟨htarget.2.1, htarget.1, Ne.symm htarget.2.2.1, ?_⟩
      simpa [symmDiff_comm] using htarget.2.2.2
    · exact Prod.ext rfl rfl
  · intro pair _hpair
    rw [Finset.union_comm]
    ring

private theorem coefficient_add_pointwise
    {N : Nat} (f g : (Fin N -> Bool) -> Rat)
    (support : Finset (Fin N)) :
    coefficient (fun input => f input + g input) support =
      coefficient f support + coefficient g support := by
  unfold coefficient
  rw [← add_div, ← Finset.sum_add_distrib]
  apply congrArg (fun value : Rat => value / (2 : Rat) ^ N)
  apply Finset.sum_congr rfl
  intro input _hinput
  ring

private theorem coefficient_sub_pointwise
    {N : Nat} (f g : (Fin N -> Bool) -> Rat)
    (support : Finset (Fin N)) :
    coefficient (fun input => f input - g input) support =
      coefficient f support - coefficient g support := by
  unfold coefficient
  rw [← sub_div, ← Finset.sum_sub_distrib]
  apply congrArg (fun value : Rat => value / (2 : Rat) ^ N)
  apply Finset.sum_congr rfl
  intro input _hinput
  ring

/-- Polarization of the symmetric concrete-mask pair form. -/
theorem structuredDualPairCorrelationAtMask_eq_quarter_polarization
    (n m cutoff : Nat) (hn : 0 < n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredDualPairCorrelationAtMask n m cutoff hn
        leftFunction rightFunction mask =
      (1 / 4 : Rat) *
        (structuredDualPairCorrelationAtMask n m cutoff hn
            (fun input => leftFunction input + rightFunction input)
            (fun input => leftFunction input + rightFunction input) mask -
          structuredDualPairCorrelationAtMask n m cutoff hn
            (fun input => leftFunction input - rightFunction input)
            (fun input => leftFunction input - rightFunction input) mask) := by
  classical
  have hsym := structuredDualPairCorrelationAtMask_symm
    n m cutoff hn rightFunction leftFunction mask
  unfold structuredDualPairCorrelationAtMask
    structuredDualAliasPairCoefficient at hsym ⊢
  have hdiff :
      (∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
          maskAllZeroIndicator (pair.1 ∪ pair.2) mask *
            (coefficient
                (fun input => leftFunction input + rightFunction input)
                pair.1 *
              coefficient
                (fun input => leftFunction input + rightFunction input)
                pair.2)) -
        (∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
          maskAllZeroIndicator (pair.1 ∪ pair.2) mask *
            (coefficient
                (fun input => leftFunction input - rightFunction input)
                pair.1 *
              coefficient
                (fun input => leftFunction input - rightFunction input)
                pair.2)) =
      2 * (∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
          maskAllZeroIndicator (pair.1 ∪ pair.2) mask *
            (coefficient leftFunction pair.1 *
              coefficient rightFunction pair.2)) +
        2 * (∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
          maskAllZeroIndicator (pair.1 ∪ pair.2) mask *
            (coefficient rightFunction pair.1 *
              coefficient leftFunction pair.2)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro pair _hpair
    rw [coefficient_add_pointwise, coefficient_add_pointwise,
      coefficient_sub_pointwise, coefficient_sub_pointwise]
    ring
  rw [hsym] at hdiff
  linarith

/-- Polarization plus the existing structured fixed-mask self bound gives a
universal constant cross bound for two pointwise-disjoint, unit-bounded
functions.  The constant is size-free but carries no `p`-decay. -/
theorem abs_structuredDualPairCorrelationAtMask_le_two_of_disjoint
    (n m : Nat) (hn : 0 < n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (hleft : ∀ input, |leftFunction input| <= 1)
    (hright : ∀ input, |rightFunction input| <= 1)
    (hdisjoint : ∀ input,
      leftFunction input * rightFunction input = 0)
    (mask : Fin (2 ^ n) -> Bool) :
    |structuredDualPairCorrelationAtMask n m (2 * m) hn
        leftFunction rightFunction mask| <= 2 := by
  let plus : (Fin (2 ^ n) -> Bool) -> Rat :=
    fun input => leftFunction input + rightFunction input
  let minus : (Fin (2 ^ n) -> Bool) -> Rat :=
    fun input => leftFunction input - rightFunction input
  have hplus : ∀ input, |plus input| <= 1 := by
    intro input
    rcases mul_eq_zero.mp (hdisjoint input) with hzero | hzero
    · simp [plus, hzero, hright input]
    · simp [plus, hzero, hleft input]
  have hminus : ∀ input, |minus input| <= 1 := by
    intro input
    rcases mul_eq_zero.mp (hdisjoint input) with hzero | hzero
    · simpa [minus, hzero] using hright input
    · simpa [minus, hzero] using hleft input
  have hself (f : (Fin (2 ^ n) -> Bool) -> Rat)
      (hf : ∀ input, |f input| <= 1) :
      |structuredDualPairCorrelationAtMask n m (2 * m) hn f f mask| <= 4 := by
    rw [structuredDualPairCorrelationAtMask_self_eq_fixedMaskAllFalseFar]
    exact abs_structured_allFalse_highTailFarPairCorrelation_le_four
      n m hn (fixedMaskAveragedFunction f mask)
        (abs_fixedMaskAveragedFunction_le_one f hf mask)
  have hplusSelf := hself plus hplus
  have hminusSelf := hself minus hminus
  rw [structuredDualPairCorrelationAtMask_eq_quarter_polarization
    n m (2 * m) hn leftFunction rightFunction mask]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Rat) <= 1 / 4)]
  nlinarith [abs_sub
    (structuredDualPairCorrelationAtMask n m (2 * m) hn plus plus mask)
    (structuredDualPairCorrelationAtMask n m (2 * m) hn minus minus mask)]

/-- Opposite query literals are pointwise disjoint and inherit the preceding
fixed-mask constant bound from unit-bounded residual factors. -/
theorem abs_structuredDualPairCorrelationAtMask_oppositeLiteral_le_two
    (n m : Nat) (hn : 0 < n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (ha : ∀ input, |a input| <= 1)
    (hb : ∀ input, |b input| <= 1)
    (mask : Fin (2 ^ n) -> Bool) :
    |structuredDualPairCorrelationAtMask n m (2 * m) hn
        (falseLiteralPart coordinate a)
        (trueLiteralPart coordinate b) mask| <= 2 := by
  apply abs_structuredDualPairCorrelationAtMask_le_two_of_disjoint
    n m hn (falseLiteralPart coordinate a)
      (trueLiteralPart coordinate b)
  · intro input
    cases hvalue : input coordinate <;>
      simp [falseLiteralPart, falseLiteral, hvalue, ha input]
  · intro input
    cases hvalue : input coordinate <;>
      simp [trueLiteralPart, trueLiteral, hvalue, hb input]
  · intro input
    cases hvalue : input coordinate <;>
      simp [falseLiteralPart, trueLiteralPart, falseLiteral, trueLiteral,
        hvalue]

/-- **Size-free outer-dual bound.**  The exact semantic aggregation and the
fixed-mask polarization cap give a universal bound `2` for the complete
actual-rank off-coordinate bulk.  This removes all dual-word multiplicity,
but the absence of any factor `2^{-tailBits * (4m+1)}` is precisely why this
unconditional estimate is too weak for the selector-pair target. -/
theorem abs_structuredActualRankOppositeLiteralBulkDualSum_le_two
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (hdependsA : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hdependsB : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (ha : ∀ input, |a input| <= 1)
    (hb : ∀ input, |b input| <= 1) :
    |structuredActualRankOppositeLiteralBulkDualSum
        n m tailBits hn htail coordinate a b| <= 2 := by
  rw [structuredActualRankOppositeLiteralBulkDualSum_eq_finiteAverage_crossCorrelation
    n m tailBits hn htail coordinate a b hdependsA hdependsB]
  apply abs_finiteAverage_le_of_pointwise_abs_le _ 2
  intro seed
  let mask :=
    (structuredDyadicPrimitive n m tailBits hn htail).generate seed
  have hlive : |maskLiveIndicator coordinate mask| <= 1 := by
    cases hvalue : mask coordinate <;>
      simp [maskLiveIndicator, hvalue]
  have hcross :
      |structuredDualPairCorrelationAtMask n m (2 * m) hn
        (falseLiteralPart coordinate a)
        (trueLiteralPart coordinate b) mask| <= 2 :=
    abs_structuredDualPairCorrelationAtMask_oppositeLiteral_le_two
      n m hn coordinate a b ha hb mask
  change |maskLiveIndicator coordinate mask *
      structuredDualPairCorrelationAtMask n m (2 * m) hn
        (falseLiteralPart coordinate a)
        (trueLiteralPart coordinate b) mask| <= 2
  rw [abs_mul]
  calc
    |maskLiveIndicator coordinate mask| *
          |structuredDualPairCorrelationAtMask n m (2 * m) hn
            (falseLiteralPart coordinate a)
            (trueLiteralPart coordinate b) mask| <=
        1 * 2 := mul_le_mul hlive hcross (abs_nonneg _) (by norm_num)
    _ = 2 := by norm_num

end FiniteBooleanOppositeLiteralDualAggregation

end

end OneTapeMagnification
end Frontier
end Pnp4
