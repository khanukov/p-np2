import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualNonzeroSeedCorrelation
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Syndrome-fiber blocks for the fixed-mask structured dual correlation

The structured dual condition on a symmetric difference says exactly that
the two supports have the same vector of low power sums.  Thus, after one
mask is fixed, the structured dual-pair operator is a direct sum over power-
syndrome fibers.  On each fiber its matrix is the all-ones rank-one form
with the diagonal removed, namely `J - I` after inserting the masked Fourier
weights.

This file records that exact algebraic identity.  It is lower-layer
infrastructure and does not by itself discharge either pnp4 mainline source
obligation.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFullIndependenceRestriction
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredMaskRank
open DPTWStructuredUnbiasedDualCode
open FiniteRankWeightAbelVariation
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualRankThresholdBridge
open FiniteStructuredDualNonzeroSeedCorrelation

namespace FiniteStructuredDualSyndromeFiberBlocks

/-- The complete parity-check syndrome used by the degree-`< 4m+1`
structured source. -/
abbrev StructuredDualPowerSyndrome (n m : Nat) :=
  Fin (structuredIndependence m) -> GaloisField 2 n

/-- The vector of all structured power sums below the independence bound. -/
def structuredDualPowerSyndrome
    (n m : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    StructuredDualPowerSyndrome n m :=
  fun exponent =>
    structuredSupportPowerSum n hn support exponent.val

private theorem galoisFieldTwo_add_self
    (n : Nat) (value : GaloisField 2 n) : value + value = 0 := by
  have htwo : (2 : GaloisField 2 n) = 0 :=
    CharP.cast_eq_zero (GaloisField 2 n) 2
  calc
    value + value = (2 : GaloisField 2 n) * value := by ring
    _ = 0 := by rw [htwo, zero_mul]

/-- In characteristic two, taking symmetric difference adds the complete
power-sum syndromes. -/
theorem structuredDualPowerSyndrome_symmDiff
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n))) :
    structuredDualPowerSyndrome n m hn (left ∆ right) =
      structuredDualPowerSyndrome n m hn left +
        structuredDualPowerSyndrome n m hn right := by
  classical
  funext exponent
  unfold structuredDualPowerSyndrome structuredSupportPowerSum
  let value := fun index : Fin (2 ^ n) =>
    structuredTruthTableNode n (Nat.ne_of_gt hn) index ^ exponent.val
  change
    (∑ index ∈ left ∆ right, value index) =
      (∑ index ∈ left, value index) +
        ∑ index ∈ right, value index
  have hsum (support : Finset (Fin (2 ^ n))) :
      (∑ index ∈ support, value index) =
        ∑ index : Fin (2 ^ n),
          if index ∈ support then value index else 0 := by
    simp
  rw [hsum (left ∆ right), hsum left, hsum right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index hindex
  by_cases hleft : index ∈ left <;>
    by_cases hright : index ∈ right <;>
      simp [Finset.mem_symmDiff, hleft, hright, galoisFieldTwo_add_self]

/-- Two supports differ by a structured dual word exactly when they lie in
the same power-syndrome fiber. -/
theorem isStructuredDualSupport_symmDiff_iff_syndrome_eq
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n))) :
    IsStructuredDualSupport n (structuredIndependence m) hn
        (left ∆ right) ↔
      structuredDualPowerSyndrome n m hn left =
        structuredDualPowerSyndrome n m hn right := by
  rw [isStructuredDualSupport_iff_powerSums_eq_zero]
  constructor
  · intro hzero
    funext exponent
    change
      structuredSupportPowerSum n hn left exponent.val =
        structuredSupportPowerSum n hn right exponent.val
    have hsymm := congrFun
      (structuredDualPowerSyndrome_symmDiff n m hn left right) exponent
    change
      structuredSupportPowerSum n hn (left ∆ right) exponent.val =
        structuredSupportPowerSum n hn left exponent.val +
          structuredSupportPowerSum n hn right exponent.val at hsymm
    have hsum :
        structuredSupportPowerSum n hn left exponent.val +
            structuredSupportPowerSum n hn right exponent.val = 0 := by
      rw [← hsymm]
      exact hzero exponent
    have hself :
        structuredSupportPowerSum n hn right exponent.val +
            structuredSupportPowerSum n hn right exponent.val = 0 :=
      galoisFieldTwo_add_self n _
    linear_combination hsum - hself
  · intro heq exponent
    have hsymm := congrFun
      (structuredDualPowerSyndrome_symmDiff n m hn left right) exponent
    change
      structuredSupportPowerSum n hn (left ∆ right) exponent.val =
        structuredSupportPowerSum n hn left exponent.val +
          structuredSupportPowerSum n hn right exponent.val at hsymm
    have heqPoint := congrFun heq exponent
    change
      structuredSupportPowerSum n hn left exponent.val =
        structuredSupportPowerSum n hn right exponent.val at heqPoint
    rw [hsymm, heqPoint]
    exact galoisFieldTwo_add_self n _

/-- A Fourier coefficient after the fixed mask has projected away every
support touching a live coordinate. -/
def structuredMaskedCoefficient
    {n : Nat} (f : (Fin n -> Bool) -> Rat) (mask : Fin n -> Bool)
    (support : Finset (Fin n)) : Rat :=
  maskAllZeroIndicator support mask * coefficient f support

/-- The total masked high-degree Fourier coefficient in one syndrome fiber. -/
def structuredSyndromeFiberCoefficientSum
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool)
    (syndrome : StructuredDualPowerSyndrome n m) : Rat :=
  ∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
    if structuredDualPowerSyndrome n m hn support = syndrome then
      structuredMaskedCoefficient f mask support
    else 0

/-- The masked high-degree diagonal cross term.  Idempotence of the Boolean
mask indicator means this is also the usual once-masked diagonal energy. -/
def structuredMaskedHighDiagonalCrossTerm
    (n cutoff : Nat)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  ∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
    structuredMaskedCoefficient leftFunction mask support *
      structuredMaskedCoefficient rightFunction mask support

/-- The product definition of the diagonal is exactly the usual single-mask
diagonal, because the mask indicator is idempotent. -/
theorem structuredMaskedHighDiagonalCrossTerm_eq
    (n cutoff : Nat)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredMaskedHighDiagonalCrossTerm n cutoff
        leftFunction rightFunction mask =
      ∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
        maskAllZeroIndicator support mask *
          coefficient leftFunction support * coefficient rightFunction support := by
  classical
  unfold structuredMaskedHighDiagonalCrossTerm structuredMaskedCoefficient
  apply Finset.sum_congr rfl
  intro support hsupport
  calc
    (maskAllZeroIndicator support mask * coefficient leftFunction support) *
        (maskAllZeroIndicator support mask * coefficient rightFunction support) =
      (maskAllZeroIndicator support mask *
          maskAllZeroIndicator support mask) *
        (coefficient leftFunction support * coefficient rightFunction support) := by
          ring
    _ = maskAllZeroIndicator support mask *
        coefficient leftFunction support * coefficient rightFunction support := by
          rw [maskAllZeroIndicator_mul_self]
          ring

/-- Generic finite `J - I` identity: the off-diagonal equal-label form is
the sum of rank-one fiber blocks minus its diagonal. -/
private theorem offDiagonalFiberSum_eq_blocks_sub_diagonal
    {Index Label : Type*} [Fintype Label]
    [DecidableEq Index] [DecidableEq Label]
    (indices : Finset Index) (label : Index -> Label)
    (leftTerm rightTerm : Index -> Rat) :
    (∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
        if leftIndex ≠ rightIndex ∧ label leftIndex = label rightIndex then
          leftTerm leftIndex * rightTerm rightIndex
        else 0) =
      (∑ fiber : Label,
        (∑ leftIndex ∈ indices,
            if label leftIndex = fiber then leftTerm leftIndex else 0) *
          (∑ rightIndex ∈ indices,
            if label rightIndex = fiber then rightTerm rightIndex else 0)) -
        ∑ index ∈ indices, leftTerm index * rightTerm index := by
  classical
  have hblocks :
      (∑ fiber : Label,
          (∑ leftIndex ∈ indices,
              if label leftIndex = fiber then leftTerm leftIndex else 0) *
            (∑ rightIndex ∈ indices,
              if label rightIndex = fiber then rightTerm rightIndex else 0)) =
        ∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if label leftIndex = label rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0 := by
    calc
      (∑ fiber : Label,
          (∑ leftIndex ∈ indices,
              if label leftIndex = fiber then leftTerm leftIndex else 0) *
            (∑ rightIndex ∈ indices,
              if label rightIndex = fiber then rightTerm rightIndex else 0)) =
        ∑ fiber : Label, ∑ leftIndex ∈ indices,
          ∑ rightIndex ∈ indices,
            (if label leftIndex = fiber then leftTerm leftIndex else 0) *
              (if label rightIndex = fiber then rightTerm rightIndex else 0) := by
                apply Fintype.sum_congr
                intro fiber
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro leftIndex hleftIndex
                rw [Finset.mul_sum]
      _ = ∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          ∑ fiber : Label,
            (if label leftIndex = fiber then leftTerm leftIndex else 0) *
              (if label rightIndex = fiber then rightTerm rightIndex else 0) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro leftIndex hleftIndex
                rw [Finset.sum_comm]
      _ = ∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if label leftIndex = label rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0 := by
                apply Finset.sum_congr rfl
                intro leftIndex hleftIndex
                apply Finset.sum_congr rfl
                intro rightIndex hrightIndex
                by_cases hlabel : label leftIndex = label rightIndex
                · rw [hlabel]
                  simp
                · rw [if_neg hlabel]
                  apply Fintype.sum_eq_zero
                  intro fiber
                  by_cases hleftFiber : label leftIndex = fiber
                  · have hrightFiber : label rightIndex ≠ fiber := by
                      intro hrightFiber
                      exact hlabel (hleftFiber.trans hrightFiber.symm)
                    simp [hleftFiber, hrightFiber]
                  · simp [hleftFiber]
  have hdiagonal :
      (∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if leftIndex = rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0) =
        ∑ index ∈ indices, leftTerm index * rightTerm index := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Finset.sum_eq_single index]
    · simp
    · intro other hother hne
      simp [hne.symm]
    · intro hnotMem
      exact (hnotMem hindex).elim
  have hsplit :
      (∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if label leftIndex = label rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0) =
        (∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if leftIndex ≠ rightIndex ∧ label leftIndex = label rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0) +
        ∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if leftIndex = rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0 := by
    calc
      (∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if label leftIndex = label rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0) =
        ∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          ((if leftIndex ≠ rightIndex ∧
              label leftIndex = label rightIndex then
              leftTerm leftIndex * rightTerm rightIndex
            else 0) +
            if leftIndex = rightIndex then
              leftTerm leftIndex * rightTerm rightIndex
            else 0) := by
              apply Finset.sum_congr rfl
              intro leftIndex hleftIndex
              apply Finset.sum_congr rfl
              intro rightIndex hrightIndex
              by_cases heq : leftIndex = rightIndex
              · subst rightIndex
                simp
              · by_cases hlabel : label leftIndex = label rightIndex <;>
                  simp [heq, hlabel]
      _ =
        (∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if leftIndex ≠ rightIndex ∧ label leftIndex = label rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0) +
        ∑ leftIndex ∈ indices, ∑ rightIndex ∈ indices,
          if leftIndex = rightIndex then
            leftTerm leftIndex * rightTerm rightIndex
          else 0 := by
            simp_rw [Finset.sum_add_distrib]
  rw [← hblocks, hdiagonal] at hsplit
  linarith only [hsplit]

/-- Exact fixed-mask syndrome-fiber block identity.  Each summand is the
rank-one all-ones block on one parity-check fiber, and subtracting the
displayed diagonal turns those blocks into `J - I`. -/
theorem structuredDualPairCorrelationAtMask_eq_syndromeFiberBlocks_sub_diagonal
    (n m cutoff : Nat) (hn : 0 < n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredDualPairCorrelationAtMask n m cutoff hn
        leftFunction rightFunction mask =
      (∑ syndrome : StructuredDualPowerSyndrome n m,
        structuredSyndromeFiberCoefficientSum n m cutoff hn
            leftFunction mask syndrome *
          structuredSyndromeFiberCoefficientSum n m cutoff hn
            rightFunction mask syndrome) -
        structuredMaskedHighDiagonalCrossTerm n cutoff
          leftFunction rightFunction mask := by
  classical
  unfold structuredDualPairCorrelationAtMask structuredDualAliasPairs
    structuredDualAliasPairCoefficient
  rw [Finset.sum_filter]
  refine (Finset.sum_product
    (highDegreeSupports (2 ^ n) cutoff)
    (highDegreeSupports (2 ^ n) cutoff)
    (fun pair =>
      if pair.1 ≠ pair.2 ∧
          IsStructuredDualSupport n (structuredIndependence m) hn
            (pair.1 ∆ pair.2) then
        maskAllZeroIndicator (pair.1 ∪ pair.2) mask *
          (coefficient leftFunction pair.1 * coefficient rightFunction pair.2)
      else 0)).trans ?_
  calc
    (∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
        ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
          if left ≠ right ∧
              IsStructuredDualSupport n (structuredIndependence m) hn
                (left ∆ right) then
            maskAllZeroIndicator (left ∪ right) mask *
              (coefficient leftFunction left * coefficient rightFunction right)
          else 0) =
      ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
        ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
          if left ≠ right ∧
              structuredDualPowerSyndrome n m hn left =
                structuredDualPowerSyndrome n m hn right then
            structuredMaskedCoefficient leftFunction mask left *
              structuredMaskedCoefficient rightFunction mask right
          else 0 := by
            apply Finset.sum_congr rfl
            intro left hleft
            apply Finset.sum_congr rfl
            intro right hright
            rw [isStructuredDualSupport_symmDiff_iff_syndrome_eq]
            by_cases hpairs : left ≠ right ∧
                structuredDualPowerSyndrome n m hn left =
                  structuredDualPowerSyndrome n m hn right
            · rw [if_pos hpairs, if_pos hpairs]
              unfold structuredMaskedCoefficient
              rw [← maskAllZeroIndicator_mul_eq_union]
              ring
            · rw [if_neg hpairs, if_neg hpairs]
    _ =
      (∑ syndrome : StructuredDualPowerSyndrome n m,
        structuredSyndromeFiberCoefficientSum n m cutoff hn
            leftFunction mask syndrome *
          structuredSyndromeFiberCoefficientSum n m cutoff hn
            rightFunction mask syndrome) -
        structuredMaskedHighDiagonalCrossTerm n cutoff
          leftFunction rightFunction mask := by
            simpa [structuredSyndromeFiberCoefficientSum,
              structuredMaskedHighDiagonalCrossTerm] using
              (offDiagonalFiberSum_eq_blocks_sub_diagonal
                (indices := highDegreeSupports (2 ^ n) cutoff)
                (label := structuredDualPowerSyndrome n m hn)
                (leftTerm := structuredMaskedCoefficient leftFunction mask)
                (rightTerm := structuredMaskedCoefficient rightFunction mask))

/-- Averaging the exact `J - I` blocks over the actual structured mask is
exactly the rank-weighted distinct-alias cross form.  This is the direct
interface between the syndrome projection problem and the selector-pair
quantity; no rank relaxation or absolute value is taken. -/
theorem structuredDualRankDistinctCrossForm_eq_finiteAverage_syndromeFiberBlocks
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          let mask :=
            (structuredDyadicPrimitive n m tailBits hn htail).generate seed
          (∑ syndrome : StructuredDualPowerSyndrome n m,
              structuredSyndromeFiberCoefficientSum n m cutoff hn
                  leftFunction mask syndrome *
                structuredSyndromeFiberCoefficientSum n m cutoff hn
                  rightFunction mask syndrome) -
            structuredMaskedHighDiagonalCrossTerm n cutoff
              leftFunction rightFunction mask) := by
  classical
  calc
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction =
      ∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
        dyadicRankWeight
            (structuredDualAliasPairRank n m tailBits hn htail pair) *
          structuredDualAliasPairCoefficient
            leftFunction rightFunction pair :=
      structuredDualRankDistinctCrossForm_eq_pairWeightedSum
        n m tailBits cutoff hn htail leftFunction rightFunction
    _ = finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          structuredDualPairCorrelationAtMask n m cutoff hn
            leftFunction rightFunction
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed)) := by
      unfold structuredDualPairCorrelationAtMask
      rw [finiteAverage_finset_sum]
      apply Finset.sum_congr rfl
      intro pair hpair
      let coefficientProduct :=
        structuredDualAliasPairCoefficient leftFunction rightFunction pair
      have hsurvival :=
        structuredDyadicPrimitive_maskSurvival_eq_invPowRank
          n m tailBits hn htail (pair.1 ∪ pair.2)
      change dyadicRankWeight
          (structuredDualAliasPairRank n m tailBits hn htail pair) *
            coefficientProduct =
        finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            maskAllZeroIndicator (pair.1 ∪ pair.2)
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  seed) *
              coefficientProduct)
      rw [dyadicRankWeight, structuredDualAliasPairRank, ← hsurvival]
      rw [show finiteAverage
            (fun seed : Fin (structuredIndependence m * n) -> Bool =>
              maskAllZeroIndicator (pair.1 ∪ pair.2)
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  seed)) * coefficientProduct =
          coefficientProduct * finiteAverage
            (fun seed : Fin (structuredIndependence m * n) -> Bool =>
              maskAllZeroIndicator (pair.1 ∪ pair.2)
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  seed)) by ring]
      rw [← finiteAverage_const_mul]
      apply finiteAverage_congr
      intro seed
      ring
    _ = _ := by
      apply finiteAverage_congr
      intro seed
      exact structuredDualPairCorrelationAtMask_eq_syndromeFiberBlocks_sub_diagonal
        n m cutoff hn leftFunction rightFunction
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)

end FiniteStructuredDualSyndromeFiberBlocks
end
end OneTapeMagnification
end Frontier
end Pnp4
