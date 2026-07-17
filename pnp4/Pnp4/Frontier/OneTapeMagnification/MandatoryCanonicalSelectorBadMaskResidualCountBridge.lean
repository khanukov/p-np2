import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorDefectiveSyndromeFrame
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Residual-count bridge for defective selector syndrome frames

This file records two exact pieces of bookkeeping for the good/bad syndrome
frame route.  First, the structured conditional mass of the actual affine-
prefixed mandatory selector is the average normalized compatible-model count.
Second, the universal fixed-mask energy envelope can retain the unused high
Fourier diagonal instead of discarding it.

Neither result bounds the bad-mask count average or proves the selector
correlation lemma.  In particular, no residual-`L2` or reverse-LCP estimate is
derived here.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanMaskedProductFactorization
open FiniteBooleanPerVertexRestrictionBound
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredFullFieldCorrelation
open FiniteStructuredDualNonzeroSeedCorrelation
open FiniteStructuredDualSyndromeFiberBlocks
open FiniteStructuredDualBlockProductSyndromeTransform
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorResidualCount
open MandatoryCanonicalSelectorDefectiveSyndromeFrame

namespace MandatoryCanonicalSelectorBadMaskResidualCountBridge

/-! ## Exact residual-count interpretation -/

/-- For the actual affine-prefixed mandatory selector, the conditional mass at
one fixed mask is exactly the structured-base average of the normalized
compatible accepted-model count. -/
theorem fixedMaskStructuredBaseMass_prefixedMandatoryCanonicalSelector_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskStructuredBaseMass n m hn
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
          mask =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (prefixedMandatoryCanonicalSelector machine n T b rounds).normalizedResidualAcceptedModelCount
              ((structuredUnbiasedPrimitive n m hn).generate seed) mask) := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  unfold fixedMaskStructuredBaseMass
  apply finiteAverage_congr
  intro seed
  change FiniteBooleanResidualMass.maskedAverage B.ratAcceptanceIndicator
      ((structuredUnbiasedPrimitive n m hn).generate seed) mask = _
  rw [FiniteUnambiguousFBDD.maskedAverage_ratAcceptanceIndicator_eq_residualAcceptedMass,
    B.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount]

/-! ## Diagonal-retaining fixed-mask envelope -/

/-- The fixed-mask syndrome energy can retain the high Fourier diagonal in
the universal mass envelope.  The low structured second moment is its exact
uniform Fourier energy; together with the complementary high diagonal it is
at most the uniform mass of a `[0,1]`-valued function. -/
theorem fixedMask_syndromeFiberEnergy_le_two_mul_structuredMass_add_two_mul_uniformMass_sub_diagonal
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hunit : forall input, 0 <= f input /\ f input <= 1)
    (mask : Fin (2 ^ n) -> Bool) :
    (Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
      (structuredSyndromeFiberCoefficientSum n m (2 * m) hn
        f mask syndrome) ^ 2)) <=
      2 * finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          fixedMaskAveragedFunction f mask
            ((structuredUnbiasedPrimitive n m hn).generate seed)) +
      2 * (finiteAverage f -
        structuredMaskedHighDiagonalCrossTerm n (2 * m) f f mask) := by
  let g := fixedMaskAveragedFunction f mask
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let low := ratLowDegreeFourierPart g (2 * m)
  have hgunit : forall input, 0 <= g input /\ g input <= 1 := by
    intro input
    dsimp only [g]
    constructor
    · unfold fixedMaskAveragedFunction
      exact finiteAverage_nonneg fun uniform =>
        (hunit (maskedInput input mask uniform)).1
    · calc
        fixedMaskAveragedFunction f mask input <=
            finiteAverage (fun _uniform : Fin (2 ^ n) -> Bool => (1 : Rat)) := by
          unfold fixedMaskAveragedFunction
          apply finiteAverage_mono
          intro uniform
          exact (hunit (maskedInput input mask uniform)).2
        _ = 1 := by simp [finiteAverage]
  have hlowExact :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            (low (D seed)) ^ 2) =
        Finset.sum (lowDegreeSupports (2 ^ n) (2 * m))
          (fun support => (coefficient g support) ^ 2) := by
    simpa only using
      (lowDegreeFourierPart_secondMoment_eq_energy
        (q := structuredIndependence m) g D
        (by unfold structuredIndependence; omega)
        (structuredUnbiasedPrimitive_patternUnbiased n m hn))
  have hdiagExact :
      structuredMaskedHighDiagonalCrossTerm n (2 * m) f f mask =
        Finset.sum (highDegreeSupports (2 ^ n) (2 * m))
          (fun support => (coefficient g support) ^ 2) := by
    rw [structuredMaskedHighDiagonalCrossTerm_eq]
    apply Finset.sum_congr rfl
    intro support _hsupport
    rw [coefficient_fixedMaskAveragedFunction]
    unfold maskAllZeroIndicator
    split <;> ring
  have hlowAddDiagonal :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            (low (D seed)) ^ 2) +
          structuredMaskedHighDiagonalCrossTerm n (2 * m) f f mask <=
        finiteAverage f := by
    rw [hlowExact, hdiagExact]
    calc
      Finset.sum (lowDegreeSupports (2 ^ n) (2 * m))
            (fun support => (coefficient g support) ^ 2) +
          Finset.sum (highDegreeSupports (2 ^ n) (2 * m))
            (fun support => (coefficient g support) ^ 2) =
        Finset.univ.sum (fun support : Finset (Fin (2 ^ n)) =>
          (coefficient g support) ^ 2) := by
            unfold lowDegreeSupports highDegreeSupports
            have hsplit := Finset.sum_filter_not_add_sum_filter
              (Finset.univ : Finset (Finset (Fin (2 ^ n))))
              (fun support => 2 * m < support.card)
              (fun support => (coefficient g support) ^ 2)
            simp only [Finset.sum_filter, Nat.not_lt] at hsplit ⊢
            linarith
      _ = finiteAverage (fun input => (g input) ^ 2) := parseval g
      _ <= finiteAverage g := by
        apply finiteAverage_mono
        intro input
        nlinarith [hgunit input]
      _ = finiteAverage f := by
        exact finiteAverage_fixedMaskAveragedFunction_eq f mask
  have hlow :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            (low (D seed)) ^ 2) <=
        finiteAverage f -
          structuredMaskedHighDiagonalCrossTerm n (2 * m) f f mask := by
    linarith
  have hbase :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            (g (D seed)) ^ 2) <=
        finiteAverage (fun seed => g (D seed)) := by
    apply finiteAverage_mono
    intro seed
    nlinarith [hgunit (D seed)]
  rw [show (Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
      (structuredSyndromeFiberCoefficientSum n m (2 * m) hn
        f mask syndrome) ^ 2)) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (structuredMaskedHighDegreeTransform n m (2 * m) hn
            f mask seed) ^ 2) by
    simpa only [pow_two] using
      (syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
        n m (2 * m) hn f f mask)]
  simp_rw [structuredMaskedHighDegreeTransform_eq_fixedMaskHighTail]
  change finiteAverage (fun seed =>
      (FiniteUnambiguousFBDD.ratHighDegreeFourierTail
        g (2 * m) (D seed)) ^ 2) <= _
  calc
    finiteAverage (fun seed =>
        (FiniteUnambiguousFBDD.ratHighDegreeFourierTail
          g (2 * m) (D seed)) ^ 2) <=
      finiteAverage (fun seed =>
        2 * (g (D seed)) ^ 2 + 2 * (low (D seed)) ^ 2) := by
          apply finiteAverage_mono
          intro seed
          rw [ratHighDegreeFourierTail_eq_sub_lowDegreePart]
          dsimp only [low]
          nlinarith [sq_nonneg (g (D seed) +
            ratLowDegreeFourierPart g (2 * m) (D seed))]
    _ = 2 * finiteAverage (fun seed => (g (D seed)) ^ 2) +
        2 * finiteAverage (fun seed => (low (D seed)) ^ 2) := by
      rw [finiteAverage_add_local, finiteAverage_const_mul,
        finiteAverage_const_mul]
    _ <= 2 * finiteAverage (fun seed => g (D seed)) +
        2 * (finiteAverage f -
          structuredMaskedHighDiagonalCrossTerm n (2 * m) f f mask) := by
      linarith
    _ = _ := by rfl

end MandatoryCanonicalSelectorBadMaskResidualCountBridge
end
end OneTapeMagnification
end Frontier
end Pnp4
