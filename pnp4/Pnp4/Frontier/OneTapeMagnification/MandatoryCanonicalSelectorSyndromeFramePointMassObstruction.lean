import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorSyndromeFrameBridge
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredPointMassCliqueObstruction
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A point-mass obstruction to relative syndrome frames

The relative frame condition `p * E <= D` is a useful sufficient condition
for the selector-pair bound, but it is substantially stronger than the
absolute syndrome-energy condition used by the residual-`L2` route (which is
itself a sufficient target distinct from the sharper one-sided far bound).
The all-false point mass exposes the difference.  The zero coefficient seed
of both structured primitives produces the all-false word.  Consequently one
joint base/mask seed can carry
macroscopic high-transform value, with probability `2^(-2Kn)`, whereas the
entire Fourier diagonal of the point mass is only `2^(-N)`.

This file proves the generic zero-seed lower bound and a point-mass no-go
under two explicit rational inequalities.  It does not claim that the point
mass violates either the absolute syndrome-energy target or the distinct
one-sided far target.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanFullIndependenceRestriction
open FiniteRankWeightAbelVariation
open DPTWFiniteFieldKWiseSeed
open DPTWStructuredFieldCoordinatePrimitive
open FiniteStructuredDualNonzeroSeedCorrelation
open FiniteStructuredDualSyndromeFiberBlocks
open FiniteStructuredDualBlockProductSyndromeTransform
open MandatoryCanonicalSelectorSyndromeFrameBridge
open DPTWStructuredPointMassCliqueObstruction

namespace MandatoryCanonicalSelectorSyndromeFramePointMassObstruction

/-- The constant all-false word on the relevant truth-table cube. -/
def allFalseWord (coordinateCount : Nat) : Fin coordinateCount -> Bool :=
  fun _ => false

/-- The zero coefficient seed evaluates to the all-false word for every
member of the structured dyadic family, including the unbiased member. -/
theorem structuredDyadicPrimitive_generate_zeroBitSeed
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n) :
    (structuredDyadicPrimitive n m tailBits hn htail).generate
        (zeroBitSeed (structuredIndependence m * n)) =
      allFalseWord (2 ^ n) := by
  funext index
  rw [structuredDyadicPrimitive_generate]
  unfold structuredPolynomialSubsetSource polynomialSubsetSource allFalseWord
  rw [structuredPolynomialBitSeedEquiv_zeroBitSeed
    (structuredIndependence m) n (Nat.ne_of_gt hn)]
  rw [fieldSubsetCoin_eq_false_iff, mem_zeroPrefixFalseSet]
  intro selected
  simp

private theorem nonzeroBitSeedAverage_nonneg
    (seedBits : Nat) (hseedBits : 0 < seedBits)
    (value : FiniteBitTape seedBits -> Rat)
    (hvalue : forall seed, 0 <= value seed) :
    0 <= nonzeroBitSeedAverage seedBits value := by
  have hden : (0 : Rat) < (2 : Rat) ^ seedBits - 1 := by
    have hpow : (1 : Rat) < (2 : Rat) ^ seedBits :=
      one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hseedBits)
    linarith
  unfold nonzeroBitSeedAverage
  exact div_nonneg
    (Finset.sum_nonneg fun seed _ => hvalue seed) (le_of_lt hden)

/-- A single zero base seed inside the zero mask seed gives a universal lower
bound on the mask-averaged syndrome energy.  This is the exact rare-spike
term which a relative-to-diagonal frame estimate cannot ignore. -/
theorem dyadicRankWeight_sq_mul_zeroSeedTransform_sq_le_syndromeEnergyAverage
    (n m tailBits cutoff : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    (dyadicRankWeight (structuredIndependence m * n)) ^ 2 *
        (structuredMaskedHighDegreeTransform n m cutoff hn f
          (allFalseWord (2 ^ n))
          (zeroBitSeed (structuredIndependence m * n))) ^ 2 <=
      structuredSyndromeEnergyAverage
        n m tailBits cutoff hn htail f := by
  classical
  let seedBits := structuredIndependence m * n
  have hseedBits : 0 < seedBits := by
    unfold seedBits structuredIndependence
    positivity
  let maskSource :=
    (structuredDyadicPrimitive n m tailBits hn htail).generate
  let zeroSeed : FiniteBitTape seedBits := zeroBitSeed seedBits
  let fixedEnergy := fun maskSeed : FiniteBitTape seedBits =>
    Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
      (structuredSyndromeFiberCoefficientSum n m cutoff hn
        f (maskSource maskSeed) syndrome) ^ 2)
  let highTransform := fun baseSeed : FiniteBitTape seedBits =>
    structuredMaskedHighDegreeTransform n m cutoff hn f
      (allFalseWord (2 ^ n)) baseSeed
  have hfixedNonneg (maskSeed : FiniteBitTape seedBits) :
      0 <= fixedEnergy maskSeed := by
    unfold fixedEnergy
    exact Finset.sum_nonneg fun syndrome _ => sq_nonneg _
  have hbaseNonneg (baseSeed : FiniteBitTape seedBits) :
      0 <= (highTransform baseSeed) ^ 2 := sq_nonneg _
  have hmaskZero : maskSource zeroSeed = allFalseWord (2 ^ n) := by
    simpa [maskSource, zeroSeed, seedBits] using
      structuredDyadicPrimitive_generate_zeroBitSeed
        n m tailBits hn htail
  have hfixedZero :
      fixedEnergy zeroSeed =
        finiteAverage (fun baseSeed : FiniteBitTape seedBits =>
          (highTransform baseSeed) ^ 2) := by
    unfold fixedEnergy highTransform
    rw [hmaskZero]
    simpa only [pow_two] using
      syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
        n m cutoff hn f f (allFalseWord (2 ^ n))
  have hbaseMixture := finiteAverage_eq_nonzeroBitSeed_mixture
    seedBits hseedBits (fun baseSeed : FiniteBitTape seedBits =>
      (highTransform baseSeed) ^ 2)
  have hbaseLower :
      dyadicRankWeight seedBits * (highTransform zeroSeed) ^ 2 <=
        fixedEnergy zeroSeed := by
    rw [hfixedZero, hbaseMixture]
    have hnonzero : 0 <= nonzeroBitSeedAverage seedBits
        (fun baseSeed : FiniteBitTape seedBits =>
          (highTransform baseSeed) ^ 2) :=
      nonzeroBitSeedAverage_nonneg seedBits hseedBits _ hbaseNonneg
    have honeMinus : 0 <= 1 - dyadicRankWeight seedBits := by
      unfold dyadicRankWeight
      rw [sub_nonneg, div_le_iff₀ (by positivity : (0 : Rat) < 2 ^ seedBits)]
      simpa only [one_mul] using
        (one_le_pow₀ (by norm_num : (1 : Rat) <= 2) :
          (1 : Rat) <= 2 ^ seedBits)
    have hterm : 0 <= (1 - dyadicRankWeight seedBits) *
        nonzeroBitSeedAverage seedBits
          (fun baseSeed : FiniteBitTape seedBits =>
            (highTransform baseSeed) ^ 2) :=
      mul_nonneg honeMinus hnonzero
    dsimp only [zeroSeed]
    linarith
  have hmaskMixture := finiteAverage_eq_nonzeroBitSeed_mixture
    seedBits hseedBits fixedEnergy
  have hmaskLower :
      dyadicRankWeight seedBits * fixedEnergy zeroSeed <=
        finiteAverage fixedEnergy := by
    rw [hmaskMixture]
    have hnonzero : 0 <= nonzeroBitSeedAverage seedBits fixedEnergy :=
      nonzeroBitSeedAverage_nonneg seedBits hseedBits _ hfixedNonneg
    have honeMinus : 0 <= 1 - dyadicRankWeight seedBits := by
      unfold dyadicRankWeight
      rw [sub_nonneg, div_le_iff₀ (by positivity : (0 : Rat) < 2 ^ seedBits)]
      simpa only [one_mul] using
        (one_le_pow₀ (by norm_num : (1 : Rat) <= 2) :
          (1 : Rat) <= 2 ^ seedBits)
    nlinarith
  have hweight : 0 <= dyadicRankWeight seedBits := by
    unfold dyadicRankWeight
    positivity
  calc
    (dyadicRankWeight seedBits) ^ 2 *
          (highTransform zeroSeed) ^ 2 =
        dyadicRankWeight seedBits *
          (dyadicRankWeight seedBits * (highTransform zeroSeed) ^ 2) := by
            ring
    _ <= dyadicRankWeight seedBits * fixedEnergy zeroSeed :=
      mul_le_mul_of_nonneg_left hbaseLower hweight
    _ <= finiteAverage fixedEnergy := hmaskLower
    _ = structuredSyndromeEnergyAverage
        n m tailBits cutoff hn htail f := by
      rfl

/-- The mask-averaged high diagonal never exceeds the full Fourier energy. -/
theorem structuredMaskedHighDiagonalAverage_le_fullFourierEnergy
    (n m tailBits cutoff : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredMaskedHighDiagonalAverage
        n m tailBits cutoff hn htail f <=
      Finset.univ.sum (fun support : Finset (Fin (2 ^ n)) =>
        (coefficient f support) ^ 2) := by
  classical
  rw [structuredMaskedHighDiagonalAverage_eq_sum]
  calc
    Finset.sum (highDegreeSupports (2 ^ n) cutoff) (fun support =>
        (coefficient f support) ^ 2 *
          finiteAverage
            (fun maskSeed : Fin (structuredIndependence m * n) -> Bool =>
              maskAllZeroIndicator support
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  maskSeed))) <=
      Finset.sum (highDegreeSupports (2 ^ n) cutoff) (fun support =>
        (coefficient f support) ^ 2) := by
          apply Finset.sum_le_sum
          intro support _hsupport
          have havg : finiteAverage
              (fun maskSeed : Fin (structuredIndependence m * n) -> Bool =>
                maskAllZeroIndicator support
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    maskSeed)) <= 1 := by
            calc
              finiteAverage
                  (fun maskSeed : Fin (structuredIndependence m * n) -> Bool =>
                    maskAllZeroIndicator support
                      ((structuredDyadicPrimitive n m tailBits hn htail).generate
                        maskSeed)) <=
                  finiteAverage
                    (fun _ : Fin (structuredIndependence m * n) -> Bool =>
                      (1 : Rat)) := by
                        apply finiteAverage_mono
                        intro maskSeed
                        unfold maskAllZeroIndicator
                        split <;> norm_num
              _ = 1 := by simp [finiteAverage]
          have hsq : 0 <= (coefficient f support) ^ 2 := sq_nonneg _
          nlinarith
    _ <= Finset.univ.sum (fun support : Finset (Fin (2 ^ n)) =>
        (coefficient f support) ^ 2) :=
      Finset.sum_le_univ_sum_of_nonneg fun support => sq_nonneg _

/-- Every point-mass diagonal is at most its uniform mass `2^-N`. -/
theorem structuredMaskedHighDiagonalAverage_zeroPointIndicator_le
    (n m tailBits cutoff : Nat) (hn : 0 < n)
    (htail : tailBits <= n) :
    structuredMaskedHighDiagonalAverage n m tailBits cutoff hn htail
        (zeroPointIndicator (2 ^ n)) <=
      1 / (2 : Rat) ^ (2 ^ n) := by
  calc
    structuredMaskedHighDiagonalAverage n m tailBits cutoff hn htail
        (zeroPointIndicator (2 ^ n)) <=
      Finset.univ.sum (fun support : Finset (Fin (2 ^ n)) =>
        (coefficient (zeroPointIndicator (2 ^ n)) support) ^ 2) :=
      structuredMaskedHighDiagonalAverage_le_fullFourierEnergy
        n m tailBits cutoff hn htail _
    _ = 1 / (2 : Rat) ^ (2 ^ n) := by
      rw [parseval]
      unfold finiteAverage zeroPointIndicator
      have hsum :
          (Finset.univ.sum (fun input : Fin (2 ^ n) -> Bool =>
            (if input = (fun _ => false) then (1 : Rat) else 0) ^ 2)) = 1 := by
        classical
        calc
          Finset.univ.sum (fun input : Fin (2 ^ n) -> Bool =>
              (if input = (fun _ => false) then (1 : Rat) else 0) ^ 2) =
            (if (fun _ : Fin (2 ^ n) => false) = (fun _ => false)
              then (1 : Rat) else 0) ^ 2 := by
                apply Fintype.sum_eq_single (fun _ => false)
                intro input hinput
                simp [hinput]
          _ = 1 := by simp
      rw [hsum]
      simp

/-- A concrete family of high-degree supports is obtained by fixing any
`cutoff + 1` coordinates and freely choosing all remaining coordinates. -/
theorem pow_sub_cutoff_succ_le_card_highDegreeSupports
    (coordinateCount cutoff : Nat)
    (hcutoff : cutoff + 1 <= coordinateCount) :
    2 ^ (coordinateCount - (cutoff + 1)) <=
      (highDegreeSupports coordinateCount cutoff).card := by
  classical
  choose anchor hanchorSubset hanchorCard using
    (Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin coordinateCount)))
      (n := cutoff + 1) (by simpa using hcutoff))
  have hintervalSubset :
      Finset.Icc anchor (Finset.univ : Finset (Fin coordinateCount)) ⊆
        highDegreeSupports coordinateCount cutoff := by
    intro support hsupport
    rw [Finset.mem_Icc] at hsupport
    rw [mem_highDegreeSupports]
    have hcard := Finset.card_le_card hsupport.1
    omega
  have hcard := Finset.card_le_card hintervalSubset
  rw [Finset.card_Icc_finset hanchorSubset, hanchorCard] at hcard
  simpa using hcard

/-- At the joint zero mask/base seed, every surviving Walsh character of the
all-false point mass equals one.  Thus the high transform is exactly the
fraction of Fourier supports above the cutoff. -/
theorem structuredMaskedHighDegreeTransform_zeroPointIndicator_zeroSeeds_eq
    (n m cutoff : Nat) (hn : 0 < n) :
    structuredMaskedHighDegreeTransform n m cutoff hn
        (zeroPointIndicator (2 ^ n)) (allFalseWord (2 ^ n))
        (zeroBitSeed (structuredIndependence m * n)) =
      ((highDegreeSupports (2 ^ n) cutoff).card : Rat) /
        (2 : Rat) ^ (2 ^ n) := by
  classical
  have hbase :
      (structuredUnbiasedPrimitive n m hn).generate
          (zeroBitSeed (structuredIndependence m * n)) =
        allFalseWord (2 ^ n) := by
    simpa [structuredUnbiasedPrimitive] using
      structuredDyadicPrimitive_generate_zeroBitSeed n m 1 hn (by omega)
  unfold structuredMaskedHighDegreeTransform
  rw [hbase]
  simp only [structuredMaskedCoefficient, coefficient_zeroPointIndicator]
  have hterm (support : Finset (Fin (2 ^ n))) :
      maskAllZeroIndicator support (allFalseWord (2 ^ n)) *
            (1 / (2 : Rat) ^ (2 ^ n)) *
          character support (allFalseWord (2 ^ n)) =
        1 / (2 : Rat) ^ (2 ^ n) := by
    simp [maskAllZeroIndicator, allFalseWord, character]
  simp_rw [hterm]
  simp [div_eq_mul_inv]

/-- Generic rare-spike criterion refuting a relative syndrome frame. -/
theorem not_structuredSyndromeFrameBound_of_zeroSeedSpike
    (n m tailBits cutoff : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (diagonalCap spikeFloor : Rat)
    (hdiag : structuredMaskedHighDiagonalAverage
      n m tailBits cutoff hn htail f <= diagonalCap)
    (hspike : spikeFloor <=
      (structuredMaskedHighDegreeTransform n m cutoff hn f
        (allFalseWord (2 ^ n))
        (zeroBitSeed (structuredIndependence m * n))) ^ 2)
    (hseparate : diagonalCap <
      (1 / (2 : Rat) ^ tailBits) *
        (dyadicRankWeight (structuredIndependence m * n)) ^ 2 *
          spikeFloor) :
    ¬ (StructuredSyndromeFrameBound
      n m tailBits cutoff hn htail f) := by
  intro hframe
  have henergy :=
    dyadicRankWeight_sq_mul_zeroSeedTransform_sq_le_syndromeEnergyAverage
      n m tailBits cutoff hn htail f
  have hweight : 0 <=
      (1 / (2 : Rat) ^ tailBits) *
        (dyadicRankWeight (structuredIndependence m * n)) ^ 2 := by
    positivity
  have hlower :
      (1 / (2 : Rat) ^ tailBits) *
          (dyadicRankWeight (structuredIndependence m * n)) ^ 2 *
            spikeFloor <=
        (1 / (2 : Rat) ^ tailBits) *
          structuredSyndromeEnergyAverage
            n m tailBits cutoff hn htail f := by
    calc
      (1 / (2 : Rat) ^ tailBits) *
          (dyadicRankWeight (structuredIndependence m * n)) ^ 2 *
            spikeFloor <=
        (1 / (2 : Rat) ^ tailBits) *
          ((dyadicRankWeight (structuredIndependence m * n)) ^ 2 *
            (structuredMaskedHighDegreeTransform n m cutoff hn f
              (allFalseWord (2 ^ n))
              (zeroBitSeed (structuredIndependence m * n))) ^ 2) := by
                nlinarith
      _ <= (1 / (2 : Rat) ^ tailBits) *
          structuredSyndromeEnergyAverage
            n m tailBits cutoff hn htail f :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
  have hframe' :
      (1 / (2 : Rat) ^ tailBits) *
          structuredSyndromeEnergyAverage
            n m tailBits cutoff hn htail f <=
        structuredMaskedHighDiagonalAverage
          n m tailBits cutoff hn htail f := by
    simpa [StructuredSyndromeFrameBound] using hframe
  linarith

/-- Point-mass specialization.  It remains only to verify a lower bound on
the zero-seed high transform and the displayed elementary scale separation.
Both hypotheses are concrete rational inequalities, with no machine or
Fourier premise hidden in them. -/
theorem not_structuredSyndromeFrameBound_zeroPointIndicator
    (n m tailBits cutoff : Nat) (hn : 0 < n)
    (htail : tailBits <= n) (spikeFloor : Rat)
    (hspike : spikeFloor <=
      (structuredMaskedHighDegreeTransform n m cutoff hn
        (zeroPointIndicator (2 ^ n)) (allFalseWord (2 ^ n))
        (zeroBitSeed (structuredIndependence m * n))) ^ 2)
    (hseparate :
      1 / (2 : Rat) ^ (2 ^ n) <
        (1 / (2 : Rat) ^ tailBits) *
          (dyadicRankWeight (structuredIndependence m * n)) ^ 2 *
            spikeFloor) :
    ¬ (StructuredSyndromeFrameBound n m tailBits cutoff hn htail
      (zeroPointIndicator (2 ^ n))) := by
  exact not_structuredSyndromeFrameBound_of_zeroSeedSpike
    n m tailBits cutoff hn htail (zeroPointIndicator (2 ^ n))
      (1 / (2 : Rat) ^ (2 ^ n)) spikeFloor
      (structuredMaskedHighDiagonalAverage_zeroPointIndicator_le
        n m tailBits cutoff hn htail)
      hspike hseparate

/-- Fully explicit point-mass obstruction: the only remaining premise is an
elementary rational comparison between the truth-table mass and the rare
joint zero-seed atom.  No transform lower bound remains as a hypothesis. -/
theorem not_structuredSyndromeFrameBound_zeroPointIndicator_of_card_scale
    (n m tailBits cutoff : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hseparate :
      1 / (2 : Rat) ^ (2 ^ n) <
        (1 / (2 : Rat) ^ tailBits) *
          (dyadicRankWeight (structuredIndependence m * n)) ^ 2 *
            (((highDegreeSupports (2 ^ n) cutoff).card : Rat) /
              (2 : Rat) ^ (2 ^ n)) ^ 2) :
    ¬ (StructuredSyndromeFrameBound n m tailBits cutoff hn htail
      (zeroPointIndicator (2 ^ n))) := by
  apply not_structuredSyndromeFrameBound_zeroPointIndicator
    n m tailBits cutoff hn htail
      ((((highDegreeSupports (2 ^ n) cutoff).card : Rat) /
        (2 : Rat) ^ (2 ^ n)) ^ 2)
  · rw [structuredMaskedHighDegreeTransform_zeroPointIndicator_zeroSeeds_eq]
  · exact hseparate

/-- More usable form of the point-mass obstruction.  Fixing `cutoff + 1`
coordinates already supplies `2^(N-cutoff-1)` positive high coefficients,
so the scale comparison below is sufficient without evaluating the full
powerset cardinality. -/
theorem not_structuredSyndromeFrameBound_zeroPointIndicator_of_free_family_scale
    (n m tailBits cutoff : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hcutoff : cutoff + 1 <= 2 ^ n)
    (hseparate :
      1 / (2 : Rat) ^ (2 ^ n) <
        (1 / (2 : Rat) ^ tailBits) *
          (dyadicRankWeight (structuredIndependence m * n)) ^ 2 *
            (((2 ^ ((2 ^ n) - (cutoff + 1)) : Nat) : Rat) /
              (2 : Rat) ^ (2 ^ n)) ^ 2) :
    ¬ (StructuredSyndromeFrameBound n m tailBits cutoff hn htail
      (zeroPointIndicator (2 ^ n))) := by
  have hcardNat := pow_sub_cutoff_succ_le_card_highDegreeSupports
    (2 ^ n) cutoff hcutoff
  have hcardRat :
      (((2 ^ ((2 ^ n) - (cutoff + 1)) : Nat) : Rat)) <=
        ((highDegreeSupports (2 ^ n) cutoff).card : Rat) := by
    exact_mod_cast hcardNat
  have hdenNonneg : 0 <= (2 : Rat) ^ (2 ^ n) := by positivity
  have hratio :
      (((2 ^ ((2 ^ n) - (cutoff + 1)) : Nat) : Rat) /
          (2 : Rat) ^ (2 ^ n)) <=
        (((highDegreeSupports (2 ^ n) cutoff).card : Rat) /
          (2 : Rat) ^ (2 ^ n)) :=
    div_le_div_of_nonneg_right hcardRat hdenNonneg
  have hratioLeft : 0 <=
      (((2 ^ ((2 ^ n) - (cutoff + 1)) : Nat) : Rat) /
        (2 : Rat) ^ (2 ^ n)) := by positivity
  have hratioRight : 0 <=
      (((highDegreeSupports (2 ^ n) cutoff).card : Rat) /
        (2 : Rat) ^ (2 ^ n)) := by positivity
  have hsquare :
      (((2 ^ ((2 ^ n) - (cutoff + 1)) : Nat) : Rat) /
          (2 : Rat) ^ (2 ^ n)) ^ 2 <=
        (((highDegreeSupports (2 ^ n) cutoff).card : Rat) /
          (2 : Rat) ^ (2 ^ n)) ^ 2 := by
    nlinarith
  apply not_structuredSyndromeFrameBound_zeroPointIndicator_of_card_scale
    n m tailBits cutoff hn htail
  have hscale : 0 <=
      (1 / (2 : Rat) ^ tailBits) *
        (dyadicRankWeight (structuredIndependence m * n)) ^ 2 := by
    positivity
  exact lt_of_lt_of_le hseparate
    (mul_le_mul_of_nonneg_left hsquare hscale)

/-- The obstruction is already present at the selector-relevant cutoff
`2*m` with `m = 1`: on `N = 2^7 = 128` truth-table coordinates, the rare
joint zero seed outweighs the full point-mass Fourier diagonal. -/
theorem not_structuredSyndromeFrameBound_zeroPointIndicator_n7_m1 :
    ¬ (StructuredSyndromeFrameBound 7 1 1 2 (by omega) (by omega)
      (zeroPointIndicator (2 ^ 7))) := by
  apply
    not_structuredSyndromeFrameBound_zeroPointIndicator_of_free_family_scale
      7 1 1 2 (by omega) (by omega) (by norm_num)
  norm_num [dyadicRankWeight, structuredIndependence]

end MandatoryCanonicalSelectorSyndromeFramePointMassObstruction
end
end OneTapeMagnification
end Frontier
end Pnp4
