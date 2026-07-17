import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorDefectiveSyndromeFrame
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorSyndromeFramePointMassObstruction
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Complement obstruction to the mass-weighted bad-mask certificate

The high Fourier layer is invariant, up to a global sign, under replacing a
Boolean indicator `f` by `1 - f`.  The mass envelope used by
`StructuredMassWeightedBadMaskSyndromeFrameCertificate` is not invariant
under this operation.  This file makes that mismatch concrete for the OR
indicator, the complement of the all-false point mass.

At `n = 7`, `m = 1`, and `tailBits = 1`, every generated mask with at least
forty frozen coordinates violates the fixed-mask relative frame inequality.
The exact one-coordinate law forces such seeds to have density at least
`25 / 89`.  Since OR has uniform mass strictly above one half, this density
alone exceeds the complete mass-weighted certificate budget.

This is an obstruction to that sufficient certificate, not to the absolute
syndrome-energy target.  OR is a width-two ordered read-once branching
program, but no semantic identification with the mandatory canonical
one-tape selector is asserted in this module.
-/

noncomputable section

set_option maxRecDepth 10000

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanPerVertexRestrictionBound
open FiniteRankWeightAbelVariation
open FiniteBooleanMaskedProductFactorization
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredFullFieldCorrelation
open FiniteStructuredDualNonzeroSeedCorrelation
open FiniteStructuredDualSyndromeFiberBlocks
open FiniteStructuredDualBlockProductSyndromeTransform
open DPTWStructuredPointMassCliqueObstruction
open MandatoryCanonicalSelectorSyndromeFramePointMassObstruction
open MandatoryCanonicalSelectorSyndromeFrameBridge
open MandatoryCanonicalSelectorDefectiveSyndromeFrame
open FiniteBooleanDualAliasConvolutionTransfer

namespace MandatoryCanonicalSelectorMassWeightedCertificateComplementObstruction

/-- The Boolean OR indicator: zero only at the all-false word. -/
def nonzeroPointIndicator (coordinateCount : Nat)
    (input : Fin coordinateCount -> Bool) : Rat :=
  1 - zeroPointIndicator coordinateCount input

private theorem coefficient_sub_pointwise
    {N : Nat} (f g : (Fin N -> Bool) -> Rat)
    (support : Finset (Fin N)) :
    coefficient (fun input => f input - g input) support =
      coefficient f support - coefficient g support := by
  unfold coefficient
  rw [<- sub_div, <- Finset.sum_sub_distrib]
  apply congrArg (fun value : Rat => value / (2 : Rat) ^ N)
  apply Finset.sum_congr rfl
  intro input _hinput
  ring

/-- On every nonempty Fourier support, OR has the negative of the all-false
point-mass coefficient. -/
theorem coefficient_nonzeroPointIndicator_of_nonempty
    (coordinateCount : Nat) (support : Finset (Fin coordinateCount))
    (hsupport : support.Nonempty) :
    coefficient (nonzeroPointIndicator coordinateCount) support =
      -(1 / (2 : Rat) ^ coordinateCount) := by
  rw [show nonzeroPointIndicator coordinateCount =
      (fun input => (fun _ : Fin coordinateCount -> Bool => (1 : Rat)) input -
        zeroPointIndicator coordinateCount input) by
    funext input
    rfl]
  rw [coefficient_sub_pointwise]
  rw [coefficient_one_eq_zero_of_nonempty hsupport]
  rw [coefficient_zeroPointIndicator]
  ring

/-- Complementing the point mass negates every structured high transform. -/
theorem structuredMaskedHighDegreeTransform_nonzeroPointIndicator_eq_neg
    (n m cutoff : Nat) (hn : 0 < n)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    structuredMaskedHighDegreeTransform n m cutoff hn
        (nonzeroPointIndicator (2 ^ n)) mask seed =
      -structuredMaskedHighDegreeTransform n m cutoff hn
        (zeroPointIndicator (2 ^ n)) mask seed := by
  classical
  unfold structuredMaskedHighDegreeTransform
  rw [<- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro support hsupport
  have hcard := mem_highDegreeSupports.mp hsupport
  have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
  unfold structuredMaskedCoefficient
  rw [coefficient_nonzeroPointIndicator_of_nonempty _ support hnonempty]
  rw [coefficient_zeroPointIndicator]
  ring

/-- The fixed-mask syndrome energy is unchanged by this complementation. -/
theorem fixedMaskSyndromeEnergy_nonzeroPointIndicator_eq
    (n m : Nat) (hn : 0 < n)
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskSyndromeEnergy n m hn
        (nonzeroPointIndicator (2 ^ n)) mask =
      fixedMaskSyndromeEnergy n m hn
        (zeroPointIndicator (2 ^ n)) mask := by
  unfold fixedMaskSyndromeEnergy
  apply Finset.sum_congr rfl
  intro syndrome _hsyndrome
  have hfiber :
      structuredSyndromeFiberCoefficientSum n m (2 * m) hn
          (nonzeroPointIndicator (2 ^ n)) mask syndrome =
        -structuredSyndromeFiberCoefficientSum n m (2 * m) hn
          (zeroPointIndicator (2 ^ n)) mask syndrome := by
    unfold structuredSyndromeFiberCoefficientSum
    rw [<- Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro support hsupport
    have hcard := mem_highDegreeSupports.mp hsupport
    have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
    split_ifs with hsame
    · unfold structuredMaskedCoefficient
      rw [coefficient_nonzeroPointIndicator_of_nonempty _ support hnonempty]
      rw [coefficient_zeroPointIndicator]
      ring
    · ring
  rw [hfiber]
  ring

/-- The fixed-mask high diagonal is also unchanged by complementation. -/
theorem fixedMaskHighDiagonal_nonzeroPointIndicator_eq
    (n m : Nat) (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskHighDiagonal n m (nonzeroPointIndicator (2 ^ n)) mask =
      fixedMaskHighDiagonal n m (zeroPointIndicator (2 ^ n)) mask := by
  classical
  unfold fixedMaskHighDiagonal structuredMaskedHighDiagonalCrossTerm
  apply Finset.sum_congr rfl
  intro support hsupport
  have hcard := mem_highDegreeSupports.mp hsupport
  have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
  unfold structuredMaskedCoefficient
  rw [coefficient_nonzeroPointIndicator_of_nonempty _ support hnonempty]
  rw [coefficient_zeroPointIndicator]
  ring

/-- Coordinates frozen by a concrete mask. -/
def frozenCoordinates {coordinateCount : Nat}
    (mask : Fin coordinateCount -> Bool) : Finset (Fin coordinateCount) :=
  Finset.univ.filter fun coordinate => mask coordinate = false

/-- High supports which survive a concrete mask. -/
def survivingHighSupports (coordinateCount cutoff : Nat)
    (mask : Fin coordinateCount -> Bool) :
    Finset (Finset (Fin coordinateCount)) :=
  (highDegreeSupports coordinateCount cutoff).filter
    fun support => support ⊆ frozenCoordinates mask

theorem maskAllZeroIndicator_eq_one_of_subset_frozen
    {coordinateCount : Nat} (mask : Fin coordinateCount -> Bool)
    (support : Finset (Fin coordinateCount))
    (hsubset : support ⊆ frozenCoordinates mask) :
    maskAllZeroIndicator support mask = 1 := by
  rw [maskAllZeroIndicator]
  split
  · rfl
  · rename_i hnot
    exfalso
    apply hnot
    intro coordinate hcoordinate
    have := hsubset hcoordinate
    simpa [frozenCoordinates] using this

theorem maskAllZeroIndicator_eq_zero_of_not_subset_frozen
    {coordinateCount : Nat} (mask : Fin coordinateCount -> Bool)
    (support : Finset (Fin coordinateCount))
    (hsubset : ¬ support ⊆ frozenCoordinates mask) :
    maskAllZeroIndicator support mask = 0 := by
  rw [maskAllZeroIndicator]
  split
  · rename_i hall
    exfalso
    apply hsubset
    intro coordinate hcoordinate
    simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hall coordinate hcoordinate
  · rfl

/-- At the zero base seed, the point-mass high transform is the normalized
number of high supports surviving the mask. -/
theorem structuredMaskedHighDegreeTransform_zeroPointIndicator_zeroBase_eq
    (n m cutoff : Nat) (hn : 0 < n)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredMaskedHighDegreeTransform n m cutoff hn
        (zeroPointIndicator (2 ^ n)) mask
        (zeroBitSeed (structuredIndependence m * n)) =
      ((survivingHighSupports (2 ^ n) cutoff mask).card : Rat) /
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
  calc
    (∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
        maskAllZeroIndicator support mask *
            (1 / (2 : Rat) ^ (2 ^ n)) *
          character support (allFalseWord (2 ^ n))) =
      ∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
        if support ⊆ frozenCoordinates mask then
          (1 / (2 : Rat) ^ (2 ^ n)) else 0 := by
            apply Finset.sum_congr rfl
            intro support _hsupport
            by_cases hsubset : support ⊆ frozenCoordinates mask
            · rw [if_pos hsubset,
                maskAllZeroIndicator_eq_one_of_subset_frozen _ _ hsubset]
              simp [allFalseWord, character]
            · rw [if_neg hsubset,
                maskAllZeroIndicator_eq_zero_of_not_subset_frozen _ _ hsubset]
              ring
    _ = ∑ support ∈ survivingHighSupports (2 ^ n) cutoff mask,
          (1 / (2 : Rat) ^ (2 ^ n)) := by
            symm
            simp only [survivingHighSupports]
            rw [Finset.sum_filter]
    _ = ((survivingHighSupports (2 ^ n) cutoff mask).card : Rat) *
          (1 / (2 : Rat) ^ (2 ^ n)) := by simp
    _ = _ := by ring

/-- The point-mass fixed-mask diagonal is the same surviving-support count
with the squared Fourier normalization. -/
theorem fixedMaskHighDiagonal_zeroPointIndicator_eq
    (n m : Nat) (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskHighDiagonal n m (zeroPointIndicator (2 ^ n)) mask =
      ((survivingHighSupports (2 ^ n) (2 * m) mask).card : Rat) /
        ((2 : Rat) ^ (2 ^ n)) ^ 2 := by
  classical
  unfold fixedMaskHighDiagonal structuredMaskedHighDiagonalCrossTerm
    structuredMaskedCoefficient
  simp_rw [coefficient_zeroPointIndicator]
  calc
    (∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
        (maskAllZeroIndicator support mask *
            (1 / (2 : Rat) ^ (2 ^ n))) *
          (maskAllZeroIndicator support mask *
            (1 / (2 : Rat) ^ (2 ^ n)))) =
      ∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
        if support ⊆ frozenCoordinates mask then
          1 / ((2 : Rat) ^ (2 ^ n)) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro support _hsupport
            by_cases hsubset : support ⊆ frozenCoordinates mask
            · rw [if_pos hsubset,
                maskAllZeroIndicator_eq_one_of_subset_frozen _ _ hsubset]
              ring
            · rw [if_neg hsubset,
                maskAllZeroIndicator_eq_zero_of_not_subset_frozen _ _ hsubset]
              ring
    _ = ∑ support ∈ survivingHighSupports (2 ^ n) (2 * m) mask,
          (1 / ((2 : Rat) ^ (2 ^ n)) ^ 2) := by
            symm
            simp only [survivingHighSupports]
            rw [Finset.sum_filter]
    _ = ((survivingHighSupports (2 ^ n) (2 * m) mask).card : Rat) *
          (1 / ((2 : Rat) ^ (2 ^ n)) ^ 2) := by simp
    _ = _ := by ring

/-- One specified bit seed contributes its dyadic atom to every nonnegative
finite average. -/
theorem dyadicRankWeight_mul_zeroBitSeed_le_finiteAverage
    (seedBits : Nat) (value : FiniteBitTape seedBits -> Rat)
    (hvalue : forall seed, 0 <= value seed) :
    dyadicRankWeight seedBits * value (zeroBitSeed seedBits) <=
      finiteAverage value := by
  have hsum : value (zeroBitSeed seedBits) <=
      ∑ seed : FiniteBitTape seedBits, value seed := by
    exact Finset.single_le_sum
      (fun seed _hseed => hvalue seed) (Finset.mem_univ _)
  unfold dyadicRankWeight finiteAverage
  have hcard :
      ((Fintype.card (FiniteBitTape seedBits) : Nat) : Rat) =
        (2 : Rat) ^ seedBits := by simp [FiniteBitTape]
  rw [hcard]
  have hden : 0 <= (2 : Rat) ^ seedBits := by positivity
  calc
    1 / (2 : Rat) ^ seedBits * value (zeroBitSeed seedBits) =
        value (zeroBitSeed seedBits) / (2 : Rat) ^ seedBits := by ring
    _ <= (∑ seed : FiniteBitTape seedBits, value seed) /
        (2 : Rat) ^ seedBits :=
      div_le_div_of_nonneg_right hsum hden

/-- The zero base seed alone gives a fixed-mask syndrome-energy lower bound. -/
theorem dyadicRankWeight_mul_zeroBaseTransform_sq_le_fixedMaskSyndromeEnergy
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    dyadicRankWeight (structuredIndependence m * n) *
        (structuredMaskedHighDegreeTransform n m (2 * m) hn f mask
          (zeroBitSeed (structuredIndependence m * n))) ^ 2 <=
      fixedMaskSyndromeEnergy n m hn f mask := by
  rw [show fixedMaskSyndromeEnergy n m hn f mask =
      finiteAverage
        (fun seed : FiniteBitTape (structuredIndependence m * n) =>
          (structuredMaskedHighDegreeTransform n m (2 * m) hn
            f mask seed) ^ 2) by
    unfold fixedMaskSyndromeEnergy
    simpa only [pow_two] using
      (syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
        n m (2 * m) hn f f mask)]
  exact dyadicRankWeight_mul_zeroBitSeed_le_finiteAverage
    (structuredIndependence m * n)
      (fun seed =>
        (structuredMaskedHighDegreeTransform n m (2 * m) hn
          f mask seed) ^ 2)
      (fun seed => sq_nonneg _)

/-- Three frozen coordinates can be anchored, while every other frozen
coordinate may be freely inserted, giving this many surviving supports above
degree two. -/
theorem pow_frozen_sub_three_le_card_survivingHighSupports
    {coordinateCount : Nat} (mask : Fin coordinateCount -> Bool)
    (hthree : 3 <= (frozenCoordinates mask).card) :
    2 ^ ((frozenCoordinates mask).card - 3) <=
      (survivingHighSupports coordinateCount 2 mask).card := by
  classical
  obtain ⟨anchor, hanchorSubset, hanchorCard⟩ :=
    Finset.exists_subset_card_eq hthree
  have hintervalSubset :
      Finset.Icc anchor (frozenCoordinates mask) ⊆
        survivingHighSupports coordinateCount 2 mask := by
    intro support hsupport
    rw [Finset.mem_Icc] at hsupport
    simp only [survivingHighSupports, Finset.mem_filter]
    constructor
    · rw [mem_highDegreeSupports]
      have hcard := Finset.card_le_card hsupport.1
      rw [hanchorCard] at hcard
      omega
    · exact hsupport.2
  have hcard := Finset.card_le_card hintervalSubset
  rw [Finset.card_Icc_finset hanchorSubset, hanchorCard] at hcard
  simpa using hcard

/-- Forty frozen coordinates force at least `2^37` surviving supports above
degree two. -/
theorem pow_thirtySeven_le_card_survivingHighSupports_of_forty_le_frozen
    {coordinateCount : Nat} (mask : Fin coordinateCount -> Bool)
    (hforty : 40 <= (frozenCoordinates mask).card) :
    2 ^ 37 <= (survivingHighSupports coordinateCount 2 mask).card := by
  have hfamily := pow_frozen_sub_three_le_card_survivingHighSupports
    mask (by omega)
  exact (Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat))
    (by omega)).trans hfamily

/-- At the concrete obstruction parameters, every mask with forty frozen
coordinates violates the point-mass fixed-mask relative frame inequality. -/
theorem fixedMaskHighDiagonal_zeroPointIndicator_lt_half_mul_energy_of_forty
    (mask : Fin (2 ^ 7) -> Bool)
    (hforty : 40 <= (frozenCoordinates mask).card) :
    fixedMaskHighDiagonal 7 1 (zeroPointIndicator (2 ^ 7)) mask <
      (1 / 2 : Rat) * fixedMaskSyndromeEnergy 7 1 (by omega)
        (zeroPointIndicator (2 ^ 7)) mask := by
  let supportCount := (survivingHighSupports (2 ^ 7) 2 mask).card
  have hcountNat : 2 ^ 37 <= supportCount := by
    exact pow_thirtySeven_le_card_survivingHighSupports_of_forty_le_frozen
      mask hforty
  have hcount : ((2 ^ 37 : Nat) : Rat) <= (supportCount : Rat) := by
    exact_mod_cast hcountNat
  have henergy :=
    dyadicRankWeight_mul_zeroBaseTransform_sq_le_fixedMaskSyndromeEnergy
      7 1 (by omega) (zeroPointIndicator (2 ^ 7)) mask
  rw [structuredMaskedHighDegreeTransform_zeroPointIndicator_zeroBase_eq]
    at henergy
  change dyadicRankWeight (structuredIndependence 1 * 7) *
      (((supportCount : Rat) / (2 : Rat) ^ (2 ^ 7)) ^ 2) <=
        fixedMaskSyndromeEnergy 7 1 (by omega)
          (zeroPointIndicator (2 ^ 7)) mask at henergy
  rw [fixedMaskHighDiagonal_zeroPointIndicator_eq]
  change (supportCount : Rat) / ((2 : Rat) ^ (2 ^ 7)) ^ 2 < _
  have hcountPositive : 0 < (supportCount : Rat) := by
    have : (0 : Rat) < ((2 ^ 37 : Nat) : Rat) := by positivity
    linarith
  have hdenPositive : 0 < ((2 : Rat) ^ (2 ^ 7)) ^ 2 := by positivity
  have hweight :
      dyadicRankWeight (structuredIndependence 1 * 7) =
        1 / (2 : Rat) ^ 35 := by
    norm_num [dyadicRankWeight, structuredIndependence]
  rw [hweight] at henergy
  have hscale : (2 : Rat) ^ 36 < (supportCount : Rat) := by
    have hstrictNat : (2 ^ 36 : Nat) < 2 ^ 37 := by
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hsupportStrictNat : (2 ^ 36 : Nat) < supportCount :=
      hstrictNat.trans_le hcountNat
    exact_mod_cast hsupportStrictNat
  let diagonalValue : Rat :=
    (supportCount : Rat) / ((2 : Rat) ^ (2 ^ 7)) ^ 2
  let scaleFactor : Rat :=
    (1 / 2 : Rat) * (1 / (2 : Rat) ^ 35) * (supportCount : Rat)
  have hdiagonalPositive : 0 < diagonalValue := by
    exact div_pos hcountPositive hdenPositive
  have hfactor : 1 < scaleFactor := by
    have hpow : (2 : Rat) ^ 36 = 2 * (2 : Rat) ^ 35 := by
      rw [show 36 = 35 + 1 by omega, pow_succ]
      ring
    have hden36 : 0 < (2 : Rat) ^ 36 := by positivity
    change 1 < (1 / 2 : Rat) * (1 / (2 : Rat) ^ 35) *
      (supportCount : Rat)
    rw [show (1 / 2 : Rat) * (1 / (2 : Rat) ^ 35) *
        (supportCount : Rat) =
        (supportCount : Rat) / (2 : Rat) ^ 36 by
      rw [hpow]
      ring]
    apply (lt_div_iff₀ hden36).2
    simpa only [one_mul] using hscale
  have hfactorIdentity :
      diagonalValue * scaleFactor =
        (1 / 2 : Rat) *
          ((1 / (2 : Rat) ^ 35) *
            (((supportCount : Rat) / (2 : Rat) ^ (2 ^ 7)) ^ 2)) := by
    dsimp only [diagonalValue, scaleFactor]
    ring
  have hlowerStrict :
      diagonalValue <
        (1 / 2 : Rat) *
          ((1 / (2 : Rat) ^ 35) *
            (((supportCount : Rat) / (2 : Rat) ^ (2 ^ 7)) ^ 2)) := by
    rw [<- hfactorIdentity]
    exact (lt_mul_iff_one_lt_right hdiagonalPositive).2 hfactor
  change diagonalValue <
    (1 / 2 : Rat) * fixedMaskSyndromeEnergy 7 1 (by omega)
      (zeroPointIndicator (2 ^ 7)) mask
  exact hlowerStrict.trans_le
    (mul_le_mul_of_nonneg_left henergy (by norm_num))

/-- The same masks violate the OR fixed-mask relative frame inequality,
because complementation changes only the global high-layer sign. -/
theorem fixedMaskHighDiagonal_nonzeroPointIndicator_lt_half_mul_energy_of_forty
    (mask : Fin (2 ^ 7) -> Bool)
    (hforty : 40 <= (frozenCoordinates mask).card) :
    fixedMaskHighDiagonal 7 1 (nonzeroPointIndicator (2 ^ 7)) mask <
      (1 / 2 : Rat) * fixedMaskSyndromeEnergy 7 1 (by omega)
        (nonzeroPointIndicator (2 ^ 7)) mask := by
  rw [fixedMaskHighDiagonal_nonzeroPointIndicator_eq,
    fixedMaskSyndromeEnergy_nonzeroPointIndicator_eq]
  exact fixedMaskHighDiagonal_zeroPointIndicator_lt_half_mul_energy_of_forty
    mask hforty

/-! ## The concrete bad-mask density -/

/-- The concrete structured half-field mask used by the obstruction. -/
def obstructionMask
    (seed : FiniteBitTape (structuredIndependence 1 * 7)) :
    Fin (2 ^ 7) -> Bool :=
  (structuredDyadicPrimitive 7 1 1 (by omega) (by omega)).generate seed

/-- Mask seeds with at least forty frozen coordinates. -/
def manyFrozenMaskSeeds :
    Finset (FiniteBitTape (structuredIndependence 1 * 7)) :=
  Finset.univ.filter fun seed =>
    40 <= (frozenCoordinates (obstructionMask seed)).card

/-- A rational presentation of the number of frozen coordinates. -/
def frozenCoordinateCountRat {coordinateCount : Nat}
    (mask : Fin coordinateCount -> Bool) : Rat :=
  ∑ coordinate : Fin coordinateCount,
    if mask coordinate = false then 1 else 0

theorem frozenCoordinateCountRat_eq_card
    {coordinateCount : Nat} (mask : Fin coordinateCount -> Bool) :
    frozenCoordinateCountRat mask = (frozenCoordinates mask).card := by
  classical
  unfold frozenCoordinateCountRat frozenCoordinates
  rw [show (∑ coordinate : Fin coordinateCount,
      if mask coordinate = false then (1 : Rat) else 0) =
      ∑ coordinate ∈ Finset.univ.filter
        (fun coordinate => mask coordinate = false), (1 : Rat) by
    rw [Finset.sum_filter]]
  simp

private theorem obstructionMask_singleton_false_average
    (coordinate : Fin (2 ^ 7)) :
    finiteAverage
        (fun seed : FiniteBitTape (structuredIndependence 1 * 7) =>
          if obstructionMask seed coordinate = false then (1 : Rat) else 0) =
      1 / 2 := by
  have hsource := structuredDyadicPrimitive_patternFalseBiased
    7 1 1 (by omega) (by omega)
  have hsingle :=
    maskAllZeroIndicator_average_eq_pow_of_patternFalseBiased
      (structuredDyadicPrimitive 7 1 1 (by omega) (by omega)).generate
      (1 / (2 : Rat) ^ 1) hsource ({coordinate} : Finset (Fin (2 ^ 7)))
      (by simp [structuredIndependence])
  calc
    finiteAverage
        (fun seed : FiniteBitTape (structuredIndependence 1 * 7) =>
          if obstructionMask seed coordinate = false then (1 : Rat) else 0) =
      finiteAverage
        (fun seed : FiniteBitTape (structuredIndependence 1 * 7) =>
          maskAllZeroIndicator {coordinate} (obstructionMask seed)) := by
            apply finiteAverage_congr
            intro seed
            simp [maskAllZeroIndicator]
    _ = (1 / (2 : Rat) ^ 1) ^ ({coordinate} : Finset (Fin (2 ^ 7))).card := by
      simpa [obstructionMask] using hsingle
    _ = 1 / 2 := by norm_num

/-- The exact one-coordinate law gives expected frozen count `64`. -/
theorem finiteAverage_frozenCoordinateCountRat_obstructionMask :
    finiteAverage
        (fun seed : FiniteBitTape (structuredIndependence 1 * 7) =>
          frozenCoordinateCountRat (obstructionMask seed)) = 64 := by
  unfold frozenCoordinateCountRat
  rw [finiteAverage_finset_sum]
  calc
    (∑ coordinate ∈ (Finset.univ : Finset (Fin (2 ^ 7))),
        finiteAverage
          (fun seed : FiniteBitTape (structuredIndependence 1 * 7) =>
            if obstructionMask seed coordinate = false then
              (1 : Rat) else 0)) =
      ∑ _coordinate ∈ (Finset.univ : Finset (Fin (2 ^ 7))),
        (1 / 2 : Rat) := by
          apply Finset.sum_congr rfl
          intro coordinate _hcoordinate
          rw [obstructionMask_singleton_false_average]
    _ = 64 := by norm_num

/-- Outside `manyFrozenMaskSeeds` the frozen count is at most `39`; inside it
the trivial cap is `128 = 39 + 89`. -/
theorem frozenCoordinateCountRat_obstructionMask_le_bad_envelope
    (seed : FiniteBitTape (structuredIndependence 1 * 7)) :
    frozenCoordinateCountRat (obstructionMask seed) <=
      39 + 89 * (if seed ∈ manyFrozenMaskSeeds then (1 : Rat) else 0) := by
  rw [frozenCoordinateCountRat_eq_card]
  by_cases hseed : seed ∈ manyFrozenMaskSeeds
  · rw [if_pos hseed]
    have hcard : (frozenCoordinates (obstructionMask seed)).card <= 128 := by
      calc
        (frozenCoordinates (obstructionMask seed)).card <=
            (Finset.univ : Finset (Fin (2 ^ 7))).card :=
          Finset.card_le_card (by simp [frozenCoordinates])
        _ = 128 := by norm_num
    exact_mod_cast hcard
  · rw [if_neg hseed]
    have hsmall : (frozenCoordinates (obstructionMask seed)).card <= 39 := by
      simp only [manyFrozenMaskSeeds, Finset.mem_filter, Finset.mem_univ,
        true_and] at hseed
      omega
    exact_mod_cast hsmall

/-- At least `25/89` of the concrete mask seeds have forty frozen
coordinates.  Only the exact one-coordinate marginal is used. -/
theorem twentyFive_div_eightyNine_le_badSeedDensity_manyFrozenMaskSeeds :
    (25 / 89 : Rat) <= badSeedDensity manyFrozenMaskSeeds := by
  have havg := finiteAverage_mono
    frozenCoordinateCountRat_obstructionMask_le_bad_envelope
  rw [finiteAverage_frozenCoordinateCountRat_obstructionMask] at havg
  have henvelope :
      finiteAverage
          (fun seed : FiniteBitTape (structuredIndependence 1 * 7) =>
            39 + 89 *
              (if seed ∈ manyFrozenMaskSeeds then (1 : Rat) else 0)) =
        39 + 89 * badSeedDensity manyFrozenMaskSeeds := by
    rw [finiteAverage_add_local, finiteAverage_const_mul,
      FiniteBooleanPerVertexRestrictionBound.finiteAverage_const]
    simp [badSeedDensity]
  rw [henvelope] at havg
  linarith

/-- Any exceptional set supporting the required relative frame inequality
off the set must contain all forty-frozen seeds. -/
theorem manyFrozenMaskSeeds_subset_bad_of_relative_frame_off_bad
    (bad : Finset (FiniteBitTape (structuredIndependence 1 * 7)))
    (hgood : forall seed, seed ∉ bad ->
      (1 / 2 : Rat) * fixedMaskSyndromeEnergy 7 1 (by omega)
          (nonzeroPointIndicator (2 ^ 7)) (obstructionMask seed) <=
        fixedMaskHighDiagonal 7 1 (nonzeroPointIndicator (2 ^ 7))
          (obstructionMask seed)) :
    manyFrozenMaskSeeds ⊆ bad := by
  intro seed hseed
  by_contra hnot
  have hforty : 40 <= (frozenCoordinates (obstructionMask seed)).card := by
    simpa [manyFrozenMaskSeeds] using hseed
  have hfail :=
    fixedMaskHighDiagonal_nonzeroPointIndicator_lt_half_mul_energy_of_forty
      (obstructionMask seed) hforty
  exact (not_lt_of_ge (hgood seed hnot)) hfail

/-- Bad-seed density is monotone under inclusion. -/
theorem badSeedDensity_mono
    {Seed : Type*} [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]
    {left right : Finset Seed} (hsubset : left ⊆ right) :
    badSeedDensity left <= badSeedDensity right := by
  unfold badSeedDensity
  apply finiteAverage_mono
  intro seed
  by_cases hleft : seed ∈ left
  · have hright := hsubset hleft
    simp [hleft, hright]
  · by_cases hright : seed ∈ right <;> simp [hleft, hright]

/-- Every admissible bad set has density strictly above one quarter. -/
theorem oneQuarter_lt_badSeedDensity_of_relative_frame_off_bad
    (bad : Finset (FiniteBitTape (structuredIndependence 1 * 7)))
    (hgood : forall seed, seed ∉ bad ->
      (1 / 2 : Rat) * fixedMaskSyndromeEnergy 7 1 (by omega)
          (nonzeroPointIndicator (2 ^ 7)) (obstructionMask seed) <=
        fixedMaskHighDiagonal 7 1 (nonzeroPointIndicator (2 ^ 7))
          (obstructionMask seed)) :
    (1 / 4 : Rat) < badSeedDensity bad := by
  have hsubset := manyFrozenMaskSeeds_subset_bad_of_relative_frame_off_bad
    bad hgood
  have hmono := badSeedDensity_mono hsubset
  have hlower := twentyFive_div_eightyNine_le_badSeedDensity_manyFrozenMaskSeeds
  norm_num at hlower ⊢
  linarith

/-! ## Impossibility of the mass-weighted certificate -/

/-- Exact uniform mass of the complement of the all-false point mass. -/
theorem finiteAverage_nonzeroPointIndicator_eq
    (coordinateCount : Nat) :
    finiteAverage (nonzeroPointIndicator coordinateCount) =
      1 - 1 / (2 : Rat) ^ coordinateCount := by
  rw [<- coefficient_empty_eq_finiteAverage]
  rw [show nonzeroPointIndicator coordinateCount =
      (fun input => (fun _ : Fin coordinateCount -> Bool => (1 : Rat)) input -
        zeroPointIndicator coordinateCount input) by
    funext input
    rfl]
  rw [coefficient_sub_pointwise, coefficient_zeroPointIndicator]
  have hone : coefficient
      (fun _ : Fin coordinateCount -> Bool => (1 : Rat)) ∅ = 1 := by
    rw [coefficient_empty_eq_finiteAverage]
    exact FiniteBooleanPerVertexRestrictionBound.finiteAverage_const 1
  rw [hone]

theorem nonzeroPointIndicator_nonneg
    (coordinateCount : Nat) (input : Fin coordinateCount -> Bool) :
    0 <= nonzeroPointIndicator coordinateCount input := by
  unfold nonzeroPointIndicator zeroPointIndicator
  split <;> norm_num

theorem fixedMaskStructuredBaseMass_nonzeroPointIndicator_nonneg
    (mask : Fin (2 ^ 7) -> Bool) :
    0 <= fixedMaskStructuredBaseMass 7 1 (by omega)
      (nonzeroPointIndicator (2 ^ 7)) mask := by
  unfold fixedMaskStructuredBaseMass
  apply finiteAverage_nonneg
  intro seed
  unfold fixedMaskAveragedFunction
  apply finiteAverage_nonneg
  intro uniform
  exact nonzeroPointIndicator_nonneg _ _

theorem badEnvelopeAverage_fixedMaskStructuredBaseMass_nonneg
    (bad : Finset (FiniteBitTape (structuredIndependence 1 * 7))) :
    0 <= badEnvelopeAverage bad
      (fun seed => fixedMaskStructuredBaseMass 7 1 (by omega)
        (nonzeroPointIndicator (2 ^ 7)) (obstructionMask seed)) := by
  unfold badEnvelopeAverage
  apply finiteAverage_nonneg
  intro seed
  split
  · exact fixedMaskStructuredBaseMass_nonzeroPointIndicator_nonneg _
  · norm_num

theorem structuredMaskedHighDiagonalAverage_nonzeroPointIndicator_nonneg :
    0 <= structuredMaskedHighDiagonalAverage 7 1 1 2
      (by omega) (by omega) (nonzeroPointIndicator (2 ^ 7)) := by
  unfold structuredMaskedHighDiagonalAverage
  apply finiteAverage_nonneg
  intro seed
  unfold structuredMaskedHighDiagonalCrossTerm
  exact Finset.sum_nonneg fun support _hsupport => mul_self_nonneg _

/-- The concrete OR function admits no mass-weighted bad-mask syndrome-frame
certificate.  The quantification over `bad`, `rho`, and `delta` is completely
arbitrary. -/
theorem not_structuredMassWeightedBadMaskSyndromeFrameCertificate_nonzeroPointIndicator
    (bad : Finset (FiniteBitTape (structuredIndependence 1 * 7)))
    (rho delta : Rat) :
    ¬ StructuredMassWeightedBadMaskSyndromeFrameCertificate
      7 1 1 (by omega) (by omega) (nonzeroPointIndicator (2 ^ 7))
        bad rho delta := by
  intro hcertificate
  have hparts := hcertificate
  dsimp only [StructuredMassWeightedBadMaskSyndromeFrameCertificate] at hparts
  have hgood : forall seed, seed ∉ bad ->
      (1 / 2 : Rat) * fixedMaskSyndromeEnergy 7 1 (by omega)
          (nonzeroPointIndicator (2 ^ 7)) (obstructionMask seed) <=
        fixedMaskHighDiagonal 7 1 (nonzeroPointIndicator (2 ^ 7))
          (obstructionMask seed) := by
    intro seed hseed
    have h := hparts.1 seed hseed
    simpa [obstructionMask] using h
  have hdensityBad : (1 / 4 : Rat) < badSeedDensity bad :=
    oneQuarter_lt_badSeedDensity_of_relative_frame_off_bad bad hgood
  have hdelta : (1 / 4 : Rat) < delta :=
    hdensityBad.trans_le hparts.2.2.1
  have hrho : 0 <= rho :=
    (badEnvelopeAverage_fixedMaskStructuredBaseMass_nonneg bad).trans
      (by simpa [obstructionMask] using hparts.2.1)
  have hmu :
      finiteAverage (nonzeroPointIndicator (2 ^ 7)) =
        1 - 1 / (2 : Rat) ^ (2 ^ 7) :=
    finiteAverage_nonzeroPointIndicator_eq (2 ^ 7)
  have hmuHalf :
      (1 / 2 : Rat) < finiteAverage (nonzeroPointIndicator (2 ^ 7)) := by
    rw [hmu]
    have hpow : (2 : Rat) < (2 : Rat) ^ (2 ^ 7) := by
      norm_num
    have hinv : 1 / (2 : Rat) ^ (2 ^ 7) < 1 / 2 := by
      exact one_div_lt_one_div_of_lt (by norm_num) hpow
    linarith
  have hproductPositive :
      0 < (finiteAverage (nonzeroPointIndicator (2 ^ 7)) - 1 / 2) *
        (delta - 1 / 4) :=
    mul_pos (by linarith) (by linarith)
  have hmudelta :
      (1 / 8 : Rat) <
        finiteAverage (nonzeroPointIndicator (2 ^ 7)) * delta := by
    nlinarith
  have hdiagonal :=
    structuredMaskedHighDiagonalAverage_nonzeroPointIndicator_nonneg
  have hbudget := hparts.2.2.2
  change structuredMaskedHighDiagonalAverage 7 1 1 2
      (by omega) (by omega) (nonzeroPointIndicator (2 ^ 7)) +
      (1 / 2 : Rat) *
        (2 * rho +
          2 * finiteAverage (nonzeroPointIndicator (2 ^ 7)) * delta) <=
        (1 / 2 : Rat) ^ 3 at hbudget
  norm_num only [div_pow] at hbudget
  nlinarith

/-- Existential form: there is no choice of exceptional set or numerical
charges making the certificate true. -/
theorem no_structuredMassWeightedBadMaskSyndromeFrameCertificate_nonzeroPointIndicator :
    ¬ ∃ (bad : Finset (FiniteBitTape (structuredIndependence 1 * 7)))
        (rho delta : Rat),
      StructuredMassWeightedBadMaskSyndromeFrameCertificate
        7 1 1 (by omega) (by omega) (nonzeroPointIndicator (2 ^ 7))
          bad rho delta := by
  rintro ⟨bad, rho, delta, hcertificate⟩
  exact not_structuredMassWeightedBadMaskSyndromeFrameCertificate_nonzeroPointIndicator
    bad rho delta hcertificate

end MandatoryCanonicalSelectorMassWeightedCertificateComplementObstruction
end
end OneTapeMagnification
end Frontier
end Pnp4
