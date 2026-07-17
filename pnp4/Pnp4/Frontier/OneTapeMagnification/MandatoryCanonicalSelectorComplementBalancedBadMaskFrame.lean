import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorBadMaskResidualCountBridge
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Complement-balanced bad-mask syndrome frames

Complementing a `[0,1]`-valued function preserves its strict high Fourier
layer up to a global sign.  Therefore its fixed-mask syndrome energy and high
diagonal are unchanged, while its structured and uniform masses become their
complements.  Applying the diagonal-retaining mass envelope to both `f` and
`1 - f` gives the smaller of the two envelopes.

The final good/bad interface is a conditional certificate on the average
balanced charge.  It does not prove that a one-tape machine supplies that
charge bound, and it does not close the small-seed selector correlation lemma.
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
open MandatoryCanonicalSelectorResidualMass
open MandatoryCanonicalSelectorAbsoluteSyndromeEnergy
open MandatoryCanonicalSelectorSyndromeFrameBridge
open MandatoryCanonicalSelectorDefectiveSyndromeFrame
open MandatoryCanonicalSelectorBadMaskResidualCountBridge
open FiniteBooleanDualAliasConvolutionTransfer

namespace MandatoryCanonicalSelectorComplementBalancedBadMaskFrame

/-! ## Complement symmetry -/

/-- Pointwise complement in the rational Boolean cube. -/
def complementFunction {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat) :
    (Fin coordinateCount -> Bool) -> Rat :=
  fun input => 1 - f input

private theorem coefficient_sub_pointwise
    {coordinateCount : Nat}
    (f g : (Fin coordinateCount -> Bool) -> Rat)
    (support : Finset (Fin coordinateCount)) :
    coefficient (fun input => f input - g input) support =
      coefficient f support - coefficient g support := by
  unfold coefficient
  rw [<- sub_div, <- Finset.sum_sub_distrib]
  apply congrArg (fun value : Rat => value / (2 : Rat) ^ coordinateCount)
  apply Finset.sum_congr rfl
  intro input _hinput
  ring

/-- Every nonconstant Fourier coefficient changes sign under complementation. -/
theorem coefficient_complementFunction_of_nonempty
    {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat)
    (support : Finset (Fin coordinateCount))
    (hsupport : support.Nonempty) :
    coefficient (complementFunction f) support = -coefficient f support := by
  rw [show complementFunction f =
      (fun input => (fun _ : Fin coordinateCount -> Bool => (1 : Rat)) input -
        f input) by
    funext input
    rfl]
  rw [coefficient_sub_pointwise]
  rw [coefficient_one_eq_zero_of_nonempty hsupport]
  ring

/-- Complementation changes a fixed-mask conditional mean to `1 - mean`. -/
theorem fixedMaskAveragedFunction_complementFunction
    {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat)
    (mask base : Fin coordinateCount -> Bool) :
    fixedMaskAveragedFunction (complementFunction f) mask base =
      1 - fixedMaskAveragedFunction f mask base := by
  unfold fixedMaskAveragedFunction complementFunction
  rw [FiniteBooleanOneRoundFoolingBound.finiteAverage_sub]
  simp

/-- Uniform mass is complemented as well. -/
theorem finiteAverage_complementFunction
    {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat) :
    finiteAverage (complementFunction f) = 1 - finiteAverage f := by
  unfold complementFunction
  rw [FiniteBooleanOneRoundFoolingBound.finiteAverage_sub]
  simp

/-- The structured-base conditional mass at a fixed mask is complemented. -/
theorem fixedMaskStructuredBaseMass_complementFunction
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskStructuredBaseMass n m hn (complementFunction f) mask =
      1 - fixedMaskStructuredBaseMass n m hn f mask := by
  unfold fixedMaskStructuredBaseMass
  simp_rw [fixedMaskAveragedFunction_complementFunction]
  rw [FiniteBooleanOneRoundFoolingBound.finiteAverage_sub]
  simp

/-- Each high syndrome-fiber coefficient sum changes by a global sign. -/
theorem structuredSyndromeFiberCoefficientSum_complementFunction_eq_neg
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool)
    (syndrome : StructuredDualPowerSyndrome n m) :
    structuredSyndromeFiberCoefficientSum n m cutoff hn
        (complementFunction f) mask syndrome =
      -structuredSyndromeFiberCoefficientSum n m cutoff hn
        f mask syndrome := by
  classical
  unfold structuredSyndromeFiberCoefficientSum
  rw [<- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro support hsupport
  have hcard := mem_highDegreeSupports.mp hsupport
  have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
  split_ifs with hsame
  · unfold structuredMaskedCoefficient
    rw [coefficient_complementFunction_of_nonempty f support hnonempty]
    ring
  · ring

/-- Fixed-mask high syndrome energy is invariant under complementation. -/
theorem fixedMaskSyndromeEnergy_complementFunction
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskSyndromeEnergy n m hn (complementFunction f) mask =
      fixedMaskSyndromeEnergy n m hn f mask := by
  unfold fixedMaskSyndromeEnergy
  apply Finset.sum_congr rfl
  intro syndrome _hsyndrome
  rw [structuredSyndromeFiberCoefficientSum_complementFunction_eq_neg]
  ring

/-- The fixed-mask high Fourier diagonal is complement invariant. -/
theorem fixedMaskHighDiagonal_complementFunction
    (n m : Nat)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskHighDiagonal n m (complementFunction f) mask =
      fixedMaskHighDiagonal n m f mask := by
  classical
  unfold fixedMaskHighDiagonal structuredMaskedHighDiagonalCrossTerm
  apply Finset.sum_congr rfl
  intro support hsupport
  have hcard := mem_highDegreeSupports.mp hsupport
  have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
  unfold structuredMaskedCoefficient
  rw [coefficient_complementFunction_of_nonempty f support hnonempty]
  ring

/-! ## Balanced fixed-mask envelope -/

/-- The complement-balanced mass envelope at one fixed mask. -/
def fixedMaskComplementBalancedEnvelope
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  let mass := fixedMaskStructuredBaseMass n m hn f mask
  let uniformMass := finiteAverage f
  let diagonal := fixedMaskHighDiagonal n m f mask
  2 * min
    (mass + uniformMass - diagonal)
    ((1 - mass) + (1 - uniformMass) - diagonal)

/-- Applying the diagonal-retaining envelope to both a function and its
complement gives the smaller of the two unconditional fixed-mask bounds. -/
theorem fixedMaskSyndromeEnergy_le_complementBalancedEnvelope
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hunit : forall input, 0 <= f input /\ f input <= 1)
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskSyndromeEnergy n m hn f mask <=
      fixedMaskComplementBalancedEnvelope n m hn f mask := by
  let mass := fixedMaskStructuredBaseMass n m hn f mask
  let uniformMass := finiteAverage f
  let diagonal := fixedMaskHighDiagonal n m f mask
  have hdirect :=
    fixedMask_syndromeFiberEnergy_le_two_mul_structuredMass_add_two_mul_uniformMass_sub_diagonal
      n m hn f hunit mask
  change fixedMaskSyndromeEnergy n m hn f mask <=
      2 * mass + 2 * (uniformMass - diagonal) at hdirect
  have hcomplementUnit : forall input,
      0 <= complementFunction f input /\ complementFunction f input <= 1 := by
    intro input
    unfold complementFunction
    constructor <;> linarith [hunit input]
  have hcomplement :=
    fixedMask_syndromeFiberEnergy_le_two_mul_structuredMass_add_two_mul_uniformMass_sub_diagonal
      n m hn (complementFunction f) hcomplementUnit mask
  change fixedMaskSyndromeEnergy n m hn (complementFunction f) mask <=
      2 * fixedMaskStructuredBaseMass n m hn (complementFunction f) mask +
        2 * (finiteAverage (complementFunction f) -
          fixedMaskHighDiagonal n m (complementFunction f) mask) at hcomplement
  rw [fixedMaskSyndromeEnergy_complementFunction,
    fixedMaskStructuredBaseMass_complementFunction,
    finiteAverage_complementFunction,
    fixedMaskHighDiagonal_complementFunction] at hcomplement
  have hleft : fixedMaskSyndromeEnergy n m hn f mask <=
      2 * (mass + uniformMass - diagonal) := by
    linarith
  have hright : fixedMaskSyndromeEnergy n m hn f mask <=
      2 * ((1 - mass) + (1 - uniformMass) - diagonal) := by
    change fixedMaskSyndromeEnergy n m hn f mask <=
      2 * ((1 - mass) + (1 - uniformMass) - diagonal)
    dsimp only [mass, uniformMass, diagonal]
    linarith
  unfold fixedMaskComplementBalancedEnvelope
  dsimp only
  rcases le_total
      (mass + uniformMass - diagonal)
      ((1 - mass) + (1 - uniformMass) - diagonal) with hle | hle
  · rw [min_eq_left hle]
    exact hleft
  · rw [min_eq_right hle]
    exact hright

/-! ## Conditional good/bad averaging -/

/-- A conditional good/bad certificate which charges every exceptional mask
by the complement-balanced fixed-mask envelope.  It is deliberately an
average-charge premise, not a theorem about one-tape transition geometry. -/
def StructuredComplementBalancedBadMaskFrameCertificate
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) : Prop :=
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  (forall seed, seed ∉ bad ->
      p * fixedMaskSyndromeEnergy n m hn f (mask seed) <=
        fixedMaskHighDiagonal n m f (mask seed)) /\
    structuredMaskedHighDiagonalAverage
        n m tailBits (2 * m) hn htail f +
      p * badEnvelopeAverage bad
        (fun seed => fixedMaskComplementBalancedEnvelope
          n m hn f (mask seed)) <=
        p ^ (2 * m + 1)

/-- The complement-balanced conditional certificate implies the absolute
structured syndrome-energy target. -/
theorem structuredSyndromeEnergyAverage_le_pow_of_complementBalancedCertificate
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hunit : forall input, 0 <= f input /\ f input <= 1)
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (hcertificate : StructuredComplementBalancedBadMaskFrameCertificate
      n m tailBits hn htail f bad) :
    structuredSyndromeEnergyAverage
        n m tailBits (2 * m) hn htail f <=
      (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  let energy := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    fixedMaskSyndromeEnergy n m hn f (mask seed)
  let diagonal := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    fixedMaskHighDiagonal n m f (mask seed)
  let envelope := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    fixedMaskComplementBalancedEnvelope n m hn f (mask seed)
  have hp : 0 < p := by dsimp [p]; positivity
  have hdiagonal : forall seed, 0 <= diagonal seed := by
    intro seed
    unfold diagonal fixedMaskHighDiagonal
      structuredMaskedHighDiagonalCrossTerm
    exact Finset.sum_nonneg fun support _ => mul_self_nonneg _
  have hparts := hcertificate
  dsimp only [StructuredComplementBalancedBadMaskFrameCertificate] at hparts
  change (forall seed, seed ∉ bad ->
      p * energy seed <= diagonal seed) /\
    structuredMaskedHighDiagonalAverage
        n m tailBits (2 * m) hn htail f +
      p * badEnvelopeAverage bad envelope <=
        p ^ (2 * m + 1) at hparts
  have hbudget : finiteAverage diagonal +
      p * badEnvelopeAverage bad envelope <= p * p ^ (2 * m) := by
    have hdiagEq : finiteAverage diagonal =
        structuredMaskedHighDiagonalAverage
          n m tailBits (2 * m) hn htail f := by rfl
    rw [hdiagEq]
    rw [show p ^ (2 * m + 1) = p * p ^ (2 * m) by
      rw [pow_succ]; ring] at hparts
    exact hparts.2
  have haverage : finiteAverage energy <= p ^ (2 * m) := by
    apply finiteAverage_energy_le_of_good_bad_envelope
      bad energy diagonal envelope p (p ^ (2 * m)) hp
        hdiagonal hparts.1
    · intro seed _hseed
      exact fixedMaskSyndromeEnergy_le_complementBalancedEnvelope
        n m hn f hunit (mask seed)
    · exact hbudget
  simpa [structuredSyndromeEnergyAverage, energy, mask, p] using haverage

/-! ## Actual affine-prefixed mandatory selector -/

/-- Complement-balanced conditional certificate for the actual selector after
one fixed affine prefix. -/
def PrefixedMandatoryCanonicalSelectorComplementBalancedBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) : Prop :=
  StructuredComplementBalancedBadMaskFrameCertificate
    n m tailBits hn htail
      (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
    bad

/-- The conditional balanced certificate implies the exact residual-mass
`L2` target for the actual affine-prefixed selector. -/
theorem residualMassL2Bound_of_prefixedComplementBalancedBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (hcertificate :
      PrefixedMandatoryCanonicalSelectorComplementBalancedBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad) :
    ResidualMassL2Bound machine n T b m tailBits hn htail rounds := by
  let f := (prefixedMandatoryCanonicalSelector machine n T b rounds)
    |>.ratAcceptanceIndicator
  have hunit : forall input, 0 <= f input /\ f input <= 1 := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have henergy :=
    structuredSyndromeEnergyAverage_le_pow_of_complementBalancedCertificate
      n m tailBits hn htail f hunit bad
        (by
          simpa [
            PrefixedMandatoryCanonicalSelectorComplementBalancedBadMaskCertificate,
            f] using hcertificate)
  apply (prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound_iff_residualMassL2Bound
    machine n T b m tailBits hn htail rounds).mp
  unfold PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
  simpa [f] using henergy

/-- Consequently the conditional balanced certificate gives the card-free
one-round `p^m` error bound. -/
theorem oneRoundError_le_pow_of_prefixedComplementBalancedBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (hcertificate :
      PrefixedMandatoryCanonicalSelectorComplementBalancedBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad) :
    let B := prefixedMandatoryCanonicalSelector machine n T b rounds
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          B.ratAcceptanceIndicator
            (maskedInput
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              uniform))) -
      finiteAverage B.ratAcceptanceIndicator| <= p ^ m := by
  exact oneRoundError_le_pow_of_residualMassL2Bound
    machine n T b m tailBits hn htail rounds
      (residualMassL2Bound_of_prefixedComplementBalancedBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad hcertificate)

end MandatoryCanonicalSelectorComplementBalancedBadMaskFrame
end
end OneTapeMagnification
end Frontier
end Pnp4
