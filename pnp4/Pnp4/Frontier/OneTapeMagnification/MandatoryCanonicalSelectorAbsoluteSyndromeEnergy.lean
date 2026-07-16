import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorSyndromeFrameBridge
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualMass
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Absolute syndrome energy for the mandatory selector

The relative syndrome-frame condition is stronger than the semantic estimate
needed by the restriction hybrid.  This file records the exact absolute
reformulation.  For the actual affine-prefixed mandatory selector, its
mask-averaged syndrome energy is the full two-seed second moment of the sum of
the genuine fixed-alpha block products minus the explicit low polynomial.

Consequently the absolute bound `E <= p^(2*m)` is exactly, rather than merely
sufficient for, the existing residual-mass `L2` target.  The one-round and
finite generated-prefix telescope endpoints therefore follow with no
relative frame premise.  No theorem here asserts the absolute bound for an
arbitrary machine.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanRestrictionMoment
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanAffineRoundsLocality
open DPTWFiniteBooleanPrimitives
open DPTWStructuredFieldCoordinatePrimitive
open FiniteAffineRestrictionHybrid
open FiniteStructuredDualSyndromeFiberBlocks
open FiniteStructuredDualBlockProductSyndromeTransform
open FiniteLayeredQueryProgramFamily
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorSyndromeFrameBridge
open MandatoryCanonicalSelectorResidualMass

namespace MandatoryCanonicalSelectorAbsoluteSyndromeEnergy

/-! ## Generic exact energy identities -/

/-- The structured high transform is the conditional high Fourier tail
averaged over the still-live uniform coordinates. -/
theorem structuredMaskedHighDegreeTransform_eq_highTailAverage
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    structuredMaskedHighDegreeTransform n m cutoff hn f mask seed =
      finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        FiniteUnambiguousFBDD.ratHighDegreeFourierTail f cutoff
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed)
            mask uniform)) := by
  classical
  rw [finiteAverage_ratHighDegreeFourierTail_masked]
  unfold structuredMaskedHighDegreeTransform structuredMaskedCoefficient
  apply Finset.sum_congr rfl
  intro support _hsupport
  rw [restrictedCharacterAverage_eq]
  ring

/-- The mask-averaged syndrome energy is exactly the full structured
base-and-mask second moment of the conditional high tail. -/
theorem structuredSyndromeEnergyAverage_eq_highTailSecondMoment
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredSyndromeEnergyAverage n m tailBits cutoff hn htail f =
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          FiniteUnambiguousFBDD.ratHighDegreeFourierTail f cutoff
            (maskedInput
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              uniform))) ^ 2) := by
  classical
  let Seed := FiniteBitTape (structuredIndependence m * n)
  let maskGenerator :=
    (structuredDyadicPrimitive n m tailBits hn htail).generate
  let tailMoment := fun (maskSeed baseSeed : Seed) =>
    (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
      FiniteUnambiguousFBDD.ratHighDegreeFourierTail f cutoff
        (maskedInput
          ((structuredUnbiasedPrimitive n m hn).generate baseSeed)
          (maskGenerator maskSeed) uniform))) ^ 2
  unfold structuredSyndromeEnergyAverage
  calc
    finiteAverage (fun maskSeed : Seed =>
        Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
          (structuredSyndromeFiberCoefficientSum n m cutoff hn f
            (maskGenerator maskSeed) syndrome) ^ 2)) =
      finiteAverage (fun maskSeed : Seed =>
        finiteAverage (fun baseSeed : Seed =>
          tailMoment maskSeed baseSeed)) := by
            apply finiteAverage_congr
            intro maskSeed
            calc
              Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
                  (structuredSyndromeFiberCoefficientSum n m cutoff hn f
                    (maskGenerator maskSeed) syndrome) ^ 2) =
                finiteAverage (fun baseSeed : Seed =>
                  (structuredMaskedHighDegreeTransform n m cutoff hn f
                    (maskGenerator maskSeed) baseSeed) ^ 2) := by
                      simpa only [pow_two] using
                        (syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
                          n m cutoff hn f f (maskGenerator maskSeed))
              _ = finiteAverage (fun baseSeed : Seed =>
                    tailMoment maskSeed baseSeed) := by
                      apply finiteAverage_congr
                      intro baseSeed
                      unfold tailMoment
                      rw [structuredMaskedHighDegreeTransform_eq_highTailAverage]
    _ = finiteAverage (fun pair : Seed × Seed =>
          tailMoment pair.1 pair.2) := by
            symm
            exact finiteAverage_prod_eq_iterated
              (fun maskSeed baseSeed => tailMoment maskSeed baseSeed)
    _ = finiteAverage (fun pair : Seed × Seed =>
          tailMoment pair.2 pair.1) := by
            exact (DPTWFiniteBooleanPrimitives.finiteAverage_comp_equiv
              (Equiv.prodComm Seed Seed)
              (fun pair : Seed × Seed => tailMoment pair.1 pair.2)).symm
    _ = finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          FiniteUnambiguousFBDD.ratHighDegreeFourierTail f cutoff
            (maskedInput
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              uniform))) ^ 2) := by
            rfl

/-- Equivalently, syndrome energy is the exact second moment of residual
conditional mass minus its low-degree predictor. -/
theorem structuredSyndromeEnergyAverage_eq_residualMassSecondMoment
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredSyndromeEnergyAverage n m tailBits cutoff hn htail f =
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (FiniteBooleanResidualMass.maskedAverage f
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              seed.2) -
          FiniteBooleanResidualMass.maskedLowDegreePredictor f cutoff
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              seed.2)) ^ 2) := by
  calc
    structuredSyndromeEnergyAverage n m tailBits cutoff hn htail f =
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          FiniteUnambiguousFBDD.ratHighDegreeFourierTail f cutoff
            (maskedInput
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              uniform))) ^ 2) :=
        structuredSyndromeEnergyAverage_eq_highTailSecondMoment
          n m tailBits cutoff hn htail f
    _ = finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (FiniteBooleanResidualMass.maskedAverage f
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              seed.2) -
          FiniteBooleanResidualMass.maskedLowDegreePredictor f cutoff
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              seed.2)) ^ 2) := by
        exact (FiniteBooleanResidualMass.deviation_secondMoment_eq_highTailSecondMoment
          f cutoff
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate).symm

/-! ## Actual affine-prefixed selector -/

/-- For the actual prefixed mandatory selector, the syndrome energy is the
full two-seed average of the sum of genuine fixed-alpha block products minus
the selector's explicit low polynomial. -/
theorem prefixedMandatoryCanonicalSelector_structuredSyndromeEnergyAverage_eq_blockProductSecondMoment
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let f := (prefixedMandatoryCanonicalSelector machine n T b rounds)
      |>.ratAcceptanceIndicator
    structuredSyndromeEnergyAverage n m tailBits (2 * m) hn htail f =
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
            machine n m T b hn hb rounds
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              seed.2)
            seed.1 -
      prefixedMandatoryCanonicalSelectorStructuredLowDegreePolynomial
            machine n m T b (2 * m) hn rounds
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              seed.2)
            seed.1) ^ 2) := by
  classical
  dsimp only
  rw [structuredSyndromeEnergyAverage_eq_highTailSecondMoment]
  apply finiteAverage_congr
  intro seed
  rw [← structuredMaskedHighDegreeTransform_eq_highTailAverage]
  rw [structuredMaskedHighDegreeTransform_eq_fixedMask_sub_low]
  rw [prefixedMandatoryCanonicalSelector_fixedMaskAveragedFunction_eq_blockProductTransform
    machine n m T b hn hb rounds]
  rfl

/-- Viable machine-specific source condition: the absolute structured
syndrome energy, with no comparison to the Fourier diagonal. -/
def PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Prop :=
  let f := (prefixedMandatoryCanonicalSelector machine n T b rounds)
    |>.ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  structuredSyndromeEnergyAverage n m tailBits (2 * m) hn htail f <=
    p ^ (2 * m)

/-- The absolute syndrome condition is exactly the semantic residual-mass
`L2` condition; neither side loses cancellation or coefficient magnitude. -/
theorem prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound_iff_residualMassL2Bound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
        machine n T b m tailBits hn htail rounds <->
      ResidualMassL2Bound machine n T b m tailBits hn htail rounds := by
  unfold PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
    ResidualMassL2Bound
  dsimp only
  rw [structuredSyndromeEnergyAverage_eq_residualMassSecondMoment]

/-- Concrete block-product characterization of the viable absolute source. -/
theorem prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound_iff_blockProductSecondMoment_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
        machine n T b m tailBits hn htail rounds <->
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
            machine n m T b hn hb rounds
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              seed.2)
            seed.1 -
          prefixedMandatoryCanonicalSelectorStructuredLowDegreePolynomial
            machine n m T b (2 * m) hn rounds
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              seed.2)
            seed.1) ^ 2) <= p ^ (2 * m) := by
  dsimp only
  unfold PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
  dsimp only
  rw [prefixedMandatoryCanonicalSelector_structuredSyndromeEnergyAverage_eq_blockProductSecondMoment
    machine n T b m tailBits hn hb htail rounds]

/-- The absolute syndrome source gives the existing card-free one-round
fooling estimate. -/
theorem oneRoundError_le_pow_of_prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (henergy : PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
      machine n T b m tailBits hn htail rounds) :
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
      ((prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound_iff_residualMassL2Bound
        machine n T b m tailBits hn htail rounds).mp henergy)

/-! ## Generated prefixes and the finite telescope -/

/-- Absolute syndrome control is needed only at generated prefixes strictly
before the terminal round. -/
def GeneratedPrefixAbsoluteSyndromeEnergyBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) : Prop :=
  forall (r : Nat), r < L ->
    forall oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
        machine n T b m tailBits hn htail
          (roundsOfSeeds
            (structuredUnbiasedPrimitive n m hn).generate
            (structuredDyadicPrimitive n m tailBits hn htail).generate
            r oldSeeds)

/-- The generated-prefix absolute condition is exactly the existing
generated-prefix residual-mass condition. -/
theorem generatedPrefixAbsoluteSyndromeEnergyBoundUpTo_iff_generatedPrefixResidualMassL2BoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) :
    GeneratedPrefixAbsoluteSyndromeEnergyBoundUpTo
        machine n T b m tailBits L hn htail <->
      GeneratedPrefixResidualMassL2BoundUpTo
        machine n T b m tailBits L hn htail := by
  constructor
  · intro henergy r hr oldSeeds
    apply (prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound_iff_residualMassL2Bound
      machine n T b m tailBits hn htail _).mp
    exact henergy r hr oldSeeds
  · intro hresidual r hr oldSeeds
    apply (prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound_iff_residualMassL2Bound
      machine n T b m tailBits hn htail _).mpr
    exact hresidual r hr oldSeeds

/-- The viable absolute syndrome source yields the exact card-free
`L * p^m` finite-round telescope. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixAbsoluteSyndromeEnergyBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (henergy : GeneratedPrefixAbsoluteSyndromeEnergyBoundUpTo
      machine n T b m tailBits L hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| <= (L : Rat) * p ^ m := by
  exact abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixResidualMassL2BoundUpTo
    machine n T b m tailBits L hn htail
      ((generatedPrefixAbsoluteSyndromeEnergyBoundUpTo_iff_generatedPrefixResidualMassL2BoundUpTo
        machine n T b m tailBits L hn htail).mp henergy)

end MandatoryCanonicalSelectorAbsoluteSyndromeEnergy
end

end OneTapeMagnification
end Frontier
end Pnp4
