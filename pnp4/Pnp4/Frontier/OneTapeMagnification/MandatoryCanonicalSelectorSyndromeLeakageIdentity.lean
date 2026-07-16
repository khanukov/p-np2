import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalComponentSyndromeLeakageIdentity
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Whole-selector structured syndrome leakage identities

Linearity upgrades the actual fixed-alpha product transform to the complete
mandatory selector.  The high-degree syndrome-fiber energy is exactly the
structured-seed average of the square of

`sum over alphas (product of local transforms) - selector low polynomial`.

The same statement holds after any common affine prefix.  These are exact
identities, not quantitative leakage bounds.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanRestrictionMoment
open FiniteBooleanMaskedProductFactorization
open FiniteBooleanAffineRoundsLocality
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanOneRoundFoolingBound
open DPTWStructuredFieldCoordinatePrimitive
open FiniteStructuredDualSyndromeFiberBlocks
open FiniteStructuredDualNonzeroSeedCorrelation
open FiniteStructuredDualBlockProductSyndromeTransform
open MandatoryCanonicalSelectorPairCorrelation

namespace FiniteLayeredQueryProgramFamily

local instance cachedInputMachineStateDecidableEqForSelectorSyndromeLeakage
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Sum, over every installed canonical alpha, of its genuine block-product
structured transform. -/
def mandatoryCanonicalSelectorBlockProductStructuredTransform
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b : Nat) (hn : 0 < n) (hb : 0 < b)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) : Rat :=
  ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
    ∏ block : Fin (T / b + 1),
      mandatoryCanonicalBlockProjectionStructuredTransform
        machine n m T b hn hb index mask seed block

/-- Explicit low-degree polynomial of the complete installed selector. -/
def mandatoryCanonicalSelectorStructuredLowDegreePolynomial
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b cutoff : Nat) (hn : 0 < n)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) : Rat :=
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily
    machine (2 ^ n) T b
  structuredMaskedLowDegreePolynomial n m cutoff hn
    family.selectorFBDD.ratAcceptanceIndicator mask seed

/-- The actual selector's fixed-mask conditional mean is exactly the sum of
the genuine fixed-alpha local-transform products. -/
theorem mandatoryCanonicalSelector_fixedMaskAveragedFunction_eq_blockProductTransform
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b : Nat) (hn : 0 < n) (hb : 0 < b)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily
      machine (2 ^ n) T b
    fixedMaskAveragedFunction
        family.selectorFBDD.ratAcceptanceIndicator mask
        ((structuredUnbiasedPrimitive n m hn).generate seed) =
      mandatoryCanonicalSelectorBlockProductStructuredTransform
        machine n m T b hn hb mask seed := by
  classical
  dsimp only
  have hfixed :=
    mandatoryCanonicalSelector_finiteAverage_maskedInput_eq_sum_projectionProd
      machine (2 ^ n) T b hb
      ((structuredUnbiasedPrimitive n m hn).generate seed) mask
  simpa [fixedMaskAveragedFunction,
    mandatoryCanonicalSelectorBlockProductStructuredTransform,
    mandatoryCanonicalBlockProjectionStructuredTransform] using hfixed

/-- **Exact whole-selector leakage identity.** -/
theorem mandatoryCanonicalSelector_syndromeFiberEnergy_eq_average_sumBlockProducts_sub_low_sq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b cutoff : Nat) (hn : 0 < n) (hb : 0 < b)
    (mask : Fin (2 ^ n) -> Bool) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily
      machine (2 ^ n) T b
    (∑ syndrome : StructuredDualPowerSyndrome n m,
      (structuredSyndromeFiberCoefficientSum n m cutoff hn
        family.selectorFBDD.ratAcceptanceIndicator mask syndrome) ^ 2) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (mandatoryCanonicalSelectorBlockProductStructuredTransform
              machine n m T b hn hb mask seed -
            mandatoryCanonicalSelectorStructuredLowDegreePolynomial
              machine n m T b cutoff hn mask seed) ^ 2) := by
  classical
  dsimp only
  let selector :=
    (mandatoryFiniteRejectingGuardedCanonicalFamily
      machine (2 ^ n) T b).selectorFBDD.ratAcceptanceIndicator
  calc
    (∑ syndrome : StructuredDualPowerSyndrome n m,
        (structuredSyndromeFiberCoefficientSum n m cutoff hn
          selector mask syndrome) ^ 2) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (structuredMaskedHighDegreeTransform n m cutoff hn
            selector mask seed) ^ 2) := by
              simpa only [pow_two] using
                (syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
                  n m cutoff hn selector selector mask)
    _ = finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (mandatoryCanonicalSelectorBlockProductStructuredTransform
              machine n m T b hn hb mask seed -
            mandatoryCanonicalSelectorStructuredLowDegreePolynomial
              machine n m T b cutoff hn mask seed) ^ 2) := by
                apply finiteAverage_congr
                intro seed
                rw [structuredMaskedHighDegreeTransform_eq_fixedMask_sub_low]
                rw [mandatoryCanonicalSelector_fixedMaskAveragedFunction_eq_blockProductTransform
                  machine n m T b hn hb mask seed]
                rfl

/-- The exact fixed-mask sum of component block products is a conditional
mean of a Boolean selector, hence lies in the unit interval. -/
theorem mandatoryCanonicalSelectorBlockProductStructuredTransform_mem_unitInterval
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b : Nat) (hn : 0 < n) (hb : 0 < b)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    0 <= mandatoryCanonicalSelectorBlockProductStructuredTransform
        machine n m T b hn hb mask seed ∧
      mandatoryCanonicalSelectorBlockProductStructuredTransform
        machine n m T b hn hb mask seed <= 1 := by
  classical
  let selector :=
    (mandatoryFiniteRejectingGuardedCanonicalFamily
      machine (2 ^ n) T b).selectorFBDD.ratAcceptanceIndicator
  have hfixed :=
    mandatoryCanonicalSelector_fixedMaskAveragedFunction_eq_blockProductTransform
      machine n m T b hn hb mask seed
  dsimp only at hfixed
  rw [← hfixed]
  constructor
  · unfold fixedMaskAveragedFunction
    apply finiteAverage_nonneg
    intro uniform
    unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  · apply le_trans (le_abs_self _)
    apply abs_fixedMaskAveragedFunction_le_one
    intro input
    unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num

/-- Sum of prefixed fixed-alpha local-transform products. -/
def prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) : Rat :=
  ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
    ∏ block : Fin (T / b + 1),
      prefixedMandatoryCanonicalBlockProjectionStructuredTransform
        machine n m T b hn hb rounds index mask seed block

/-- Explicit low-degree polynomial of the complete prefixed selector. -/
def prefixedMandatoryCanonicalSelectorStructuredLowDegreePolynomial
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b cutoff : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) : Rat :=
  structuredMaskedLowDegreePolynomial n m cutoff hn
    (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
    mask seed

/-- Prefix-stable fixed-mask linearity: the conditional mean of the complete
prefixed selector is the sum of its prefixed local block products. -/
theorem prefixedMandatoryCanonicalSelector_fixedMaskAveragedFunction_eq_blockProductTransform
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    fixedMaskAveragedFunction
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
        mask
        ((structuredUnbiasedPrimitive n m hn).generate seed) =
      prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
        machine n m T b hn hb rounds mask seed := by
  classical
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily
    machine (2 ^ n) T b
  let base := (structuredUnbiasedPrimitive n m hn).generate seed
  let scheduled := fun index :
      BuiltRejectingGuardedCanonicalAlphaIndex machine T b =>
    builtTimedAlphaVisitSchedule (cachedInputMachine machine) index.1
  let blockFactor := fun
      (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
      (block : Fin (T / b + 1))
      (input : Fin (2 ^ n) -> Bool) =>
    finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
      machine hb index.1 (scheduled index) block
        (applyAffineRestrictionRounds rounds input)
  have hpointwise (input : Fin (2 ^ n) -> Bool) :
      ((prefixedMandatoryCanonicalSelector machine n T b rounds)
          |>.ratAcceptanceIndicator) input =
        ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
          ∏ block : Fin (T / b + 1), blockFactor index block input := by
    rw [FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq]
    rw [family.selector_ratAcceptanceIndicator_eq_sum_components
      (mandatoryFiniteRejectingGuardedCanonicalFamily_isUnambiguous
        machine (2 ^ n) T b hb)
      (applyAffineRestrictionRounds rounds input)]
    apply Finset.sum_congr rfl
    intro index _hindex
    simpa [family, scheduled, blockFactor] using
      (prefixedMandatoryCanonicalComponentIndicator_eq_blockProjectionProduct
        machine (2 ^ n) T b hb rounds index input)
  unfold fixedMaskAveragedFunction
  calc
    finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        ((prefixedMandatoryCanonicalSelector machine n T b rounds)
          |>.ratAcceptanceIndicator) (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
          ∏ block : Fin (T / b + 1),
            blockFactor index block (maskedInput base mask uniform)) := by
              apply finiteAverage_congr
              intro uniform
              exact hpointwise (maskedInput base mask uniform)
    _ = ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          ∏ block : Fin (T / b + 1),
            blockFactor index block (maskedInput base mask uniform)) := by
              exact finiteAverage_fintype_sum _
    _ = ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        ∏ block : Fin (T / b + 1),
          finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
            blockFactor index block (maskedInput base mask uniform)) := by
              apply Finset.sum_congr rfl
              intro index _hindex
              simpa using
                (finiteAverage_finset_prod_maskedInput_eq_prod
                  (Finset.univ : Finset (Fin (T / b + 1)))
                  (fun block =>
                    finiteCachedTimedScheduleBlockQuerySupport
                      (2 ^ n) (scheduled index) block)
                  (blockFactor index)
                  (by
                    intro block _hblock
                    exact dependsOnlyOn_applyAffineRestrictionRounds
                      (finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor_dependsOnlyOn
                        machine hb index.1 (scheduled index) block)
                      rounds)
                  (by
                    intro left _hleft right _hright hne
                    exact finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
                      (scheduled index)
                      (builtRejectingGuardedCanonicalIndex_chained machine index)
                      (builtRejectingGuardedCanonicalIndexMonotone machine index)
                      hne)
                  base mask)
    _ = prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
        machine n m T b hn hb rounds mask seed := by
          rfl

/-- **Exact affine-prefixed whole-selector leakage identity.** -/
theorem prefixedMandatoryCanonicalSelector_syndromeFiberEnergy_eq_average_sumBlockProducts_sub_low_sq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b cutoff : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    let selector :=
      (prefixedMandatoryCanonicalSelector machine n T b rounds)
        |>.ratAcceptanceIndicator
    (∑ syndrome : StructuredDualPowerSyndrome n m,
      (structuredSyndromeFiberCoefficientSum n m cutoff hn
        selector mask syndrome) ^ 2) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
              machine n m T b hn hb rounds mask seed -
            prefixedMandatoryCanonicalSelectorStructuredLowDegreePolynomial
              machine n m T b cutoff hn rounds mask seed) ^ 2) := by
  classical
  dsimp only
  let selector :=
    (prefixedMandatoryCanonicalSelector machine n T b rounds)
      |>.ratAcceptanceIndicator
  calc
    (∑ syndrome : StructuredDualPowerSyndrome n m,
        (structuredSyndromeFiberCoefficientSum n m cutoff hn
          selector mask syndrome) ^ 2) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (structuredMaskedHighDegreeTransform n m cutoff hn
            selector mask seed) ^ 2) := by
              simpa only [pow_two] using
                (syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
                  n m cutoff hn selector selector mask)
    _ = finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
              machine n m T b hn hb rounds mask seed -
            prefixedMandatoryCanonicalSelectorStructuredLowDegreePolynomial
              machine n m T b cutoff hn rounds mask seed) ^ 2) := by
                apply finiteAverage_congr
                intro seed
                rw [structuredMaskedHighDegreeTransform_eq_fixedMask_sub_low]
                rw [prefixedMandatoryCanonicalSelector_fixedMaskAveragedFunction_eq_blockProductTransform
                  machine n m T b hn hb rounds mask seed]
                rfl

/-- The prefixed sum of local component products is still a conditional mean
of a Boolean selector and therefore remains in the unit interval. -/
theorem prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform_mem_unitInterval
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    0 <= prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
        machine n m T b hn hb rounds mask seed ∧
      prefixedMandatoryCanonicalSelectorBlockProductStructuredTransform
        machine n m T b hn hb rounds mask seed <= 1 := by
  classical
  let selector :=
    (prefixedMandatoryCanonicalSelector machine n T b rounds)
      |>.ratAcceptanceIndicator
  have hfixed :=
    prefixedMandatoryCanonicalSelector_fixedMaskAveragedFunction_eq_blockProductTransform
      machine n m T b hn hb rounds mask seed
  change fixedMaskAveragedFunction selector mask
      ((structuredUnbiasedPrimitive n m hn).generate seed) = _ at hfixed
  rw [← hfixed]
  dsimp only [selector]
  constructor
  · unfold fixedMaskAveragedFunction
    apply finiteAverage_nonneg
    intro uniform
    unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  · apply le_trans (le_abs_self _)
    apply abs_fixedMaskAveragedFunction_le_one
    intro input
    unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num

end FiniteLayeredQueryProgramFamily
end
end OneTapeMagnification
end Frontier
end Pnp4
