import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualBlockProductSyndromeTransform
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorFourierFactorization
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPrefixedFourierFactorization
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Actual fixed-alpha syndrome leakage identity

The generic structured syndrome transform is instantiated here on one actual
mandatory canonical-alpha component.  The installed chaining and input-
monotonicity facts discharge locality and pairwise support disjointness for
its genuine block-projection factors.

The resulting theorem is an exact identity: the component's squared
high-degree syndrome-fiber energy is the structured-seed average of a local
block product minus its explicit low-degree polynomial.  No leakage bound is
assumed or proved here.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanRestrictionMoment
open FiniteBooleanAffineRoundsLocality
open DPTWStructuredFieldCoordinatePrimitive
open FiniteStructuredDualSyndromeFiberBlocks
open FiniteStructuredDualNonzeroSeedCorrelation
open FiniteStructuredDualBlockProductSyndromeTransform

namespace FiniteLayeredQueryProgramFamily

local instance cachedInputMachineStateDecidableEqForComponentSyndromeLeakage
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- The structured transform of one genuine canonical block projection at a
fixed mask and structured seed. -/
def mandatoryCanonicalBlockProjectionStructuredTransform
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b : Nat) (hn : 0 < n) (hb : 0 < b)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool)
    (block : Fin (T / b + 1)) : Rat :=
  fixedMaskAveragedFunction
    (finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
      machine hb index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1)
        block)
    mask ((structuredUnbiasedPrimitive n m hn).generate seed)

/-- The low-degree polynomial of the actual installed fixed-alpha component.
It is retained explicitly in the leakage identity. -/
def mandatoryCanonicalComponentStructuredLowDegreePolynomial
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b cutoff : Nat) (hn : 0 < n)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) : Rat :=
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily
    machine (2 ^ n) T b
  structuredMaskedLowDegreePolynomial n m cutoff hn
    (family.ratComponentAcceptanceIndicator index) mask seed

/-- **Exact actual fixed-alpha leakage identity.**

All factors and supports are those of the installed mandatory canonical
component.  Its static chaining and input-monotonicity theorems discharge the
generic disjoint-product premises, so the only remaining mathematical task
is to bound the displayed product-minus-low expression. -/
theorem mandatoryCanonicalComponent_syndromeFiberEnergy_eq_average_blockProduct_sub_low_sq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b cutoff : Nat) (hn : 0 < n) (hb : 0 < b)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (mask : Fin (2 ^ n) -> Bool) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily
      machine (2 ^ n) T b
    (∑ syndrome : StructuredDualPowerSyndrome n m,
      (structuredSyndromeFiberCoefficientSum n m cutoff hn
        (family.ratComponentAcceptanceIndicator index)
        mask syndrome) ^ 2) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          ((∏ block : Fin (T / b + 1),
              mandatoryCanonicalBlockProjectionStructuredTransform
                machine n m T b hn hb index mask seed block) -
            mandatoryCanonicalComponentStructuredLowDegreePolynomial
              machine n m T b cutoff hn index mask seed) ^ 2) := by
  classical
  dsimp only
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily
    machine (2 ^ n) T b
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let blockSupport : Fin (T / b + 1) -> Finset (Fin (2 ^ n)) :=
    fun block =>
      finiteCachedTimedScheduleBlockQuerySupport (2 ^ n) scheduled block
  let blockFactor : Fin (T / b + 1) ->
      (Fin (2 ^ n) -> Bool) -> Rat :=
    fun block =>
      finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
        machine hb index.1 scheduled block
  have hfunction : family.ratComponentAcceptanceIndicator index =
      fun input => ∏ block ∈ (Finset.univ : Finset (Fin (T / b + 1))),
        blockFactor block input := by
    funext input
    simpa [family, scheduled, blockFactor] using
      (mandatoryCanonical_ratComponentAcceptanceIndicator_eq_blockProjectionProduct_fin
        machine (2 ^ n) T b hb index input)
  have hgeneric :=
    syndromeFiberEnergy_disjointProduct_eq_average_prod_sub_low_sq
      n m cutoff hn
      (Finset.univ : Finset (Fin (T / b + 1)))
      blockSupport blockFactor
      (by
        intro block _hblock
        exact
          finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor_dependsOnlyOn
            machine hb index.1 scheduled block)
      (by
        intro left _hleft right _hright hne
        exact finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
          scheduled
          (builtRejectingGuardedCanonicalIndex_chained machine index)
          (builtRejectingGuardedCanonicalIndexMonotone machine index) hne)
      mask
  rw [← hfunction] at hgeneric
  simpa [mandatoryCanonicalBlockProjectionStructuredTransform,
    mandatoryCanonicalComponentStructuredLowDegreePolynomial,
    family, scheduled, blockSupport, blockFactor] using hgeneric

/-- The structured transform of one genuine canonical block projection after
the same fixed affine prefix is applied to every block factor. -/
def prefixedMandatoryCanonicalBlockProjectionStructuredTransform
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool)
    (block : Fin (T / b + 1)) : Rat :=
  fixedMaskAveragedFunction
    (fun input =>
      finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
        machine hb index.1
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1)
          block (applyAffineRestrictionRounds rounds input))
    mask ((structuredUnbiasedPrimitive n m hn).generate seed)

/-- The explicit low-degree polynomial of the actual prefixed fixed-alpha
component. -/
def prefixedMandatoryCanonicalComponentStructuredLowDegreePolynomial
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b cutoff : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) : Rat :=
  structuredMaskedLowDegreePolynomial n m cutoff hn
    (prefixedMandatoryCanonicalComponentIndicator
      machine (2 ^ n) T b rounds index) mask seed

/-- Prefix-stable form of the exact actual fixed-alpha leakage identity.
Coordinatewise affine restriction rounds preserve each advertised dependency
support, so no additional locality or disjointness premise is required. -/
theorem prefixedMandatoryCanonicalComponent_syndromeFiberEnergy_eq_average_blockProduct_sub_low_sq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n m T b cutoff : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (mask : Fin (2 ^ n) -> Bool) :
    (∑ syndrome : StructuredDualPowerSyndrome n m,
      (structuredSyndromeFiberCoefficientSum n m cutoff hn
        (prefixedMandatoryCanonicalComponentIndicator
          machine (2 ^ n) T b rounds index)
        mask syndrome) ^ 2) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          ((∏ block : Fin (T / b + 1),
              prefixedMandatoryCanonicalBlockProjectionStructuredTransform
                machine n m T b hn hb rounds index mask seed block) -
            prefixedMandatoryCanonicalComponentStructuredLowDegreePolynomial
              machine n m T b cutoff hn rounds index mask seed) ^ 2) := by
  classical
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let blockSupport : Fin (T / b + 1) -> Finset (Fin (2 ^ n)) :=
    fun block =>
      finiteCachedTimedScheduleBlockQuerySupport (2 ^ n) scheduled block
  let blockFactor : Fin (T / b + 1) ->
      (Fin (2 ^ n) -> Bool) -> Rat :=
    fun block input =>
      finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
        machine hb index.1 scheduled block
          (applyAffineRestrictionRounds rounds input)
  have hfunction :
      prefixedMandatoryCanonicalComponentIndicator
          machine (2 ^ n) T b rounds index =
        fun input => ∏ block ∈
            (Finset.univ : Finset (Fin (T / b + 1))),
          blockFactor block input := by
    funext input
    simpa [scheduled, blockFactor] using
      (prefixedMandatoryCanonicalComponentIndicator_eq_blockProjectionProduct
        machine (2 ^ n) T b hb rounds index input)
  have hgeneric :=
    syndromeFiberEnergy_disjointProduct_eq_average_prod_sub_low_sq
      n m cutoff hn
      (Finset.univ : Finset (Fin (T / b + 1)))
      blockSupport blockFactor
      (by
        intro block _hblock
        exact dependsOnlyOn_applyAffineRestrictionRounds
          (finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor_dependsOnlyOn
            machine hb index.1 scheduled block)
          rounds)
      (by
        intro left _hleft right _hright hne
        exact finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
          scheduled
          (builtRejectingGuardedCanonicalIndex_chained machine index)
          (builtRejectingGuardedCanonicalIndexMonotone machine index) hne)
      mask
  rw [← hfunction] at hgeneric
  simpa [prefixedMandatoryCanonicalBlockProjectionStructuredTransform,
    prefixedMandatoryCanonicalComponentStructuredLowDegreePolynomial,
    scheduled, blockSupport, blockFactor] using hgeneric

end FiniteLayeredQueryProgramFamily
end
end OneTapeMagnification
end Frontier
end Pnp4
