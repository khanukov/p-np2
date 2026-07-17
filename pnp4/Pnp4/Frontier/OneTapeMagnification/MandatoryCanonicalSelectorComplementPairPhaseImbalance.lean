import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorComplementPairResidualCountBridge
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Phase imbalance for the accepting/nonaccepting selector pair

The complement-balanced exceptional-mask charge is the minimum of two
positive residual-count sides.  This file keeps the cancellation between the
two canonical selector families explicit.  Their residual phase imbalance is
the structured average of

```text
  accepting compatible-model mass - nonaccepting compatible-model mass
```

plus the analogous signed uniform selector mass.  The complete balanced
envelope is exactly

```text
  2 - 2 * highDiagonal - |residualPhaseImbalance|.
```

Thus the absolute value is taken only after the accepting and nonaccepting
outer families have been aggregated.  No absolute value is inserted at the
component, cell, model, or dual-word level.  The exceptional-mask charge and
certificate are rewritten into this phase-preserving form by exact
equalities.  This file proves no numerical estimate of the resulting charge.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open DPTWStructuredFieldCoordinatePrimitive
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorSyndromeFrameBridge
open MandatoryCanonicalSelectorDefectiveSyndromeFrame
open MandatoryCanonicalSelectorComplementBalancedBadMaskFrame
open MandatoryCanonicalSelectorComplementBalancedResidualCountBridge
open MandatoryCanonicalSelectorComplementPairResidualCountBridge

namespace MandatoryCanonicalSelectorComplementPairPhaseImbalance

/-! ## Signed outer aggregation at one mask -/

/-- The signed residual phase of the accepting/nonaccepting selector pair.
Both differences are formed pointwise before their outer finite averages.
Consequently this definition retains cancellation across all canonical
accepted models of the two selector families. -/
def prefixedComplementPairResidualPhaseImbalance
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  let accepting := prefixedMandatoryCanonicalSelector machine n T b rounds
  let nonaccepting := prefixedMandatoryCanonicalNonacceptingSelector
    machine (2 ^ n) T b rounds
  finiteAverage
      (fun seed : Fin (structuredIndependence m * n) -> Bool =>
        accepting.normalizedResidualAcceptedModelCount
            ((structuredUnbiasedPrimitive n m hn).generate seed) mask -
          nonaccepting.normalizedResidualAcceptedModelCount
            ((structuredUnbiasedPrimitive n m hn).generate seed) mask) +
    finiteAverage (fun input =>
      accepting.ratAcceptanceIndicator input -
        nonaccepting.ratAcceptanceIndicator input)

/-- The signed residual phase is exactly the difference of the two symmetric
envelope sides.  The common high diagonal cancels only after using the exact
selector-complement theorem. -/
theorem prefixedAcceptingSelectorPairResidualEnvelopeSide_sub_nonaccepting_eq_phaseImbalance
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    prefixedAcceptingSelectorPairResidualEnvelopeSide
          machine n T b m hn rounds mask -
        prefixedNonacceptingSelectorPairResidualEnvelopeSide
          machine n T b m hn rounds mask =
      prefixedComplementPairResidualPhaseImbalance
        machine n T b m hn rounds mask := by
  unfold prefixedAcceptingSelectorPairResidualEnvelopeSide
    prefixedNonacceptingSelectorPairResidualEnvelopeSide
    prefixedComplementPairResidualPhaseImbalance
  dsimp only
  rw [FiniteBooleanOneRoundFoolingBound.finiteAverage_sub,
    FiniteBooleanOneRoundFoolingBound.finiteAverage_sub,
    fixedMaskHighDiagonal_prefixedMandatoryCanonicalNonacceptingSelector_eq
      machine n T b m hb rounds mask]
  ring

/-- The two selector-pair sides conserve the total residual mass. -/
theorem prefixedAcceptingSelectorPairResidualEnvelopeSide_add_nonaccepting_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    prefixedAcceptingSelectorPairResidualEnvelopeSide
          machine n T b m hn rounds mask +
        prefixedNonacceptingSelectorPairResidualEnvelopeSide
          machine n T b m hn rounds mask =
      2 - 2 * fixedMaskHighDiagonal n m
        (prefixedMandatoryCanonicalSelector
          machine n T b rounds).ratAcceptanceIndicator mask := by
  rw [prefixedAcceptingSelectorPairResidualEnvelopeSide_eq,
    prefixedNonacceptingSelectorPairResidualEnvelopeSide_eq
      machine n T b m hn hb rounds mask]
  exact prefixedAcceptedResidualEnvelopeSide_add_rejected_eq
    machine n T b m hn rounds mask

/-- The minimum of the two positive sides is the conserved total minus the
absolute value of their signed outer phase.  In particular, no triangle
inequality over either selector family is used. -/
theorem two_mul_min_prefixedComplementPairResidualEnvelopeSides_eq_phaseImbalance
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    2 * min
        (prefixedAcceptingSelectorPairResidualEnvelopeSide
          machine n T b m hn rounds mask)
        (prefixedNonacceptingSelectorPairResidualEnvelopeSide
          machine n T b m hn rounds mask) =
      2 - 2 * fixedMaskHighDiagonal n m
          (prefixedMandatoryCanonicalSelector
            machine n T b rounds).ratAcceptanceIndicator mask -
        |prefixedComplementPairResidualPhaseImbalance
          machine n T b m hn rounds mask| := by
  let left := prefixedAcceptingSelectorPairResidualEnvelopeSide
    machine n T b m hn rounds mask
  let right := prefixedNonacceptingSelectorPairResidualEnvelopeSide
    machine n T b m hn rounds mask
  have hsum : left + right =
      2 - 2 * fixedMaskHighDiagonal n m
        (prefixedMandatoryCanonicalSelector
          machine n T b rounds).ratAcceptanceIndicator mask := by
    exact prefixedAcceptingSelectorPairResidualEnvelopeSide_add_nonaccepting_eq
      machine n T b m hn hb rounds mask
  have hsub : left - right =
      prefixedComplementPairResidualPhaseImbalance
        machine n T b m hn rounds mask := by
    exact prefixedAcceptingSelectorPairResidualEnvelopeSide_sub_nonaccepting_eq_phaseImbalance
      machine n T b m hn hb rounds mask
  have hmin : 2 * min left right = left + right - |left - right| := by
    by_cases hle : left <= right
    · rw [min_eq_left hle, abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    · have hright : right <= left := (lt_of_not_ge hle).le
      rw [min_eq_right hright, abs_of_nonneg (sub_nonneg.mpr hright)]
      ring
  rw [hmin, hsum, hsub]

/-- Exact phase-preserving form of the actual complement-balanced fixed-mask
envelope. -/
theorem fixedMaskComplementBalancedEnvelope_prefixedMandatoryCanonicalSelector_eq_phaseImbalance
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskComplementBalancedEnvelope n m hn
        (prefixedMandatoryCanonicalSelector
          machine n T b rounds).ratAcceptanceIndicator mask =
      2 - 2 * fixedMaskHighDiagonal n m
          (prefixedMandatoryCanonicalSelector
            machine n T b rounds).ratAcceptanceIndicator mask -
        |prefixedComplementPairResidualPhaseImbalance
          machine n T b m hn rounds mask| := by
  rw [fixedMaskComplementBalancedEnvelope_prefixedMandatoryCanonicalSelector_eq_pairResidualCounts
    machine n T b m hn hb rounds mask]
  exact two_mul_min_prefixedComplementPairResidualEnvelopeSides_eq_phaseImbalance
    machine n T b m hn hb rounds mask

/-! ## Exceptional-mask phase charge -/

/-- The exceptional-mask charge with the accepting/nonaccepting cancellation
performed before the single absolute value.  This definition is an exact
target, not a numerical bound. -/
def prefixedComplementPairPhaseImbalanceBadCharge
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) : Rat :=
  let accepting := prefixedMandatoryCanonicalSelector machine n T b rounds
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  badEnvelopeAverage bad (fun seed =>
    2 - 2 * fixedMaskHighDiagonal n m
        accepting.ratAcceptanceIndicator (mask seed) -
      |prefixedComplementPairResidualPhaseImbalance
        machine n T b m hn rounds (mask seed)|)

/-- The residual-count pair charge is exactly its signed phase-imbalance
form. -/
theorem prefixedComplementPairResidualCountBadCharge_eq_phaseImbalanceBadCharge
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) :
    prefixedComplementPairResidualCountBadCharge
        machine n T b m tailBits hn htail rounds bad =
      prefixedComplementPairPhaseImbalanceBadCharge
        machine n T b m tailBits hn htail rounds bad := by
  unfold prefixedComplementPairResidualCountBadCharge
    prefixedComplementPairPhaseImbalanceBadCharge
  dsimp only
  apply finiteAverage_congr
  intro seed
  by_cases hmem : seed ∈ bad
  · simp only [hmem, if_true]
    exact two_mul_min_prefixedComplementPairResidualEnvelopeSides_eq_phaseImbalance
      machine n T b m hn hb rounds _
  · simp [hmem]

/-- The original balanced exceptional-mask charge is exactly the outer
phase-imbalance charge. -/
theorem badEnvelopeAverage_prefixedComplementBalanced_eq_phaseImbalanceBadCharge
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) :
    let accepting := prefixedMandatoryCanonicalSelector machine n T b rounds
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    badEnvelopeAverage bad (fun seed =>
        fixedMaskComplementBalancedEnvelope n m hn
          accepting.ratAcceptanceIndicator (mask seed)) =
      prefixedComplementPairPhaseImbalanceBadCharge
        machine n T b m tailBits hn htail rounds bad := by
  dsimp only
  rw [badEnvelopeAverage_prefixedComplementBalanced_eq_pairResidualCountBadCharge
    machine n T b m tailBits hn hb htail rounds bad]
  exact prefixedComplementPairResidualCountBadCharge_eq_phaseImbalanceBadCharge
    machine n T b m tailBits hn hb htail rounds bad

/-! ## Equivalent phase certificate -/

/-- The complement-balanced certificate with its bad-mask budget written as
one signed accepting/nonaccepting outer phase.  The good-mask condition is
unchanged. -/
def PrefixedMandatoryCanonicalSelectorComplementPairPhaseImbalanceCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) : Prop :=
  let accepting := prefixedMandatoryCanonicalSelector machine n T b rounds
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  (forall seed, seed ∉ bad ->
      p * fixedMaskSyndromeEnergy n m hn
          accepting.ratAcceptanceIndicator (mask seed) <=
        fixedMaskHighDiagonal n m
          accepting.ratAcceptanceIndicator (mask seed)) /\
    structuredMaskedHighDiagonalAverage
        n m tailBits (2 * m) hn htail accepting.ratAcceptanceIndicator +
      p * prefixedComplementPairPhaseImbalanceBadCharge
        machine n T b m tailBits hn htail rounds bad <=
        p ^ (2 * m + 1)

/-- The phase-imbalance certificate is exactly the complement-balanced
certificate.  Hence it isolates the same unresolved numerical obligation
without assuming the desired residual-mass bound. -/
theorem prefixedComplementPairPhaseImbalanceCertificate_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) :
    PrefixedMandatoryCanonicalSelectorComplementPairPhaseImbalanceCertificate
        machine n T b m tailBits hn htail rounds bad <->
      PrefixedMandatoryCanonicalSelectorComplementBalancedBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad := by
  unfold PrefixedMandatoryCanonicalSelectorComplementPairPhaseImbalanceCertificate
    PrefixedMandatoryCanonicalSelectorComplementBalancedBadMaskCertificate
    StructuredComplementBalancedBadMaskFrameCertificate
  dsimp only
  have hcharge :=
    badEnvelopeAverage_prefixedComplementBalanced_eq_phaseImbalanceBadCharge
      machine n T b m tailBits hn hb htail rounds bad
  dsimp only at hcharge
  rw [hcharge]

end MandatoryCanonicalSelectorComplementPairPhaseImbalance
end

end OneTapeMagnification
end Frontier
end Pnp4
