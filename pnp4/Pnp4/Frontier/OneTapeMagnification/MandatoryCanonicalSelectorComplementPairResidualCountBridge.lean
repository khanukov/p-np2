import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalNonacceptingSelector
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorComplementBalancedResidualCountBridge
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Accepted-model pairs for the complement-balanced selector envelope

The complement-balanced envelope initially presents its second side as a
rejected-input count for the accepting mandatory selector.  When `0 < b`, the
parallel nonaccepting selector computes the exact pointwise complement, even
after an arbitrary affine prefix.  Its compatible accepted models therefore
count exactly those rejected inputs.

This file replaces the accepted/rejected presentation by a symmetric pair of
accepted-model presentations: one for the accepting selector and one for the
nonaccepting selector.  Both sides can consequently use the existing
`AcceptedModel`, accepting-walk, and last-common-prefix APIs.  All results are
exact rewrites; no numerical charge bound or selector-pair correlation bound
is proved.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open DPTWStructuredFieldCoordinatePrimitive
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorDefectiveSyndromeFrame
open MandatoryCanonicalSelectorComplementBalancedBadMaskFrame
open MandatoryCanonicalSelectorComplementBalancedResidualCountBridge

namespace MandatoryCanonicalSelectorComplementPairResidualCountBridge

/-! ## Pointwise complement and residual counts -/

/-- After the same affine prefix, the nonaccepting selector indicator is the
pointwise complement of the accepting selector indicator. -/
theorem prefixedMandatoryCanonicalNonacceptingSelector_ratAcceptanceIndicator_eq_complementFunction
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    (prefixedMandatoryCanonicalNonacceptingSelector
        machine (2 ^ n) T b rounds).ratAcceptanceIndicator =
      complementFunction
        (prefixedMandatoryCanonicalSelector
          machine n T b rounds).ratAcceptanceIndicator := by
  funext input
  unfold complementFunction
  simpa [prefixedMandatoryCanonicalSelector] using
    (prefixedMandatoryCanonicalNonacceptingSelector_ratAcceptanceIndicator_eq_one_sub
      machine (2 ^ n) T b hb rounds input)

/-- Uniform acceptance mass of the nonaccepting selector is exactly the
complement of the accepting selector's uniform mass. -/
theorem finiteAverage_prefixedMandatoryCanonicalNonacceptingSelector_eq_one_sub
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    finiteAverage
        (prefixedMandatoryCanonicalNonacceptingSelector
          machine (2 ^ n) T b rounds).ratAcceptanceIndicator =
      1 - finiteAverage
        (prefixedMandatoryCanonicalSelector
          machine n T b rounds).ratAcceptanceIndicator := by
  rw [prefixedMandatoryCanonicalNonacceptingSelector_ratAcceptanceIndicator_eq_complementFunction
    machine n T b hb rounds]
  exact finiteAverage_complementFunction _

/-- The high diagonal is the same for the accepting and nonaccepting
selectors, because complementation only negates nonconstant coefficients. -/
theorem fixedMaskHighDiagonal_prefixedMandatoryCanonicalNonacceptingSelector_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskHighDiagonal n m
        (prefixedMandatoryCanonicalNonacceptingSelector
          machine (2 ^ n) T b rounds).ratAcceptanceIndicator mask =
      fixedMaskHighDiagonal n m
        (prefixedMandatoryCanonicalSelector
          machine n T b rounds).ratAcceptanceIndicator mask := by
  rw [prefixedMandatoryCanonicalNonacceptingSelector_ratAcceptanceIndicator_eq_complementFunction
    machine n T b hb rounds]
  exact fixedMaskHighDiagonal_complementFunction _ _ _ _

/-- For every base and mask, the normalized compatible accepted-model count
of the nonaccepting selector is exactly the normalized rejected-input count
of the accepting selector.  This is the pointwise bridge that equips the
complementary side with canonical accepting models and walks. -/
theorem normalizedResidualAcceptedModelCount_prefixedNonaccepting_eq_rejectedInputCount
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (base mask : Fin (2 ^ n) -> Bool) :
    (prefixedMandatoryCanonicalNonacceptingSelector
        machine (2 ^ n) T b rounds).normalizedResidualAcceptedModelCount
          base mask =
      (prefixedMandatoryCanonicalSelector
        machine n T b rounds).normalizedResidualRejectedInputCount
          base mask := by
  let accepting := prefixedMandatoryCanonicalSelector machine n T b rounds
  let nonaccepting := prefixedMandatoryCanonicalNonacceptingSelector
    machine (2 ^ n) T b rounds
  calc
    nonaccepting.normalizedResidualAcceptedModelCount base mask =
        nonaccepting.residualAcceptedMass base mask :=
      (nonaccepting.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount
        base mask).symm
    _ = FiniteBooleanResidualMass.maskedAverage
        nonaccepting.ratAcceptanceIndicator base mask :=
      (nonaccepting.maskedAverage_ratAcceptanceIndicator_eq_residualAcceptedMass
        base mask).symm
    _ = FiniteBooleanResidualMass.maskedAverage
        (complementFunction accepting.ratAcceptanceIndicator) base mask := by
      rw [prefixedMandatoryCanonicalNonacceptingSelector_ratAcceptanceIndicator_eq_complementFunction
        machine n T b hb rounds]
    _ = 1 - FiniteBooleanResidualMass.maskedAverage
        accepting.ratAcceptanceIndicator base mask := by
      unfold FiniteBooleanResidualMass.maskedAverage complementFunction
      rw [FiniteBooleanOneRoundFoolingBound.finiteAverage_sub]
      simp
    _ = 1 - accepting.residualAcceptedMass base mask := by
      rw [accepting.maskedAverage_ratAcceptanceIndicator_eq_residualAcceptedMass]
    _ = 1 - accepting.normalizedResidualAcceptedModelCount base mask := by
      rw [accepting.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount]
    _ = accepting.normalizedResidualRejectedInputCount base mask :=
      (accepting.normalizedResidualRejectedInputCount_eq_one_sub base mask).symm

/-- Structured averaging preserves the pointwise accepted/nonaccepting versus
rejected/accepting count identity. -/
theorem finiteAverage_normalizedResidualAcceptedModelCount_prefixedNonaccepting_eq_rejectedInputCount
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (prefixedMandatoryCanonicalNonacceptingSelector
            machine (2 ^ n) T b rounds).normalizedResidualAcceptedModelCount
              ((structuredUnbiasedPrimitive n m hn).generate seed) mask) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (prefixedMandatoryCanonicalSelector
            machine n T b rounds).normalizedResidualRejectedInputCount
              ((structuredUnbiasedPrimitive n m hn).generate seed) mask) := by
  apply finiteAverage_congr
  intro seed
  exact normalizedResidualAcceptedModelCount_prefixedNonaccepting_eq_rejectedInputCount
    machine n T b hb rounds _ mask

/-! ## Symmetric accepted-model envelope -/

/-- The accepting half of the symmetric pair envelope. -/
def prefixedAcceptingSelectorPairResidualEnvelopeSide
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  let accepting := prefixedMandatoryCanonicalSelector machine n T b rounds
  finiteAverage
      (fun seed : Fin (structuredIndependence m * n) -> Bool =>
        accepting.normalizedResidualAcceptedModelCount
          ((structuredUnbiasedPrimitive n m hn).generate seed) mask) +
    finiteAverage accepting.ratAcceptanceIndicator -
    fixedMaskHighDiagonal n m accepting.ratAcceptanceIndicator mask

/-- The complementary half of the symmetric pair envelope.  Every count on
this side is now an accepted-model count of the nonaccepting selector. -/
def prefixedNonacceptingSelectorPairResidualEnvelopeSide
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  let nonaccepting := prefixedMandatoryCanonicalNonacceptingSelector
    machine (2 ^ n) T b rounds
  finiteAverage
      (fun seed : Fin (structuredIndependence m * n) -> Bool =>
        nonaccepting.normalizedResidualAcceptedModelCount
          ((structuredUnbiasedPrimitive n m hn).generate seed) mask) +
    finiteAverage nonaccepting.ratAcceptanceIndicator -
    fixedMaskHighDiagonal n m nonaccepting.ratAcceptanceIndicator mask

/-- The accepting pair side is definitionally the earlier accepted residual
side. -/
theorem prefixedAcceptingSelectorPairResidualEnvelopeSide_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    prefixedAcceptingSelectorPairResidualEnvelopeSide
        machine n T b m hn rounds mask =
      prefixedAcceptedResidualEnvelopeSide
        machine n T b m hn rounds mask := by
  rfl

/-- Under `0 < b`, the nonaccepting accepted-model side is exactly the earlier
rejected-input side, including uniform mass and high diagonal. -/
theorem prefixedNonacceptingSelectorPairResidualEnvelopeSide_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    prefixedNonacceptingSelectorPairResidualEnvelopeSide
        machine n T b m hn rounds mask =
      prefixedRejectedResidualEnvelopeSide
        machine n T b m hn rounds mask := by
  unfold prefixedNonacceptingSelectorPairResidualEnvelopeSide
    prefixedRejectedResidualEnvelopeSide
  dsimp only
  rw [finiteAverage_normalizedResidualAcceptedModelCount_prefixedNonaccepting_eq_rejectedInputCount
      machine n T b m hn hb rounds mask,
    finiteAverage_prefixedMandatoryCanonicalNonacceptingSelector_eq_one_sub
      machine n T b hb rounds,
    fixedMaskHighDiagonal_prefixedMandatoryCanonicalNonacceptingSelector_eq
      machine n T b m hb rounds mask]

/-- Exact complement-balanced envelope using only normalized accepted-model
counts of the accepting/nonaccepting selector pair. -/
theorem fixedMaskComplementBalancedEnvelope_prefixedMandatoryCanonicalSelector_eq_pairResidualCounts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskComplementBalancedEnvelope n m hn
        (prefixedMandatoryCanonicalSelector
          machine n T b rounds).ratAcceptanceIndicator mask =
      2 * min
        (prefixedAcceptingSelectorPairResidualEnvelopeSide
          machine n T b m hn rounds mask)
        (prefixedNonacceptingSelectorPairResidualEnvelopeSide
          machine n T b m hn rounds mask) := by
  rw [fixedMaskComplementBalancedEnvelope_prefixedMandatoryCanonicalSelector_eq_residualCounts]
  rw [prefixedAcceptingSelectorPairResidualEnvelopeSide_eq,
    prefixedNonacceptingSelectorPairResidualEnvelopeSide_eq
      machine n T b m hn hb rounds mask]

/-! ## Symmetric accepted-model bad charge -/

/-- Exceptional-mask charge written with accepted-model counts from the
accepting/nonaccepting selector pair.  It is only an exact definition; no
numerical upper bound is asserted. -/
def prefixedComplementPairResidualCountBadCharge
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) : Rat :=
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  badEnvelopeAverage bad (fun seed =>
    2 * min
      (prefixedAcceptingSelectorPairResidualEnvelopeSide
        machine n T b m hn rounds (mask seed))
      (prefixedNonacceptingSelectorPairResidualEnvelopeSide
        machine n T b m hn rounds (mask seed)))

/-- The earlier accepted/rejected residual-count charge is exactly the new
accepted/accepted selector-pair charge.  Thus the rewrite exposes canonical
walks on both sides without changing the quantity to be bounded. -/
theorem prefixedComplementBalancedResidualCountBadCharge_eq_pairResidualCountBadCharge
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) :
    prefixedComplementBalancedResidualCountBadCharge
        machine n T b m tailBits hn htail rounds bad =
      prefixedComplementPairResidualCountBadCharge
        machine n T b m tailBits hn htail rounds bad := by
  unfold prefixedComplementBalancedResidualCountBadCharge
    prefixedComplementPairResidualCountBadCharge
  dsimp only
  apply finiteAverage_congr
  intro seed
  by_cases hmem : seed ∈ bad
  · simp only [hmem, if_true]
    rw [prefixedAcceptingSelectorPairResidualEnvelopeSide_eq,
      prefixedNonacceptingSelectorPairResidualEnvelopeSide_eq
        machine n T b m hn hb rounds _]
  · simp [hmem]

/-- The original complement-balanced envelope charge is exactly the
accepted-model pair charge.  This is the strongest charge-level rewrite here;
it proves no estimate of that common value. -/
theorem badEnvelopeAverage_prefixedComplementBalanced_eq_pairResidualCountBadCharge
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
      prefixedComplementPairResidualCountBadCharge
        machine n T b m tailBits hn htail rounds bad := by
  dsimp only
  rw [badEnvelopeAverage_prefixedComplementBalanced_eq_residualCountBadCharge]
  exact prefixedComplementBalancedResidualCountBadCharge_eq_pairResidualCountBadCharge
    machine n T b m tailBits hn hb htail rounds bad

end MandatoryCanonicalSelectorComplementPairResidualCountBridge
end

end OneTapeMagnification
end Frontier
end Pnp4
