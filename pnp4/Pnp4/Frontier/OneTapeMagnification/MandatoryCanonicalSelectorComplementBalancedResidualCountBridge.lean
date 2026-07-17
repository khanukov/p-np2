import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorComplementBalancedBadMaskFrame
import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDResidualRejectedInputCount
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Residual-count form of the complement-balanced selector envelope

For the actual affine-prefixed mandatory selector, this file rewrites both
sides of the complement-balanced fixed-mask envelope into literal residual
counts.  The accepting side uses the structured average of the normalized
compatible accepted-model count; the complementary side uses the structured
average of the normalized compatible rejected-input count.  The remaining
terms are exactly the uniform selector mass (or its complement) and the same
high Fourier diagonal.

The exceptional-mask charge and certificate are then rewritten by exact
identities.  No estimate of either residual count, no numerical bad-charge
bound, and no small-seed selector correlation lemma is proved here.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open DPTWStructuredFieldCoordinatePrimitive
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorSyndromeFrameBridge
open MandatoryCanonicalSelectorDefectiveSyndromeFrame
open MandatoryCanonicalSelectorBadMaskResidualCountBridge
open MandatoryCanonicalSelectorComplementBalancedBadMaskFrame

namespace MandatoryCanonicalSelectorComplementBalancedResidualCountBridge

/-! ## The two literal residual-count sides -/

/-- The accepting side of the balanced envelope, written entirely with the
structured normalized accepted-model count, the uniform selector mass, and
the high Fourier diagonal. -/
def prefixedAcceptedResidualEnvelopeSide
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  finiteAverage
      (fun seed : Fin (structuredIndependence m * n) -> Bool =>
        B.normalizedResidualAcceptedModelCount
          ((structuredUnbiasedPrimitive n m hn).generate seed) mask) +
    finiteAverage B.ratAcceptanceIndicator -
    fixedMaskHighDiagonal n m B.ratAcceptanceIndicator mask

/-- The rejecting side of the balanced envelope, written entirely with the
structured normalized rejected-input count, the complement of the uniform
selector mass, and the same high Fourier diagonal. -/
def prefixedRejectedResidualEnvelopeSide
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  finiteAverage
      (fun seed : Fin (structuredIndependence m * n) -> Bool =>
        B.normalizedResidualRejectedInputCount
          ((structuredUnbiasedPrimitive n m hn).generate seed) mask) +
    (1 - finiteAverage B.ratAcceptanceIndicator) -
    fixedMaskHighDiagonal n m B.ratAcceptanceIndicator mask

/-- The structured complement of the selector mass is exactly the
structured normalized rejected-input count. -/
theorem one_sub_fixedMaskStructuredBaseMass_prefixedMandatoryCanonicalSelector_eq_rejectedCount
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    1 - fixedMaskStructuredBaseMass n m hn
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
          mask =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (prefixedMandatoryCanonicalSelector machine n T b rounds).normalizedResidualRejectedInputCount
              ((structuredUnbiasedPrimitive n m hn).generate seed) mask) := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  rw [fixedMaskStructuredBaseMass_prefixedMandatoryCanonicalSelector_eq]
  exact (B.fixedMaskStructuredAverage_normalizedResidualRejectedInputCount_eq_one_sub
    n m hn mask).symm

/-- The direct side of the complement-balanced envelope is exactly the
accepted residual-count side. -/
theorem prefixedAcceptedResidualEnvelopeSide_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskStructuredBaseMass n m hn
          ((prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator)
          mask +
        finiteAverage
          ((prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator) -
        fixedMaskHighDiagonal n m
          ((prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator) mask =
      prefixedAcceptedResidualEnvelopeSide
        machine n T b m hn rounds mask := by
  unfold prefixedAcceptedResidualEnvelopeSide
  dsimp only
  rw [fixedMaskStructuredBaseMass_prefixedMandatoryCanonicalSelector_eq]

/-- The complementary side of the complement-balanced envelope is exactly
the rejected residual-count side. -/
theorem prefixedRejectedResidualEnvelopeSide_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    (1 - fixedMaskStructuredBaseMass n m hn
          ((prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator)
          mask) +
        (1 - finiteAverage
          ((prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator)) -
        fixedMaskHighDiagonal n m
          ((prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator) mask =
      prefixedRejectedResidualEnvelopeSide
        machine n T b m hn rounds mask := by
  unfold prefixedRejectedResidualEnvelopeSide
  dsimp only
  rw [one_sub_fixedMaskStructuredBaseMass_prefixedMandatoryCanonicalSelector_eq_rejectedCount]

/-- Exact residual-count expression for the whole complement-balanced
fixed-mask envelope.  This is an identity, not an upper bound on either side. -/
theorem fixedMaskComplementBalancedEnvelope_prefixedMandatoryCanonicalSelector_eq_residualCounts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    fixedMaskComplementBalancedEnvelope n m hn
        ((prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator) mask =
      2 * min
        (prefixedAcceptedResidualEnvelopeSide
          machine n T b m hn rounds mask)
        (prefixedRejectedResidualEnvelopeSide
          machine n T b m hn rounds mask) := by
  unfold fixedMaskComplementBalancedEnvelope
  dsimp only
  rw [prefixedAcceptedResidualEnvelopeSide_eq,
    prefixedRejectedResidualEnvelopeSide_eq]

/-- The accepted and rejected sides partition the two unit masses and retain
two copies of the same diagonal.  This exact conservation identity is useful
when analyzing which side realizes the minimum. -/
theorem prefixedAcceptedResidualEnvelopeSide_add_rejected_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (mask : Fin (2 ^ n) -> Bool) :
    prefixedAcceptedResidualEnvelopeSide
          machine n T b m hn rounds mask +
        prefixedRejectedResidualEnvelopeSide
          machine n T b m hn rounds mask =
      2 - 2 * fixedMaskHighDiagonal n m
        ((prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator) mask := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  unfold prefixedAcceptedResidualEnvelopeSide
    prefixedRejectedResidualEnvelopeSide
  dsimp only
  rw [B.fixedMaskStructuredAverage_normalizedResidualRejectedInputCount_eq_one_sub
    n m hn mask]
  ring

/-! ## Exact exceptional-mask charge -/

/-- The literal residual-count charge carried by an exceptional set of mask
seeds.  This definition records the quantity still requiring a machine-
specific estimate; it asserts no numerical bound. -/
def prefixedComplementBalancedResidualCountBadCharge
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) : Rat :=
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  badEnvelopeAverage bad (fun seed =>
    2 * min
      (prefixedAcceptedResidualEnvelopeSide
        machine n T b m hn rounds (mask seed))
      (prefixedRejectedResidualEnvelopeSide
        machine n T b m hn rounds (mask seed)))

/-- The original balanced bad-envelope average and the literal residual-count
bad charge are exactly equal.  In particular, moving to count language loses
no diagonal term and performs no relaxation. -/
theorem badEnvelopeAverage_prefixedComplementBalanced_eq_residualCountBadCharge
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) :
    let B := prefixedMandatoryCanonicalSelector machine n T b rounds
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    badEnvelopeAverage bad (fun seed =>
        fixedMaskComplementBalancedEnvelope n m hn
          B.ratAcceptanceIndicator (mask seed)) =
      prefixedComplementBalancedResidualCountBadCharge
        machine n T b m tailBits hn htail rounds bad := by
  dsimp only
  unfold prefixedComplementBalancedResidualCountBadCharge
  dsimp only
  apply finiteAverage_congr
  intro seed
  by_cases hmem : seed ∈ bad
  · simp only [hmem, if_true]
    exact fixedMaskComplementBalancedEnvelope_prefixedMandatoryCanonicalSelector_eq_residualCounts
      machine n T b m hn rounds _
  · simp [hmem]

/-! ## Count-form certificate -/

/-- The complement-balanced good/bad certificate with its exceptional charge
written in literal accepted/rejected residual-count language.  This remains a
conditional certificate: this file does not establish its budget inequality. -/
def PrefixedMandatoryCanonicalSelectorComplementBalancedResidualCountCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) : Prop :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  (forall seed, seed ∉ bad ->
      p * fixedMaskSyndromeEnergy n m hn
          B.ratAcceptanceIndicator (mask seed) <=
        fixedMaskHighDiagonal n m B.ratAcceptanceIndicator (mask seed)) /\
    structuredMaskedHighDiagonalAverage
        n m tailBits (2 * m) hn htail B.ratAcceptanceIndicator +
      p * prefixedComplementBalancedResidualCountBadCharge
        machine n T b m tailBits hn htail rounds bad <=
        p ^ (2 * m + 1)

/-- The count-form certificate is exactly the existing complement-balanced
certificate.  This equivalence is non-circular: neither side assumes the
residual-mass `L2` target, and no numerical estimate is introduced. -/
theorem prefixedComplementBalancedResidualCountCertificate_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n))) :
    PrefixedMandatoryCanonicalSelectorComplementBalancedResidualCountCertificate
        machine n T b m tailBits hn htail rounds bad <->
      PrefixedMandatoryCanonicalSelectorComplementBalancedBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  unfold PrefixedMandatoryCanonicalSelectorComplementBalancedResidualCountCertificate
    PrefixedMandatoryCanonicalSelectorComplementBalancedBadMaskCertificate
    StructuredComplementBalancedBadMaskFrameCertificate
  dsimp only
  have hcharge :=
    badEnvelopeAverage_prefixedComplementBalanced_eq_residualCountBadCharge
      machine n T b m tailBits hn htail rounds bad
  dsimp only at hcharge
  rw [hcharge]

end MandatoryCanonicalSelectorComplementBalancedResidualCountBridge
end

end OneTapeMagnification
end Frontier
end Pnp4
