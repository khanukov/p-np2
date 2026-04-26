import Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound
import Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
MCSP-to-coin reduction witness specialized to the paper-facing half-vs-fair
regime on truth-table inputs.
-/
abbrev HalfVsFairMCSPCoinReductionWitness
    (hardness : HalfVsFairTruthTableCoinHardness)
    (n : Nat) : Type :=
  MCSPCoinReductionWitness
    n
    (((1 : Rat) - hardness.biasGap n) / 2)
    ((1 : Rat) / 2)
    (halfVsFair_lowBias_nonneg (hardness.biasGap_le_one n))
    (by norm_num)
    (halfVsFair_lowBias_lt_fair (hardness.biasGap_pos n))
    (hardness.advantage n)

/--
Acceptance-profile contract for the MCSP-to-coin reduction on truth-table
inputs.

This splits the statistical obligation into falsifiable pieces: an upper bound
on low-bias acceptance, a lower bound on fair-coin acceptance, and a certificate
that those two bounds leave at least the requested advantage gap.
-/
structure HalfVsFairMCSPCoinAcceptanceProfile
    (hardness : HalfVsFairTruthTableCoinHardness) where
  threshold : Nat → Nat
  lowAcceptanceUpper : Nat → Rat
  fairAcceptanceLower : Nat → Rat
  low_acceptance_le :
    ∀ n : Nat,
      acceptanceProbability (hardness.instance n).lowBias
          (exactTreeMCSPThresholdDecision n (threshold n)) ≤
        lowAcceptanceUpper n
  fair_acceptance_ge :
    ∀ n : Nat,
      fairAcceptanceLower n ≤
        acceptanceProbability (hardness.instance n).highBias
          (exactTreeMCSPThresholdDecision n (threshold n))
  advantage_gap :
    ∀ n : Nat,
      hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n

/--
The decomposed acceptance-profile contract implies the original monolithic
coin-solving statement.
-/
theorem HalfVsFairMCSPCoinAcceptanceProfile.exact_solvesCoin
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinAcceptanceProfile hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (profile.threshold n))
      (hardness.advantage n) := by
  exact solvesCoinProblem_of_acceptanceProbability_bounds
    (inst := hardness.instance n)
    (A := exactTreeMCSPThresholdDecision n (profile.threshold n))
    (adv := hardness.advantage n)
    (lowAcceptanceUpper := profile.lowAcceptanceUpper n)
    (highAcceptanceLower := profile.fairAcceptanceLower n)
    (profile.low_acceptance_le n)
    (profile.fair_acceptance_ge n)
    (profile.advantage_gap n)

/--
Smaller theorem-facing contract for the MCSP-to-coin reduction on truth-table
inputs.

Instead of carrying an arbitrary threshold oracle for each slice, this packages
exactly the threshold schedule together with the decomposed acceptance profile
that proves the corresponding exact thresholded tree-MCSP decision function
solves the half-vs-fair coin problem.
-/
structure HalfVsFairMCSPCoinReductionContract
    (hardness : HalfVsFairTruthTableCoinHardness)
    extends HalfVsFairMCSPCoinAcceptanceProfile hardness

/--
Named constructor for the MCSP-side half-vs-fair reduction contract from the
three distribution facts that remain after the exact threshold predicate is
fixed.
-/
def HalfVsFairMCSPCoinReductionContract.of_distributionFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_acceptance_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (exactTreeMCSPThresholdDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_acceptance_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (exactTreeMCSPThresholdDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinReductionContract hardness where
  threshold := threshold
  lowAcceptanceUpper := lowAcceptanceUpper
  fairAcceptanceLower := fairAcceptanceLower
  low_acceptance_le := low_acceptance_le
  fair_acceptance_ge := fair_acceptance_ge
  advantage_gap := advantage_gap

/--
Recover the original monolithic coin-solving statement from the decomposed
reduction contract.
-/
theorem HalfVsFairMCSPCoinReductionContract.exact_solvesCoin
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (contract.threshold n))
      (hardness.advantage n) :=
  contract.toHalfVsFairMCSPCoinAcceptanceProfile.exact_solvesCoin n

/--
Exact thresholded MCSP language attached to one half-vs-fair reduction
contract.
-/
noncomputable def halfVsFairMCSPCoinLanguage
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) : BitVecLanguage :=
  exactTreeMCSPThresholdLanguage n (contract.threshold n)

/--
Pointwise lower-bound schedule attached to one half-vs-fair reduction contract.

The reduction contract fixes only the thresholded language; the forbidden size
bound still comes from the target-class lower-bound contract.
-/
def halfVsFairMCSPCoinLowerBound
    {hardness : HalfVsFairTruthTableCoinHardness}
    (_contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n maxSize : Nat) : Nat → Nat :=
  exactTreeMCSPThresholdLowerBound n maxSize

/--
Read the smaller theorem-facing reduction contract back as the older witness
package expected by the first-layer `AC0[p]` route.
-/
noncomputable def HalfVsFairMCSPCoinReductionContract.toWitness
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    HalfVsFairMCSPCoinReductionWitness hardness n where
  oracle := {
    threshold := contract.threshold n
    decide := exactTreeMCSPThresholdDecision n (contract.threshold n)
    correct := exactTreeMCSPThresholdDecision_spec
  }
  solvesCoin := contract.exact_solvesCoin n

/-- The witness reconstructed from the smaller contract has the expected threshold. -/
@[simp] theorem HalfVsFairMCSPCoinReductionContract.toWitness_threshold
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    (contract.toWitness n).oracle.threshold = contract.threshold n :=
  rfl

/-- The witness reconstructed from the smaller contract uses the exact slice decision. -/
@[simp] theorem HalfVsFairMCSPCoinReductionContract.toWitness_decide
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    (contract.toWitness n).oracle.decide =
      exactTreeMCSPThresholdDecision n (contract.threshold n) :=
  rfl

end AlgorithmsToLowerBounds
end Pnp4
