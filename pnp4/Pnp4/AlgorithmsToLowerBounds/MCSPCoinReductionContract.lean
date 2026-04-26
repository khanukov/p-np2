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
Build the half-vs-fair reduction contract from probability-mass bounds for the
proof-level tree-MCSP predicate itself.

This is the next decomposition layer below `of_distributionFacts`: downstream
counting or concentration arguments should now target the mass of
`treeMCSPPredicateDecision`, not the exact decision wrapper.
-/
def HalfVsFairMCSPCoinReductionContract.of_treeMCSPPredicateMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_mass_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_mass_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (treeMCSPPredicateDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinReductionContract hardness :=
  HalfVsFairMCSPCoinReductionContract.of_distributionFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    (fun n =>
      acceptanceProbability_exactTreeMCSPThresholdDecision_le_of_treeMCSPPredicateDecision_bound
        (n := n)
        (threshold := threshold n)
        (bias := (hardness.instance n).lowBias)
        (q := lowAcceptanceUpper n)
        (hardness.instance n).low_nonneg
        (hardness.instance n).low_le_one
        (low_mass_le n))
    (fun n =>
      treeMCSPPredicateDecision_bound_le_acceptanceProbability_exactTreeMCSPThresholdDecision
        (n := n)
        (threshold := threshold n)
        (bias := (hardness.instance n).highBias)
        (q := fairAcceptanceLower n)
        (hardness.instance n).high_nonneg
        (hardness.instance n).high_le_one
        (fair_mass_ge n))
    advantage_gap

/--
In the half-vs-fair regime, `highBias` is the fair side `1 / 2`.  Therefore the
Shannon-counting upper bound applies directly to the `highBias` mass of
low-tree-complexity truth tables.
-/
theorem halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    acceptanceProbability (hardness.instance n).highBias
        (treeMCSPPredicateDecision n threshold) ≤
      (Pnp3.Models.circuitCountBound n threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) := by
  simpa [HalfVsFairTruthTableCoinHardness.instance, halfVsFairCoinInstance] using
    fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio n threshold

/--
Convenience form: if the Shannon-counting ratio is bounded by `q`, then the
fair-side mass of low-tree-complexity truth tables is at most `q`.
-/
theorem halfVsFair_highBias_treeMCSPPredicateDecision_le_of_countRatio_le
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hRatio :
      (Pnp3.Models.circuitCountBound n threshold : Rat) /
          (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) ≤ q) :
    acceptanceProbability (hardness.instance n).highBias
        (treeMCSPPredicateDecision n threshold) ≤ q :=
  le_trans
    (halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio
      (hardness := hardness) n threshold)
    hRatio

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
