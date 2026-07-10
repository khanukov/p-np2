import Pnp4.Frontier.OneTapeMagnification.LocalHSGToMCSP
import Pnp4.Frontier.OneTapeMagnification.WeightedPRGSupport

/-!
# From signed weighted approximation to dense hitting

`WeightedPRGSupport` proves the support principle for an arbitrary Boolean
predicate.  This file instantiates it with bounded-time deterministic
one-tape acceptance and discharges the finite density arithmetic used by
`LocalHSGToMCSP`.

The acceptance proposition need not carry a computable decision procedure in
this layer.  Its Boolean indicator is therefore declared `noncomputable` and
uses classical decidability.  This is harmless for the finite averaging
argument, but it does not claim an executable PRG test or construct the
missing weighted generator.
-/

open scoped BigOperators

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open StreamingMagnification
open StreamingMagnification.TotalSearch

/-- Classical Boolean indicator of bounded-time deterministic acceptance. -/
noncomputable def deterministicTableAcceptanceIndicator
    (machine : DeterministicMachine) {n : Nat} (steps : Nat)
    (table : TruthTable n) : Bool :=
  @ite Bool (deterministicTableAcceptance machine steps table)
    (Classical.propDecidable _) true false

@[simp]
theorem deterministicTableAcceptanceIndicator_eq_true_iff
    (machine : DeterministicMachine) {n : Nat} (steps : Nat)
    (table : TruthTable n) :
    deterministicTableAcceptanceIndicator machine (n := n) steps table = true ↔
      deterministicTableAcceptance machine steps table := by
  classical
  simp [deterministicTableAcceptanceIndicator]

/-- A propositionally dense accepting set has Boolean uniform average
strictly above one half.  The denominator is the exact nonzero cardinality
`2^(2^n)` of the truth-table cube. -/
theorem uniform_deterministicAcceptanceIndicator_gt_half
    (machine : DeterministicMachine) {n : Nat} (steps : Nat)
    (hDense : DenseAboveHalf n
      (deterministicTableAcceptance machine steps)) :
    (1 : Rat) / 2 <
      uniformPredicateAverage
        (deterministicTableAcceptanceIndicator machine (n := n) steps) := by
  classical
  rcases hDense with ⟨witnesses, hWitnessCard, hWitnessAccepts⟩
  have hPointwise : ∀ table : TruthTable n,
      (if table ∈ witnesses then (1 : Rat) else 0) ≤
        boolIndicator
          (deterministicTableAcceptanceIndicator machine steps table) := by
    intro table
    by_cases hMem : table ∈ witnesses
    · have hAccept := hWitnessAccepts table hMem
      simp [hMem, boolIndicator,
        deterministicTableAcceptanceIndicator, hAccept]
    · simp only [hMem, ↓reduceIte]
      cases hValue : deterministicTableAcceptanceIndicator machine steps table <;>
        simp [boolIndicator]
  have hSum :
      (witnesses.card : Rat) ≤
        ∑ table : TruthTable n,
          boolIndicator
            (deterministicTableAcceptanceIndicator machine steps table) := by
    have hTermwise := Finset.sum_le_sum fun table (_hMem : table ∈
        (Finset.univ : Finset (TruthTable n))) => hPointwise table
    simpa using hTermwise
  have hWitnessCardRat :
      ((2 ^ (2 ^ n) : Nat) : Rat) < (witnesses.card : Rat) * 2 := by
    exact_mod_cast hWitnessCard
  unfold uniformPredicateAverage
  rw [truthTableSpace_card n]
  have hDenominatorPositive : (0 : Rat) < (2 ^ (2 ^ n) : Nat) := by
    positivity
  apply (lt_div_iff₀ hDenominatorPositive).2
  linarith

/-- Any signed weighted approximation with error below one half has an
accepting seed of nonzero weight whenever bounded-time acceptance is dense
above one half.  No positivity or normalization of the weights is used. -/
theorem signedWeightedApproximation_nonzeroSupport_hits_denseAcceptance
    (machine : DeterministicMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (steps : Nat)
    (weight : FiniteBitTape generator.seedBits → Rat)
    (epsilon : Rat)
    (hEpsilonNonnegative : 0 ≤ epsilon)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      abs (uniformPredicateAverage
          (deterministicTableAcceptanceIndicator machine (n := n) steps) -
        weightedGeneratorAverage generator.generate weight
          (deterministicTableAcceptanceIndicator machine (n := n) steps)) ≤ epsilon)
    (hDense : DenseAboveHalf n
      (deterministicTableAcceptance machine steps)) :
    ∃ seed : FiniteBitTape generator.seedBits,
      weight seed ≠ 0 ∧
      deterministicTableAcceptance machine steps (generator.generate seed) := by
  have hMass : epsilon <
      uniformPredicateAverage
        (deterministicTableAcceptanceIndicator machine (n := n) steps) :=
    lt_trans hEpsilon
      (uniform_deterministicAcceptanceIndicator_gt_half
        machine steps hDense)
  rcases weightedApproximation_support_hits
      generator.generate weight
      (deterministicTableAcceptanceIndicator machine (n := n) steps) epsilon
      hEpsilonNonnegative hApprox hMass with ⟨seed, hWeight, hAccept⟩
  exact ⟨seed, hWeight,
    (deterministicTableAcceptanceIndicator_eq_true_iff
      machine steps (generator.generate seed)).1 hAccept⟩

/-- The support consequence in exactly the interface consumed by the local
HSG-to-MCSP capstone.  The stronger witness theorem above also records that
the accepting seed has nonzero signed weight. -/
theorem signedWeightedApproximation_hitsDenseOneTapeAcceptance
    (machine : DeterministicMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (steps : Nat)
    (weight : FiniteBitTape generator.seedBits → Rat)
    (epsilon : Rat)
    (hEpsilonNonnegative : 0 ≤ epsilon)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      abs (uniformPredicateAverage
          (deterministicTableAcceptanceIndicator machine (n := n) steps) -
        weightedGeneratorAverage generator.generate weight
          (deterministicTableAcceptanceIndicator machine (n := n) steps)) ≤ epsilon) :
    HitsDenseOneTapeAcceptance machine generator steps := by
  intro hDense
  rcases signedWeightedApproximation_nonzeroSupport_hits_denseAcceptance
      machine generator steps weight epsilon hEpsilonNonnegative hEpsilon
      hApprox hDense with ⟨seed, _hWeight, hAccept⟩
  exact ⟨seed, hAccept⟩

/-- Direct deterministic MCSP-decider capstone for a signed weighted
approximation.  The approximated predicate is bounded-time acceptance of the
complemented machine; dense hitting then contradicts exact MCSP decision at
the same finite length and DAG threshold. -/
theorem signedWeightedApproximation_excludes_exactMCSPDecision
    (machine : DeterministicMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (steps : Nat)
    (weight : FiniteBitTape generator.seedBits → Rat)
    (epsilon : Rat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hEpsilonNonnegative : 0 ≤ epsilon)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      abs (uniformPredicateAverage
          (deterministicTableAcceptanceIndicator
            (complementMachine machine) (n := n) steps) -
        weightedGeneratorAverage generator.generate weight
          (deterministicTableAcceptanceIndicator
            (complementMachine machine) (n := n) steps)) ≤ epsilon) :
    ¬ ExactMCSPDecisionBehavior machine n threshold steps := by
  apply localGenerator_denseHitting_excludes_exactMCSPDecision
    machine generator steps hLength
  exact signedWeightedApproximation_hitsDenseOneTapeAcceptance
    (complementMachine machine) generator steps weight epsilon
    hEpsilonNonnegative hEpsilon hApprox

end OneTapeMagnification
end Frontier
end Pnp4
