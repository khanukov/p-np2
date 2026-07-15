import Pnp4.Frontier.OneTapeMagnification.FiniteCheckpointToPpolyDAGBridge
import Pnp4.Frontier.OneTapeMagnification.GuardedCanonicalAggregateEndpoint
import Pnp4.Frontier.OneTapeMagnification.WeightedPRGToHSG
import Pnp4.Frontier.StreamingMagnification.EncodedTotalSearch

/-!
# Signed local generators against standard DAGs

This file records a direct transfer from a signed, reverse one-sided
approximation for the repository's standard DAG model to a `PpolyDAG`
lower bound.  The signed approximation is deliberately left as an explicit
all-exponent hypothesis: nothing here constructs the required weighted local
generator.  The same generic lemma also strengthens the implemented single
canonical-aggregate endpoint from absolute error to the reverse one-sided
inequality actually needed by the support argument.

The support argument needs only

`uniform acceptance - weighted acceptance <= epsilon`.

It does not need nonnegative weights, normalized weights, a two-sided absolute
error estimate, or even `0 <= epsilon`.
-/

open scoped BigOperators

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
open StreamingMagnification
open StreamingMagnification.TotalSearch
open ContractExpansion

local instance cachedInputMachineStateDecidableEqForSignedDAGTransfer
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-! ## Generic signed support transfer -/

/-- A reverse one-sided signed approximation whose error is below the uniform
acceptance mass must place nonzero weight on an accepting generator output.

No sign or normalization condition is imposed on the weights, and no
nonnegativity assumption on `epsilon` is needed. -/
theorem lowerWeightedApproximation_support_hits
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    (generator : Seed -> Input) (weight : Seed -> Rat)
    (predicate : Input -> Bool) (epsilon : Rat)
    (hApprox :
      uniformPredicateAverage predicate -
        weightedGeneratorAverage generator weight predicate <= epsilon)
    (hMass : epsilon < uniformPredicateAverage predicate) :
    exists seed, weight seed ≠ 0 /\ predicate (generator seed) = true := by
  by_contra hNoHit
  have hRejects :
      forall seed, weight seed ≠ 0 -> predicate (generator seed) = false := by
    intro seed hWeight
    cases hValue : predicate (generator seed) with
    | false => rfl
    | true => exact False.elim (hNoHit <| Exists.intro seed <| And.intro hWeight hValue)
  have hWeightedZero :
      weightedGeneratorAverage generator weight predicate = 0 :=
    weightedGeneratorAverage_eq_zero_of_nonzero_support_rejects
      generator weight predicate hRejects
  rw [hWeightedZero, sub_zero] at hApprox
  exact (not_lt_of_ge hApprox) hMass

/-! ## Reverse one-sided endpoint for the implemented single aggregate -/

/-- A reverse one-sided approximation of the cache-normalized guarded
aggregate supplies its support-HSG property.  Compared with the older
absolute-error endpoint, this needs neither `abs`, `0 <= epsilon`, nor any
weight normalization. -/
theorem reverseOneSidedWeightedApproximation_hits_singleMasterGuardedCachedCanonicalAggregate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (epsilon : Rat)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      uniformPredicateAverage (fun table : TruthTable n =>
          timedAlphaInPlaceAcceptingAggregateCheck (cachedInputMachine machine)
            (tableBits table) (T + 1) b hb) -
        weightedGeneratorAverage generator.generate weight
          (fun table : TruthTable n =>
            timedAlphaInPlaceAcceptingAggregateCheck
              (cachedInputMachine machine) (tableBits table) (T + 1) b hb) <=
        epsilon) :
    HitsSingleMasterGuardedCachedCanonicalAggregate
      machine generator T b hb := by
  intro hDense
  let aggregate : TruthTable n -> Bool := fun table =>
    timedAlphaInPlaceAcceptingAggregateCheck (cachedInputMachine machine)
      (tableBits table) (T + 1) b hb
  have hPointwise : aggregate =
      deterministicTableAcceptanceIndicator machine T := by
    funext table
    simpa only [aggregate] using
      cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_baseAcceptanceIndicator
        machine T b hb table
  have hMass : epsilon < uniformPredicateAverage aggregate := by
    rw [hPointwise]
    exact lt_trans hEpsilon
      (uniform_deterministicAcceptanceIndicator_gt_half machine T hDense)
  rcases lowerWeightedApproximation_support_hits
      generator.generate weight aggregate epsilon hApprox hMass with
    ⟨seed, _hWeight, hAggregate⟩
  refine ⟨seed, ?_⟩
  simpa only [aggregate] using hAggregate

/-- Strongest current finite aggregate capstone: one reverse one-sided signed
approximation of the cache-normalized complemented aggregate excludes exact
standard-DAG MCSP decision. -/
theorem reverseOneSidedWeightedSingleMasterGuardedCachedCanonicalAggregateApproximation_excludes_exactMCSPDecision
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (epsilon : Rat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      uniformPredicateAverage (fun table : TruthTable n =>
          timedAlphaInPlaceAcceptingAggregateCheck
            (cachedInputMachine (complementMachine machine))
            (tableBits table) (T + 1) b hb) -
        weightedGeneratorAverage generator.generate weight
          (fun table : TruthTable n =>
            timedAlphaInPlaceAcceptingAggregateCheck
              (cachedInputMachine (complementMachine machine))
              (tableBits table) (T + 1) b hb) <= epsilon) :
    Not (ExactMCSPDecisionBehavior machine n threshold T) := by
  apply
    singleMasterGuardedCachedCanonicalAggregateHSG_excludes_exactMCSPDecision
      machine generator T b hb hLength
  exact
    reverseOneSidedWeightedApproximation_hits_singleMasterGuardedCachedCanonicalAggregate
      (complementMachine machine) generator T b hb weight epsilon
        hEpsilon hApprox

/-! ## Dense predicates as uniform mass -/

/-- Any Boolean predicate containing an explicit set larger than half of the
truth-table cube has uniform rational average larger than one half. -/
theorem uniformPredicateAverage_gt_half_of_dense
    {n : Nat} (predicate : TruthTable n -> Bool)
    (hDense : DenseAboveHalf n (fun table => predicate table = true)) :
    (1 : Rat) / 2 < uniformPredicateAverage predicate := by
  classical
  rcases hDense with ⟨witnesses, hWitnessCard, hWitnessAccepts⟩
  have hPointwise : forall table : TruthTable n,
      (if table ∈ witnesses then (1 : Rat) else 0) <=
        boolIndicator (predicate table) := by
    intro table
    by_cases hMem : table ∈ witnesses
    · have hAccept := hWitnessAccepts table hMem
      simp [hMem, boolIndicator, hAccept]
    · simp only [hMem, ↓reduceIte]
      cases hValue : predicate table <;> simp [boolIndicator]
  have hSum :
      (witnesses.card : Rat) <=
        ∑ table : TruthTable n, boolIndicator (predicate table) := by
    have hTermwise := Finset.sum_le_sum fun table
      (_hMem : table ∈ (Finset.univ : Finset (TruthTable n))) =>
        hPointwise table
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

/-! ## Standard-DAG reverse one-sided fooling -/

/-- Signed reverse one-sided fooling for the exact standard-DAG class used by
`PpolyDAG`.  The inequality is stated for acceptance predicates; a one-gate
output negation below turns an MCSP decider into the dense coMCSP predicate.

This is an explicit mathematical hypothesis, not a provider or existence
claim. -/
def ReverseOneSidedFoolsDAGLocalGenerator
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (maxSize : Nat) (epsilon : Rat) : Prop :=
  forall circuit : C_DAG.Family (Pnp3.Models.Partial.tableLen n),
    C_DAG.size circuit <= maxSize ->
      uniformPredicateAverage
          (fun table : TruthTable n => C_DAG.eval circuit table) -
        weightedGeneratorAverage generator.generate weight
          (fun table : TruthTable n => C_DAG.eval circuit table) <= epsilon

/-! ## Constructive fixed-seed locality adapters -/

/-- A fixed-seed DAG bound can be weakened monotonically without changing
the seed space or any generated truth table. -/
def DAGLocalGenerator.weaken
    {n smallThreshold largeThreshold : Nat}
    (generator : DAGLocalGenerator n smallThreshold)
    (hThreshold : smallThreshold <= largeThreshold) :
    DAGLocalGenerator n largeThreshold where
  seedBits := generator.seedBits
  generate := generator.generate
  image_easy := fun seed => by
    rcases generator.image_easy seed with
      ⟨circuit, hSize, hBasis, hComputes⟩
    exact ⟨circuit, hSize.trans hThreshold, hBasis, hComputes⟩

/-- One joint constant-free circuit on `(seed,input)` supplies a local
generator at any larger target threshold.  The exact hardwiring cost remains
`uniform.gateCount + 2*seedBits`; the final inequality is explicit. -/
def dagLocalGeneratorOfJointCircuitAtThreshold
    {seedBits n threshold : Nat} (hPositive : 0 < n)
    (uniform : StreamingMagnification.StandardDAG.FlatCircuit (seedBits + n))
    (hUniformBasis : uniform.UsesOnlyAndOrNot)
    (hGateBound : uniform.gateCount + 2 * seedBits <= threshold) :
    DAGLocalGenerator n threshold :=
  (dagLocalGeneratorOfJointCircuit hPositive uniform hUniformBasis).weaken
    hGateBound

/-! ## One-gate output negation -/

/-- The unary standard DAG computing Boolean negation. -/
private def unaryNotDAG : DagCircuit 1 where
  gates := 1
  gate := fun _ => DagGate.not (DagWire.input (0 : Fin 1))
  output := DagWire.gate (0 : Fin 1)

@[simp] private theorem eval_unaryNotDAG (input : Bitstring 1) :
    DagCircuit.eval unaryNotDAG input = !input 0 := by
  simp [unaryNotDAG, DagCircuit.eval, DagCircuit.eval.evalGateAt]

/-- Negate only the output of a standard DAG, sharing the entire original
circuit. -/
private def negateDAG {inputBits : Nat} (circuit : DagCircuit inputBits) :
    DagCircuit inputBits :=
  substInputs unaryNotDAG (fun _ => circuit)

@[simp] private theorem eval_negateDAG
    {inputBits : Nat} (circuit : DagCircuit inputBits)
    (input : Bitstring inputBits) :
    DagCircuit.eval (negateDAG circuit) input =
      !DagCircuit.eval circuit input := by
  simp [negateDAG]

@[simp] private theorem size_negateDAG
    {inputBits : Nat} (circuit : DagCircuit inputBits) :
    DagCircuit.size (negateDAG circuit) = DagCircuit.size circuit + 1 := by
  rw [negateDAG, size_substInputs, bundleOfFamily_gates]
  simp [unaryNotDAG, DagCircuit.size]

/-! ## Direct conditional `PpolyDAG` lower bound -/

/-- An all-exponent signed local generator that reverse-one-sided-fools the
exact standard DAG class excludes a `PpolyDAG` family deciding standard-DAG
MCSP on the stated slices.

The `+ 1` in the fooling size bound is exactly the single shared output-NOT
gate.  The all-exponent signed-fooling premise is the unresolved lower-layer
obligation and remains fully visible in the theorem statement. -/
theorem not_PpolyDAG_of_signed_DAGLocalGenerator_slices
    (L : Language) (threshold : Nat -> Nat)
    (hSlice : forall n : Nat, forall table : TruthTable n,
      L (Pnp3.Models.Partial.tableLen n) table =
        EncodedTotalSearch.referenceDecision (s := threshold n) table)
    (hSigned : forall exponent : Nat,
      exists n : Nat,
      exists generator : DAGLocalGenerator n (threshold n),
      exists weight : FiniteBitTape generator.seedBits -> Rat,
      exists epsilon : Rat,
        DAGCodec.codeLength n (threshold n) + 2 < 2 ^ n /\
        epsilon < (1 : Rat) / 2 /\
        ReverseOneSidedFoolsDAGLocalGenerator generator weight
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)
          epsilon) :
    Not (PpolyDAG L) := by
  intro hDAG
  have hFamily := PpolyDAG_decider_as_C_DAG_decider hDAG
  choose exponent hCircuits using hFamily
  rcases hSigned exponent with
    ⟨n, generator, weight, epsilon, hLength, hEpsilon, hFools⟩
  rcases hCircuits (Pnp3.Models.Partial.tableLen n) with
    ⟨circuit, hCircuitSize, hCorrect⟩
  let complementCircuit := negateDAG circuit
  have hComplementSize :
      C_DAG.size complementCircuit <=
        (Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1 := by
    change DagCircuit.size complementCircuit <= _
    change DagCircuit.size circuit <= _ at hCircuitSize
    simpa [complementCircuit] using Nat.add_le_add_right hCircuitSize 1
  have hApprox := hFools complementCircuit hComplementSize
  have hDenseComplement : DenseAboveHalf n
      (fun table : TruthTable n =>
        C_DAG.eval complementCircuit table = true) := by
    rcases coMCSP_denseAboveHalf n (threshold n) hLength with
      ⟨witnesses, hWitnessCard, hHard⟩
    refine ⟨witnesses, hWitnessCard, ?_⟩
    intro table hMem
    have hNoCircuit : Not (HasCircuit n (threshold n) table) :=
      hHard table hMem
    have hReferenceFalse :
        EncodedTotalSearch.referenceDecision (s := threshold n) table = false := by
      cases hReference :
          EncodedTotalSearch.referenceDecision (s := threshold n) table with
      | false => rfl
      | true =>
          exact False.elim
            (hNoCircuit
              ((EncodedTotalSearch.referenceDecision_eq_true_iff table).1
                hReference))
    have hCircuitFalse : C_DAG.eval circuit table = false := by
      calc
        C_DAG.eval circuit table =
            L (Pnp3.Models.Partial.tableLen n) table := hCorrect table
        _ = EncodedTotalSearch.referenceDecision
              (s := threshold n) table := hSlice n table
        _ = false := hReferenceFalse
    change DagCircuit.eval complementCircuit table = true
    simpa [complementCircuit, hCircuitFalse]
  have hUniformMass :
      (1 : Rat) / 2 <
        uniformPredicateAverage
          (fun table : TruthTable n =>
            C_DAG.eval complementCircuit table) :=
    uniformPredicateAverage_gt_half_of_dense
      (fun table : TruthTable n => C_DAG.eval complementCircuit table)
      hDenseComplement
  have hMass : epsilon <
      uniformPredicateAverage
        (fun table : TruthTable n =>
          C_DAG.eval complementCircuit table) :=
    lt_trans hEpsilon hUniformMass
  rcases lowerWeightedApproximation_support_hits
      generator.generate weight
      (fun table : TruthTable n => C_DAG.eval complementCircuit table)
      epsilon hApprox hMass with
    ⟨seed, _hWeight, hComplementAccepts⟩
  have hReferenceTrue :
      EncodedTotalSearch.referenceDecision (s := threshold n)
          (generator.generate seed) = true :=
    (EncodedTotalSearch.referenceDecision_eq_true_iff
      (generator.generate seed)).2 (generator.image_easy seed)
  have hCircuitTrue :
      C_DAG.eval circuit (generator.generate seed) = true := by
    calc
      C_DAG.eval circuit (generator.generate seed) =
          L (Pnp3.Models.Partial.tableLen n) (generator.generate seed) :=
        hCorrect (generator.generate seed)
      _ = EncodedTotalSearch.referenceDecision (s := threshold n)
            (generator.generate seed) :=
        hSlice n (generator.generate seed)
      _ = true := hReferenceTrue
  have hComplementFalse :
      C_DAG.eval complementCircuit (generator.generate seed) = false := by
    change DagCircuit.eval complementCircuit (generator.generate seed) = false
    simpa [complementCircuit, hCircuitTrue]
  have : (false : Bool) = true :=
    hComplementFalse.symm.trans hComplementAccepts
  cases this

/-- Package the direct signed-DAG transfer into the repository's honest
`VerifiedNPDAGLowerBoundSource` interface.  All three substantive inputs —
NP membership, slice identity, and all-exponent signed fooling — remain
arguments of this definition rather than hidden fields or instances. -/
def verifiedNPDAGLowerBoundSource_of_signed_DAGLocalGenerator_slices
    (L : Language) (threshold : Nat -> Nat)
    (hNP : NP L)
    (hSlice : forall n : Nat, forall table : TruthTable n,
      L (Pnp3.Models.Partial.tableLen n) table =
        EncodedTotalSearch.referenceDecision (s := threshold n) table)
    (hSigned : forall exponent : Nat,
      exists n : Nat,
      exists generator : DAGLocalGenerator n (threshold n),
      exists weight : FiniteBitTape generator.seedBits -> Rat,
      exists epsilon : Rat,
        DAGCodec.codeLength n (threshold n) + 2 < 2 ^ n /\
        epsilon < (1 : Rat) / 2 /\
        ReverseOneSidedFoolsDAGLocalGenerator generator weight
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)
          epsilon) :
    Pnp4.AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource where
  L := L
  inNP := hNP
  notInPpolyDAG :=
    not_PpolyDAG_of_signed_DAGLocalGenerator_slices
      L threshold hSlice hSigned

end OneTapeMagnification
end Frontier
end Pnp4
