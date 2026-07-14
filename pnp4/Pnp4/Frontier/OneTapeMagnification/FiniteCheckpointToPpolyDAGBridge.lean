import Pnp4.Frontier.OneTapeMagnification.LocalPRGToMCSP
import Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG
import Complexity.DagCompose
import Mathlib.Tactic

/-!
# From a finite one-tape checkpoint to the remaining `PpolyDAG` obligation

This module separates two issues which were previously easy to conflate.

First, the easy-image part of a local generator is constructive.  If one
constant-free standard DAG on inputs `(seed, x)` computes all generator bits,
then fixing a seed gives a constant-free standard DAG on `x`.  Because the
paper basis has no constant gates, a fixed Boolean value is implemented by
`x_0 AND NOT x_0` or `x_0 OR NOT x_0`; this costs exactly two gates per seed
bit and requires the explicit, unavoidable condition `0 < n`.

Second, neither this hardwiring lemma nor the finite one-tape checkpoint proves
the pseudorandomness needed against arbitrary polynomial-size DAG families.
The final theorems therefore expose, without a contract structure, the exact
finite behavior-extraction arrow and the exact asymptotic `C_DAG`-fooling
statement that would imply a `PpolyDAG` lower bound.  All mathematical
hypotheses remain visible in the theorem signatures.

No theorem in this file asserts that the required fooling family exists.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
open StreamingMagnification
open StreamingMagnification.StandardDAG
open StreamingMagnification.TotalSearch
open AlgorithmsToLowerBounds
open ContractExpansion

/-! ## Constant-free seed hardwiring -/

/-- A dependent DAG gate belongs to the constant-free AND/OR/NOT basis. -/
def noConstDAGGate {n k : Nat} (gate : DagGate n k) : Prop :=
  match gate with
  | .const _ => False
  | .not _ | .and _ _ | .or _ _ => True

/-- Flattening a constant-free dependent gate produces a paper-basis gate. -/
lemma gateOfDag_inPaperBasis_of_noConst
    {n k : Nat} (gate : DagGate n k)
    (hGate : noConstDAGGate gate) :
    (FlatCircuit.gateOfDag gate).InPaperBasis := by
  cases gate <;> trivial

/-- A constant-free dependent DAG flattens to a standard paper-basis DAG. -/
theorem ofDag_usesOnlyAndOrNot_of_noConst
    {n : Nat} (circuit : DagCircuit n)
    (hCircuit : forall i, noConstDAGGate (circuit.gate i)) :
    (FlatCircuit.ofDag circuit).UsesOnlyAndOrNot := by
  intro i
  unfold FlatCircuit.ofDag
  simp only [List.get_ofFn]
  apply gateOfDag_inPaperBasis_of_noConst
  apply hCircuit

/-- Translating a paper-basis flat gate to the dependent representation does
not introduce a constant gate. -/
lemma noConst_gateToDag_of_inPaperBasis
    {n k : Nat} (gate : FlatGate)
    (hValid : gate.Valid n k) (hBasis : gate.InPaperBasis) :
    noConstDAGGate (FlatCircuit.gateToDag gate hValid) := by
  cases gate with
  | const value => exact hBasis
  | notGate source => trivial
  | andGate left right => trivial
  | orGate left right => trivial

/-- A standard DAG satisfying the explicit paper-basis predicate has no
constant gates after translation to the dependent representation. -/
theorem toDag_noConst_of_usesOnlyAndOrNot
    {n : Nat} (circuit : FlatCircuit n)
    (hCircuit : circuit.UsesOnlyAndOrNot) :
    forall i, noConstDAGGate (circuit.toDag.gate i) := by
  intro i
  let j : Fin circuit.val.gates.length :=
    Fin.cast circuit.property.1.symm i
  change noConstDAGGate
    (FlatCircuit.gateToDag (circuit.val.gates.get j) _)
  apply noConst_gateToDag_of_inPaperBasis
  exact hCircuit j

/-- A two-gate, constant-free circuit for the Boolean constant `value`.

The first gate computes `NOT x_0`.  The second computes either
`x_0 AND NOT x_0` or `x_0 OR NOT x_0`. -/
def paperBasisConstantDAG
    (n : Nat) (hPositive : 0 < n) (value : Bool) : DagCircuit n where
  gates := 2
  gate := fun i =>
    Fin.cases
      (DagGate.not (DagWire.input (Fin.mk 0 hPositive)))
      (fun j : Fin 1 =>
        if value then
          DagGate.or
            (DagWire.input (Fin.mk 0 hPositive))
            (DagWire.gate (Fin.mk 0 (Nat.zero_lt_succ j.val)))
        else
          DagGate.and
            (DagWire.input (Fin.mk 0 hPositive))
            (DagWire.gate (Fin.mk 0 (Nat.zero_lt_succ j.val))))
      i
  output := DagWire.gate (Fin.mk 1 (by omega))

@[simp] theorem paperBasisConstantDAG_gates
    (n : Nat) (hPositive : 0 < n) (value : Bool) :
    (paperBasisConstantDAG n hPositive value).gates = 2 := rfl

/-- The two-gate construction computes the requested constant. -/
@[simp] theorem eval_paperBasisConstantDAG
    (n : Nat) (hPositive : 0 < n) (value : Bool)
    (input : Bitstring n) :
    DagCircuit.eval (paperBasisConstantDAG n hPositive value) input = value := by
  rw [DagCircuit.eval.eq_1]
  change DagCircuit.eval.evalGateAt
    (paperBasisConstantDAG n hPositive value) input 1 _ = value
  rw [DagCircuit.eval.evalGateAt.eq_1]
  have hTop
      (hIndex : 1 < (paperBasisConstantDAG n hPositive value).gates) :
      (paperBasisConstantDAG n hPositive value).gate (Fin.mk 1 hIndex) =
        if value then
          DagGate.or
            (DagWire.input (Fin.mk 0 hPositive))
            (DagWire.gate (0 : Fin 1))
        else
          DagGate.and
            (DagWire.input (Fin.mk 0 hPositive))
            (DagWire.gate (0 : Fin 1)) := by
    rfl
  rw [hTop]
  have hZero
      (hIndex : 0 < (paperBasisConstantDAG n hPositive value).gates) :
      (paperBasisConstantDAG n hPositive value).gate (Fin.mk 0 hIndex) =
        DagGate.not (DagWire.input (Fin.mk 0 hPositive)) := by
    rfl
  cases value with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      change
        (input (Fin.mk 0 hPositive) &&
          DagCircuit.eval.evalGateAt
            (paperBasisConstantDAG n hPositive false) input 0 _) = false
      rw [DagCircuit.eval.evalGateAt.eq_1]
      rw [hZero]
      dsimp only
      cases input (Fin.mk 0 hPositive) <;> rfl
  | true =>
      rw [if_pos rfl]
      dsimp only
      change
        (input (Fin.mk 0 hPositive) ||
          DagCircuit.eval.evalGateAt
            (paperBasisConstantDAG n hPositive true) input 0 _) = true
      rw [DagCircuit.eval.evalGateAt.eq_1]
      rw [hZero]
      dsimp only
      cases input (Fin.mk 0 hPositive) <;> rfl

/-- Every gate of `paperBasisConstantDAG` is in the constant-free basis. -/
theorem paperBasisConstantDAG_noConst
    (n : Nat) (hPositive : 0 < n) (value : Bool) :
    forall i,
      noConstDAGGate ((paperBasisConstantDAG n hPositive value).gate i) := by
  intro i
  fin_cases i
  next => trivial
  next => cases value <;> trivial

lemma noConst_shiftGateBy
    {n k : Nat} (offset : Nat) (gate : DagGate n k)
    (hGate : noConstDAGGate gate) :
    noConstDAGGate (shiftGateBy offset gate) := by
  cases gate <;> trivial

lemma noConst_substGateWithBundle
    {n m k : Nat} (bundle : DagBundle m n) (gate : DagGate n k)
    (hGate : noConstDAGGate gate) :
    noConstDAGGate (substGateWithBundle bundle gate) := by
  cases gate <;> trivial

/-- Bundling a family of constant-free DAGs preserves constant-freeness. -/
lemma bundleOfFamily_noConst {n : Nat} :
    forall {out : Nat} (family : Fin out -> DagCircuit n),
      (forall output gate,
        noConstDAGGate ((family output).gate gate)) ->
      forall gate,
        noConstDAGGate ((bundleOfFamily out family).gate gate) := by
  intro out
  induction out with
  | zero =>
      intro family hFamily gate
      exact Fin.elim0 gate
  | succ out ih =>
      intro family hFamily gate
      refine Fin.addCases
        (motive := fun gate =>
          noConstDAGGate ((bundleOfFamily (out + 1) family).gate gate))
        (fun oldGate => by
          have hOld := ih
            (fun output => family (Fin.castAdd 1 output))
            (fun output innerGate =>
              hFamily (Fin.castAdd 1 output) innerGate)
            oldGate
          simpa only [bundleOfFamily, snocBundle_gate_left] using hOld)
        (fun newGate => by
          have hNew := noConst_shiftGateBy
            (bundleOfFamily out
              (fun output => family (Fin.castAdd 1 output))).gates
            ((family (Fin.natAdd out (0 : Fin 1))).gate newGate)
            (hFamily (Fin.natAdd out (0 : Fin 1)) newGate)
          simpa only [bundleOfFamily, snocBundle_gate_right] using hNew)
        gate

/-- Input substitution preserves the absence of constant gates. -/
lemma substInputs_noConst
    {n m : Nat} (outer : DagCircuit n)
    (inputs : Fin n -> DagCircuit m)
    (hOuter : forall gate, noConstDAGGate (outer.gate gate))
    (hInputs : forall input gate,
      noConstDAGGate ((inputs input).gate gate)) :
    forall gate,
      noConstDAGGate ((substInputs outer inputs).gate gate) := by
  intro gate
  refine Fin.addCases
    (motive := fun gate =>
      noConstDAGGate ((substInputs outer inputs).gate gate))
    (fun inputGate => by
      have hInput := bundleOfFamily_noConst inputs hInputs inputGate
      simpa only [substInputs, substInputsWithBundle_gate_left] using hInput)
    (fun outerGate => by
      have hSubstituted := noConst_substGateWithBundle
        (bundleOfFamily n inputs) (outer.gate outerGate) (hOuter outerGate)
      simpa only [substInputs, substInputsWithBundle_gate_right] using hSubstituted)
    gate

/-- Circuit substituted for one joint `(seed, x)` input. -/
def hardwireInputDAG
    {seedBits n : Nat} (hPositive : 0 < n)
    (seed : FiniteBitTape seedBits) :
    Fin (seedBits + n) -> DagCircuit n :=
  Fin.addCases
    (fun seedIndex =>
      paperBasisConstantDAG n hPositive (seed seedIndex))
    (fun inputIndex => inputProj inputIndex)

/-- Fix `seed` in one joint standard DAG on `(seed, x)` inputs. -/
def hardwireSeedDAG
    {seedBits n : Nat} (hPositive : 0 < n)
    (uniform : FlatCircuit (seedBits + n))
    (seed : FiniteBitTape seedBits) : DagCircuit n :=
  substInputs uniform.toDag (hardwireInputDAG hPositive seed)

/-- Flat standard-DAG presentation of `hardwireSeedDAG`. -/
def hardwireSeedCircuit
    {seedBits n : Nat} (hPositive : 0 < n)
    (uniform : FlatCircuit (seedBits + n))
    (seed : FiniteBitTape seedBits) : FlatCircuit n :=
  FlatCircuit.ofDag (hardwireSeedDAG hPositive uniform seed)

@[simp] theorem hardwireInputDAG_seed
    {seedBits n : Nat} (hPositive : 0 < n)
    (seed : FiniteBitTape seedBits) (index : Fin seedBits) :
    hardwireInputDAG hPositive seed (Fin.castAdd n index) =
      paperBasisConstantDAG n hPositive (seed index) := by
  simp [hardwireInputDAG]

@[simp] theorem hardwireInputDAG_input
    {seedBits n : Nat} (hPositive : 0 < n)
    (seed : FiniteBitTape seedBits) (index : Fin n) :
    hardwireInputDAG hPositive seed (Fin.natAdd seedBits index) =
      inputProj index := by
  simp [hardwireInputDAG]

/-- Hardwiring has the exact gate count promised in the module statement. -/
theorem hardwireSeedCircuit_gateCount
    {seedBits n : Nat} (hPositive : 0 < n)
    (uniform : FlatCircuit (seedBits + n))
    (seed : FiniteBitTape seedBits) :
    (hardwireSeedCircuit hPositive uniform seed).gateCount =
      uniform.gateCount + 2 * seedBits := by
  change
    (bundleOfFamily (seedBits + n)
      (hardwireInputDAG hPositive seed)).gates + uniform.toDag.gates =
      uniform.gateCount + 2 * seedBits
  rw [bundleOfFamily_gates, Fin.sum_univ_add]
  simp only [hardwireInputDAG_seed, hardwireInputDAG_input,
    paperBasisConstantDAG_gates, inputProj]
  simp
  omega

/-- Evaluation after hardwiring is exactly evaluation of the joint circuit at
the concatenated assignment `(seed, input)`. -/
theorem hardwireSeedCircuit_eval
    {seedBits n : Nat} (hPositive : 0 < n)
    (uniform : FlatCircuit (seedBits + n))
    (seed : FiniteBitTape seedBits) (input : Bitstring n) :
    (hardwireSeedCircuit hPositive uniform seed).eval input =
      uniform.eval (Fin.addCases seed input) := by
  unfold hardwireSeedCircuit FlatCircuit.eval
  rw [FlatCircuit.toDag_ofDag]
  change
    DagCircuit.eval (hardwireSeedDAG hPositive uniform seed) input =
      DagCircuit.eval uniform.toDag (Fin.addCases seed input)
  rw [hardwireSeedDAG, eval_substInputs]
  congr 1
  funext index
  refine Fin.addCases
    (motive := fun index =>
      DagCircuit.eval (hardwireInputDAG hPositive seed index) input =
        Fin.addCases seed input index)
    (fun seedIndex => by simp)
    (fun inputIndex => by simp)
    index

/-- Hardwiring preserves the exact paper basis. -/
theorem hardwireSeedCircuit_usesOnlyAndOrNot
    {seedBits n : Nat} (hPositive : 0 < n)
    (uniform : FlatCircuit (seedBits + n))
    (hUniformBasis : uniform.UsesOnlyAndOrNot)
    (seed : FiniteBitTape seedBits) :
    (hardwireSeedCircuit hPositive uniform seed).UsesOnlyAndOrNot := by
  apply ofDag_usesOnlyAndOrNot_of_noConst
  apply substInputs_noConst
  next => exact toDag_noConst_of_usesOnlyAndOrNot uniform hUniformBasis
  next =>
    intro inputIndex
    refine Fin.addCases
      (motive := fun inputIndex =>
        forall gate,
          noConstDAGGate
            ((hardwireInputDAG hPositive seed inputIndex).gate gate))
      (fun seedIndex => by
        unfold hardwireInputDAG
        dsimp only
        rw [Fin.addCases_left]
        exact paperBasisConstantDAG_noConst
          n hPositive (seed seedIndex))
      (fun realInput => by
        unfold hardwireInputDAG
        dsimp only
        rw [Fin.addCases_right]
        intro gate
        exact Fin.elim0 gate)
      inputIndex

/-- The truth table of the fixed-seed circuit is the corresponding slice of
the joint circuit. -/
theorem circuitTruthTable_hardwireSeedCircuit
    {seedBits n : Nat} (hPositive : 0 < n)
    (uniform : FlatCircuit (seedBits + n))
    (seed : FiniteBitTape seedBits) :
    circuitTruthTable (hardwireSeedCircuit hPositive uniform seed) =
      fun index => uniform.eval
        (Fin.addCases seed (lexInput n index)) := by
  funext index
  exact hardwireSeedCircuit_eval hPositive uniform seed (lexInput n index)

/-- A single constant-free joint standard DAG constructively supplies the
easy-image field of a `DAGLocalGenerator`, at the explicit threshold
`uniform.gateCount + 2 * seedBits`. -/
def dagLocalGeneratorOfJointCircuit
    {seedBits n : Nat} (hPositive : 0 < n)
    (uniform : FlatCircuit (seedBits + n))
    (hUniformBasis : uniform.UsesOnlyAndOrNot) :
    DAGLocalGenerator n (uniform.gateCount + 2 * seedBits) where
  seedBits := seedBits
  generate := fun seed index =>
    uniform.eval (Fin.addCases seed (lexInput n index))
  image_easy := fun seed => by
    refine Exists.intro
      (hardwireSeedCircuit hPositive uniform seed) ?_
    exact And.intro
      (by rw [hardwireSeedCircuit_gateCount])
      (And.intro
        (hardwireSeedCircuit_usesOnlyAndOrNot
          hPositive uniform hUniformBasis seed)
        (circuitTruthTable_hardwireSeedCircuit
          hPositive uniform seed))

/-! ## Exact remaining finite and asymptotic arrows -/

/-- The finite one-tape contradiction needs one additional, explicit arrow:
if a `PpolyDAG` decider for `L` can be extracted into the stated bounded-error
behavior of this same machine and slice, the already-proved finite local-PRG
checkpoint excludes that decider. -/
theorem not_PpolyDAG_of_oneTape_checkpoint_and_behavior_extraction
    (L : Language) (machine : RandomizedMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hFools : FoolsOneTapeMachineWithin
      machine generator randomBits steps ((1 : Rat) / 6))
    (hBehaviorExtraction : PpolyDAG L ->
      BoundedErrorMCSPBehavior
        machine n threshold randomBits steps) :
    Not (PpolyDAG L) := by
  intro hDAG
  exact
    (localGenerator_fooling_excludes_boundedErrorMCSP
      machine generator randomBits steps hLength hFools)
    (hBehaviorExtraction hDAG)

/-- Explicit asymptotic missing statement for the final DAG lower bound.

For every polynomial exponent, one slice must carry an easy-image local PRG
that one-sided-fools *the exact repository `C_DAG` class* up to that exponent,
with error below the Shannon counting gap.  Under precisely those visible
hypotheses, a `PpolyDAG` decider for the slice language is impossible.

This is a conditional bridge to the mainline endpoint, not a proof that such
PRGs exist. -/
theorem not_PpolyDAG_of_C_DAG_localPRG_slices
    (L : Language) (threshold : Nat -> Nat)
    (hSlice : forall n : Nat,
      forall table : AlgorithmsToLowerBounds.TruthTable n,
        L (Pnp3.Models.Partial.tableLen n) table =
          exactTreeMCSPThresholdDecision n (threshold n) table)
    (hLocalPRG : forall exponent : Nat,
      exists n : Nat,
      exists prg : TruthTableLocalPRG n,
      exists epsilon : Rat,
        prg.imageSizeBound <= threshold n /\
        OneSidedFoolsBoundedTruthTableClass prg C_DAG
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent)
          epsilon /\
        epsilon < 1 - treeMCSPCountRatio n (threshold n)) :
    Not (PpolyDAG L) := by
  intro hDAG
  have hFamily := PpolyDAG_decider_as_C_DAG_decider hDAG
  choose exponent hCircuits using hFamily
  have hLocal := hLocalPRG exponent
  choose n prg epsilon hLocalSpec using hLocal
  have hThreshold := hLocalSpec.1
  have hFools := hLocalSpec.2.1
  have hEpsilon := hLocalSpec.2.2
  have hCircuit := hCircuits (Pnp3.Models.Partial.tableLen n)
  choose circuit hCircuitSpec using hCircuit
  have hSize := hCircuitSpec.1
  have hCorrect := hCircuitSpec.2
  exact smallCircuit_contradiction_of_localPRGTransfer
    prg hThreshold hFools
    (by simpa [treeMCSPCountRatio] using hEpsilon)
    circuit hSize
    (fun table => (hCorrect table).trans (hSlice n table))

/-- The same explicit hypotheses, plus visible NP membership, give the
repository's `NP_not_subset_PpolyDAG` endpoint. -/
theorem NP_not_subset_PpolyDAG_of_C_DAG_localPRG_slices
    (L : Language) (threshold : Nat -> Nat)
    (hNP : NP L)
    (hSlice : forall n : Nat,
      forall table : AlgorithmsToLowerBounds.TruthTable n,
        L (Pnp3.Models.Partial.tableLen n) table =
          exactTreeMCSPThresholdDecision n (threshold n) table)
    (hLocalPRG : forall exponent : Nat,
      exists n : Nat,
      exists prg : TruthTableLocalPRG n,
      exists epsilon : Rat,
        prg.imageSizeBound <= threshold n /\
        OneSidedFoolsBoundedTruthTableClass prg C_DAG
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent)
          epsilon /\
        epsilon < 1 - treeMCSPCountRatio n (threshold n)) :
    NP_not_subset_PpolyDAG := by
  exact Exists.intro L (And.intro hNP
    (not_PpolyDAG_of_C_DAG_localPRG_slices
      L threshold hSlice hLocalPRG))

/-- Fully explicit conditional endpoint.  The unproved input is still the
quantified `C_DAG`-fooling family above (and the stated NP slice language), so
this theorem is not an unconditional `P != NP` proof. -/
theorem P_ne_NP_of_C_DAG_localPRG_slices
    (L : Language) (threshold : Nat -> Nat)
    (hNP : NP L)
    (hSlice : forall n : Nat,
      forall table : AlgorithmsToLowerBounds.TruthTable n,
        L (Pnp3.Models.Partial.tableLen n) table =
          exactTreeMCSPThresholdDecision n (threshold n) table)
    (hLocalPRG : forall exponent : Nat,
      exists n : Nat,
      exists prg : TruthTableLocalPRG n,
      exists epsilon : Rat,
        prg.imageSizeBound <= threshold n /\
        OneSidedFoolsBoundedTruthTableClass prg C_DAG
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent)
          epsilon /\
        epsilon < 1 - treeMCSPCountRatio n (threshold n)) :
    Not (P = NP) := by
  exact Pnp3.ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
    (NP_not_subset_PpolyDAG_of_C_DAG_localPRG_slices
      L threshold hNP hSlice hLocalPRG)
    Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_internal

end OneTapeMagnification
end Frontier
end Pnp4
