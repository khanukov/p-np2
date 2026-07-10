import Pnp4.Frontier.StreamingMagnification.FixedBitstringCodec
import Pnp4.Frontier.StreamingMagnification.PaddedDAGEvalTrace
import Pnp4.Frontier.StreamingMagnification.StreamMergeChoice
import Pnp4.Frontier.StreamingMagnification.StreamMergeTracedCounterexample

/-!
# Fixed-length failure witnesses for Stream-Merge candidates

`StreamMergeChoice.CodeFits` can fail for three disjoint reasons: the external
body does not decode, the decoded circuit uses a gate outside the paper basis,
or a paper-basis circuit disagrees with the constrained prefix at one physical
truth-table coordinate.  This module packages all three cases in one relation
whose witness always has exactly `n + (s + s)` bits:

* `n` bits encode the physical coordinate in big-endian order;
* `s` bits carry the candidate's canonically padded local DAG trace;
* `s` bits carry the prior circuit's canonically padded local DAG trace.

The coordinate and trace fields are ignored in the two syntactic failure
branches.  In the semantic mismatch branch they are checked locally through
`PaddedDAGEvalTrace.IsPaddedTrace`.  The final theorem is an exact fixed-slice
semantic equivalence.  It is not yet a uniform polynomial-time checker or a
`Sigma_3` membership theorem.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeFailureMatrix

open Pnp3.ComplexityInterfaces
open StandardDAG
open TotalSearch
open StreamMerge
open StreamMergeChoice
open StreamMergeTracedCounterexample
open PaddedDAGEvalTrace

/-- One physical coordinate and two threshold-padded gate traces. -/
abbrev FailureWitness (n s : Nat) :=
  DAGCodec.BitString (n + (s + s))

/-- The coordinate field of a failure witness. -/
def indexBits {n s : Nat} (witness : FailureWitness n s) :
    DAGCodec.BitString n :=
  fun index => witness (Fin.castAdd (s + s) index)

/-- The candidate-trace field of a failure witness. -/
def candidateValues {n s : Nat} (witness : FailureWitness n s) :
    PaddedGateValues s :=
  fun index => witness (Fin.natAdd n (Fin.castAdd s index))

/-- The prior-trace field of a failure witness. -/
def priorValues {n s : Nat} (witness : FailureWitness n s) :
    PaddedGateValues s :=
  fun index => witness (Fin.natAdd n (Fin.natAdd s index))

/-- Assemble the three fixed-length witness fields. -/
def pack {n s : Nat} (coordinate : DAGCodec.BitString n)
    (candidateTrace priorTrace : PaddedGateValues s) : FailureWitness n s :=
  Fin.append coordinate (Fin.append candidateTrace priorTrace)

@[simp] theorem indexBits_pack {n s : Nat}
    (coordinate : DAGCodec.BitString n)
    (candidateTrace priorTrace : PaddedGateValues s) :
    indexBits (pack coordinate candidateTrace priorTrace) = coordinate := by
  funext index
  simp [indexBits, pack]

@[simp] theorem candidateValues_pack {n s : Nat}
    (coordinate : DAGCodec.BitString n)
    (candidateTrace priorTrace : PaddedGateValues s) :
    candidateValues (pack coordinate candidateTrace priorTrace) =
      candidateTrace := by
  funext index
  simp [candidateValues, pack]

@[simp] theorem priorValues_pack {n s : Nat}
    (coordinate : DAGCodec.BitString n)
    (candidateTrace priorTrace : PaddedGateValues s) :
    priorValues (pack coordinate candidateTrace priorTrace) = priorTrace := by
  funext index
  change
    Fin.append coordinate (Fin.append candidateTrace priorTrace)
        (Fin.natAdd n (Fin.natAdd s index)) = priorTrace index
  rw [Fin.append_right, Fin.append_right]

/-- The physical truth-table coordinate decoded from the first `n` bits. -/
def decodedIndex {n s : Nat} (witness : FailureWitness n s) : Fin (2 ^ n) :=
  FixedBitstringCodec.rank (indexBits witness)

@[simp] theorem decodedIndex_pack {n s : Nat}
    (coordinate : Fin (2 ^ n))
    (candidateTrace priorTrace : PaddedGateValues s) :
    decodedIndex
        (pack (FixedBitstringCodec.unrank coordinate)
          candidateTrace priorTrace) = coordinate := by
  simp [decodedIndex]

/-- Turn an in-range decoded physical coordinate into the constrained-prefix
index consumed by the existing traced-counterexample relation. -/
def boundedIndex {n s start blockLength : Nat}
    (witness : FailureWitness n s)
    (hindex : (decodedIndex witness).val < start + blockLength) :
    Fin (start + blockLength) :=
  ⟨(decodedIndex witness).val, hindex⟩

/-- The padded form of the existing dependent traced counterexample. -/
def PaddedTracedCounterexampleAt {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    (candidateTrace priorTrace : PaddedGateValues s) : Prop :=
  IsPaddedTrace candidate (indexInput hwindow index) candidateTrace ∧
    IsPaddedTrace prior (indexInput hwindow index) priorTrace ∧
      outputValue candidate (indexInput hwindow index) candidateTrace ≠
        tracedExpectedBit prior block hwindow index
          (PaddedDAGEvalTrace.restrict prior priorTrace)

instance instDecidablePaddedTracedCounterexampleAt
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    (candidateTrace priorTrace : PaddedGateValues s) :
    Decidable (PaddedTracedCounterexampleAt prior candidate block hwindow
      index candidateTrace priorTrace) := by
  unfold PaddedTracedCounterexampleAt
  infer_instance

/-- Existential padded form, before the three fields are concatenated. -/
def HasPaddedTracedCounterexample {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) : Prop :=
  Exists fun index : Fin (start + block.length) =>
    Exists fun candidateTrace : PaddedGateValues s =>
      Exists fun priorTrace : PaddedGateValues s =>
        PaddedTracedCounterexampleAt prior candidate block hwindow index
          candidateTrace priorTrace

/-- Padding removes the dependent trace types without changing the semantic
counterexample relation. -/
theorem hasTracedCounterexample_iff_hasPadded
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) :
    HasTracedCounterexample prior candidate block hwindow ↔
      HasPaddedTracedCounterexample prior candidate block hwindow := by
  constructor
  · rintro ⟨index, candidateTrace, priorTrace, hcounterexample⟩
    rcases hcounterexample with
      ⟨hcandidateTrace, hpriorTrace, hmismatch⟩
    refine ⟨index,
      PaddedDAGEvalTrace.extend candidate candidateTrace,
      PaddedDAGEvalTrace.extend prior priorTrace, ?_⟩
    refine ⟨
      (isPaddedTrace_extend_iff candidate
        (indexInput hwindow index) candidateTrace).2 hcandidateTrace,
      (isPaddedTrace_extend_iff prior
        (indexInput hwindow index) priorTrace).2 hpriorTrace,
      ?_⟩
    simpa [PaddedDAGEvalTrace.outputValue] using hmismatch
  · rintro ⟨index, candidateTrace, priorTrace, hcounterexample⟩
    rcases hcounterexample with
      ⟨hcandidateTrace, hpriorTrace, hmismatch⟩
    exact ⟨index,
      PaddedDAGEvalTrace.restrict candidate candidateTrace,
      PaddedDAGEvalTrace.restrict prior priorTrace,
      hcandidateTrace.1, hpriorTrace.1, by
        simpa [PaddedDAGEvalTrace.outputValue] using hmismatch⟩

/-- For a decoded paper-basis circuit, padded failure witnesses are still
exactly failure of `Fits`. -/
theorem not_fits_iff_hasPaddedTracedCounterexample
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (hbasis : candidate.val.UsesOnlyAndOrNot) :
    Not (Fits prior candidate start block) ↔
      HasPaddedTracedCounterexample prior candidate block hwindow := by
  rw [not_fits_iff_hasTracedCounterexample prior candidate block hwindow hbasis]
  exact hasTracedCounterexample_iff_hasPadded prior candidate block hwindow

/--
One fixed-length matrix covering malformed decoding, wrong basis, and a traced
semantic mismatch.  Only the last branch consumes the witness fields.
-/
def FailureMatrix {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (code : DAGCodec.Code n s) (witness : FailureWitness n s) : Prop :=
  match DAGCodec.decode code with
  | none => True
  | some candidate =>
      if candidate.val.UsesOnlyAndOrNot then
        if hindex :
            (decodedIndex witness).val < start + block.length then
          PaddedTracedCounterexampleAt prior candidate block hwindow
            (boundedIndex witness hindex)
            (candidateValues witness) (priorValues witness)
        else False
      else True

/--
Direct Boolean checker for one fixed failure row.  This deliberately mirrors
the logical matrix instead of applying `decide` to it: the latter leaves a
dependent private match splitter in generated interpreter code.
-/
def check {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (code : DAGCodec.Code n s) (witness : FailureWitness n s) : Bool :=
  match DAGCodec.decode code with
  | none => true
  | some candidate =>
      if candidate.val.UsesOnlyAndOrNot then
        if hindex :
            (decodedIndex witness).val < start + block.length then
          decide (PaddedTracedCounterexampleAt prior candidate block hwindow
            (boundedIndex witness hindex)
            (candidateValues witness) (priorValues witness))
        else false
      else true

@[simp] theorem check_eq_true_iff
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (code : DAGCodec.Code n s) (witness : FailureWitness n s) :
    check prior block hwindow code witness = true ↔
      FailureMatrix prior block hwindow code witness := by
  unfold check FailureMatrix
  cases hdecode : DAGCodec.decode code with
  | none => simp
  | some candidate =>
      simp only
      by_cases hbasis : candidate.val.UsesOnlyAndOrNot
      case pos =>
        simp only [hbasis, if_pos]
        by_cases hindex :
            (decodedIndex witness).val < start + block.length
        case pos => simp [hindex]
        case neg => simp [hindex]
      case neg => simp [hbasis]

/-- Decidability is reflected from the direct checker, so clients of
`decide` use the same interpreter-safe implementation. -/
instance instDecidableFailureMatrix
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (code : DAGCodec.Code n s) (witness : FailureWitness n s) :
    Decidable (FailureMatrix prior block hwindow code witness) :=
  decidable_of_iff (check prior block hwindow code witness = true)
    (check_eq_true_iff prior block hwindow code witness)

/-- Canonical ignored witness for the two syntactic failure branches. -/
def zeroWitness (n s : Nat) : FailureWitness n s :=
  fun _ => false

/-- A padded traced mismatch can be packed into the fixed matrix witness. -/
theorem failureMatrix_pack_of_paddedCounterexample
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (code : DAGCodec.Code n s)
    (hdecode : DAGCodec.decode code = some candidate)
    (hbasis : candidate.val.UsesOnlyAndOrNot)
    (index : Fin (start + block.length))
    (candidateTrace priorTrace : PaddedGateValues s)
    (hcounterexample :
      PaddedTracedCounterexampleAt prior candidate block hwindow index
        candidateTrace priorTrace) :
    FailureMatrix prior block hwindow code
      (pack (FixedBitstringCodec.unrank (tableIndex hwindow index))
        candidateTrace priorTrace) := by
  rw [FailureMatrix, hdecode]
  simp only [hbasis, if_pos]
  let witness : FailureWitness n s :=
    pack (FixedBitstringCodec.unrank (tableIndex hwindow index))
      candidateTrace priorTrace
  have hdecoded : decodedIndex witness = tableIndex hwindow index := by
    unfold decodedIndex
    rw [indexBits_pack]
    exact FixedBitstringCodec.rank_unrank (tableIndex hwindow index)
  have hindex : (decodedIndex witness).val < start + block.length := by
    rw [hdecoded]
    exact index.isLt
  rw [dif_pos hindex]
  have hbounded : boundedIndex witness hindex = index := by
    apply Fin.ext
    change (decodedIndex witness).val = index.val
    rw [hdecoded]
    rfl
  change
    PaddedTracedCounterexampleAt prior candidate block hwindow
      (boundedIndex witness hindex)
      (candidateValues witness) (priorValues witness)
  rw [hbounded]
  simpa [witness] using hcounterexample

/--
Complete fixed-length failure theorem.  No cause of `CodeFits` failure is
hidden in a dependent witness type or in a promise branch.
-/
theorem not_codeFits_iff_exists_failureWitness
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (code : DAGCodec.Code n s) :
    Not (CodeFits prior start block code) ↔
      Exists fun witness : FailureWitness n s =>
        FailureMatrix prior block hwindow code witness := by
  constructor
  · intro hnotFitsCode
    cases hdecode : DAGCodec.decode code with
    | none =>
        exact ⟨zeroWitness n s, by simp [FailureMatrix, hdecode]⟩
    | some candidate =>
        by_cases hbasis : candidate.val.UsesOnlyAndOrNot
        · have hnotFits : Not (Fits prior candidate start block) := by
            intro hfits
            exact hnotFitsCode ⟨candidate, hdecode, hfits⟩
          rcases (not_fits_iff_hasPaddedTracedCounterexample
            prior candidate block hwindow hbasis).1 hnotFits with
            ⟨index, candidateTrace, priorTrace, hcounterexample⟩
          exact ⟨
            pack (FixedBitstringCodec.unrank (tableIndex hwindow index))
              candidateTrace priorTrace,
            failureMatrix_pack_of_paddedCounterexample
              prior candidate block hwindow code hdecode hbasis index
                candidateTrace priorTrace hcounterexample⟩
        · exact ⟨zeroWitness n s, by
            simp [FailureMatrix, hdecode, hbasis]⟩
  · rintro ⟨witness, hmatrix⟩ hcodeFits
    rcases hcodeFits with ⟨candidate, hdecode, hfits⟩
    by_cases hindex :
        (decodedIndex witness).val < start + block.length
    · have hcounterexample :
          PaddedTracedCounterexampleAt prior candidate block hwindow
            (boundedIndex witness hindex)
            (candidateValues witness) (priorValues witness) := by
        simpa [FailureMatrix, hdecode, hfits.1, hindex] using hmatrix
      have hnotFits : Not (Fits prior candidate start block) :=
        (not_fits_iff_hasPaddedTracedCounterexample
          prior candidate block hwindow hfits.1).2
          ⟨boundedIndex witness hindex,
            candidateValues witness, priorValues witness, hcounterexample⟩
      exact hnotFits hfits
    · have : False := by
        simp [FailureMatrix, hdecode, hfits.1, hindex] at hmatrix
      exact this.elim

/-- Quantifier orientation used by the later universal competitor query. -/
theorem exists_failureWitness_iff_not_codeFits
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (code : DAGCodec.Code n s) :
    (Exists fun witness : FailureWitness n s =>
      FailureMatrix prior block hwindow code witness) ↔
      Not (CodeFits prior start block code) :=
  (not_codeFits_iff_exists_failureWitness prior block hwindow code).symm

end StreamMergeFailureMatrix
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeFailureMatrix.not_codeFits_iff_exists_failureWitness
