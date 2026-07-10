import Pnp4.Frontier.StreamingMagnification.FixedBitstringCodec
import Pnp4.Frontier.StreamingMagnification.PaddedDAGEvalTrace
import Pnp4.Frontier.StreamingMagnification.StreamMergeAgreement
import Pnp4.Frontier.StreamingMagnification.StreamMergeFailureMatrix

/-!
# Fixed-coordinate agreement matrix for Stream-Merge candidates

This module gives the positive counterpart of `StreamMergeFailureMatrix`.
The outer coordinate is always exactly `n` bits.  The inner witness reuses
the uniform `FailureWitness n s` body: its two `s`-bit trace slices carry
canonically padded local evaluation traces for the candidate and prior
circuits.  Its first `n` bits are deliberately ignored here.

Coordinates outside the constrained prefix are vacuous.  At every in-range
coordinate, the matrix checks both padded traces and equality between the
candidate output reconstructed from its trace and the expected bit
reconstructed from the prior trace (or read literally from the new block).

The final theorem is an exact fixed-coordinate semantic equivalence with
`StreamMerge.Fits`.  It makes no uniform running-time, circuit-size, or
complexity-class claim.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeAgreementMatrix

open Pnp3.ComplexityInterfaces
open StandardDAG
open TotalSearch
open StreamMerge
open StreamMergeAgreement
open StreamMergeTracedCounterexample
open StreamMergeFailureMatrix
open PaddedDAGEvalTrace

/-- Decode the fixed outer coordinate using the repository-wide big-endian
truth-table convention. -/
def decodedCoordinate {n : Nat}
    (coordinateBits : DAGCodec.BitString n) : Fin (2 ^ n) :=
  FixedBitstringCodec.rank coordinateBits

/-- Turn an in-range outer coordinate into the constrained-prefix index. -/
def constrainedIndex {n start blockLength : Nat}
    (coordinateBits : DAGCodec.BitString n)
    (hindex : (decodedCoordinate coordinateBits).val < start + blockLength) :
    Fin (start + blockLength) :=
  ⟨(decodedCoordinate coordinateBits).val, hindex⟩

/--
The positive local trace relation at one constrained coordinate.  Both trace
bodies have the externally fixed length `s`; the equality is stated using
the values reconstructed from those locally checked traces.
-/
def PaddedTracedAgreementAt {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    (candidateTrace priorTrace : PaddedGateValues s) : Prop :=
  IsPaddedTrace candidate (indexInput hwindow index) candidateTrace ∧
    IsPaddedTrace prior (indexInput hwindow index) priorTrace ∧
      outputValue candidate (indexInput hwindow index) candidateTrace =
        tracedExpectedBit prior block hwindow index
          (PaddedDAGEvalTrace.restrict prior priorTrace)

instance instDecidablePaddedTracedAgreementAt
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    (candidateTrace priorTrace : PaddedGateValues s) :
    Decidable (PaddedTracedAgreementAt prior candidate block hwindow index
      candidateTrace priorTrace) := by
  unfold PaddedTracedAgreementAt
  infer_instance

/--
Fixed-coordinate positive matrix.  Out-of-range truth-table coordinates are
unconstrained.  An in-range coordinate consumes only the two padded trace
slices of the uniform inner witness.
-/
def AgreementMatrix {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (coordinateBits : DAGCodec.BitString n)
    (inner : FailureWitness n s) : Prop :=
  if hindex :
      (decodedCoordinate coordinateBits).val < start + block.length then
    PaddedTracedAgreementAt prior candidate block hwindow
      (constrainedIndex coordinateBits hindex)
      (candidateValues inner) (priorValues inner)
  else True

instance instDecidableAgreementMatrix
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (coordinateBits : DAGCodec.BitString n)
    (inner : FailureWitness n s) :
    Decidable (AgreementMatrix prior candidate block hwindow
      coordinateBits inner) := by
  unfold AgreementMatrix
  split <;> infer_instance

/-- A checked padded candidate trace reconstructs the existing local
`candidateBit`. -/
theorem outputValue_eq_candidateBit_of_isPaddedTrace
    {n s blockLength start : Nat}
    (candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    {values : PaddedGateValues s}
    (htrace : IsPaddedTrace candidate (indexInput hwindow index) values) :
    outputValue candidate (indexInput hwindow index) values =
      candidateBit candidate block hwindow index := by
  exact flatOutputValue_eq_candidateBit_of_isTrace
    candidate block hwindow index htrace.1

/-- A checked padded prior trace reconstructs the existing local
`expectedBit`. -/
theorem tracedExpectedBit_eq_expectedBit_of_isPaddedTrace
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    {values : PaddedGateValues s}
    (htrace : IsPaddedTrace prior (indexInput hwindow index) values) :
    tracedExpectedBit prior block hwindow index
        (PaddedDAGEvalTrace.restrict prior values) =
      expectedBit prior block hwindow index := by
  exact tracedExpectedBit_eq_expectedBit_of_isTrace
    prior block hwindow index htrace.1

/-- Canonical padded traces witness the matrix at any in-range coordinate
where the candidate and expected bits agree. -/
theorem exists_agreementMatrix_of_coordinate_agreement
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (coordinateBits : DAGCodec.BitString n)
    (hindex : (decodedCoordinate coordinateBits).val < start + block.length)
    (hagreement :
      candidateBit candidate block hwindow
          (constrainedIndex coordinateBits hindex) =
        expectedBit prior block hwindow
          (constrainedIndex coordinateBits hindex)) :
    ∃ inner : FailureWitness n s,
      AgreementMatrix prior candidate block hwindow coordinateBits inner := by
  let index := constrainedIndex coordinateBits hindex
  let candidateTrace := PaddedDAGEvalTrace.canonicalValues candidate
    (indexInput hwindow index)
  let priorTrace := PaddedDAGEvalTrace.canonicalValues prior
    (indexInput hwindow index)
  let inner : FailureWitness n s :=
    StreamMergeFailureMatrix.pack coordinateBits candidateTrace priorTrace
  refine ⟨inner, ?_⟩
  rw [AgreementMatrix, dif_pos hindex]
  change PaddedTracedAgreementAt prior candidate block hwindow index
    (candidateValues inner) (priorValues inner)
  have hcandidate :
      IsPaddedTrace candidate (indexInput hwindow index) candidateTrace :=
    canonicalValues_isPaddedTrace candidate (indexInput hwindow index)
  have hprior :
      IsPaddedTrace prior (indexInput hwindow index) priorTrace :=
    canonicalValues_isPaddedTrace prior (indexInput hwindow index)
  have hcandidateOutput :
      outputValue candidate (indexInput hwindow index) candidateTrace =
        candidateBit candidate block hwindow index :=
    outputValue_eq_candidateBit_of_isPaddedTrace
      candidate block hwindow index hcandidate
  have hpriorOutput :
      tracedExpectedBit prior block hwindow index
          (PaddedDAGEvalTrace.restrict prior priorTrace) =
        expectedBit prior block hwindow index :=
    tracedExpectedBit_eq_expectedBit_of_isPaddedTrace
      prior block hwindow index hprior
  simpa [inner, candidateTrace, priorTrace, PaddedTracedAgreementAt] using
    And.intro hcandidate (And.intro hprior
      (hcandidateOutput.trans (hagreement.trans hpriorOutput.symm)))

/--
Exact fixed-coordinate EAE characterization of `Fits`.  The candidate must use the
paper basis, and every one of the `2^n` outer coordinate strings has a single
fixed-length inner witness.  Coordinates beyond the constrained prefix use
the vacuous branch of `AgreementMatrix`.
-/
theorem fits_iff_usesOnlyAndOrNot_and_forall_exists_agreementMatrix
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) :
    Fits prior candidate start block ↔
      candidate.val.UsesOnlyAndOrNot ∧
        ∀ coordinateBits : DAGCodec.BitString n,
          ∃ inner : FailureWitness n s,
            AgreementMatrix prior candidate block hwindow
              coordinateBits inner := by
  rw [fits_iff_usesOnlyAndOrNot_and_pointwiseAgreement
    prior candidate block hwindow]
  apply and_congr Iff.rfl
  constructor
  · intro hagreement coordinateBits
    by_cases hindex :
        (decodedCoordinate coordinateBits).val < start + block.length
    · exact exists_agreementMatrix_of_coordinate_agreement
        prior candidate block hwindow coordinateBits hindex
        (hagreement (constrainedIndex coordinateBits hindex))
    · exact ⟨zeroWitness n s, by
        simp [AgreementMatrix, hindex]⟩
  · intro hmatrix index
    let coordinateBits : DAGCodec.BitString n :=
      FixedBitstringCodec.unrank (tableIndex hwindow index)
    rcases hmatrix coordinateBits with ⟨inner, hinner⟩
    have hdecoded :
        decodedCoordinate coordinateBits = tableIndex hwindow index := by
      simp [coordinateBits, decodedCoordinate]
    have hindex :
        (decodedCoordinate coordinateBits).val < start + block.length := by
      rw [hdecoded]
      exact index.isLt
    have hconstrained : constrainedIndex coordinateBits hindex = index := by
      apply Fin.ext
      change (decodedCoordinate coordinateBits).val = index.val
      rw [hdecoded]
      rfl
    have hagreementAt :
        PaddedTracedAgreementAt prior candidate block hwindow
          (constrainedIndex coordinateBits hindex)
          (candidateValues inner) (priorValues inner) := by
      simpa [AgreementMatrix, hindex] using hinner
    rw [hconstrained] at hagreementAt
    rcases hagreementAt with
      ⟨hcandidateTrace, hpriorTrace, houtputs⟩
    rw [← outputValue_eq_candidateBit_of_isPaddedTrace
      candidate block hwindow index hcandidateTrace]
    rw [← tracedExpectedBit_eq_expectedBit_of_isPaddedTrace
      prior block hwindow index hpriorTrace]
    exact houtputs

end StreamMergeAgreementMatrix
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeAgreementMatrix.fits_iff_usesOnlyAndOrNot_and_forall_exists_agreementMatrix
