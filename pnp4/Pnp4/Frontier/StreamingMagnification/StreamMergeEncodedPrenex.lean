import Pnp4.Frontier.StreamingMagnification.StreamMergeAgreementMatrix
import Pnp4.Frontier.StreamingMagnification.StreamMergeOptimalityMatrix
import Pnp4.Frontier.StreamingMagnification.StreamMergeOutputFormula
import Pnp4.Frontier.StreamingMagnification.StreamMergePrenexWire

/-!
# Fixed-slice encoded EAE shell for one Stream-Merge output bit

For a valid prior code and a well-formed block, one true bit of the executable
reference Stream-Merge result is equivalent to an explicit fixed-wire shell

`exists choice, forall query, exists inner, OutputBitMatrix ...`.

The outer wire chooses `found` plus a selected code, or canonical
`noCircuit`.  A universal query selects either a truth-table coordinate or a
competitor code.  The inner fixed wire supplies padded agreement traces or a
complete code-failure witness.

The row predicate contains only executable bounded finite loops after the
three wires are supplied, but its operational polynomial running time has not
been proved.  This theorem is deliberately fixed-slice: the request parameters
remain Lean indices/arguments.  Consequently it is not yet a `Sigma_3`
language-membership theorem and not a PH-collapse or streaming-runtime theorem.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeEncodedPrenex

open StreamMerge
open StreamMergeChoice
open StreamMergeOutputFormula
open StreamMergeFailureMatrix
open StreamMergeAgreementMatrix
open StreamMergeOptimalityMatrix
open StreamMergePrenexWire

/-- One decidable fixed-wire row after the three witnesses have been supplied. -/
def OutputBitMatrix {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s))
    (choice : ChoiceWire n s) (query : QueryWire n s)
    (inner : InnerWire n s) : Prop :=
  if choiceTag choice then
    match DAGCodec.decode (choiceCode choice) with
    | none => False
    | some selected =>
        StreamMergeWire.outputBit
            (StreamMerge.Result.found (choiceCode choice)) position = true ∧
          selected.val.UsesOnlyAndOrNot ∧
            if queryTag query then
              CompetitorMatrix prior block hwindow
                (choiceCode choice) selected (queryCode query) inner
            else
              AgreementMatrix prior selected block hwindow
                (queryCoordinate query) inner
  else
    choiceCode choice = zeroCode n s ∧
      StreamMergeWire.outputBit
          (StreamMerge.Result.noCircuit : StreamMerge.Result n s)
          position = true ∧
        FailureMatrix prior block hwindow (queryCode query) inner

instance instDecidableOutputBitMatrix
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s))
    (choice : ChoiceWire n s) (query : QueryWire n s)
    (inner : InnerWire n s) :
    Decidable (OutputBitMatrix prior block hwindow position
      choice query inner) := by
  unfold OutputBitMatrix
  by_cases hchoice : choiceTag choice = true
  · rw [if_pos hchoice]
    cases hdecode : DAGCodec.decode (choiceCode choice) with
    | none => infer_instance
    | some selected =>
        simp only
        by_cases hquery : queryTag query = true
        · rw [if_pos hquery]
          infer_instance
        · rw [if_neg hquery]
          infer_instance
  · rw [if_neg hchoice]
    infer_instance

/-- Executable Boolean facade for the complete fixed-wire row predicate. -/
def check {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s))
    (choice : ChoiceWire n s) (query : QueryWire n s)
    (inner : InnerWire n s) : Bool :=
  decide (OutputBitMatrix prior block hwindow position choice query inner)

@[simp] theorem check_eq_true_iff
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s))
    (choice : ChoiceWire n s) (query : QueryWire n s)
    (inner : InnerWire n s) :
    check prior block hwindow position choice query inner = true ↔
      OutputBitMatrix prior block hwindow position choice query inner := by
  simp [check]

/-- The explicit fixed-wire `exists-forall-exists` shell over a decidable row. -/
def EncodedEAEShell {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s)) : Prop :=
  Exists fun choice : ChoiceWire n s =>
    forall query : QueryWire n s,
      Exists fun inner : InnerWire n s =>
        OutputBitMatrix prior block hwindow position choice query inner

/-! ## Exact output-bit equivalence -/

/--
One true reference output bit has exactly the encoded fixed-slice
`exists-forall-exists` shell above.
-/
theorem referenceOutputBit_eq_true_iff_encodedEAEShell
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s)) :
    StreamMergeWire.referenceOutputBit
        priorCode blockLength start block position = true ↔
      EncodedEAEShell prior block hwindow position := by
  rw [StreamMergeOutputFormula.referenceOutputBit_eq_true_iff
    block priorCode prior hprior hwindow position]
  constructor
  · rintro (⟨selectedCode, hoptimal, houtput⟩ |
      ⟨hnoCandidate, houtput⟩)
    · rcases hoptimal with
        ⟨selected, hselectedDecode, hselectedFits, hminimal⟩
      have hagreement :=
        (fits_iff_usesOnlyAndOrNot_and_forall_exists_agreementMatrix
          prior selected block hwindow).1 hselectedFits
      have hcompetitors :=
        (forall_exists_competitorMatrix_iff_minimality
          prior block hwindow selectedCode selected
            hselectedDecode hselectedFits).2 hminimal
      refine ⟨packChoice true selectedCode, ?_⟩
      intro query
      cases hquery : queryTag query with
      | false =>
          rcases hagreement.2 (queryCoordinate query) with
            ⟨inner, hinner⟩
          refine ⟨inner, ?_⟩
          simpa [OutputBitMatrix, hselectedDecode, hselectedFits.1,
            houtput, hquery] using hinner
      | true =>
          rcases hcompetitors (queryCode query) with ⟨inner, hinner⟩
          refine ⟨inner, ?_⟩
          simpa [OutputBitMatrix, hselectedDecode, hselectedFits.1,
            houtput, hquery] using hinner
    · refine ⟨packChoice false (zeroCode n s), ?_⟩
      intro query
      rcases (not_codeFits_iff_exists_failureWitness
        prior block hwindow (queryCode query)).1
          (hnoCandidate (queryCode query)) with ⟨inner, hinner⟩
      refine ⟨inner, ?_⟩
      simpa [OutputBitMatrix, houtput] using hinner
  · rintro ⟨choice, hrows⟩
    cases hchoice : choiceTag choice with
    | false =>
        rcases hrows (zeroQuery n s) with ⟨baseInner, hbase⟩
        have hbase' := hbase
        rw [OutputBitMatrix, hchoice] at hbase'
        refine Or.inr ⟨?_, hbase'.2.1⟩
        intro code
        rcases hrows
          (packQuery true (zeroCoordinate n) code) with
          ⟨inner, hinner⟩
        have hfailure :
            FailureMatrix prior block hwindow code inner := by
          rw [OutputBitMatrix, hchoice] at hinner
          simpa using hinner.2.2
        exact
          (not_codeFits_iff_exists_failureWitness
            prior block hwindow code).2 ⟨inner, hfailure⟩
    | true =>
        cases hdecode : DAGCodec.decode (choiceCode choice) with
        | none =>
            rcases hrows (zeroQuery n s) with ⟨inner, hinner⟩
            simp [OutputBitMatrix, hchoice, hdecode] at hinner
        | some selected =>
            rcases hrows (zeroQuery n s) with ⟨baseInner, hbase⟩
            have hbase' := hbase
            rw [OutputBitMatrix, hchoice, hdecode] at hbase'
            have houtput := hbase'.1
            have hbasis := hbase'.2.1
            have hagreementRows :
                forall coordinate : DAGCodec.BitString n,
                  exists inner : FailureWitness n s,
                    AgreementMatrix prior selected block hwindow
                      coordinate inner := by
              intro coordinate
              rcases hrows
                (packQuery false coordinate (zeroCode n s)) with
                ⟨inner, hinner⟩
              refine ⟨inner, ?_⟩
              rw [OutputBitMatrix, hchoice, hdecode] at hinner
              simpa using hinner.2.2
            have hselectedFits : Fits prior selected start block :=
              (fits_iff_usesOnlyAndOrNot_and_forall_exists_agreementMatrix
                prior selected block hwindow).2 ⟨hbasis, hagreementRows⟩
            have hcompetitorRows :
                forall otherCode : DAGCodec.Code n s,
                  exists inner : FailureWitness n s,
                    CompetitorMatrix prior block hwindow
                      (choiceCode choice) selected otherCode inner := by
              intro otherCode
              rcases hrows
                (packQuery true (zeroCoordinate n) otherCode) with
                ⟨inner, hinner⟩
              refine ⟨inner, ?_⟩
              rw [OutputBitMatrix, hchoice, hdecode] at hinner
              simpa using hinner.2.2
            have hminimal :=
              (forall_exists_competitorMatrix_iff_minimality
                prior block hwindow (choiceCode choice) selected
                  hdecode hselectedFits).1 hcompetitorRows
            refine Or.inl ⟨choiceCode choice, ?_, houtput⟩
            exact ⟨selected, hdecode, hselectedFits, hminimal⟩

/-- The same fixed-slice shell stated directly with the reflected Boolean
checker at every innermost row. -/
theorem referenceOutputBit_eq_true_iff_encodedEAECheck
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s)) :
    StreamMergeWire.referenceOutputBit
        priorCode blockLength start block position = true ↔
      Exists fun choice : ChoiceWire n s =>
        forall query : QueryWire n s,
          Exists fun inner : InnerWire n s =>
            check prior block hwindow position choice query inner = true := by
  rw [referenceOutputBit_eq_true_iff_encodedEAEShell
    block priorCode prior hprior hwindow position]
  simp [EncodedEAEShell]

end StreamMergeEncodedPrenex
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeEncodedPrenex.referenceOutputBit_eq_true_iff_encodedEAEShell
#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeEncodedPrenex.referenceOutputBit_eq_true_iff_encodedEAECheck
