import Pnp4.Frontier.StreamingMagnification.DAGEvalTrace
import Pnp4.Frontier.StreamingMagnification.StreamMergeAgreement

/-!
# Trace-certified Stream-Merge counterexamples

This module refines the concrete mismatch supplied by
`StreamMergeAgreement.not_fits_iff_exists_counterexample`.  At one constrained
truth-table coordinate, a certificate now carries complete local gate-value
traces for both the candidate circuit and the prior circuit.  The traces are
checked only through `DAGEvalTrace.FlatIsTrace`; their reconstructed outputs
are then compared with the prior-or-literal expected bit.

For a decoded candidate already known to use the exact paper basis, such
trace data exists exactly when `StreamMerge.Fits` fails.

No complexity-class or running-time claim is made here.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeTracedCounterexample

open Pnp3.ComplexityInterfaces
open StandardDAG
open TotalSearch
open StreamMerge
open StreamMergeAgreement
open DAGEvalTrace

/-! ## One indexed trace instance -/

/-- The physical truth-table coordinate constrained by a merge index. -/
def tableIndex {n blockLength start : Nat} {block : List Bool}
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length)) : Fin (2 ^ n) :=
  Fin.castLE (nextConsumed_le hwindow) index

/-- The Boolean input assignment at one constrained physical coordinate. -/
def indexInput {n blockLength start : Nat} {block : List Bool}
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length)) : Bitstring n :=
  lexInput n (tableIndex hwindow index)

/--
Expected bit reconstructed from one prior-circuit trace on the old-prefix
branch, or read directly from the literal block on the new-block branch.
-/
def tracedExpectedBit {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    (priorValues : FlatGateValues prior.val) : Bool :=
  Fin.append
    (fun prefixIndex : Fin start =>
      flatOutputValue prior.val
        (lexInput n (Fin.castLE hwindow.1 prefixIndex)) priorValues)
    block.get index

/--
All data certifying one genuine mismatch: the index, a locally valid trace
for each circuit at that index, and inequality of the reconstructed bits.
-/
def TracedCounterexampleAt {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    (candidateValues : FlatGateValues candidate.val)
    (priorValues : FlatGateValues prior.val) : Prop :=
  FlatIsTrace candidate.val (indexInput hwindow index) candidateValues /\
    FlatIsTrace prior.val (indexInput hwindow index) priorValues /\
      flatOutputValue candidate.val (indexInput hwindow index)
          candidateValues ≠
        tracedExpectedBit prior block hwindow index priorValues

/-- Existential package containing an index and both full gate-value traces. -/
def HasTracedCounterexample {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) : Prop :=
  Exists fun index : Fin (start + block.length) =>
    Exists fun candidateValues : FlatGateValues candidate.val =>
      Exists fun priorValues : FlatGateValues prior.val =>
        TracedCounterexampleAt prior candidate block hwindow index
          candidateValues priorValues

/-! ## Trace soundness at the selected coordinate -/

/-- A checked candidate trace reconstructs exactly the existing local bit. -/
theorem flatOutputValue_eq_candidateBit_of_isTrace
    {n s blockLength start : Nat}
    (candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    {values : FlatGateValues candidate.val}
    (htrace : FlatIsTrace candidate.val (indexInput hwindow index) values) :
    flatOutputValue candidate.val (indexInput hwindow index) values =
      candidateBit candidate block hwindow index := by
  rw [flatOutputValue_eq_eval_of_isTrace candidate.val
    (indexInput hwindow index) htrace]
  rfl

/-- A checked prior trace reconstructs exactly the old-prefix expected bit. -/
theorem tracedExpectedBit_eq_expectedBit_of_isTrace
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length))
    {values : FlatGateValues prior.val}
    (htrace : FlatIsTrace prior.val (indexInput hwindow index) values) :
    tracedExpectedBit prior block hwindow index values =
      expectedBit prior block hwindow index := by
  exact Fin.addCases
    (motive := fun index =>
      forall values : FlatGateValues prior.val,
        FlatIsTrace prior.val (indexInput hwindow index) values ->
          tracedExpectedBit prior block hwindow index values =
            expectedBit prior block hwindow index)
    (fun prefixIndex values htrace => by
      rw [tracedExpectedBit, Fin.append_left, expectedBit_prefix]
      have htrace' :
          FlatIsTrace prior.val
            (lexInput n (Fin.castLE hwindow.1 prefixIndex)) values := by
        simpa [indexInput, tableIndex, lexInput] using htrace
      rw [flatOutputValue_eq_eval_of_isTrace prior.val
        (lexInput n (Fin.castLE hwindow.1 prefixIndex)) htrace']
      rfl)
    (fun blockIndex values _htrace => by
      simp [tracedExpectedBit, expectedBit_block])
    index values htrace

/-! ## Exact equivalence with failure of Fits -/

/--
For a decoded bounded candidate in the exact paper basis, `Fits` fails iff
there is one index carrying locally valid traces for both circuits and an
unequal reconstructed expected bit.
-/
theorem not_fits_iff_hasTracedCounterexample
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (hbasis : candidate.val.UsesOnlyAndOrNot) :
    Not (Fits prior candidate start block) <->
      HasTracedCounterexample prior candidate block hwindow := by
  constructor
  · intro hnotFits
    rcases (not_fits_iff_exists_counterexample
      prior candidate block hwindow hbasis).1 hnotFits with
      ⟨index, hcounterexample⟩
    rcases flat_exists_isTrace candidate.val (indexInput hwindow index) with
      ⟨candidateValues, hcandidateTrace⟩
    rcases flat_exists_isTrace prior.val (indexInput hwindow index) with
      ⟨priorValues, hpriorTrace⟩
    refine ⟨index, candidateValues, priorValues,
      hcandidateTrace, hpriorTrace, ?_⟩
    rw [flatOutputValue_eq_candidateBit_of_isTrace
      candidate block hwindow index hcandidateTrace]
    rw [tracedExpectedBit_eq_expectedBit_of_isTrace
      prior block hwindow index hpriorTrace]
    exact hcounterexample
  · rintro ⟨index, candidateValues, priorValues,
      hcandidateTrace, hpriorTrace, hcounterexample⟩
    apply (not_fits_iff_exists_counterexample
      prior candidate block hwindow hbasis).2
    refine ⟨index, ?_⟩
    rw [← flatOutputValue_eq_candidateBit_of_isTrace
      candidate block hwindow index hcandidateTrace]
    rw [← tracedExpectedBit_eq_expectedBit_of_isTrace
      prior block hwindow index hpriorTrace]
    exact hcounterexample

end StreamMergeTracedCounterexample
end StreamingMagnification
end Frontier
end Pnp4
