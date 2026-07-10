import Pnp4.Frontier.StreamingMagnification.EncodedTotalSearch
import Pnp4.Frontier.StreamingMagnification.PolynomialBounds
import Mathlib.Tactic

/-!
# The concrete MMW total-search streaming predicate

`PolynomialBounds` intentionally separates operational resource quantifiers
from the problem being solved.  This module instantiates that generic layer
with the exact fixed-length, tagged, standard-DAG total search-MCSP wire from
`EncodedTotalSearch`.

A correct completed run must consume the whole one-way table, emit exactly
one result wire, parse and validate that wire, and satisfy both the positive
and negative semantic branches of `TotalSearch.Correct`.  No function from a
whole table to a result is inserted into the operational program.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace MMWProblem

open StreamingRAM
open PolynomialBounds

/-- Convert a list to an exact result wire, rejecting every wrong length. -/
def listToResultWire? {n s : Nat} (bits : List Bool) :
    Option (EncodedTotalSearch.ResultWire n s) :=
  if hlength : bits.length = 1 + DAGCodec.codeLength n s then
    some fun index => bits.get ⟨index.val, by
      rw [hlength]
      exact index.isLt⟩
  else
    none

/-- Materialize a fixed result wire in emitted left-to-right order. -/
def resultWireBits {n s : Nat}
    (wire : EncodedTotalSearch.ResultWire n s) : List Bool :=
  List.ofFn wire

@[simp]
theorem resultWireBits_length {n s : Nat}
    (wire : EncodedTotalSearch.ResultWire n s) :
    (resultWireBits wire).length = 1 + DAGCodec.codeLength n s := by
  simp [resultWireBits]

@[simp]
theorem listToResultWire_resultWireBits {n s : Nat}
    (wire : EncodedTotalSearch.ResultWire n s) :
    listToResultWire? (resultWireBits wire) = some wire := by
  simp only [listToResultWire?, resultWireBits, List.length_ofFn, dite_true]
  congr 1
  funext index
  simp

/--
Exact correctness of one completed operational run for `search-MCSP[s_k]`.
The program argument remains visible in the generic specification type even
though semantic validation needs only its completed trace.
-/
def TotalSearchRunCorrect (k : Nat) :
    CompletedRunSpecification truthTableLength :=
  fun _program n table completed =>
    completed.bitsRead = truthTableLength n /\
      Exists fun wire :
          EncodedTotalSearch.ResultWire n (thresholdSchedule k n) =>
        Exists fun result :
            TotalSearch.MCSPResult n (thresholdSchedule k n) =>
          listToResultWire? completed.output = some wire /\
            EncodedTotalSearch.decodeSemantic wire = some result /\
            TotalSearch.Correct table result

/-- One uniform operational program with full polynomial resource quantifiers. -/
def PolyStreamingSearchMCSPSolvable (k : Nat) : Prop :=
  MMWPolyStreamingSolvable k (TotalSearchRunCorrect k)

/-- The exact MMW lower-bound antecedent negates the whole positive predicate. -/
def NoPolyStreamingSearchMCSPSolver (k : Nat) : Prop :=
  NoMMWPolyStreamingSolver k (TotalSearchRunCorrect k)

/-- The lower-bound name is definitionally the negation of the entire solver
existence statement, not a fixed exponent or a fixed program. -/
theorem noPolyStreamingSearchMCSPSolver_iff (k : Nat) :
    NoPolyStreamingSearchMCSPSolver k <->
      Not (PolyStreamingSearchMCSPSolvable k) := by
  rfl

/-- A semantically correct completed output decides exact standard-DAG MCSP. -/
theorem completedRun_decision_iff
    {k n : Nat} {program : Program}
    {table : Input (truthTableLength n)}
    {completed : CompletedRun program table}
    (hcorrect : TotalSearchRunCorrect k program n table completed) :
    Exists fun wire :
        EncodedTotalSearch.ResultWire n (thresholdSchedule k n) =>
      Exists fun result :
          TotalSearch.MCSPResult n (thresholdSchedule k n) =>
        listToResultWire? completed.output = some wire /\
          EncodedTotalSearch.decodeSemantic wire = some result /\
          (EncodedTotalSearch.decisionFromWire wire = some true <->
            TotalSearch.HasCircuit n (thresholdSchedule k n) table) := by
  rcases hcorrect.2 with ⟨wire, result, hwire, hdecode, hsemantic⟩
  refine ⟨wire, result, hwire, hdecode, ?_⟩
  exact EncodedTotalSearch.decisionFromWire_eq_some_true_iff
    hdecode hsemantic

end MMWProblem
end StreamingMagnification
end Frontier
end Pnp4
