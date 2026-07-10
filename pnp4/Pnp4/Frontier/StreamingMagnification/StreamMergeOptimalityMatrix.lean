import Pnp4.Frontier.StreamingMagnification.StreamMergeFailureMatrix

/-!
# Fixed-witness optimality matrix for Stream-Merge

The universal minimality clause in `StreamMergeChoice.IsOptimalCode` says that
every decoded fitting competitor is no better than the selected code.  This
module gives that clause the fixed-witness form needed by the logical MMW
frontier: for each external competitor body, an inner witness either certifies
malformed decoding, a wrong gate basis, or a traced semantic mismatch through
`StreamMergeFailureMatrix.FailureMatrix`, or the decoded fitting competitor
satisfies the required size-and-lexicographic order.

The result below is an exact semantic equivalence.  It makes no runtime,
polynomial-bound, finite-PH, or streaming-compilation claim.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeOptimalityMatrix

open StreamMerge
open StreamMergeChoice
open StreamMergeFailureMatrix

/-- The selected code precedes a decoded fitting competitor in the exact
size-then-serialized-lex order used by `IsOptimalCode`. -/
def OrderOK {n s : Nat}
    (selectedCode : DAGCodec.Code n s)
    (selected : DAGCodec.BoundedCircuit n s)
    (otherCode : DAGCodec.Code n s)
    (other : DAGCodec.BoundedCircuit n s) : Prop :=
  selected.val.gateCount <= other.val.gateCount /\
    (selected.val.gateCount = other.val.gateCount ->
      SerializedLexLE selectedCode otherCode)

instance instDecidableOrderOK {n s : Nat}
    (selectedCode : DAGCodec.Code n s)
    (selected : DAGCodec.BoundedCircuit n s)
    (otherCode : DAGCodec.Code n s)
    (other : DAGCodec.BoundedCircuit n s) :
    Decidable (OrderOK selectedCode selected otherCode other) := by
  unfold OrderOK
  infer_instance

/--
One fixed-witness competitor row.  The left branch delegates every reason why
`otherCode` is not a candidate to `FailureMatrix`; the right branch only
decodes the body and checks the exact order required of a genuine competitor.
It deliberately does not recompute the whole-prefix `Fits` predicate: a
fitting body cannot pass `FailureMatrix`, while a nonfitting body has a fixed
failure witness.
-/
def CompetitorMatrix {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (selectedCode : DAGCodec.Code n s)
    (selected : DAGCodec.BoundedCircuit n s)
    (otherCode : DAGCodec.Code n s)
    (inner : FailureWitness n s) : Prop :=
  FailureMatrix prior block hwindow otherCode inner \/
    match DAGCodec.decode otherCode with
    | none => False
    | some other =>
        OrderOK selectedCode selected otherCode other

instance instDecidableCompetitorMatrix
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (selectedCode : DAGCodec.Code n s)
    (selected : DAGCodec.BoundedCircuit n s)
    (otherCode : DAGCodec.Code n s)
    (inner : FailureWitness n s) :
    Decidable
      (CompetitorMatrix prior block hwindow selectedCode selected
        otherCode inner) := by
  unfold CompetitorMatrix
  split <;> infer_instance

/--
Assuming the outer selected body decodes and fits, the fixed-witness
`forall`-`exists` competitor formula is exactly the universal minimality
conjunct appearing in `IsOptimalCode`.
-/
theorem forall_exists_competitorMatrix_iff_minimality
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (selectedCode : DAGCodec.Code n s)
    (selected : DAGCodec.BoundedCircuit n s)
    (_hselectedDecode : DAGCodec.decode selectedCode = some selected)
    (_hselectedFits : Fits prior selected start block) :
    (forall otherCode : DAGCodec.Code n s,
      exists inner : FailureWitness n s,
        CompetitorMatrix prior block hwindow selectedCode selected
          otherCode inner) <->
      forall (otherCode : DAGCodec.Code n s)
        (other : DAGCodec.BoundedCircuit n s),
        DAGCodec.decode otherCode = some other ->
        Fits prior other start block ->
        selected.val.gateCount <= other.val.gateCount /\
          (selected.val.gateCount = other.val.gateCount ->
            SerializedLexLE selectedCode otherCode) := by
  constructor
  · intro hmatrix otherCode other hdecode hfits
    rcases hmatrix otherCode with ⟨inner, hfailure | horder⟩
    · have hnotCodeFits : Not (CodeFits prior start block otherCode) :=
        (not_codeFits_iff_exists_failureWitness
          prior block hwindow otherCode).2 ⟨inner, hfailure⟩
      exact (hnotCodeFits ⟨other, hdecode, hfits⟩).elim
    · rw [hdecode] at horder
      simpa [OrderOK] using horder
  · intro hminimal otherCode
    by_cases hcodeFits : CodeFits prior start block otherCode
    · rcases hcodeFits with ⟨other, hdecode, hfits⟩
      refine ⟨zeroWitness n s, Or.inr ?_⟩
      rw [hdecode]
      simpa [OrderOK] using
        hminimal otherCode other hdecode hfits
    · rcases (not_codeFits_iff_exists_failureWitness
        prior block hwindow otherCode).1 hcodeFits with
        ⟨inner, hfailure⟩
      exact ⟨inner, Or.inl hfailure⟩

/-- With the selected decode-and-fit witnesses fixed, the complete
`IsOptimalCode` predicate is equivalent to the fixed-witness competitor
formula. -/
theorem isOptimalCode_iff_forall_exists_competitorMatrix
    {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (selectedCode : DAGCodec.Code n s)
    (selected : DAGCodec.BoundedCircuit n s)
    (hselectedDecode : DAGCodec.decode selectedCode = some selected)
    (hselectedFits : Fits prior selected start block) :
    IsOptimalCode prior start block selectedCode <->
      forall otherCode : DAGCodec.Code n s,
        exists inner : FailureWitness n s,
          CompetitorMatrix prior block hwindow selectedCode selected
            otherCode inner := by
  constructor
  · rintro ⟨selected', hdecode', _hfits', hminimal⟩
    have hselected : selected' = selected := by
      exact Option.some.inj (hdecode'.symm.trans hselectedDecode)
    subst selected'
    exact
      (forall_exists_competitorMatrix_iff_minimality
        prior block hwindow selectedCode selected
          hselectedDecode hselectedFits).2 hminimal
  · intro hmatrix
    refine ⟨selected, hselectedDecode, hselectedFits, ?_⟩
    exact
      (forall_exists_competitorMatrix_iff_minimality
        prior block hwindow selectedCode selected
          hselectedDecode hselectedFits).1 hmatrix

end StreamMergeOptimalityMatrix
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeOptimalityMatrix.forall_exists_competitorMatrix_iff_minimality
#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeOptimalityMatrix.isOptimalCode_iff_forall_exists_competitorMatrix
