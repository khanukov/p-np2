import Pnp4.Frontier.StreamingMagnification.StreamMergeCorrectness
import Mathlib.Data.Fin.Tuple.Take

/-!
# Index-local Stream-Merge agreement

`StreamMerge.Fits` is intentionally convenient for the executable reference
search: it compares two materialized prefix lists.  This module gives the
equivalent index-local view needed by later logical encodings.

For a well-formed request, `expectedBit` reads exactly one old-prefix bit or
one literal block bit.  `candidateBit` reads the candidate circuit at the
same physical truth-table coordinate.  We prove that `Fits` is precisely the
paper-basis condition together with equality of these two bits at every
coordinate of the enlarged prefix.  Once the paper-basis condition is known,
failure of `Fits` is therefore witnessed by one concrete unequal coordinate.

No complexity-class or running-time claim is made here.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeAgreement

open StandardDAG
open TotalSearch
open StreamMerge

/-! ## Local expected and candidate bits -/

/-- The candidate circuit bit at one coordinate of the enlarged prefix. -/
def candidateBit {n s blockLength start : Nat}
    (candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length)) : Bool :=
  Fin.take (start + block.length) (nextConsumed_le hwindow)
    (circuitTruthTable candidate.val) index

/--
The expected bit at one coordinate of a well-formed merge request.

The first `start` coordinates are read from the prior circuit.  The remaining
`block.length` coordinates are read directly from the supplied literal block.
-/
def expectedBit {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin (start + block.length)) : Bool :=
  Fin.append
    (Fin.take start hwindow.1 (circuitTruthTable prior.val))
    block.get index

@[simp] theorem expectedBit_prefix {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin start) :
    expectedBit prior block hwindow (Fin.castAdd block.length index) =
      circuitTruthTable prior.val (Fin.castLE hwindow.1 index) := by
  simp [expectedBit, Fin.take]

@[simp] theorem expectedBit_block {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (index : Fin block.length) :
    expectedBit prior block hwindow (Fin.natAdd start index) = block.get index := by
  simp [expectedBit]

/-- Pointwise equality on every coordinate constrained by this merge. -/
def PointwiseAgreement {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) : Prop :=
  forall index : Fin (start + block.length),
    candidateBit candidate block hwindow index =
      expectedBit prior block hwindow index

instance instDecidablePointwiseAgreement
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) :
    Decidable (PointwiseAgreement prior candidate block hwindow) := by
  unfold PointwiseAgreement
  exact Fintype.decidableForallFintype

/-! ## Connection to the existing materialized-prefix specification -/

theorem ofFn_candidateBit {n s blockLength start : Nat}
    (candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) :
    List.ofFn (candidateBit candidate block hwindow) =
      (circuitBits candidate.val).take (start + block.length) := by
  simpa [candidateBit, circuitBits, tableBits] using
    (Fin.ofFn_take_eq_take_ofFn
      (nextConsumed_le hwindow) (circuitTruthTable candidate.val))

theorem ofFn_expectedBit {n s blockLength start : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) :
    List.ofFn (expectedBit prior block hwindow) =
      targetPrefix prior start block := by
  unfold expectedBit targetPrefix circuitBits tableBits
  rw [List.ofFn_fin_append,
    Fin.ofFn_take_eq_take_ofFn hwindow.1,
    List.ofFn_get]

/--
Exact index-local form of `Fits`: target basis plus agreement at every
coordinate below `start + block.length`.
-/
theorem fits_iff_usesOnlyAndOrNot_and_pointwiseAgreement
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block) :
    Fits prior candidate start block <->
      candidate.val.UsesOnlyAndOrNot /\
        PointwiseAgreement prior candidate block hwindow := by
  constructor
  · rintro ⟨hbasis, hagreement⟩
    refine ⟨hbasis, ?_⟩
    have hlists :
        List.ofFn (candidateBit candidate block hwindow) =
          List.ofFn (expectedBit prior block hwindow) := by
      rw [ofFn_candidateBit, ofFn_expectedBit, hagreement]
    have hfunctions := List.ofFn_inj.mp hlists
    intro index
    exact congrFun hfunctions index
  · rintro ⟨hbasis, hagreement⟩
    refine ⟨hbasis, ?_⟩
    have hfunctions :
        candidateBit candidate block hwindow =
          expectedBit prior block hwindow := by
      funext index
      exact hagreement index
    have hlists := congrArg List.ofFn hfunctions
    rwa [ofFn_candidateBit, ofFn_expectedBit] at hlists

/-! ## Concrete counterexamples -/

/--
For an already decoded candidate in the exact paper basis, failure of `Fits`
is equivalent to one explicit unequal prefix coordinate.
-/
theorem not_fits_iff_exists_counterexample
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (hbasis : candidate.val.UsesOnlyAndOrNot) :
    Not (Fits prior candidate start block) <->
      Exists fun index : Fin (start + block.length) =>
        candidateBit candidate block hwindow index ≠
          expectedBit prior block hwindow index := by
  rw [fits_iff_usesOnlyAndOrNot_and_pointwiseAgreement
    prior candidate block hwindow]
  simp only [hbasis, true_and, PointwiseAgreement]
  exact Decidable.not_forall

/-- A displayed counterexample directly refutes `Fits` for a paper candidate. -/
theorem not_fits_of_counterexample
    {n s blockLength start : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s) (block : List Bool)
    (hwindow : WindowWellFormed n blockLength start block)
    (hbasis : candidate.val.UsesOnlyAndOrNot)
    (index : Fin (start + block.length))
    (hcounterexample :
      candidateBit candidate block hwindow index ≠
        expectedBit prior block hwindow index) :
    Not (Fits prior candidate start block) :=
  (not_fits_iff_exists_counterexample
    prior candidate block hwindow hbasis).2 ⟨index, hcounterexample⟩

end StreamMergeAgreement
end StreamingMagnification
end Frontier
end Pnp4
