import Pnp4.Frontier.StreamingMagnification.StreamMergeChoice
import Pnp4.Frontier.StreamingMagnification.StreamMergeWire

/-!
# Search-free formula for one Stream-Merge output bit

For a valid prior body and a well-formed window, malformed result tags are
impossible.  This module decomposes one reference output bit into exactly the
two remaining semantic branches: an existential optimal found code, or
universal failure of all fixed-length candidate codes.

This is the logical shell of the MMW output-bit argument.  It deliberately
makes no finite-PH or polynomial-time claim; the local counterexample and
gate-trace matrices are separate layers.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeOutputFormula

open StreamMerge
open StreamMergeChoice

/-- Exact found/no-circuit decomposition of one `true` output bit. -/
theorem referenceOutputBit_eq_true_iff
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block)
    (position : Fin (StreamMergeWire.wireLength n s)) :
    StreamMergeWire.referenceOutputBit
        priorCode blockLength start block position = true <->
      (exists code : DAGCodec.Code n s,
        IsOptimalCode prior start block code /\
          StreamMergeWire.outputBit
            (StreamMerge.Result.found code) position = true) \/
      ((forall code : DAGCodec.Code n s,
          Not (CodeFits prior start block code)) /\
        StreamMergeWire.outputBit
          (StreamMerge.Result.noCircuit : StreamMerge.Result n s)
          position = true) := by
  constructor
  · intro hbit
    cases hchoice : selectCode prior start block with
    | none =>
        right
        constructor
        · have hmerge :
              referenceStreamMerge priorCode blockLength start block =
                StreamMerge.Result.noCircuit := by
            rw [referenceStreamMerge_valid_eq
              block priorCode prior hprior hwindow, hchoice]
          exact
            (referenceStreamMerge_noCircuit_iff_forall_not_codeFits
              block priorCode prior hprior hwindow).mp hmerge
        · simpa [StreamMergeWire.referenceOutputBit,
            referenceStreamMerge_valid_eq
              block priorCode prior hprior hwindow,
            hchoice] using hbit
    | some code =>
        left
        refine ⟨code, ?_, ?_⟩
        · exact
            (selectCode_eq_some_iff_isOptimal
              prior start block code).mp hchoice
        · simpa [StreamMergeWire.referenceOutputBit,
            referenceStreamMerge_valid_eq
              block priorCode prior hprior hwindow,
            hchoice] using hbit
  · rintro (⟨code, hoptimal, hbit⟩ | ⟨habsent, hbit⟩)
    · have hmerge :
          referenceStreamMerge priorCode blockLength start block =
            StreamMerge.Result.found code :=
        (referenceStreamMerge_found_iff_isOptimal
          block priorCode code prior hprior hwindow).mpr hoptimal
      simpa [StreamMergeWire.referenceOutputBit, hmerge] using hbit
    · have hmerge :
          referenceStreamMerge priorCode blockLength start block =
            StreamMerge.Result.noCircuit :=
        (referenceStreamMerge_noCircuit_iff_forall_not_codeFits
          block priorCode prior hprior hwindow).mpr habsent
      simpa [StreamMergeWire.referenceOutputBit, hmerge] using hbit

end StreamMergeOutputFormula
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeOutputFormula.referenceOutputBit_eq_true_iff
