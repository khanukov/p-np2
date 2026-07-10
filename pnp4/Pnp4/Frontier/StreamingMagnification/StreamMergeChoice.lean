import Pnp4.Frontier.StreamingMagnification.StreamMergeCorrectness

/-!
# Search-free characterization of the Stream-Merge choice

`StreamMerge.selectCode` is an executable exhaustive reference search.  The
MMW output-bit argument must instead expose the selected code by a witness and
verify that no better fitting code exists.  This module proves the exact
semantic equivalence, without making a complexity-class or runtime claim.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeChoice

open StreamMerge

/-- A canonical external body decodes to a circuit satisfying the request. -/
def CodeFits {n s : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (start : Nat) (block : List Bool)
    (code : DAGCodec.Code n s) : Prop :=
  exists candidate : DAGCodec.BoundedCircuit n s,
    DAGCodec.decode code = some candidate /\
      Fits prior candidate start block

/-- Circuit-level existence and code-level existence are exactly equivalent. -/
theorem exists_codeFits_iff_hasCandidate
    {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) :
    (exists code : DAGCodec.Code n s,
      CodeFits prior start block code) <->
      HasCandidate prior start block := by
  constructor
  · rintro ⟨code, candidate, _hdecode, hfits⟩
    exact ⟨candidate, hfits⟩
  · rintro ⟨candidate, hfits⟩
    exact ⟨DAGCodec.encode candidate, candidate,
      DAGCodec.decode_encode candidate, hfits⟩

/-- Genuine absence is the universal failure of every fixed-length body. -/
theorem not_hasCandidate_iff_forall_not_codeFits
    {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) :
    Not (HasCandidate prior start block) <->
      forall code : DAGCodec.Code n s,
        Not (CodeFits prior start block code) := by
  rw [← exists_codeFits_iff_hasCandidate prior start block]
  simp only [not_exists]

/--
A canonical external body is the exact size-then-serialized-lex minimum among
all bodies satisfying the merge request.  Successful decoding supplies the
canonicality and gate-count bound.
-/
def IsOptimalCode {n s : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (start : Nat) (block : List Bool)
    (code : DAGCodec.Code n s) : Prop :=
  exists selected : DAGCodec.BoundedCircuit n s,
    DAGCodec.decode code = some selected /\
      Fits prior selected start block /\
      forall (otherCode : DAGCodec.Code n s)
        (other : DAGCodec.BoundedCircuit n s),
        DAGCodec.decode otherCode = some other ->
        Fits prior other start block ->
        selected.val.gateCount <= other.val.gateCount /\
          (selected.val.gateCount = other.val.gateCount ->
            SerializedLexLE code otherCode)

/-- The exhaustive reference search returns exactly the semantic optimum. -/
theorem selectCode_eq_some_iff_isOptimal
    {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) (code : DAGCodec.Code n s) :
    selectCode prior start block = some code <->
      IsOptimalCode prior start block code := by
  constructor
  · intro hselect
    exact selectCode_some_optimal hselect
  · rintro ⟨selected, hdecode, hfits, hminimal⟩
    cases hchoice : selectCode prior start block with
    | none =>
        have hnone : Not (HasCandidate prior start block) :=
          (selectCode_eq_none_iff prior start block).mp hchoice
        exact (hnone ⟨selected, hfits⟩).elim
    | some chosenCode =>
        rcases selectCode_some_optimal hchoice with
          ⟨chosen, hchosenDecode, hchosenFits, hchosenMinimal⟩
        have hselectedLE :=
          hminimal chosenCode chosen hchosenDecode hchosenFits
        have hchosenLE :=
          hchosenMinimal code selected hdecode hfits
        have hgate : selected.val.gateCount = chosen.val.gateCount :=
          Nat.le_antisymm hselectedLE.1 hchosenLE.1
        have hcodeLE : SerializedLexLE code chosenCode :=
          hselectedLE.2 hgate
        have hchosenCodeLE : SerializedLexLE chosenCode code :=
          hchosenLE.2 hgate.symm
        have hindex : serializedIndex code = serializedIndex chosenCode :=
          Fin.le_antisymm hcodeLE hchosenCodeLE
        have hcode : code = chosenCode :=
          serializedIndex_injective hindex
        subst chosenCode
        rfl

/--
On a well-formed request with a valid prior body, the public `found` result is
equivalent to the search-free optimal-code predicate.
-/
theorem referenceStreamMerge_found_iff_isOptimal
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode code : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block) :
    referenceStreamMerge priorCode blockLength start block =
        StreamMerge.Result.found code <->
      IsOptimalCode prior start block code := by
  rw [referenceStreamMerge_found_iff_selectCode
    block priorCode code prior hprior hwindow]
  exact selectCode_eq_some_iff_isOptimal prior start block code

/-- The public `noCircuit` branch is the universal code-failure formula. -/
theorem referenceStreamMerge_noCircuit_iff_forall_not_codeFits
    {n s blockLength start : Nat} (block : List Bool)
    (priorCode : DAGCodec.Code n s)
    (prior : DAGCodec.BoundedCircuit n s)
    (hprior : DAGCodec.decode priorCode = some prior)
    (hwindow : WindowWellFormed n blockLength start block) :
    referenceStreamMerge priorCode blockLength start block =
        StreamMerge.Result.noCircuit <->
      forall code : DAGCodec.Code n s,
        Not (CodeFits prior start block code) := by
  rw [referenceStreamMerge_noCircuit_iff
    block priorCode prior hprior hwindow]
  exact not_hasCandidate_iff_forall_not_codeFits prior start block

end StreamMergeChoice
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeChoice.selectCode_eq_some_iff_isOptimal
#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeChoice.referenceStreamMerge_found_iff_isOptimal
#print axioms Pnp4.Frontier.StreamingMagnification.StreamMergeChoice.referenceStreamMerge_noCircuit_iff_forall_not_codeFits
