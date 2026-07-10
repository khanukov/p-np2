import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaPrefixClosure

/-!
# Exact handoff from the operational gamma front end to the real request tail

The fixed tagged machine works with the unary-prefix length and the remaining
binary payload of each gamma word.  The Stream-Merge codec, by contrast, is
indexed by the decoded values `n`, `s`, and `blockLength`.  This module proves
the exact conversion between those views and instantiates the arbitrary
suffix theorem with the real `start ++ prior ++ block ++ position` tail.

No parser for those remaining fields and no acceptance theorem is asserted.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalTaggedGamma

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity
open OperationalGammaZipper
open Pnp4.Frontier.ContractExpansion
open StreamMergeRequestCodec

/-! ## One codec gamma word as a zipper body -/

/-- Number of zeros before the leading one in the gamma code for `value`. -/
def codecGammaWidth (value : Nat) : Nat := bitLength (value + 1) - 1

theorem bitLength_eq_codecGammaWidth_add_one (value : Nat) :
    bitLength (value + 1) = codecGammaWidth value + 1 := by
  have hpositive := bitLength_pos_of_pos (Nat.succ_pos value)
  have hone : 1 ≤ bitLength (value + 1) := hpositive
  exact (Nat.sub_add_cancel hone).symm

/-- The low-order payload bits after the gamma word's leading one. -/
def codecGammaPayload (value : Nat) : List Bool :=
  List.ofFn fun index : Fin (codecGammaWidth value) =>
    gammaBit value
      ⟨bitLength (value + 1) + index.val, by
        rw [gammaLen_eq_zeros_add_bitLength]
        change bitLength (value + 1) + index.val <
          codecGammaWidth value + bitLength (value + 1)
        have hindex := index.isLt
        rw [bitLength_eq_codecGammaWidth_add_one]
        omega⟩

@[simp] theorem codecGammaPayload_length (value : Nat) :
    (codecGammaPayload value).length = codecGammaWidth value := by
  simp [codecGammaPayload]

/-- Literal list of all bits in the codec's canonical gamma word. -/
def codecGammaWord (value : Nat) : List Bool :=
  List.ofFn fun index : Fin (gammaLen value) => gammaBit value index

@[simp] theorem codecGammaWord_length (value : Nat) :
    (codecGammaWord value).length = gammaLen value := by
  simp only [codecGammaWord, List.length_ofFn]

/-- The codec gamma word is exactly the raw body expected by the zipper. -/
theorem codecGammaWord_eq_gammaBody (value : Nat) :
    codecGammaWord value =
      gammaBody (codecGammaWidth value) (codecGammaPayload value) := by
  apply List.ext_getElem
  · simp only [codecGammaWord_length, gammaBody_length,
      codecGammaPayload_length]
    rw [gammaLen_eq_two_mul_zeros_add_one]
    simp only [codecGammaWidth]
    omega
  · intro position hword hbody
    simp only [codecGammaWord, List.getElem_ofFn]
    by_cases hprefix : position < codecGammaWidth value
    · simp only [gammaBody]
      have hprefix' :
          position < (List.replicate (codecGammaWidth value) false).length := by
        simpa using hprefix
      rw [List.getElem_append_left hprefix', List.getElem_replicate]
      exact gammaBit_zero_prefix value hprefix
    · have hge : codecGammaWidth value ≤ position := Nat.le_of_not_gt hprefix
      by_cases hterminator : position = codecGammaWidth value
      · subst position
        simp only [gammaBody]
        have hge' :
            (List.replicate (codecGammaWidth value) false).length ≤
              codecGammaWidth value := by simp
        rw [List.getElem_append_right hge']
        simp only [List.length_replicate, Nat.sub_self, List.getElem_cons_zero]
        convert gammaBit_terminator value using 1
      · have hgt : codecGammaWidth value < position := by omega
        let payloadPosition := position - (codecGammaWidth value + 1)
        have hpayload : payloadPosition < codecGammaWidth value := by
          have hword' : position < gammaLen value := by simpa using hword
          rw [gammaLen_eq_two_mul_zeros_add_one] at hword'
          simp only [payloadPosition, codecGammaWidth] at *
          omega
        have hposition :
            position = bitLength (value + 1) + payloadPosition := by
          rw [bitLength_eq_codecGammaWidth_add_one]
          simp only [payloadPosition]
          omega
        simp only [gammaBody]
        have hge' :
            (List.replicate (codecGammaWidth value) false).length ≤ position := by
          simpa using hge
        rw [List.getElem_append_right hge']
        have hoffset : position - (List.replicate
            (codecGammaWidth value) false).length = payloadPosition + 1 := by
          simp only [List.length_replicate, payloadPosition]
          omega
        simp only [hoffset, List.getElem_cons_succ]
        simp only [codecGammaPayload, List.getElem_ofFn]
        exact congrArg (gammaBit value) (Fin.ext hposition)

/-! ## The literal remainder of a canonical request -/

/-- The four fields that remain untouched after the operational front end has
finished the three gamma words. -/
def requestRawTail (request : RequestFields) : List Bool :=
  List.ofFn (startBits request) ++
    List.ofFn request.priorCode ++
      List.ofFn request.blockBits ++
        List.ofFn (positionBits request)

@[simp] theorem requestRawTail_length (request : RequestFields) :
    (requestRawTail request).length =
      startWidth request.n +
        (DAGCodec.codeLength request.n request.s +
          (StreamMerge.expectedLength request.n request.blockLength request.start +
            positionWidth request.n request.s)) := by
  simp [requestRawTail, startWidth]
  omega

/-- The canonical encoder is literally the tagged machine's three input
frames followed by the untouched four-field request tail. -/
theorem encodeRequest_list_eq_tripleInitialFrame_append_tail
    (request : RequestFields) :
    List.ofFn (encodeRequest request) =
      tripleInitialFrame
          (codecGammaWidth request.n) (codecGammaPayload request.n)
          (codecGammaWidth request.s) (codecGammaPayload request.s)
          (codecGammaWidth request.blockLength)
            (codecGammaPayload request.blockLength) ++
        requestRawTail request := by
  unfold StreamMergeRequestCodec.encodeRequest
  simp only [List.ofFn_fin_append]
  rw [← requestTagList_eq_codec]
  change requestTagList ++ (codecGammaWord request.n ++
      (codecGammaWord request.s ++ (codecGammaWord request.blockLength ++
        (List.ofFn (startBits request) ++ (List.ofFn request.priorCode ++
          (List.ofFn request.blockBits ++ List.ofFn (positionBits request))))))) = _
  rw [codecGammaWord_eq_gammaBody, codecGammaWord_eq_gammaBody,
    codecGammaWord_eq_gammaBody]
  simp only [tripleInitialFrame, requestTagList, requestRawTail,
    List.append_assoc]

/-- The operational three-word footprint ends at exactly the codec's first
`start` bit. -/
theorem startOffset_eq_codecTripleFootprint (n s blockLength : Nat) :
    startOffset n s blockLength =
      tripleFootprint (codecGammaWidth n) (codecGammaWidth s)
        (codecGammaWidth blockLength) := by
  unfold startOffset blockLengthOffset sOffset
  rw [show gammaLen n = 2 * codecGammaWidth n + 1 by
      simpa [codecGammaWidth] using gammaLen_eq_two_mul_zeros_add_one n]
  rw [show gammaLen s = 2 * codecGammaWidth s + 1 by
      simpa [codecGammaWidth] using gammaLen_eq_two_mul_zeros_add_one s]
  rw [show gammaLen blockLength = 2 * codecGammaWidth blockLength + 1 by
      simpa [codecGammaWidth] using
        gammaLen_eq_two_mul_zeros_add_one blockLength]
  simp only [tagLen, tripleFootprint]
  omega

theorem firstGammaStart_eq_tagLen : firstGammaStart = tagLen := by
  rfl

theorem secondGammaStart_eq_sOffset (n : Nat) :
    secondGammaStart (codecGammaWidth n) = sOffset n := by
  unfold secondGammaStart sOffset
  rw [show gammaLen n = 2 * codecGammaWidth n + 1 by
      simpa [codecGammaWidth] using gammaLen_eq_two_mul_zeros_add_one n]
  simp only [tagLen]
  omega

theorem thirdGammaStart_eq_blockLengthOffset (n s : Nat) :
    thirdGammaStart (codecGammaWidth n) (codecGammaWidth s) =
      blockLengthOffset n s := by
  unfold thirdGammaStart blockLengthOffset sOffset
  rw [show gammaLen n = 2 * codecGammaWidth n + 1 by
      simpa [codecGammaWidth] using gammaLen_eq_two_mul_zeros_add_one n]
  rw [show gammaLen s = 2 * codecGammaWidth s + 1 by
      simpa [codecGammaWidth] using gammaLen_eq_two_mul_zeros_add_one s]
  simp only [tagLen]
  omega

/-- The dependent length carried by `encodeRequest` is the operational prefix
footprint plus the literal raw tail length. -/
theorem encodedLength_eq_codecTripleFootprint_add_tail
    (request : RequestFields) :
    request.encodedLength =
      tripleFootprint (codecGammaWidth request.n)
          (codecGammaWidth request.s) (codecGammaWidth request.blockLength) +
        (requestRawTail request).length := by
  have hlength := congrArg List.length
    (encodeRequest_list_eq_tripleInitialFrame_append_tail request)
  simpa only [List.length_ofFn, List.length_append,
    tripleInitialFrame_length, codecGammaPayload_length] using hlength

theorem encodedLength_eq_startOffset_add_tail (request : RequestFields) :
    request.encodedLength =
      startOffset request.n request.s request.blockLength +
        (requestRawTail request).length := by
  rw [encodedLength_eq_codecTripleFootprint_add_tail,
    startOffset_eq_codecTripleFootprint]

/-- Cast-free slice API for the next parser stage: dropping the proved handoff
coordinate exposes exactly `start ++ prior ++ block ++ position`. -/
theorem encodeRequest_drop_startOffset_eq_rawTail (request : RequestFields) :
    (List.ofFn (encodeRequest request)).drop
        (startOffset request.n request.s request.blockLength) =
      requestRawTail request := by
  rw [encodeRequest_list_eq_tripleInitialFrame_append_tail,
    startOffset_eq_codecTripleFootprint]
  rw [← tripleInitialFrame_length
    (codecGammaPayload_length request.n)
    (codecGammaPayload_length request.s)
    (codecGammaPayload_length request.blockLength)]
  simp

/-- Dually, taking through `startOffset` returns exactly the tag and three
canonical gamma words used by the operational front end. -/
theorem encodeRequest_take_startOffset_eq_tripleInitialFrame
    (request : RequestFields) :
    (List.ofFn (encodeRequest request)).take
        (startOffset request.n request.s request.blockLength) =
      tripleInitialFrame
        (codecGammaWidth request.n) (codecGammaPayload request.n)
        (codecGammaWidth request.s) (codecGammaPayload request.s)
        (codecGammaWidth request.blockLength)
          (codecGammaPayload request.blockLength) := by
  rw [encodeRequest_list_eq_tripleInitialFrame_append_tail,
    startOffset_eq_codecTripleFootprint]
  rw [← tripleInitialFrame_length
    (codecGammaPayload_length request.n)
    (codecGammaPayload_length request.s)
    (codecGammaPayload_length request.blockLength)]
  simp

/-- Reading the canonical encoded request with blanks after its end is exactly
the framed gamma prefix followed by the four-field raw tail. -/
theorem finiteSuffixTape_encodeRequest_eq_framedTail
    (request : RequestFields) :
    finiteSuffixTape (List.ofFn (encodeRequest request)) =
      framedTape
        (tripleInitialFrame
          (codecGammaWidth request.n) (codecGammaPayload request.n)
          (codecGammaWidth request.s) (codecGammaPayload request.s)
          (codecGammaWidth request.blockLength)
            (codecGammaPayload request.blockLength))
        (finiteSuffixTape (requestRawTail request)) := by
  funext position
  rw [encodeRequest_list_eq_tripleInitialFrame_append_tail]
  exact (framedTape_finiteSuffixTape _ _ position).symm

/-! ## Direct bridge for the actual encoded request -/

/-- The actual initial configuration on `encodeRequest` agrees with the
natural-coordinate blank extension of that exact finite input. -/
theorem encodeRequest_initialConfig_finiteNatAgree
    (request : RequestFields) :
    TaggedFiniteNatAgree
      (TaggedExecutionTM.initialConfig (encodeRequest request))
      ⟨.tag0, 0, finiteSuffixTape (List.ofFn (encodeRequest request))⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  intro index
  unfold TM.initialConfig
  dsimp only
  unfold finiteSuffixTape
  by_cases hinput : index.val < request.encodedLength
  · simp only [hinput, dite_true]
    have hlist : index.val < (List.ofFn (encodeRequest request)).length := by
      simpa using hinput
    rw [List.getElem?_eq_getElem hlist]
    simp only [List.getElem_ofFn]
    congr
  · simp only [hinput, dite_false]
    rw [List.getElem?_eq_none_iff.mpr]
    · rfl
    · simpa using Nat.le_of_not_gt hinput

/-- The exact useful front-end time fits in the actual tape allocated for the
whole encoded request. -/
theorem codecTripleTime_lt_encodeRequest_tapeLength
    (request : RequestFields) :
    taggedTripleTime (codecGammaWidth request.n)
        (codecGammaWidth request.s) (codecGammaWidth request.blockLength) <
      TaggedExecutionTM.tapeLength request.encodedLength := by
  have hroom := taggedTripleTime_lt_extendedTapeLength
    (codecGammaPayload request.n) (codecGammaPayload request.s)
    (codecGammaPayload request.blockLength) (requestRawTail request)
  simpa only [codecGammaPayload_length,
    encodedLength_eq_codecTripleFootprint_add_tail] using hroom

/-- On the literal encoded request, the natural-coordinate front end reaches
`done` with its head exactly at `startOffset`; the remaining four fields are
still present verbatim as the finite suffix. -/
theorem taggedNatRun_encodeRequest_handoff (request : RequestFields) :
    taggedNatRun
        ⟨.tag0, 0, finiteSuffixTape (List.ofFn (encodeRequest request))⟩
        (taggedTripleTime (codecGammaWidth request.n)
          (codecGammaWidth request.s) (codecGammaWidth request.blockLength)) =
      ⟨.done, startOffset request.n request.s request.blockLength,
        framedTape
          (tripleFinalFrame (codecGammaPayload request.n)
            (codecGammaPayload request.s)
            (codecGammaPayload request.blockLength))
          (finiteSuffixTape (requestRawTail request))⟩ := by
  rw [finiteSuffixTape_encodeRequest_eq_framedTail]
  have hrun := taggedNatRun_triple
    (codecGammaPayload request.n) (codecGammaPayload request.s)
    (codecGammaPayload request.blockLength)
    (finiteSuffixTape (requestRawTail request))
  simpa only [codecGammaPayload_length,
    ← startOffset_eq_codecTripleFootprint] using hrun

/-- Direct finite-TM handoff theorem for the repository's real canonical
encoder.  This is the strongest current operational statement: the machine
has consumed exactly the tag and the three gamma fields, is positioned at the
first `start` bit, and agrees cell-for-cell with the transformed prefix plus
the untouched request tail. -/
theorem taggedExecution_runConfig_encodeRequest_handoff
    (request : RequestFields) :
    TaggedFiniteNatAgree
      (TaggedExecutionTM.runConfig
        (TaggedExecutionTM.initialConfig (encodeRequest request))
        (taggedTripleTime (codecGammaWidth request.n)
          (codecGammaWidth request.s) (codecGammaWidth request.blockLength)))
      ⟨.done, startOffset request.n request.s request.blockLength,
        framedTape
          (tripleFinalFrame (codecGammaPayload request.n)
            (codecGammaPayload request.s)
            (codecGammaPayload request.blockLength))
          (finiteSuffixTape (requestRawTail request))⟩ := by
  have hagrees := taggedFiniteNatAgree_run
    (TaggedExecutionTM.initialConfig (encodeRequest request))
    ⟨.tag0, 0, finiteSuffixTape (List.ofFn (encodeRequest request))⟩
    (taggedTripleTime (codecGammaWidth request.n)
      (codecGammaWidth request.s) (codecGammaWidth request.blockLength))
    (encodeRequest_initialConfig_finiteNatAgree request)
    (by simpa using codecTripleTime_lt_encodeRequest_tapeLength request)
  rw [taggedNatRun_encodeRequest_handoff] at hagrees
  exact hagrees

theorem taggedExecution_runConfig_encodeRequest_state_done
    (request : RequestFields) :
    (TaggedExecutionTM.runConfig
      (TaggedExecutionTM.initialConfig (encodeRequest request))
      (taggedTripleTime (codecGammaWidth request.n)
        (codecGammaWidth request.s) (codecGammaWidth request.blockLength))).state =
      .done :=
  (taggedExecution_runConfig_encodeRequest_handoff request).1

theorem taggedExecution_runConfig_encodeRequest_head_eq_startOffset
    (request : RequestFields) :
    (TaggedExecutionTM.runConfig
      (TaggedExecutionTM.initialConfig (encodeRequest request))
      (taggedTripleTime (codecGammaWidth request.n)
        (codecGammaWidth request.s)
        (codecGammaWidth request.blockLength))).head.val =
      startOffset request.n request.s request.blockLength :=
  (taggedExecution_runConfig_encodeRequest_handoff request).2.1

end OperationalTaggedGamma
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.codecGammaWord_eq_gammaBody
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.encodeRequest_list_eq_tripleInitialFrame_append_tail
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_encodeRequest_handoff
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedExecution_runConfig_encodeRequest_handoff
