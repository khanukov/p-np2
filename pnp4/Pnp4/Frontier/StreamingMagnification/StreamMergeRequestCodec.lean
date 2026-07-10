import Pnp4.Frontier.ContractExpansion.PrefixParserConvention
import Pnp4.Frontier.StreamingMagnification.StreamMergeEncodedPrenex
import Pnp4.Frontier.StreamingMagnification.StreamMergePrenexBounds
import Pnp4.Frontier.StreamingMagnification.StreamMergeCertificatePadding

/-!
# A global self-delimiting request codec for one Stream-Merge output bit

The fixed-slice EAE theorem takes `n`, `s`, the block parameters, and the
requested output position as Lean indices.  This module serializes those data
into one exact-length language input:

`tag ++ gamma(n) ++ gamma(s) ++ gamma(blockLength) ++ start ++ prior ++ block ++ position`.

The start field has width `n + 1`, so it includes the completed boundary
`start = 2 ^ n` and makes `n` bounded by the ambient request length.  The full
prior-code field similarly controls `s`.  The parser checks the exact ambient
length and therefore ignores no suffix.

This is serialization and semantic-reflection infrastructure.  The executable
Lean parser and row checker are not thereby realized by one `OperationalTM`,
and no polynomial running-time or complexity-class membership theorem is
claimed here.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeRequestCodec

open Pnp3.ComplexityInterfaces
open StreamMerge
open StreamMergePrenexWire
open Pnp4.Frontier.ContractExpansion

/-- Fresh one-byte domain tag for the Stream-Merge output-bit language. -/
def requestTag : Nat := 179

/-- The legal completed boundary `2 ^ n` requires one more bit than an input
coordinate. -/
def startWidth (n : Nat) : Nat := n + 1

/-- Fixed width of a physical result-wire position. -/
def positionWidth (n s : Nat) : Nat :=
  bitLength (StreamMergeWire.wireLength n s)

def sOffset (n : Nat) : Nat :=
  tagLen + gammaLen n

def blockLengthOffset (n s : Nat) : Nat :=
  sOffset n + gammaLen s

def startOffset (n s blockLength : Nat) : Nat :=
  blockLengthOffset n s + gammaLen blockLength

def priorOffset (n s blockLength : Nat) : Nat :=
  startOffset n s blockLength + startWidth n

def blockOffset (n s blockLength : Nat) : Nat :=
  priorOffset n s blockLength + DAGCodec.codeLength n s

def positionOffset (n s blockLength start : Nat) : Nat :=
  blockOffset n s blockLength + expectedLength n blockLength start

/-- Exact request length.  Parenthesization matches `encodeRequest` so no cast
or hidden padding is needed. -/
def requestLength (n s blockLength start : Nat) : Nat :=
  tagLen +
    (gammaLen n +
      (gammaLen s +
        (gammaLen blockLength +
          (startWidth n +
            (DAGCodec.codeLength n s +
              (expectedLength n blockLength start + positionWidth n s))))))

/-- Fully validated semantic fields carried by one canonical request. -/
structure RequestFields where
  n : Nat
  s : Nat
  blockLength : Nat
  start : Nat
  start_le : start ≤ 2 ^ n
  priorCode : DAGCodec.Code n s
  prior : DAGCodec.BoundedCircuit n s
  prior_decode : DAGCodec.decode priorCode = some prior
  blockBits : DAGCodec.BitString (expectedLength n blockLength start)
  position : Fin (StreamMergeWire.wireLength n s)

namespace RequestFields

def blockList (request : RequestFields) : List Bool :=
  List.ofFn request.blockBits

@[simp] theorem blockList_length (request : RequestFields) :
    request.blockList.length =
      expectedLength request.n request.blockLength request.start := by
  simp [blockList]

def windowWellFormed (request : RequestFields) :
    WindowWellFormed request.n request.blockLength request.start
      request.blockList :=
  ⟨request.start_le, request.blockList_length⟩

def encodedLength (request : RequestFields) : Nat :=
  requestLength request.n request.s request.blockLength request.start

end RequestFields

/-- Successful parses carry the exact ambient-length equation. -/
abbrev ParsedRequest (m : Nat) :=
  { request : RequestFields // request.encodedLength = m }

/-- Canonical tag bits. -/
def requestTagBits : DAGCodec.BitString tagLen :=
  natBEField requestTag tagLen

/-- Canonical fixed-width start field. -/
def startBits (request : RequestFields) :
    DAGCodec.BitString (startWidth request.n) :=
  natBEField request.start (startWidth request.n)

/-- Canonical fixed-width result position. -/
def positionBits (request : RequestFields) :
    DAGCodec.BitString (positionWidth request.n request.s) :=
  natBEField request.position.val
    (positionWidth request.n request.s)

/-- Fully executable canonical encoder. -/
def encodeRequest (request : RequestFields) :
    DAGCodec.BitString request.encodedLength :=
  Fin.append requestTagBits
    (Fin.append (fun index => gammaBit request.n index)
      (Fin.append (fun index => gammaBit request.s index)
        (Fin.append (fun index => gammaBit request.blockLength index)
          (Fin.append (startBits request)
            (Fin.append request.priorCode
              (Fin.append request.blockBits (positionBits request)))))))

theorem encodeRequest_tag_apply (request : RequestFields)
    (t : Nat) (ht : t < tagLen) :
    encodeRequest request ⟨t, by
      unfold RequestFields.encodedLength requestLength
      omega⟩ = requestTagBits ⟨t, ht⟩ := by
  unfold encodeRequest
  rw [show (⟨t, by
        unfold RequestFields.encodedLength requestLength
        omega⟩ : Fin request.encodedLength) =
      Fin.castAdd
        (gammaLen request.n +
          (gammaLen request.s +
            (gammaLen request.blockLength +
              (startWidth request.n +
                (DAGCodec.codeLength request.n request.s +
                  (expectedLength request.n request.blockLength request.start +
                    positionWidth request.n request.s))))))
        ⟨t, ht⟩ by
      apply Fin.ext
      rfl]
  rw [Fin.append_left]

theorem encodeRequest_n_apply (request : RequestFields)
    (t : Nat) (ht : t < gammaLen request.n) :
    encodeRequest request ⟨tagLen + t, by
      unfold RequestFields.encodedLength requestLength
      omega⟩ = gammaBit request.n ⟨t, ht⟩ := by
  unfold encodeRequest
  rw [show (⟨tagLen + t, by
        unfold RequestFields.encodedLength requestLength
        omega⟩ : Fin request.encodedLength) =
      Fin.natAdd tagLen (Fin.castAdd _ ⟨t, ht⟩) by
      apply Fin.ext
      simp]
  rw [Fin.append_right, Fin.append_left]

theorem encodeRequest_s_apply (request : RequestFields)
    (t : Nat) (ht : t < gammaLen request.s) :
    encodeRequest request ⟨sOffset request.n + t, by
      unfold RequestFields.encodedLength requestLength sOffset
      omega⟩ = gammaBit request.s ⟨t, ht⟩ := by
  unfold encodeRequest
  rw [show (⟨sOffset request.n + t, by
        unfold RequestFields.encodedLength requestLength sOffset
        omega⟩ : Fin request.encodedLength) =
      Fin.natAdd tagLen
        (Fin.natAdd (gammaLen request.n) (Fin.castAdd _ ⟨t, ht⟩)) by
      apply Fin.ext
      simp [sOffset]
      omega]
  rw [Fin.append_right, Fin.append_right, Fin.append_left]

theorem encodeRequest_blockLength_apply (request : RequestFields)
    (t : Nat) (ht : t < gammaLen request.blockLength) :
    encodeRequest request ⟨blockLengthOffset request.n request.s + t, by
      unfold RequestFields.encodedLength requestLength blockLengthOffset sOffset
      omega⟩ = gammaBit request.blockLength ⟨t, ht⟩ := by
  unfold encodeRequest
  rw [show (⟨blockLengthOffset request.n request.s + t, by
        unfold RequestFields.encodedLength requestLength blockLengthOffset sOffset
        omega⟩ : Fin request.encodedLength) =
      Fin.natAdd tagLen
        (Fin.natAdd (gammaLen request.n)
          (Fin.natAdd (gammaLen request.s) (Fin.castAdd _ ⟨t, ht⟩))) by
      apply Fin.ext
      simp [blockLengthOffset, sOffset]
      omega]
  rw [Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_left]

theorem encodeRequest_start_apply (request : RequestFields)
    (index : Fin (startWidth request.n)) :
    encodeRequest request
      ⟨startOffset request.n request.s request.blockLength + index.val, by
        unfold RequestFields.encodedLength requestLength startOffset
          blockLengthOffset sOffset
        omega⟩ = startBits request index := by
  unfold encodeRequest
  rw [show (⟨startOffset request.n request.s request.blockLength + index.val, by
        unfold RequestFields.encodedLength requestLength startOffset
          blockLengthOffset sOffset
        omega⟩ : Fin request.encodedLength) =
      Fin.natAdd tagLen
        (Fin.natAdd (gammaLen request.n)
          (Fin.natAdd (gammaLen request.s)
            (Fin.natAdd (gammaLen request.blockLength)
              (Fin.castAdd _ index)))) by
      apply Fin.ext
      simp [startOffset, blockLengthOffset, sOffset]
      omega]
  rw [Fin.append_right, Fin.append_right, Fin.append_right,
    Fin.append_right, Fin.append_left]

theorem encodeRequest_prior_apply (request : RequestFields)
    (index : Fin (DAGCodec.codeLength request.n request.s)) :
    encodeRequest request
      ⟨priorOffset request.n request.s request.blockLength + index.val, by
        unfold RequestFields.encodedLength requestLength priorOffset startOffset
          blockLengthOffset sOffset startWidth
        omega⟩ = request.priorCode index := by
  unfold encodeRequest
  rw [show (⟨priorOffset request.n request.s request.blockLength + index.val, by
        unfold RequestFields.encodedLength requestLength priorOffset startOffset
          blockLengthOffset sOffset startWidth
        omega⟩ : Fin request.encodedLength) =
      Fin.natAdd tagLen
        (Fin.natAdd (gammaLen request.n)
          (Fin.natAdd (gammaLen request.s)
            (Fin.natAdd (gammaLen request.blockLength)
              (Fin.natAdd (startWidth request.n) (Fin.castAdd _ index))))) by
      apply Fin.ext
      simp [priorOffset, startOffset, blockLengthOffset, sOffset]
      omega]
  rw [Fin.append_right, Fin.append_right, Fin.append_right,
    Fin.append_right, Fin.append_right, Fin.append_left]

theorem encodeRequest_block_apply (request : RequestFields)
    (index : Fin (expectedLength request.n request.blockLength request.start)) :
    encodeRequest request
      ⟨blockOffset request.n request.s request.blockLength + index.val, by
        unfold RequestFields.encodedLength requestLength blockOffset priorOffset
          startOffset blockLengthOffset sOffset startWidth
        omega⟩ = request.blockBits index := by
  unfold encodeRequest
  rw [show (⟨blockOffset request.n request.s request.blockLength + index.val, by
        unfold RequestFields.encodedLength requestLength blockOffset priorOffset
          startOffset blockLengthOffset sOffset startWidth
        omega⟩ : Fin request.encodedLength) =
      Fin.natAdd tagLen
        (Fin.natAdd (gammaLen request.n)
          (Fin.natAdd (gammaLen request.s)
            (Fin.natAdd (gammaLen request.blockLength)
              (Fin.natAdd (startWidth request.n)
                (Fin.natAdd (DAGCodec.codeLength request.n request.s)
                  (Fin.castAdd _ index)))))) by
      apply Fin.ext
      simp [blockOffset, priorOffset, startOffset, blockLengthOffset, sOffset]
      omega]
  rw [Fin.append_right, Fin.append_right, Fin.append_right,
    Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_left]

theorem encodeRequest_position_apply (request : RequestFields)
    (index : Fin (positionWidth request.n request.s)) :
    encodeRequest request
      ⟨positionOffset request.n request.s request.blockLength request.start +
          index.val, by
        unfold RequestFields.encodedLength requestLength positionOffset blockOffset
          priorOffset startOffset blockLengthOffset sOffset startWidth
        omega⟩ = positionBits request index := by
  unfold encodeRequest
  rw [show (⟨positionOffset request.n request.s request.blockLength request.start +
          index.val, by
        unfold RequestFields.encodedLength requestLength positionOffset blockOffset
          priorOffset startOffset blockLengthOffset sOffset startWidth
        omega⟩ : Fin request.encodedLength) =
      Fin.natAdd tagLen
        (Fin.natAdd (gammaLen request.n)
          (Fin.natAdd (gammaLen request.s)
            (Fin.natAdd (gammaLen request.blockLength)
              (Fin.natAdd (startWidth request.n)
                (Fin.natAdd (DAGCodec.codeLength request.n request.s)
                  (Fin.natAdd
                    (expectedLength request.n request.blockLength request.start)
                    index)))))) by
      apply Fin.ext
      simp [positionOffset, blockOffset, priorOffset, startOffset,
        blockLengthOffset, sOffset]
      omega]
  rw [Fin.append_right, Fin.append_right, Fin.append_right,
    Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_right]

/-! ## Length and local reader facts -/

theorem n_le_requestLength (n s blockLength start : Nat) :
    n ≤ requestLength n s blockLength start := by
  unfold requestLength startWidth
  omega

theorem s_le_requestLength (n s blockLength start : Nat) :
    s ≤ requestLength n s blockLength start := by
  have hcode := StreamMergePrenexBounds.three_mul_le_codeLength n s
  unfold requestLength
  omega

theorem RequestFields.n_le_encodedLength (request : RequestFields) :
    request.n ≤ request.encodedLength := by
  exact n_le_requestLength request.n request.s request.blockLength request.start

theorem RequestFields.s_le_encodedLength (request : RequestFields) :
    request.s ≤ request.encodedLength := by
  exact s_le_requestLength request.n request.s request.blockLength request.start

theorem start_lt_two_pow_startWidth (request : RequestFields) :
    request.start < 2 ^ startWidth request.n := by
  have hpos : 0 < 2 ^ request.n := Nat.two_pow_pos request.n
  have hle := request.start_le
  rw [show startWidth request.n = request.n + 1 by rfl, pow_succ]
  omega

theorem position_lt_two_pow_positionWidth (request : RequestFields) :
    request.position.val < 2 ^ positionWidth request.n request.s := by
  exact request.position.isLt.trans
    (nat_lt_two_pow_bitLength (StreamMergeWire.wireLength request.n request.s))

theorem readBit_encodeRequest_tag (request : RequestFields)
    (t : Nat) (ht : t < tagLen) :
    readBit? (encodeRequest request) t =
      some (requestTagBits ⟨t, ht⟩) := by
  unfold readBit?
  have hm : t < request.encodedLength :=
    Nat.lt_of_lt_of_le ht (by
      unfold RequestFields.encodedLength requestLength
      omega)
  simp [hm, encodeRequest_tag_apply request t ht]

theorem readBit_encodeRequest_n (request : RequestFields)
    (t : Nat) (ht : t < gammaLen request.n) :
    readBit? (encodeRequest request) (tagLen + t) =
      some (gammaBit request.n ⟨t, ht⟩) := by
  unfold readBit?
  have hm : tagLen + t < request.encodedLength := by
    unfold RequestFields.encodedLength requestLength
    omega
  simp [hm, encodeRequest_n_apply request t ht]

theorem readBit_encodeRequest_s (request : RequestFields)
    (t : Nat) (ht : t < gammaLen request.s) :
    readBit? (encodeRequest request) (sOffset request.n + t) =
      some (gammaBit request.s ⟨t, ht⟩) := by
  unfold readBit?
  have hm : sOffset request.n + t < request.encodedLength := by
    unfold RequestFields.encodedLength requestLength sOffset
    omega
  simp [hm, encodeRequest_s_apply request t ht]

theorem readBit_encodeRequest_blockLength (request : RequestFields)
    (t : Nat) (ht : t < gammaLen request.blockLength) :
    readBit? (encodeRequest request)
        (blockLengthOffset request.n request.s + t) =
      some (gammaBit request.blockLength ⟨t, ht⟩) := by
  unfold readBit?
  have hm : blockLengthOffset request.n request.s + t <
      request.encodedLength := by
    unfold RequestFields.encodedLength requestLength blockLengthOffset sOffset
    omega
  simp [hm, encodeRequest_blockLength_apply request t ht]

theorem readBit_encodeRequest_start (request : RequestFields)
    (t : Nat) (ht : t < startWidth request.n) :
    readBit? (encodeRequest request)
        (startOffset request.n request.s request.blockLength + t) =
      some (startBits request ⟨t, ht⟩) := by
  unfold readBit?
  have hm : startOffset request.n request.s request.blockLength + t <
      request.encodedLength := by
    unfold RequestFields.encodedLength requestLength startOffset
      blockLengthOffset sOffset
    omega
  simp [hm, encodeRequest_start_apply request ⟨t, ht⟩]

theorem readBit_encodeRequest_position (request : RequestFields)
    (t : Nat) (ht : t < positionWidth request.n request.s) :
    readBit? (encodeRequest request)
        (positionOffset request.n request.s request.blockLength request.start + t) =
      some (positionBits request ⟨t, ht⟩) := by
  unfold readBit?
  have hm :
      positionOffset request.n request.s request.blockLength request.start + t <
        request.encodedLength := by
    unfold RequestFields.encodedLength requestLength positionOffset blockOffset
      priorOffset startOffset blockLengthOffset sOffset startWidth
    omega
  simp [hm, encodeRequest_position_apply request ⟨t, ht⟩]

theorem readNatBE_encodeRequest_tag (request : RequestFields) :
    readNatBE (encodeRequest request) 0 tagLen = some requestTag := by
  calc
    readNatBE (encodeRequest request) 0 tagLen =
        readNatBE requestTagBits 0 tagLen := by
      apply readNatBE_eq_of_readBit_eq
      intro t ht
      simpa [Nat.zero_add, readBit?, ht] using
        readBit_encodeRequest_tag request t ht
    _ = some requestTag := by
      exact readNatBE_natBEField_zero requestTag tagLen
        (by norm_num [requestTag, tagLen])

theorem decodeGamma_encodeRequest_n (request : RequestFields) :
    decodeGamma? (encodeRequest request) tagLen =
      some (request.n, gammaLen request.n) := by
  unfold decodeGamma?
  apply decodeGammaAux_gammaBit_from_at
  · intro t ht
    exact readBit_encodeRequest_n request t ht
  · omega
  · have hlen := gammaLen_eq_zeros_add_bitLength request.n
    unfold RequestFields.encodedLength requestLength
    omega

theorem decodeGamma_encodeRequest_s (request : RequestFields) :
    decodeGamma? (encodeRequest request) (sOffset request.n) =
      some (request.s, gammaLen request.s) := by
  unfold decodeGamma?
  apply decodeGammaAux_gammaBit_from_at
  · intro t ht
    exact readBit_encodeRequest_s request t ht
  · omega
  · have hlen := gammaLen_eq_zeros_add_bitLength request.s
    unfold RequestFields.encodedLength requestLength
    omega

theorem decodeGamma_encodeRequest_blockLength (request : RequestFields) :
    decodeGamma? (encodeRequest request)
        (blockLengthOffset request.n request.s) =
      some (request.blockLength, gammaLen request.blockLength) := by
  unfold decodeGamma?
  apply decodeGammaAux_gammaBit_from_at
  · intro t ht
    exact readBit_encodeRequest_blockLength request t ht
  · omega
  · have hlen := gammaLen_eq_zeros_add_bitLength request.blockLength
    unfold RequestFields.encodedLength requestLength
    omega

theorem readNatBE_encodeRequest_start (request : RequestFields) :
    readNatBE (encodeRequest request)
        (startOffset request.n request.s request.blockLength)
        (startWidth request.n) = some request.start := by
  calc
    readNatBE (encodeRequest request)
        (startOffset request.n request.s request.blockLength)
        (startWidth request.n) =
      readNatBE (startBits request) 0 (startWidth request.n) := by
        apply readNatBE_eq_of_readBit_eq
        intro t ht
        rw [readBit_encodeRequest_start request t ht]
        simp [readBit?, ht]
    _ = some request.start := by
      exact readNatBE_natBEField_zero request.start (startWidth request.n)
        (start_lt_two_pow_startWidth request)

theorem sliceBits_encodeRequest_prior (request : RequestFields) :
    sliceBits? (encodeRequest request)
        (priorOffset request.n request.s request.blockLength)
        (DAGCodec.codeLength request.n request.s) =
      some request.priorCode := by
  unfold sliceBits?
  have hWithin :
      priorOffset request.n request.s request.blockLength +
          DAGCodec.codeLength request.n request.s ≤
        request.encodedLength := by
    unfold RequestFields.encodedLength requestLength priorOffset startOffset
      blockLengthOffset sOffset startWidth
    omega
  simp only [hWithin, dite_true]
  congr 1
  funext index
  exact encodeRequest_prior_apply request index

theorem sliceBits_encodeRequest_block (request : RequestFields) :
    sliceBits? (encodeRequest request)
        (blockOffset request.n request.s request.blockLength)
        (expectedLength request.n request.blockLength request.start) =
      some request.blockBits := by
  unfold sliceBits?
  have hWithin :
      blockOffset request.n request.s request.blockLength +
          expectedLength request.n request.blockLength request.start ≤
        request.encodedLength := by
    unfold RequestFields.encodedLength requestLength blockOffset priorOffset
      startOffset blockLengthOffset sOffset startWidth
    omega
  simp only [hWithin, dite_true]
  congr 1
  funext index
  exact encodeRequest_block_apply request index

theorem readNatBE_encodeRequest_position (request : RequestFields) :
    readNatBE (encodeRequest request)
        (positionOffset request.n request.s request.blockLength request.start)
        (positionWidth request.n request.s) = some request.position.val := by
  calc
    readNatBE (encodeRequest request)
        (positionOffset request.n request.s request.blockLength request.start)
        (positionWidth request.n request.s) =
      readNatBE (positionBits request) 0
        (positionWidth request.n request.s) := by
        apply readNatBE_eq_of_readBit_eq
        intro t ht
        rw [readBit_encodeRequest_position request t ht]
        simp [readBit?, ht]
    _ = some request.position.val := by
      exact readNatBE_natBEField_zero request.position.val
        (positionWidth request.n request.s)
        (position_lt_two_pow_positionWidth request)

/-! ## Executable canonical parser -/

/-- Decode one gamma field and explicitly enforce its canonical consumed
length before using the value to determine any later field width. -/
def decodeCanonicalGamma? {m : Nat} (input : PrefixBitVec m)
    (offset : Nat) : Option Nat := do
  let decoded ← decodeGamma? input offset
  if decoded.2 = gammaLen decoded.1 then
    some decoded.1
  else
    none

@[simp] theorem decodeCanonicalGamma_encodeRequest_n
    (request : RequestFields) :
    decodeCanonicalGamma? (encodeRequest request) tagLen = some request.n := by
  simp [decodeCanonicalGamma?, decodeGamma_encodeRequest_n]

@[simp] theorem decodeCanonicalGamma_encodeRequest_s
    (request : RequestFields) :
    decodeCanonicalGamma? (encodeRequest request) (sOffset request.n) =
      some request.s := by
  simp [decodeCanonicalGamma?, decodeGamma_encodeRequest_s]

@[simp] theorem decodeCanonicalGamma_encodeRequest_blockLength
    (request : RequestFields) :
    decodeCanonicalGamma? (encodeRequest request)
        (blockLengthOffset request.n request.s) =
      some request.blockLength := by
  simp [decodeCanonicalGamma?, decodeGamma_encodeRequest_blockLength]

/--
Parse one exact request.  The `n ≤ m` and `s ≤ m` guards occur immediately
after the respective gamma fields, before either value is used to drive a
dependent-width scan.  Invalid prior codes, out-of-range starts and positions,
wrong ambient lengths, and every extra suffix are rejected.
-/
def parseRequest {m : Nat} (input : PrefixBitVec m) :
    Option (ParsedRequest m) := do
  let tag ← readNatBE input 0 tagLen
  if _htag : tag = requestTag then
    let n ← decodeCanonicalGamma? input tagLen
    if _hn : n ≤ m then
      let s ← decodeCanonicalGamma? input (sOffset n)
      if _hs : s ≤ m then
        let blockLength ←
          decodeCanonicalGamma? input (blockLengthOffset n s)
        let start ← readNatBE input (startOffset n s blockLength)
          (startWidth n)
        if hstart : start ≤ 2 ^ n then
          if hlength : requestLength n s blockLength start = m then
            let priorCode ← sliceBits? input
              (priorOffset n s blockLength) (DAGCodec.codeLength n s)
            match hprior : DAGCodec.decode priorCode with
            | none => none
            | some prior => do
                let blockBits ← sliceBits? input
                  (blockOffset n s blockLength)
                  (expectedLength n blockLength start)
                let positionValue ← readNatBE input
                  (positionOffset n s blockLength start)
                  (positionWidth n s)
                if hposition :
                    positionValue < StreamMergeWire.wireLength n s then
                  let request : RequestFields := {
                    n := n
                    s := s
                    blockLength := blockLength
                    start := start
                    start_le := hstart
                    priorCode := priorCode
                    prior := prior
                    prior_decode := hprior
                    blockBits := blockBits
                    position := ⟨positionValue, hposition⟩
                  }
                  some ⟨request, by
                    simpa [RequestFields.encodedLength] using hlength⟩
                else
                  none
          else
            none
        else
          none
      else
        none
    else
      none
  else
    none

/-- The encoder is a right inverse of the exact parser. -/
@[simp] theorem parse_encodeRequest (request : RequestFields) :
    parseRequest (encodeRequest request) = some ⟨request, rfl⟩ := by
  cases hdecode : DAGCodec.decode request.priorCode with
  | none =>
      have himpossible := request.prior_decode
      rw [hdecode] at himpossible
      contradiction
  | some decodedPrior =>
      have hpriorEq : decodedPrior = request.prior := by
        have h := request.prior_decode
        rw [hdecode] at h
        exact Option.some.inj h
      subst decodedPrior
      unfold parseRequest
      rw [readNatBE_encodeRequest_tag]
      simp
      refine ⟨request.n_le_encodedLength, request.s_le_encodedLength, ?_⟩
      simp [readNatBE_encodeRequest_start,
        request.start_le,
        RequestFields.encodedLength,
        sliceBits_encodeRequest_prior,
        sliceBits_encodeRequest_block,
        readNatBE_encodeRequest_position,
        request.position.isLt]
      split
      · rename_i hnone
        rw [hdecode] at hnone
        contradiction
      · rename_i decoded hsome
        have hdecoded : decoded = request.prior := by
          rw [hdecode] at hsome
          exact Option.some.inj hsome.symm
        subst decoded
        congr 1

/-- Successful parsing exposes the exact ambient-length convention. -/
theorem parseRequest_length_exact {m : Nat} {input : PrefixBitVec m}
    {request : ParsedRequest m}
    (_hparse : parseRequest input = some request) :
    request.1.encodedLength = m :=
  request.2

theorem ParsedRequest.n_le_ambient {m : Nat}
    (request : ParsedRequest m) : request.1.n ≤ m := by
  calc
    request.1.n ≤ request.1.encodedLength := request.1.n_le_encodedLength
    _ = m := request.2

theorem ParsedRequest.s_le_ambient {m : Nat}
    (request : ParsedRequest m) : request.1.s ≤ m := by
  calc
    request.1.s ≤ request.1.encodedLength := request.1.s_le_encodedLength
    _ = m := request.2

/-! ## One global language and semantic EAE reflection -/

/-- Reference bit selected by the fully parsed request.  This is semantic
specification code and retains the exhaustive reference search. -/
def RequestFields.referenceBit (request : RequestFields) : Bool :=
  StreamMergeWire.referenceOutputBit request.priorCode request.blockLength
    request.start request.blockList request.position

/-- The existing fixed-wire EAE shell instantiated by parsed fields. -/
def RequestFields.encodedEAEShell (request : RequestFields) : Prop :=
  StreamMergeEncodedPrenex.EncodedEAEShell request.prior request.blockList
    request.windowWellFormed request.position

/-- The same shell stated directly with the reflected Boolean row checker. -/
def RequestFields.encodedEAECheck (request : RequestFields) : Prop :=
  Exists fun choice : ChoiceWire request.n request.s =>
    forall query : QueryWire request.n request.s,
      Exists fun inner : InnerWire request.n request.s =>
        StreamMergeEncodedPrenex.check request.prior request.blockList
          request.windowWellFormed request.position choice query inner = true

/-- Parameter-free output-bit language.  Parse failures, including every wrong
ambient length or appended suffix, are ordinary false instances. -/
def OutputBitLanguage : Language :=
  fun _m input =>
    match parseRequest input with
    | none => false
    | some request => request.1.referenceBit

theorem outputBitLanguage_rejects_parse_failure
    {m : Nat} {input : Bitstring m}
    (hparse : parseRequest input = none) :
    OutputBitLanguage m input = false := by
  simp [OutputBitLanguage, hparse]

theorem outputBitLanguage_eq_referenceBit_of_parse
    {m : Nat} {input : Bitstring m} {request : ParsedRequest m}
    (hparse : parseRequest input = some request) :
    OutputBitLanguage m input = request.1.referenceBit := by
  simp [OutputBitLanguage, hparse]

@[simp] theorem outputBitLanguage_encode (request : RequestFields) :
    OutputBitLanguage request.encodedLength (encodeRequest request) =
      request.referenceBit := by
  simp [OutputBitLanguage]

/-- A successful global parse removes all request hardwiring from the existing
fixed-slice semantic EAE theorem. -/
theorem outputBitLanguage_eq_true_iff_encodedEAEShell_of_parse
    {m : Nat} {input : Bitstring m} {request : ParsedRequest m}
    (hparse : parseRequest input = some request) :
    OutputBitLanguage m input = true ↔ request.1.encodedEAEShell := by
  rw [outputBitLanguage_eq_referenceBit_of_parse hparse]
  exact
    StreamMergeEncodedPrenex.referenceOutputBit_eq_true_iff_encodedEAEShell
      request.1.blockList request.1.priorCode request.1.prior
      request.1.prior_decode request.1.windowWellFormed request.1.position

/-- Canonical encodings satisfy the same EAE reflection directly. -/
theorem outputBitLanguage_encode_eq_true_iff_encodedEAEShell
    (request : RequestFields) :
    OutputBitLanguage request.encodedLength (encodeRequest request) = true ↔
      request.encodedEAEShell := by
  rw [outputBitLanguage_encode]
  exact
    StreamMergeEncodedPrenex.referenceOutputBit_eq_true_iff_encodedEAEShell
      request.blockList request.priorCode request.prior request.prior_decode
      request.windowWellFormed request.position

/-- Global successful parses also expose the reflected Boolean checker at each
innermost row. -/
theorem outputBitLanguage_eq_true_iff_encodedEAECheck_of_parse
    {m : Nat} {input : Bitstring m} {request : ParsedRequest m}
    (hparse : parseRequest input = some request) :
    OutputBitLanguage m input = true ↔ request.1.encodedEAECheck := by
  rw [outputBitLanguage_eq_referenceBit_of_parse hparse]
  exact
    StreamMergeEncodedPrenex.referenceOutputBit_eq_true_iff_encodedEAECheck
      request.1.blockList request.1.priorCode request.1.prior
      request.1.prior_decode request.1.windowWellFormed request.1.position

/-- Canonical encodings satisfy the Boolean-check EAE reflection directly. -/
theorem outputBitLanguage_encode_eq_true_iff_encodedEAECheck
    (request : RequestFields) :
    OutputBitLanguage request.encodedLength (encodeRequest request) = true ↔
      request.encodedEAECheck := by
  rw [outputBitLanguage_encode]
  exact
    StreamMergeEncodedPrenex.referenceOutputBit_eq_true_iff_encodedEAECheck
      request.blockList request.priorCode request.prior request.prior_decode
      request.windowWellFormed request.position

/-! ## Global certificate-length EAE shell -/

/-- The successful-parse reflection with all three quantifier carriers padded
to the successive ambient certificate lengths. -/
theorem outputBitLanguage_eq_true_iff_paddedCertificateEAEShell_of_parse
    {m : Nat} {input : Bitstring m} {request : ParsedRequest m}
    (hparse : parseRequest input = some request) :
    OutputBitLanguage m input = true ↔
      StreamMergeCertificatePadding.PaddedCertificateEAEShell
        request.n_le_ambient request.s_le_ambient request.1.prior
        request.1.blockList request.1.windowWellFormed request.1.position := by
  rw [outputBitLanguage_eq_referenceBit_of_parse hparse]
  exact
    StreamMergeCertificatePadding.referenceOutputBit_eq_true_iff_paddedCertificateEAEShell
      request.n_le_ambient request.s_le_ambient request.1.blockList
      request.1.priorCode request.1.prior request.1.prior_decode
      request.1.windowWellFormed request.1.position

/-- Canonical request encoding followed by the padded certificate EAE shell. -/
theorem outputBitLanguage_encode_eq_true_iff_paddedCertificateEAEShell
    (request : RequestFields) :
    OutputBitLanguage request.encodedLength (encodeRequest request) = true ↔
      StreamMergeCertificatePadding.PaddedCertificateEAEShell
        request.n_le_encodedLength request.s_le_encodedLength request.prior
        request.blockList request.windowWellFormed request.position := by
  rw [outputBitLanguage_encode]
  exact
    StreamMergeCertificatePadding.referenceOutputBit_eq_true_iff_paddedCertificateEAEShell
      request.n_le_encodedLength request.s_le_encodedLength request.blockList
      request.priorCode request.prior request.prior_decode
      request.windowWellFormed request.position

/--
One parameter-free padded EAE predicate.  The deterministic parser match adds
no logical quantifier: malformed strings map to `False`, while successful
strings use certificate carriers determined solely by the ambient length `m`.
-/
def GlobalPaddedEAEShell (m : Nat) (input : Bitstring m) : Prop :=
  match parseRequest input with
  | none => False
  | some request =>
      StreamMergeCertificatePadding.PaddedCertificateEAEShell
        request.n_le_ambient request.s_le_ambient request.1.prior
        request.1.blockList request.1.windowWellFormed request.1.position

/-- Exact global semantic capstone: one self-delimiting request language is
equivalent to the successive-certificate EAE shell on every ambient string,
with malformed inputs rejected on both sides. -/
theorem outputBitLanguage_eq_true_iff_globalPaddedEAEShell
    (m : Nat) (input : Bitstring m) :
    OutputBitLanguage m input = true ↔ GlobalPaddedEAEShell m input := by
  cases hparse : parseRequest input with
  | none =>
      simp [OutputBitLanguage, GlobalPaddedEAEShell, hparse]
  | some request =>
      simpa [GlobalPaddedEAEShell, hparse] using
        outputBitLanguage_eq_true_iff_paddedCertificateEAEShell_of_parse hparse

end StreamMergeRequestCodec
end StreamingMagnification
end Frontier
end Pnp4
