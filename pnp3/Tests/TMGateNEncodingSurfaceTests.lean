import Complexity.TMVerifier.TuringToolkit.GateNEncodingExamples

/-!
# GN-1 pure ABI surface

Definitions receive direct `#check` pins.  Every public source theorem receives
an exact named theorem wrapper below.  This surface introduces no new claim.
-/

namespace Pnp3.Tests.TMGateNEncodingSurface

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

-- Definitions only.
#check @GNField
#check @GNProgram
#check @gnGateFields
#check @GNField.CanonicalFor
#check @gnFieldRequest
#check @gnFieldEval
#check @g1RecordFrames
#check @gnRecordFrames
#check @encodeGNRecord
#check @gnRecordSize
#check @parseGNRecordBody
#check @parseGNRecord
#check @decodeGNRecordFrames?
#check @decodeGNRecord?
#check @gnAssignFrames
#check @gnSlotFrames
#check @gnFieldRecordsFrames
#check @gnRecordsFrames
#check @encodeGNFrames
#check @encodeGN
#check @parseGNAssign
#check @parseGNSlots
#check @parseGNRecords
#check @gnGateOfFields?
#check @gnGatesOfFields?
#check @gnProgramOf?
#check @gnCanonicalTail
#check @decodeGNTail?
#check @decodeGNFrameList?
#check @decodeGN?
#check @evalGNFields
#check @evalGNProgramAll
#check @evalGNProgram
#check @GNEncodingExamples.capProgram
#check @GNEncodingExamples.capFrames
#check @GNEncodingExamples.capBits
#check @GNEncodingExamples.badMarkerFrames
#check @GNEncodingExamples.badSlotCountFrames
#check @GNEncodingExamples.badTagFrames
#check @GNEncodingExamples.invalidInputIndexFrames
#check @GNEncodingExamples.priorIndexBelowWidthFrames

-- Exact theorem-contract wrappers.
theorem check_gnGateFields_input {n : Nat} (i : Fin n) :
    gnGateFields (SLGate.input i) = (G1Tag.input, i.val, 0) :=
  gnGateFields_input i

theorem check_gnGateFields_const {n : Nat} (b : Bool) :
    gnGateFields (SLGate.const b : SLGate n) =
      (G1Tag.const, if b then 1 else 0, 0) :=
  gnGateFields_const b

theorem check_gnGateFields_not {n : Nat} (k : Nat) :
    gnGateFields (SLGate.notGate k : SLGate n) = (.not, n + k, 0) :=
  gnGateFields_not k

theorem check_gnGateFields_and {n : Nat} (k l : Nat) :
    gnGateFields (SLGate.andGate k l : SLGate n) = (.and, n + k, n + l) :=
  gnGateFields_and k l

theorem check_gnGateFields_or {n : Nat} (k l : Nat) :
    gnGateFields (SLGate.orGate k l : SLGate n) = (.or, n + k, n + l) :=
  gnGateFields_or k l

theorem check_gnFieldEval_input {n : Nat} (i : Fin n) (vals : List Bool) :
    gnFieldEval (gnGateFields (SLGate.input i)) vals = vals[i.val]? :=
  gnFieldEval_input i vals

theorem check_gnFieldEval_const {n : Nat} (b : Bool) (vals : List Bool) :
    gnFieldEval (gnGateFields (SLGate.const b : SLGate n)) vals = some b :=
  gnFieldEval_const b vals

theorem check_gnFieldEval_not {n : Nat} (k : Nat) (vals : List Bool) :
    gnFieldEval (gnGateFields (SLGate.notGate k : SLGate n)) vals =
      vals[n + k]?.map (!·) :=
  gnFieldEval_not k vals

theorem check_gnFieldEval_and {n : Nat} (k l : Nat) (vals : List Bool)
    (a b : Bool) (h1 : vals[n + k]? = some a) (h2 : vals[n + l]? = some b) :
    gnFieldEval (gnGateFields (SLGate.andGate k l : SLGate n)) vals =
      some (a && b) :=
  gnFieldEval_and k l vals a b h1 h2

theorem check_gnFieldEval_or {n : Nat} (k l : Nat) (vals : List Bool)
    (a b : Bool) (h1 : vals[n + k]? = some a) (h2 : vals[n + l]? = some b) :
    gnFieldEval (gnGateFields (SLGate.orGate k l : SLGate n)) vals =
      some (a || b) :=
  gnFieldEval_or k l vals a b h1 h2

theorem check_gnFieldEval_isSome_iff (f : GNField) (vals : List Bool) :
    (gnFieldEval f vals).isSome = true ↔ (gnFieldRequest f vals).WellFormed :=
  gnFieldEval_isSome_iff f vals

theorem check_g1RecordFrames_length (marker : G1Frame) (f : GNField) :
    (g1RecordFrames marker f).length = gnRecordSize f :=
  g1RecordFrames_length marker f

theorem check_encodeGNRecord_length (marker : G1Frame) (f : GNField) :
    (encodeGNRecord marker f).length = 4 * gnRecordSize f :=
  encodeGNRecord_length marker f

theorem check_decodeGNRecordFrames?_encoded (marker : G1Frame) (f : GNField) :
    decodeGNRecordFrames? marker (g1RecordFrames marker f) = some f :=
  decodeGNRecordFrames?_encoded marker f

theorem check_decodeGNRecord?_encoded (marker : G1Frame) (f : GNField) :
    decodeGNRecord? marker (encodeGNRecord marker f) = some f :=
  decodeGNRecord?_encoded marker f

theorem check_encodeGNRecord_injective (marker : G1Frame) :
    Function.Injective (encodeGNRecord marker) :=
  encodeGNRecord_injective marker

theorem check_gnAssignFrames_length (inputs : List Bool) :
    (gnAssignFrames inputs).length = inputs.length :=
  gnAssignFrames_length inputs

theorem check_gnSlotFrames_length (m : Nat) :
    (gnSlotFrames m).length = m :=
  gnSlotFrames_length m

theorem check_gnRecordsFrames_length {n : Nat} (marker : G1Frame)
    (gates : List (SLGate n)) :
    (gnRecordsFrames marker gates).length =
      (gates.map (gnRecordSize ∘ gnGateFields)).sum :=
  gnRecordsFrames_length marker gates

theorem check_encodeGNFrames_length (r : GNProgram) :
    (encodeGNFrames r).length = r.inputs.length + r.program.gates.length +
      (r.program.gates.map (gnRecordSize ∘ gnGateFields)).sum + 5 :=
  encodeGNFrames_length r

theorem check_encodeGN_length (r : GNProgram) :
    (encodeGN r).length = 4 * (encodeGNFrames r).length :=
  encodeGN_length r

theorem check_gnGateOfFields?_gnGateFields {n : Nat} (g : SLGate n) :
    gnGateOfFields? n (gnGateFields g) = some g :=
  gnGateOfFields?_gnGateFields g

theorem check_gnGateFields_canonical {n : Nat} (g : SLGate n) :
    (gnGateFields g).CanonicalFor n :=
  gnGateFields_canonical g

theorem check_gnGateOfFields?_eq_some {n : Nat} {f : GNField} {g : SLGate n}
    (h : gnGateOfFields? n f = some g) : f = gnGateFields g :=
  gnGateOfFields?_eq_some h

theorem check_gnGateOfFields?_isSome_iff (n : Nat) (f : GNField) :
    (gnGateOfFields? n f).isSome = true ↔ f.CanonicalFor n :=
  gnGateOfFields?_isSome_iff n f

theorem check_decodeGNFrameList?_encodeGNFrames (r : GNProgram) :
    decodeGNFrameList? (encodeGNFrames r) = some r :=
  decodeGNFrameList?_encodeGNFrames r

theorem check_decodeGN?_encodeGN (r : GNProgram) :
    decodeGN? (encodeGN r) = some r :=
  decodeGN?_encodeGN r

theorem check_encodeGN_injective : Function.Injective encodeGN :=
  encodeGN_injective

theorem check_decodeGN?_reserved_aligned (pre : List G1Frame)
    {b0 b1 b2 b3 : Bool}
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) (rest : List Bool) :
    decodeGN?
        (pre.flatMap G1Frame.bits ++ b0 :: b1 :: b2 :: b3 :: rest) = none :=
  decodeGN?_reserved_aligned pre hbad rest

theorem check_evalGNFields_length {fields : List GNField} {vals out : List Bool}
    (h : evalGNFields fields vals = some out) :
    out.length = vals.length + fields.length :=
  evalGNFields_length h

theorem check_capstone_frames_literal :
    GNEncodingExamples.capFrames =
      [.bof, .data true, .output false, .output false, .separator,
        .cursor, .tag, .argSep, .argSep, .finish,
        .bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
        .separator, .output false, .finish] :=
  GNEncodingExamples.capstone_frames_literal

theorem check_capstone_counts :
    GNEncodingExamples.capFrames.length = 21 ∧
      GNEncodingExamples.capBits.length = 84 :=
  GNEncodingExamples.capstone_counts

theorem check_capstone_records_decode :
    decodeGNRecordFrames? .cursor
        [.cursor, .tag, .argSep, .argSep, .finish] =
          some (G1Tag.input, 0, 0) ∧
      decodeGNRecordFrames? .bof
        [.bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish] =
          some (G1Tag.not, 1, 0) :=
  GNEncodingExamples.capstone_records_decode

theorem check_capstone_decode_and_eval :
    decodeGN? GNEncodingExamples.capBits = some GNEncodingExamples.capProgram ∧
      evalGNProgram GNEncodingExamples.capProgram = some false :=
  GNEncodingExamples.capstone_decode_and_eval

theorem check_capstone_eval_all :
    evalGNProgramAll GNEncodingExamples.capProgram = some [true, true, false] :=
  GNEncodingExamples.capstone_eval_all

theorem check_reject_wrong_marker :
    decodeGN? (GNEncodingExamples.badMarkerFrames.flatMap G1Frame.bits) = none :=
  GNEncodingExamples.reject_wrong_marker

theorem check_reject_slot_record_mismatch :
    decodeGN? (GNEncodingExamples.badSlotCountFrames.flatMap G1Frame.bits) = none :=
  GNEncodingExamples.reject_slot_record_mismatch

theorem check_reject_bad_tag_run :
    decodeGN? (GNEncodingExamples.badTagFrames.flatMap G1Frame.bits) = none :=
  GNEncodingExamples.reject_bad_tag_run

theorem check_reject_invalid_input_index :
    decodeGN? (GNEncodingExamples.invalidInputIndexFrames.flatMap G1Frame.bits) = none :=
  GNEncodingExamples.reject_invalid_input_index

theorem check_reject_prior_index_below_width :
    decodeGN?
        (GNEncodingExamples.priorIndexBelowWidthFrames.flatMap G1Frame.bits) = none :=
  GNEncodingExamples.reject_prior_index_below_width

theorem check_reject_trailing_frame :
    decodeGN? (GNEncodingExamples.capBits ++ G1Frame.blank.bits) = none :=
  GNEncodingExamples.reject_trailing_frame

theorem check_reject_reserved_mid (rest : List Bool) :
    decodeGN?
        (([.bof, .data true, .output false, .output false, .separator,
            .cursor] : List G1Frame).flatMap G1Frame.bits ++
          true :: true :: false :: true :: rest) = none :=
  GNEncodingExamples.reject_reserved_mid rest

end Pnp3.Tests.TMGateNEncodingSurface
