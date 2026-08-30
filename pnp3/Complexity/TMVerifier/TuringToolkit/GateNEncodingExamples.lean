import Complexity.TMVerifier.TuringToolkit.GateNEncoding

/-!
# GN-1 named pure capstone

Infrastructure-only executable probes for the fixed ABI.  The capstone has
one serialized input value and two serialized records: `input 0`, then
`notGate 0`.  The second record contains absolute operand index `1`.  All
rejection statements are about the pure exact-list parser, not a machine.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM.GNEncodingExamples

open Encoding

def capProgram : GNProgram :=
  ⟨[true], ⟨[SLGate.input ⟨0, by decide⟩, SLGate.notGate 0]⟩⟩

def capFrames : List G1Frame := encodeGNFrames capProgram

def capBits : List Bool := encodeGN capProgram

def emptyProgram : GNProgram := ⟨[true], ⟨[]⟩⟩

theorem capstone_frames_literal :
    capFrames =
      [.bof, .data true, .output false, .output false, .separator,
        .cursor, .tag, .argSep, .argSep, .finish,
        .bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
        .separator, .output false, .finish] := by decide

theorem capstone_counts :
    capFrames.length = 21 ∧ capBits.length = 84 := by decide

theorem capstone_records_decode :
    decodeGNRecordFrames? .cursor
        [.cursor, .tag, .argSep, .argSep, .finish] =
          some (G1Tag.input, 0, 0) ∧
      decodeGNRecordFrames? .bof
        [.bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish] =
          some (G1Tag.not, 1, 0) := by decide

/-- The nonvacuous two-gate endpoint: the serialized program decodes exactly,
and current-value semantics yields the successful Boolean result `false`. -/
theorem capstone_decode_and_eval :
    decodeGN? capBits = some capProgram ∧ evalGNProgram capProgram = some false := by
  constructor
  · exact decodeGN?_encodeGN capProgram
  · decide

theorem capstone_eval_all :
    evalGNProgramAll capProgram = some [true, true, false] := by decide

/-- Regression: inputs remain in the full environment, but are not a gate
result and therefore cannot become the program output. -/
theorem empty_program_eval : evalGNProgram emptyProgram = none := by decide

theorem empty_program_eval_all :
    evalGNProgramAll emptyProgram = some [true] := by decide

def badMarkerFrames : List G1Frame :=
  [.bof, .data true, .output false, .output false, .separator,
    .bof, .tag, .argSep, .argSep, .finish,
    .bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
    .separator, .output false, .finish]

def badSlotCountFrames : List G1Frame :=
  [.bof, .data true, .output false, .separator,
    .cursor, .tag, .argSep, .argSep, .finish,
    .bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
    .separator, .output false, .finish]

def badTagFrames : List G1Frame :=
  [.bof, .data true, .output false, .separator,
    .cursor, .tag, .tag, .tag, .tag, .tag, .tag,
      .argSep, .argSep, .finish,
    .separator, .output false, .finish]

def invalidInputIndexFrames : List G1Frame :=
  [.bof, .data true, .output false, .separator,
    .cursor, .tag, .argSep, .index, .argSep, .finish,
    .separator, .output false, .finish]

def priorIndexBelowWidthFrames : List G1Frame :=
  [.bof, .data true, .output false, .separator,
    .cursor, .tag, .tag, .tag, .argSep, .argSep, .finish,
    .separator, .output false, .finish]

theorem reject_wrong_marker :
    decodeGN? (badMarkerFrames.flatMap G1Frame.bits) = none := by rfl

theorem reject_slot_record_mismatch_frames :
    decodeGNFrameList? badSlotCountFrames = none := by rfl

theorem reject_slot_record_mismatch :
    decodeGN? (badSlotCountFrames.flatMap G1Frame.bits) = none := by rfl

theorem reject_bad_tag_run :
    decodeGN? (badTagFrames.flatMap G1Frame.bits) = none := by rfl

theorem reject_invalid_input_index :
    decodeGN? (invalidInputIndexFrames.flatMap G1Frame.bits) = none := by rfl

theorem reject_prior_index_below_width :
    decodeGN? (priorIndexBelowWidthFrames.flatMap G1Frame.bits) = none := by rfl

theorem reject_trailing_frame :
    decodeGN? (capBits ++ G1Frame.blank.bits) = none := by rfl

theorem reject_trailing_frame_frames :
    decodeGNFrameList? (capFrames ++ [.blank]) = none := by rfl

theorem reject_reserved_mid (rest : List Bool) :
    decodeGN?
        (([.bof, .data true, .output false, .output false, .separator,
            .cursor] : List G1Frame).flatMap G1Frame.bits ++
          true :: true :: false :: true :: rest) = none :=
  decodeGN?_reserved_aligned _ rfl rest

end Pnp3.Internal.PsubsetPpoly.TM.GNEncodingExamples
