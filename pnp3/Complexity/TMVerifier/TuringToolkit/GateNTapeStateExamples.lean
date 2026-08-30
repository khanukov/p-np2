import Complexity.TMVerifier.TuringToolkit.GateNTapeState
import Complexity.TMVerifier.TuringToolkit.GateNEncodingExamples

/-!
# GN-2 named pure tape-state capstone

The GN-1 program `[input 0, notGate 0]` has full value environment
`[true, true, false]`.  These named examples commit the two results in order
and end with final output `false`.  They execute no machine.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM.GNTapeStateExamples

open Encoding

abbrev capProgram : GNProgram := GNEncodingExamples.capProgram

def capInitialFrames : List G1Frame := encodeGNAtFrames capProgram []

def capFirstFrames : List G1Frame := encodeGNAtFrames capProgram [true]

def capFinalFrames : List G1Frame := encodeGNAtFrames capProgram [true, false]

theorem capstone_initial_literal :
    capInitialFrames =
      [.bof, .data true, .output false, .output false, .separator,
        .cursor, .tag, .argSep, .argSep, .finish,
        .bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
        .separator, .output false, .finish] := by decide

theorem capstone_initial_state :
    GateNTapeState capProgram [] capInitialFrames := by
  exact GateNTapeState.initial capProgram

theorem capstone_first_literal :
    capFirstFrames =
      [.bof, .data true, .data true, .output false, .separator,
        .spent, .tag, .argSep, .argSep, .finish,
        .cursor, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
        .separator, .output false, .finish] := by decide

theorem capstone_first_commit :
    gnCommit? capProgram [] true = some ([true], capFirstFrames) := by decide

theorem capstone_first_state :
    GateNTapeState capProgram [true] capFirstFrames := by
  exact ⟨by decide, rfl⟩

theorem capstone_first_values :
    gnCurrentValues capProgram [true] = [true, true] := by decide

theorem capstone_second_selected :
    gnSelectedGate? capProgram [true] = some (SLGate.notGate 0) := rfl

theorem capstone_second_record_decode :
    decodeGNRecordFrames? .cursor
        [.cursor, .tag, .tag, .tag, .argSep, .index, .argSep, .finish] =
      some (G1Tag.not, 1, 0) := by decide

theorem capstone_second_work :
    gnCurrentWork? capProgram [true] =
      some (encodeG1Frames ⟨.not, 1, 0, [true, true]⟩) := by decide

theorem capstone_final_literal :
    capFinalFrames =
      [.bof, .data true, .data true, .data false, .separator,
        .spent, .tag, .argSep, .argSep, .finish,
        .spent, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
        .separator, .output false, .finish] := by decide

theorem capstone_second_commit :
    gnCommit? capProgram [true] false = some ([true, false], capFinalFrames) := by decide

theorem capstone_final_state :
    GateNTapeState capProgram [true, false] capFinalFrames := by
  exact ⟨by decide, rfl⟩

theorem capstone_final_values :
    gnCurrentValues capProgram [true, false] = [true, true, false] := by decide

theorem capstone_final_output :
    capFinalFrames[gnFinalOutputFrame capProgram]? = some (.output false) := by decide

theorem capstone_final_terminal :
    gnCommit? capProgram [true, false] true = none ∧
      (gnRecordsAtFrames 2 capProgram.program.gates).count .cursor = 0 := by decide

theorem capstone_lengths :
    capInitialFrames.length = 21 ∧ capFirstFrames.length = 21 ∧
      capFinalFrames.length = 21 ∧ (encodeGN capProgram).length = 84 := by decide

theorem capstone_eval_consistent :
    evalGNProgramAll capProgram = some [true, true, false] ∧
      evalGNProgram capProgram = some false := by decide

theorem capstone_first_scratch_cell_blank :
    gnTapeCell capProgram [true] 84 = false := by decide

def tightProgram : GNProgram := ⟨[], ⟨[SLGate.const false]⟩⟩

theorem tight_work_length :
    (encodeG1 (gnFieldRequest (gnGateFields (SLGate.const false : SLGate 0))
      (gnCurrentValues tightProgram []))).length = 32 := by decide

theorem tight_input_length : (encodeGN tightProgram).length = 48 := by decide

theorem tight_bound_eq :
    (encodeG1 (gnFieldRequest (gnGateFields (SLGate.const false : SLGate 0))
      (gnCurrentValues tightProgram []))).length + 16 =
        (encodeGN tightProgram).length := by decide

/-- Boundary counterexample: strengthening the uniform constant to 17 is false. -/
theorem tight_bound_seventeen_false :
    ¬((encodeG1 (gnFieldRequest (gnGateFields (SLGate.const false : SLGate 0))
      (gnCurrentValues tightProgram []))).length + 17 ≤
        (encodeGN tightProgram).length) := by decide

end Pnp3.Internal.PsubsetPpoly.TM.GNTapeStateExamples
