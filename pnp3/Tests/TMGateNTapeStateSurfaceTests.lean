import Complexity.TMVerifier.TuringToolkit.GateNTapeStateExamples

/-!
# GN-2 pure tape-state surface

Definitions receive `#check` pins only.  Every public source/example theorem
receives a named wrapper whose inferred type is exactly the source theorem's
type.  No theorem is proved independently here.
-/

namespace Pnp3.Tests.TMGateNTapeStateSurface

open Pnp3.Internal.PsubsetPpoly.TM

/-- Local shorthand for an exact-type theorem alias. -/
syntax (priority := high) "theorem " ident " := " term : command
macro_rules
  | `(theorem $name:ident := $proof:term) =>
      `(theorem $name : type_of% $proof := $proof)

#check @gnUniformRecordsFrames
#check @gnRecordsAtFrames
#check @gnCurrentValues
#check @gnReadCurrentValues
#check @gnFinalValue
#check @gnFinalTail
#check @encodeGNAtFrames
#check @encodeGNAt
#check @gnSelectedGate?
#check @gnSelectedRecord?
#check @gnWorkRequest?
#check @gnCurrentWork?
#check @gnCommit?
#check @GateNTapeState
#check @gnTapeFrames
#check @gnTapeCell
#check @GNTapeStateExamples.capProgram
#check @GNTapeStateExamples.capInitialFrames
#check @GNTapeStateExamples.capFirstFrames
#check @GNTapeStateExamples.capFinalFrames
#check @GNTapeStateExamples.tightProgram

theorem check_gnIndex_lt_length := @gnIndex_lt_length
theorem check_gnNat_le_sum := @gnNat_le_sum
theorem check_gnUniformRecordsFrames_nil := @gnUniformRecordsFrames_nil
theorem check_gnUniformRecordsFrames_length := @gnUniformRecordsFrames_length
theorem check_gnRecordsFrames_bof := @gnRecordsFrames_bof
theorem check_gnRecordsAtFrames_nil := @gnRecordsAtFrames_nil
theorem check_gnRecordsAtFrames_zero := @gnRecordsAtFrames_zero
theorem check_gnRecordsAtFrames_length := @gnRecordsAtFrames_length
theorem check_gnRecordsAtFrames_split := @gnRecordsAtFrames_split
theorem check_gnRecordsAtFrames_succ_split := @gnRecordsAtFrames_succ_split
theorem check_gnRecordsAtFrames_all_spent := @gnRecordsAtFrames_all_spent
theorem check_gnRecordsAtFrames_count_cursor := @gnRecordsAtFrames_count_cursor
theorem check_gnRecordsAtFrames_count_spent := @gnRecordsAtFrames_count_spent
theorem check_encodeGNAtFrames_shape := @encodeGNAtFrames_shape
theorem check_encodeGNAtFrames_zero := @encodeGNAtFrames_zero
theorem check_encodeGNAt_zero := @encodeGNAt_zero
theorem check_encodeGNAtFrames_length := @encodeGNAtFrames_length
theorem check_encodeGNAt_length := @encodeGNAt_length
theorem check_encodeGNAt_regions := @encodeGNAt_regions
theorem check_gnReadCurrentValues_exact := @gnReadCurrentValues_exact
theorem check_gnSelectedGate_exact := @gnSelectedGate?_exact
theorem check_gnSelectedRecord_exact := @gnSelectedRecord?_exact
theorem check_gnSelectedRecord_decode := @gnSelectedRecord_decode
theorem check_gnSelectedRecord_embedded := @gnSelectedRecord_embedded
theorem check_gnSelected_index_bound := @gnSelected_index_bound
theorem check_gnCurrentValues_length := @gnCurrentValues_length
theorem check_gnCurrentWork_exact := @gnCurrentWork?_exact
theorem check_gnWorkRequest_spec := @gnWorkRequest_spec
theorem check_gnCommit_exact := @gnCommit?_exact
theorem check_gnCommit_terminal := @gnCommit?_terminal
theorem check_encodeGNAt_commit_shape := @encodeGNAt_commit_shape
theorem check_encodeGNAt_commit_length := @encodeGNAt_commit_length
theorem check_encodeGNAt_commit_inputs := @encodeGNAt_commit_inputs
theorem check_encodeGNAt_commit_records := @encodeGNAt_commit_records
theorem check_gnFinalValue_before_terminal := @gnFinalValue_before_terminal
theorem check_gnFinalValue_terminal_commit := @gnFinalValue_terminal_commit
theorem check_gnFinalValue_nonterminal_commit := @gnFinalValue_nonterminal_commit
theorem check_GateNTapeState_initial := @GateNTapeState.initial
theorem check_GateNTapeState_step := @GateNTapeState.step
theorem check_GateNTapeState_cursor_count := @GateNTapeState.cursor_count
theorem check_GateNTapeState_initial_parser := @GateNTapeState.initial_parser
theorem check_gnTapeFrames_scratch := @gnTapeFrames_scratch
theorem check_gnTapeCell_scratch_blank := @gnTapeCell_scratch_blank
theorem check_gnWorkWord_length := @gnWorkWord_length
theorem check_encodeGN_length_eq := @encodeGN_length_eq
theorem check_gnRecordSize_le_recordsLength := @gnRecordSize_le_recordsLength
theorem check_gnWorkWord_add_sixteen_le_input := @gnWorkWord_add_sixteen_le_input

theorem check_capstone_initial_literal := @GNTapeStateExamples.capstone_initial_literal
theorem check_capstone_initial_state := @GNTapeStateExamples.capstone_initial_state
theorem check_capstone_first_literal := @GNTapeStateExamples.capstone_first_literal
theorem check_capstone_first_commit := @GNTapeStateExamples.capstone_first_commit
theorem check_capstone_first_state := @GNTapeStateExamples.capstone_first_state
theorem check_capstone_first_values := @GNTapeStateExamples.capstone_first_values
theorem check_capstone_second_selected := @GNTapeStateExamples.capstone_second_selected
theorem check_capstone_second_record_decode :=
  @GNTapeStateExamples.capstone_second_record_decode
theorem check_capstone_second_work := @GNTapeStateExamples.capstone_second_work
theorem check_capstone_final_literal := @GNTapeStateExamples.capstone_final_literal
theorem check_capstone_second_commit := @GNTapeStateExamples.capstone_second_commit
theorem check_capstone_final_state := @GNTapeStateExamples.capstone_final_state
theorem check_capstone_final_values := @GNTapeStateExamples.capstone_final_values
theorem check_capstone_final_output := @GNTapeStateExamples.capstone_final_output
theorem check_capstone_final_terminal := @GNTapeStateExamples.capstone_final_terminal
theorem check_capstone_lengths := @GNTapeStateExamples.capstone_lengths
theorem check_capstone_eval_consistent := @GNTapeStateExamples.capstone_eval_consistent
theorem check_capstone_first_scratch_cell_blank :=
  @GNTapeStateExamples.capstone_first_scratch_cell_blank
theorem check_tight_work_length := @GNTapeStateExamples.tight_work_length
theorem check_tight_input_length := @GNTapeStateExamples.tight_input_length
theorem check_tight_bound_eq := @GNTapeStateExamples.tight_bound_eq
theorem check_tight_bound_seventeen_false :=
  @GNTapeStateExamples.tight_bound_seventeen_false

end Pnp3.Tests.TMGateNTapeStateSurface
