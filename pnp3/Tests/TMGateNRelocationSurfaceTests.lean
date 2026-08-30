import Complexity.TMVerifier.TuringToolkit.GateNRelocationExamples

/-!
# GN-3A generic local-relocation surface

Definitions receive `#check` pins only.  Every source/example theorem receives
a named exact-type wrapper and is proved only by the corresponding direct
source theorem.
-/

namespace Pnp3.Tests.TMGateNRelocationSurface

open Pnp3.Internal.PsubsetPpoly.TM

syntax (priority := high) "theorem " ident " := " term : command
macro_rules
  | `(theorem $name:ident := $proof:term) =>
      `(theorem $name : type_of% $proof := $proof)

#check @gnLocalSpan
#check @gnSourceIndex
#check @gnTargetIndex
#check @gnOverlayTape
#check @gnShiftConfig
#check @G1LocalStepSafe
#check @G1StepDelegates
#check @G1RunSafe
#check @G1RunDelegates
#check @GNRelocationExamples.capSource
#check @GNRelocationExamples.capAmbient
#check @GNRelocationExamples.capInject
#check @GNRelocationExamples.leftZeroSource

theorem check_gnLocalSpan_le_g1_tapeLength := @gnLocalSpan_le_g1_tapeLength
theorem check_gnLocalSpan_final_frame_fits := @gnLocalSpan_final_frame_fits
theorem check_gnLocalSpan_four_insufficient := @gnLocalSpan_four_insufficient
theorem check_gnLocalSpan_room_iff := @gnLocalSpan_room_iff
theorem check_gnSourceIndex_val := @gnSourceIndex_val
theorem check_gnTargetIndex_val := @gnTargetIndex_val
theorem check_gnOverlayTape_inside := @gnOverlayTape_inside
theorem check_gnOverlayTape_outside := @gnOverlayTape_outside
theorem check_gnShiftConfig_state := @gnShiftConfig_state
theorem check_gnShiftConfig_state_eq_iff := @gnShiftConfig_state_eq_iff
theorem check_gnShiftConfig_head_val := @gnShiftConfig_head_val
theorem check_gnShiftConfig_bit_inside := @gnShiftConfig_bit_inside
theorem check_gnShiftConfig_bit_outside := @gnShiftConfig_bit_outside
theorem check_gnShiftConfig_frame_inside := @gnShiftConfig_frame_inside
theorem check_gnOverlayTape_ext := @gnOverlayTape_ext
theorem check_gnShiftConfig_ext := @gnShiftConfig_ext
theorem check_gn_local_step_safe_next_head := @gn_local_step_safe_next_head
theorem check_gn_shift_moveHead_val := @gn_shift_moveHead_val
theorem check_gn_shift_write_tape := @gn_shift_write_tape
theorem check_gn_delegate_step_shift := @gn_delegate_step_shift
theorem check_G1RunSafe_mono := @G1RunSafe.mono
theorem check_G1RunDelegates_mono := @G1RunDelegates.mono
theorem check_gn_run_safe_endpoint_head := @gn_run_safe_endpoint_head
theorem check_gn_delegate_run_shift := @gn_delegate_run_shift
theorem check_gn_delegate_run_shift_outside_prefix :=
  @gn_delegate_run_shift_outside_prefix
theorem check_gn_delegate_run_shift_outside := @gn_delegate_run_shift_outside
theorem check_gnLocalSpan_room_in_input_of_add_sixteen :=
  @gnLocalSpan_room_in_input_of_add_sixteen
theorem check_gn_g1_target_room_of_add_sixteen :=
  @gn_g1_target_room_of_add_sixteen
theorem check_gn_g1_target_room_zero_of_add_sixteen :=
  @gn_g1_target_room_zero_of_add_sixteen

theorem check_cap_inject_injective := @GNRelocationExamples.cap_inject_injective
theorem check_cap_room := @GNRelocationExamples.cap_room
theorem check_cap_head_local := @GNRelocationExamples.cap_head_local
theorem check_cap_source_move := @GNRelocationExamples.cap_source_move
theorem check_cap_step_safe := @GNRelocationExamples.cap_step_safe
theorem check_cap_step_delegates := @GNRelocationExamples.cap_step_delegates
theorem check_cap_source_step_head := @GNRelocationExamples.cap_source_step_head
theorem check_cap_source_step_move := @GNRelocationExamples.cap_source_step_move
theorem check_capstone_shifted_one_step :=
  @GNRelocationExamples.capstone_shifted_one_step
theorem check_cap_run_safe_two := @GNRelocationExamples.cap_run_safe_two
theorem check_cap_run_delegates_two :=
  @GNRelocationExamples.cap_run_delegates_two
theorem check_capstone_shifted_short_run :=
  @GNRelocationExamples.capstone_shifted_short_run
theorem check_capstone_outside_every_prefix :=
  @GNRelocationExamples.capstone_outside_every_prefix
theorem check_capstone_footprint_exact :=
  @GNRelocationExamples.capstone_footprint_exact
theorem check_left_zero_head_local := @GNRelocationExamples.left_zero_head_local
theorem check_left_zero_target_room :=
  @GNRelocationExamples.left_zero_target_room
theorem check_left_zero_source_next_local :=
  @GNRelocationExamples.left_zero_source_next_local
theorem check_capstone_left_zero_unconditional_shift_false :=
  @GNRelocationExamples.capstone_left_zero_unconditional_shift_false

end Pnp3.Tests.TMGateNRelocationSurface
