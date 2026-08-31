import Complexity.TMVerifier.TuringToolkit.GateOneTraceSafety

/-!
# GN-3B1 + GN-3B2a + GN-3B2b validation/rewind safety surface (2026-08-31)

Definitions receive `#check` pins only.  Every theorem receives a named
exact-type wrapper rooted directly in its source theorem.
-/

namespace Pnp3.Tests.TMGateOneTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly.TM

syntax (priority := high) "theorem " ident " := " term : command
macro_rules
  | `(theorem $name:ident := $proof:term) =>
      `(theorem $name : type_of% $proof := $proof)

#check @g1GateDoneSteps
#check @g1FramePositionOffset
#check @G1ForwardBufferCoherent
#check @G1ValidationScannerMicrostate
#check @G1ValidationScannerMicrostate.mk
#check @G1ValidationRewindBoundary
#check @G1ValidationRewindBoundary.mk
#check @G1ValidationScannerEnvelope
#check @G1ValidationScannerEnvelope.scanning
#check @G1ValidationScannerEnvelope.boundary
#check @g1ValidationRewindSteps
#check @g1ReverseFrameSteps
#check @G1ReversePath
#check @G1ReversePath.bof
#check @G1ReversePath.step
#check @G1ReverseBufferCoherent
#check @G1RewindScannerMicrostate
#check @G1RewindScannerMicrostate.mk
#check @G1RewindHandoff
#check @G1RewindHandoff.mk
#check @G1RewindEnvelope
#check @G1RewindEnvelope.rewinding
#check @G1RewindEnvelope.handoff
#check @G1RewindScannerMicrostate.stepsRemaining
#check @G1RewindStepResult
#check @G1RewindStepResult.rewinding
#check @G1RewindStepResult.handoff

theorem check_g1GateDoneSteps_provenance := @g1GateDoneSteps_provenance
theorem check_g1GateAcceptSteps_eq_done_add_one :=
  @g1GateAcceptSteps_eq_done_add_one
theorem check_g1GateDoneSteps_closed := @g1GateDoneSteps_closed
theorem check_g1GateDoneSteps_const := @g1GateDoneSteps_const
theorem check_g1GateDoneSteps_input := @g1GateDoneSteps_input
theorem check_g1GateDoneSteps_not := @g1GateDoneSteps_not
theorem check_g1GateDoneSteps_and := @g1GateDoneSteps_and
theorem check_g1GateDoneSteps_or := @g1GateDoneSteps_or
theorem check_g1GateDoneSteps_le_clock := @g1GateDoneSteps_le_clock
theorem check_g1CS_output_done_exact := @g1CS_output_done_exact
theorem check_g1CS_gate_done_exact := @g1CS_gate_done_exact
theorem check_g1CS_gate_done_state := @g1CS_gate_done_state
theorem check_g1CS_gate_done_mode := @g1CS_gate_done_mode
theorem check_g1CS_gate_done_context := @g1CS_gate_done_context
theorem check_g1CS_gate_done_head := @g1CS_gate_done_head
theorem check_g1CS_gate_done_tape := @g1CS_gate_done_tape
theorem check_g1CS_gate_done_frames := @g1CS_gate_done_frames
theorem check_g1CS_gate_done_output := @g1CS_gate_done_output
theorem check_g1CS_gate_done_off := @g1CS_gate_done_off
theorem check_g1_runConfig_head_le_start_add :=
  @g1_runConfig_head_le_start_add
theorem check_g1_initial_prefix_head_le_steps :=
  @g1_initial_prefix_head_le_steps
theorem check_g1_local_right_safe_of_head_le_span_pred :=
  @g1_local_right_safe_of_head_le_span_pred
theorem check_g1_initial_prefix_right_safe_of_steps_lt_span :=
  @g1_initial_prefix_right_safe_of_steps_lt_span
theorem check_g1Validation_initial_envelope :=
  @g1Validation_initial_envelope
theorem check_g1Validation_envelope_local_safe :=
  @g1Validation_envelope_local_safe
theorem check_g1Validation_scanner_step_exact :=
  @g1Validation_scanner_step_exact
theorem check_g1Validation_run_envelope := @g1Validation_run_envelope
theorem check_g1Validation_run_safe := @g1Validation_run_safe
theorem check_g1CS_validation_reaches_span_pred :=
  @g1CS_validation_reaches_span_pred
theorem check_g1CS_validation_span_pred_moves_left :=
  @g1CS_validation_span_pred_moves_left
theorem check_g1CS_validation_span_pred_local_safe :=
  @g1CS_validation_span_pred_local_safe
theorem check_g1Validation_run_safe_through_boundary :=
  @g1Validation_run_safe_through_boundary
theorem check_g1CS_validation_trace_safe := @g1CS_validation_trace_safe
theorem check_g1Validation_rewind_entry_exact :=
  @g1Validation_rewind_entry_exact
theorem check_g1Validation_rewind_entry_envelope :=
  @g1Validation_rewind_entry_envelope
theorem check_g1Rewind_microstate_local_safe :=
  @g1Rewind_microstate_local_safe
theorem check_g1Rewind_microstate_step_ranked :=
  @g1Rewind_microstate_step_ranked
theorem check_g1Rewind_microstate_step_exact :=
  @g1Rewind_microstate_step_exact
theorem check_g1Rewind_envelope_local_safe :=
  @g1Rewind_envelope_local_safe
theorem check_g1Validation_rewind_entry_ranked :=
  @g1Validation_rewind_entry_ranked
theorem check_g1Rewind_microstate_run_safe :=
  @g1Rewind_microstate_run_safe
theorem check_g1ValidationRewindSteps_closed :=
  @g1ValidationRewindSteps_closed
theorem check_g1ValidationRewindSteps_add_boundary :=
  @g1ValidationRewindSteps_add_boundary
theorem check_g1Validation_rewind_run_safe :=
  @g1Validation_rewind_run_safe
theorem check_g1ValidationRewind_run_safe_to_readB :=
  @g1ValidationRewind_run_safe_to_readB
theorem check_g1ValidationRewind_prefix_head_lt :=
  @g1ValidationRewind_prefix_head_lt
theorem check_g1ValidationRewind_no_left_at_zero :=
  @g1ValidationRewind_no_left_at_zero
theorem check_g1CS_validation_rewind_trace_safe :=
  @g1CS_validation_rewind_trace_safe
theorem check_literal_done_steps := @G1TraceSafetyProbes.literal_done_steps
theorem check_literal_false_done := @G1TraceSafetyProbes.literal_false_done
theorem check_literal_true_done := @G1TraceSafetyProbes.literal_true_done
theorem check_literal_false_span_pred_safe :=
  @G1TraceSafetyProbes.literal_false_span_pred_safe
theorem check_literal_true_span_pred_safe :=
  @G1TraceSafetyProbes.literal_true_span_pred_safe

end Pnp3.Tests.TMGateOneTraceSafetySurface
