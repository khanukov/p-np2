import Complexity.TMVerifier.TuringToolkit.GateOnePassBTraceSafety

/-!
# GN-3B2c1 pass-B trace-safety surface (2026-08-31)

Definitions and constructors receive `#check` pins only.  Every theorem has an
exact named wrapper rooted directly in its source theorem.
-/

namespace Pnp3.Tests.TMGateOnePassBTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly.TM

syntax (priority := high) "theorem " ident " := " term : command
macro_rules
  | `(theorem $name:ident := $proof:term) =>
      `(theorem $name : type_of% $proof := $proof)

#check @G1ForwardScannerMicrostate
#check @G1ForwardScannerMicrostate.mk
#check @G1ForwardScannerHandoff
#check @G1ForwardScannerHandoff.mk
#check @G1ForwardScannerEnvelope
#check @G1ForwardScannerEnvelope.scanning
#check @G1ForwardScannerEnvelope.handoff
#check @G1ForwardStepResult
#check @G1ForwardStepResult.scanning
#check @G1ForwardStepResult.handoff
#check @g1Forward_scan_entry

theorem check_g1LocalStepSafe_of_interior := @g1LocalStepSafe_of_interior
theorem check_g1LocalStepSafe_at_zero_of_not_left :=
  @g1LocalStepSafe_at_zero_of_not_left
theorem check_g1Forward_microstate_localSafe :=
  @g1Forward_microstate_localSafe
theorem check_g1Forward_microstate_step := @g1Forward_microstate_step
theorem check_g1Forward_microstate_runSafe := @g1Forward_microstate_runSafe
theorem check_g1Forward_scan_runSafe := @g1Forward_scan_runSafe
theorem check_g1Walk_reverseFrame_runSafe := @g1Walk_reverseFrame_runSafe
theorem check_g1Walk_revSkip_runSafe := @g1Walk_revSkip_runSafe
theorem check_g1Walk_seekToMarker_runSafe := @g1Walk_seekToMarker_runSafe
theorem check_g1RunSafe_of_margins := @g1RunSafe_of_margins
theorem check_g1Forward_frame_runSafe := @g1Forward_frame_runSafe
theorem check_g1Forward_scanFrom_runSafe := @g1Forward_scanFrom_runSafe
theorem check_g1CS_walk_seek_mark_runSafe := @g1CS_walk_seek_mark_runSafe
theorem check_g1CS_walk_fwd_to_cursor_runSafe :=
  @g1CS_walk_fwd_to_cursor_runSafe
theorem check_g1CS_readB_install_scan_runSafe :=
  @g1CS_readB_install_scan_runSafe
theorem check_g1CS_walk_install_runSafe := @g1CS_walk_install_runSafe
theorem check_g1CS_walk_iteration_runSafe := @g1CS_walk_iteration_runSafe
theorem check_g1CS_walk_one_round_trace_safe :=
  @g1CS_walk_one_round_trace_safe

end Pnp3.Tests.TMGateOnePassBTraceSafetySurface
