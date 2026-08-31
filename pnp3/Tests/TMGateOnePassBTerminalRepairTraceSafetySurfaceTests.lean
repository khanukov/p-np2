import Complexity.TMVerifier.TuringToolkit.GateOnePassBTerminalRepairTraceSafety

/-!
# GN-3B2c2 terminal pass-B cleanup/repair safety surface (2026-08-31)

Definitions and constructors receive `#check` pins only.  Every theorem has an
exact named wrapper rooted directly in its source theorem.
-/

namespace Pnp3.Tests.TMGateOnePassBTerminalRepairTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly.TM

syntax (priority := high) "theorem " ident " := " term : command
macro_rules
  | `(theorem $name:ident := $proof:term) =>
      `(theorem $name : type_of% $proof := $proof)

#check @G1TerminalBShape
#check @G1TerminalBShape.mk
#check @G1TerminalBShape.of_request
#check @G1RepairSweepShape
#check @G1RepairSweepShape.mk
#check @G1RepairSweepShape.of_request
#check @G1PassBTerminalRepairTraceProbes.reqAnd

theorem check_g1CS_walk_seek_exhaust_runSafe :=
  @g1CS_walk_seek_exhaust_runSafe
theorem check_g1CS_walk_exh_to_cursor_runSafe :=
  @g1CS_walk_exh_to_cursor_runSafe
theorem check_g1CS_walk_terminal_turn_restore_runSafe :=
  @g1CS_walk_terminal_turn_restore_runSafe
theorem check_g1CS_walk_terminal_trace_safe :=
  @g1CS_walk_terminal_trace_safe
theorem check_g1Repair_reverseFrame_runSafe :=
  @g1Repair_reverseFrame_runSafe
theorem check_g1CS_repair_scan_skip_runSafe :=
  @g1CS_repair_scan_skip_runSafe
theorem check_g1CS_repair_cycle_runSafe :=
  @g1CS_repair_cycle_runSafe
theorem check_g1CS_repair_spent_run_runSafe :=
  @g1CS_repair_spent_run_runSafe
theorem check_g1CS_repair_finish_runSafe :=
  @g1CS_repair_finish_runSafe
theorem check_g1CS_repair_sweep_runSafe :=
  @g1CS_repair_sweep_runSafe
theorem check_g1CS_walk_terminal_repair_trace_safe :=
  @g1CS_walk_terminal_repair_trace_safe
theorem check_reqAnd_canonical :=
  @G1PassBTerminalRepairTraceProbes.reqAnd_canonical
theorem check_literal_terminal_repair_trace_safe :=
  @G1PassBTerminalRepairTraceProbes.literal_terminal_repair_trace_safe

end Pnp3.Tests.TMGateOnePassBTerminalRepairTraceSafetySurface
