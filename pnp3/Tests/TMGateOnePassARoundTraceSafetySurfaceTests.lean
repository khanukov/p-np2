import Complexity.TMVerifier.TuringToolkit.GateOnePassARoundTraceSafety

/-!
# GN-3B2e1b one-round pass-A trace safety surface (2026-09-01)

Definitions receive `#check` pins.  Every public source theorem has one exact
named wrapper rooted directly in that theorem.  No driver, terminal repair or
full-gate surface is exported here.
-/

namespace Pnp3.Tests.TMGateOnePassARoundTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly.TM

syntax (priority := high) "theorem " ident " := " term : command
macro_rules
  | `(theorem $name:ident := $proof:term) =>
      `(theorem $name : type_of% $proof := $proof)

#check @g1ASeekRevAdvance
#check @g1ASeekRevComplete
#check @G1ASeekStop
#check @G1ASeekOutSkip
#check @G1ASeekInSkip
#check @g1AWalkRoundSteps
#check @G1PassATraceProbes.reqA

theorem check_g1ASeek_reverseFrame_runSafe :=
  @g1ASeek_reverseFrame_runSafe
theorem check_g1ASeek_revSkip_runSafe :=
  @g1ASeek_revSkip_runSafe
theorem check_g1ASeekOut_revSkip_runSafe :=
  @g1ASeekOut_revSkip_runSafe
theorem check_g1ASeekIn_revSkip_runSafe :=
  @g1ASeekIn_revSkip_runSafe
theorem check_g1ASeek_acrossBoundary_runSafe :=
  @g1ASeek_acrossBoundary_runSafe
theorem check_g1CS_aWalk_seek_index_runSafe :=
  @g1CS_aWalk_seek_index_runSafe
theorem check_g1CS_aWalk_fwd_to_cursor_runSafe :=
  @g1CS_aWalk_fwd_to_cursor_runSafe
theorem check_g1CS_aWalk_round_runSafe :=
  @g1CS_aWalk_round_runSafe
theorem check_g1CS_aWalk_round_trace_safe :=
  @g1CS_aWalk_round_trace_safe
theorem check_g1CS_readA_binary_one_round_from_initial_trace_safe :=
  @g1CS_readA_binary_one_round_from_initial_trace_safe
theorem check_literal_round_trace_safe :=
  @G1PassATraceProbes.literal_round_trace_safe
theorem check_literal_one_round_from_initial_trace_safe :=
  @G1PassATraceProbes.literal_one_round_from_initial_trace_safe

end Pnp3.Tests.TMGateOnePassARoundTraceSafetySurface
