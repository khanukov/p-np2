import Complexity.TMVerifier.TuringToolkit.GateOnePassBDriverTraceSafety

/-!
# GN-3B2d arbitrary-arg2 pass-B driver safety surface (2026-08-31)

Every public theorem has an exact named wrapper rooted directly in its source
theorem.  This surface introduces no example declarations.
-/

namespace Pnp3.Tests.TMGateOnePassBDriverTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly.TM

syntax (priority := high) "theorem " ident " := " term : command
macro_rules
  | `(theorem $name:ident := $proof:term) =>
      `(theorem $name : type_of% $proof := $proof)

theorem check_g1CS_walk_loop_runSafe := @g1CS_walk_loop_runSafe
theorem check_g1CS_readB_zero_runSafe := @g1CS_readB_zero_runSafe
theorem check_g1CS_readB_positive_repaired_trace_safe :=
  @g1CS_readB_positive_repaired_trace_safe
theorem check_g1CS_readB_zero_repaired_trace_safe :=
  @g1CS_readB_zero_repaired_trace_safe
theorem check_g1CS_readB_repaired_trace_safe :=
  @g1CS_readB_repaired_trace_safe
theorem check_literal_positive_trace_safe :=
  @G1PassBDriverTraceProbes.literal_positive_trace_safe
theorem check_literal_zero_trace_safe :=
  @G1PassBDriverTraceProbes.literal_zero_trace_safe

end Pnp3.Tests.TMGateOnePassBDriverTraceSafetySurface
