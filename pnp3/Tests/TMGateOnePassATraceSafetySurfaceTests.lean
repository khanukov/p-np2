import Complexity.TMVerifier.TuringToolkit.GateOnePassATraceSafety

/-!
# GN-3B2e1a binary pass-A installation safety surface (2026-08-31)

Definitions receive `#check` pins.  Every public theorem has an exact named
wrapper rooted directly in its source theorem.  No one-round safety surface is
claimed by this dependency-closed e1a split.
-/

namespace Pnp3.Tests.TMGateOnePassATraceSafetySurface

open Pnp3.Internal.PsubsetPpoly.TM

syntax (priority := high) "theorem " ident " := " term : command
macro_rules
  | `(theorem $name:ident := $proof:term) =>
      `(theorem $name : type_of% $proof := $proof)

#check @g1AReadInstallSteps
#check @G1PassATraceProbes.reqA

theorem check_g1CS_readA_install_runSafe
    (r : G1Request) (htag : r.tag ≠ .const) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    G1RunSafe (g1ReadAConfig r bB) (g1AReadInstallSteps r) :=
  g1CS_readA_install_runSafe r htag bA bB rest hv
theorem check_g1CS_readA_binary_install_runSafe :=
  @g1CS_readA_binary_install_runSafe
theorem check_g1CS_readA_binary_install_trace_safe :=
  @g1CS_readA_binary_install_trace_safe
theorem check_g1CS_readA_binary_install_from_initial_trace_safe :=
  @g1CS_readA_binary_install_from_initial_trace_safe
theorem check_g1CS_readA_binary_install_structure :=
  @g1CS_readA_binary_install_structure
theorem check_literal_install_trace_safe :=
  @G1PassATraceProbes.literal_install_trace_safe

end Pnp3.Tests.TMGateOnePassATraceSafetySurface
