import Complexity.TMVerifier.TuringToolkit.GateOneFiveTagTraceSafety

/-!
# GN-3B2fC complete five-tag output-done safety surface (2026-09-01)

Definitions are pinned with `#check`.  Every theorem wrapper states its full
proposition and is rooted directly in the named source theorem.  There are no
inferred aliases or Lean `example` declarations.
-/

namespace Pnp3.Tests.TMGateOneFiveTagTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.G1PassATraceProbes
open Pnp3.Internal.PsubsetPpoly.TM.G1AResultProbes

#check @G1Request
#check @G1Request.Canonical
#check @G1Request.spec
#check @G1RunSafe
#check @G1M.initialConfig
#check @g1Point
#check @encodeG1
#check @g1GateDoneSteps
#check @g1AUnaryRepairSteps
#check @g1ConstActivatedSteps
#check @g1OutputKernelSteps
#check @g1OutputDoneConfig
#check @g1OutputPosition
#check @g1OutputExitHead
#check @g1OutputDoneState
#check @g1RejectState
#check @g1OOBState
#check @G1AResultProbes.reqInputT
#check @G1AResultProbes.reqConstF
#check @G1AResultProbes.reqConstT
#check @G1AResultProbes.reqNotF
#check @G1AResultProbes.reqAndF
#check @G1AResultProbes.reqOrT
#check @G1PassATraceProbes.reqA

theorem check_g1GateDoneSteps_unary_trace_eq (r : G1Request)
    (ht : r.tag = .input ∨ r.tag = .not) :
    g1GateDoneSteps r =
      g1AUnaryRepairSteps r + 3 + 1 + g1OutputKernelSteps r :=
  g1GateDoneSteps_unary_trace_eq r ht

theorem check_g1CS_gate_done_unary_trace_safe
    (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (res : Bool)
    (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1GateDoneSteps r) = g1OutputDoneConfig r res :=
  g1CS_gate_done_unary_trace_safe r hc ht res hs

theorem check_g1GateDoneSteps_const_trace_eq (r : G1Request)
    (ht : r.tag = .const) :
    g1GateDoneSteps r =
      g1ConstActivatedSteps r + 1 + g1OutputKernelSteps r :=
  g1GateDoneSteps_const_trace_eq r ht

theorem check_g1CS_gate_done_const_trace_safe
    (r : G1Request) (hc : r.Canonical) (ht : r.tag = .const)
    (res : Bool) (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1GateDoneSteps r) = g1OutputDoneConfig r res :=
  g1CS_gate_done_const_trace_safe r hc ht res hs

theorem check_g1CS_gate_done_trace_safe
    (r : G1Request) (hc : r.Canonical) (res : Bool)
    (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1GateDoneSteps r) = g1OutputDoneConfig r res :=
  g1CS_gate_done_trace_safe r hc res hs

theorem check_g1CS_gate_done_structure
    (r : G1Request) (hc : r.Canonical) (res : Bool)
    (hs : r.spec = some res) :
    let out := TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) (g1GateDoneSteps r)
    out.tape = writeCell (g1OutputPosition r) res
        (G1M.initialConfig (g1Point (encodeG1 r))).tape ∧
      (out.head : Nat) = g1OutputExitHead r ∧
      out.state.snd = g1OutputDoneState res ∧
      out.state.snd.mode = (if res then .outputDoneTrue else .outputDoneFalse) ∧
      out.state.snd.ctx = g1Ctx0 ∧
      out.state.snd ≠ g1RejectState ∧
      (∀ ctx, out.state.snd ≠ g1OOBState ctx) ∧
      (∀ i : Fin (G1M.tapeLength (encodeG1 r).length),
        (i : Nat) = g1OutputPosition r -> out.tape i = res) ∧
      (∀ i : Fin (G1M.tapeLength (encodeG1 r).length),
        (i : Nat) ≠ g1OutputPosition r ->
          out.tape i =
            (G1M.initialConfig (g1Point (encodeG1 r))).tape i) :=
  g1CS_gate_done_structure r hc res hs

theorem check_literal_done_steps :
    g1GateDoneSteps reqInputT = 229 ∧
      g1GateDoneSteps reqConstF = 151 ∧
      g1GateDoneSteps reqConstT = 171 ∧
      g1GateDoneSteps reqNotF = 285 ∧
      g1GateDoneSteps reqAndF = 484 ∧
      g1GateDoneSteps reqOrT = 512 ∧
      g1GateDoneSteps reqA = 606 :=
  G1FiveTagTraceProbes.literal_done_steps

theorem check_literal_input_true_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 229 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 229 =
        g1OutputDoneConfig reqInputT true :=
  G1FiveTagTraceProbes.literal_input_true_done

theorem check_literal_const_false_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 151 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 151 =
        g1OutputDoneConfig reqConstF false :=
  G1FiveTagTraceProbes.literal_const_false_done

theorem check_literal_const_true_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 171 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 171 =
        g1OutputDoneConfig reqConstT true :=
  G1FiveTagTraceProbes.literal_const_true_done

theorem check_literal_not_false_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 285 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 285 =
        g1OutputDoneConfig reqNotF false :=
  G1FiveTagTraceProbes.literal_not_false_done

theorem check_literal_and_false_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 484 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 484 =
        g1OutputDoneConfig reqAndF false :=
  G1FiveTagTraceProbes.literal_and_false_done

theorem check_literal_or_true_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 512 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 512 =
        g1OutputDoneConfig reqOrT true :=
  G1FiveTagTraceProbes.literal_or_true_done

theorem check_literal_binary_a_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqA))) 606 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqA))) 606 =
        g1OutputDoneConfig reqA true :=
  G1FiveTagTraceProbes.literal_binary_a_done

end Pnp3.Tests.TMGateOneFiveTagTraceSafetySurface
