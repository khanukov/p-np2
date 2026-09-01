import Complexity.TMVerifier.TuringToolkit.GateOneOutputDoneTraceSafety

/-!
# GN-3B2e4 binary output-done trace safety surface (2026-09-01)

Definitions are pinned with `#check`.  Every theorem has an explicit
proposition and is rooted directly in its named source theorem.  There are no
inferred-type wrappers or Lean `example` declarations.
-/

namespace Pnp3.Tests.TMGateOneOutputDoneTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.G1PassATraceProbes
open Pnp3.Internal.PsubsetPpoly.TM.G1AResultProbes

#check @G1RunSafe
#check @G1LocalStepSafe
#check @g1ARepairDoneConfig
#check @g1CombineConfig
#check @g1OutputStartConfig
#check @g1OutputDoneConfig
#check @g1OutputKernelSteps
#check @g1GateDoneSteps
#check @g1OutputPosition
#check @g1OutputExitHead
#check @G1Mode.aRepairDone
#check @G1Mode.aResultStart
#check @G1Mode.readAStart
#check @G1Mode.combineStart
#check @G1Mode.outSeek
#check @G1Mode.outTurn
#check @G1Mode.outWriteFalse
#check @G1Mode.outWriteTrue
#check @G1Mode.outputDoneFalse
#check @G1Mode.outputDoneTrue
#check @G1PassATraceProbes.reqA
#check @G1AResultProbes.reqAndF
#check @G1AResultProbes.reqOrT

theorem check_g1CS_aRepairDone_result_runSafe
    (r : G1Request) (b v : Bool) :
    G1RunSafe (g1ARepairDoneConfig r b v) 3 :=
  g1CS_aRepairDone_result_runSafe r b v

theorem check_g1CS_aRepairDone_combine_trace_safe
    (r : G1Request) (b v : Bool) :
    G1RunSafe (g1ARepairDoneConfig r b v) 3 ∧
      TM.runConfig (M := G1M) (g1ARepairDoneConfig r b v) 3 =
        g1CombineConfig r ((g1Residual r.tag b).apply v) :=
  g1CS_aRepairDone_combine_trace_safe r b v

theorem check_g1CS_combine_entry_runSafe (r : G1Request) (res : Bool) :
    G1RunSafe (g1CombineConfig r res) 1 :=
  g1CS_combine_entry_runSafe r res

theorem check_g1CS_output_scan_runSafe (r : G1Request) (res : Bool) :
    G1RunSafe (g1OutputStartConfig r res)
      (4 * ((g1PrefixFrames r).length + 1)) :=
  g1CS_output_scan_runSafe r res

theorem check_g1CS_output_turn_write_runSafe (r : G1Request) (res : Bool) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length (g1OutputBase r + 4)
        (g1OutputBase_safe r)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .outTurn .p0 false false false (g1ResultCtx res)) 5 :=
  g1CS_output_turn_write_runSafe r res

theorem check_g1CS_output_kernel_trace_safe (r : G1Request) (res : Bool) :
    G1RunSafe (g1OutputStartConfig r res) (g1OutputKernelSteps r) ∧
      TM.runConfig (M := G1M) (g1OutputStartConfig r res)
        (g1OutputKernelSteps r) = g1OutputDoneConfig r res :=
  g1CS_output_kernel_trace_safe r res

theorem check_g1CS_output_done_trace_safe (r : G1Request) (res : Bool) :
    G1RunSafe (g1CombineConfig r res) (1 + g1OutputKernelSteps r) ∧
      TM.runConfig (M := G1M) (g1CombineConfig r res)
        (1 + g1OutputKernelSteps r) = g1OutputDoneConfig r res :=
  g1CS_output_done_trace_safe r res

theorem check_g1GateDoneSteps_binary_trace_eq (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1GateDoneSteps r =
      g1ABinaryRepairSteps r + 3 + 1 + g1OutputKernelSteps r :=
  g1GateDoneSteps_binary_trace_eq r ht

theorem check_g1CS_aRepairDone_output_trace_safe
    (r : G1Request) (b v : Bool) :
    let res := (g1Residual r.tag b).apply v
    G1RunSafe (g1ARepairDoneConfig r b v)
        (3 + (1 + g1OutputKernelSteps r)) ∧
      TM.runConfig (M := G1M) (g1ARepairDoneConfig r b v)
          (3 + (1 + g1OutputKernelSteps r)) =
        g1OutputDoneConfig r res :=
  g1CS_aRepairDone_output_trace_safe r b v

theorem check_g1CS_gate_done_binary_trace_safe
    (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (res : Bool)
    (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1GateDoneSteps r) = g1OutputDoneConfig r res :=
  g1CS_gate_done_binary_trace_safe r hc ht res hs

theorem check_g1CS_gate_done_binary_structure
    (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (res : Bool)
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
  g1CS_gate_done_binary_structure r hc ht res hs

theorem check_literal_binary_done_steps : g1GateDoneSteps reqA = 606 :=
  G1OutputDoneTraceProbes.literal_binary_done_steps

theorem check_literal_binary_output_done_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqA))) 606 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqA))) 606 =
        g1OutputDoneConfig reqA true :=
  G1OutputDoneTraceProbes.literal_binary_output_done_trace_safe

theorem check_literal_binary_false_done_steps :
    g1GateDoneSteps reqAndF = 484 :=
  G1OutputDoneTraceProbes.literal_binary_false_done_steps

theorem check_literal_binary_false_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 484 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 484 =
        g1OutputDoneConfig reqAndF false :=
  G1OutputDoneTraceProbes.literal_binary_false_done

theorem check_literal_binary_true_done_steps :
    g1GateDoneSteps reqOrT = 512 :=
  G1OutputDoneTraceProbes.literal_binary_true_done_steps

theorem check_literal_binary_true_done :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 512 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 512 =
        g1OutputDoneConfig reqOrT true :=
  G1OutputDoneTraceProbes.literal_binary_true_done

end Pnp3.Tests.TMGateOneOutputDoneTraceSafetySurface
