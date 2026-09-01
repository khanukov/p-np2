import Complexity.TMVerifier.TuringToolkit.GateOneARepairTraceSafety

/-!
# GN-3B2e3 complete live operand-A repair safety surface (2026-09-01)

Definitions and the live repair constructors are pinned with `#check`.  Every
theorem below has an explicit proposition and is rooted directly in the named
source theorem; there are no inferred-type wrappers or Lean `example` commands.
-/

namespace Pnp3.Tests.TMGateOneARepairTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

set_option maxRecDepth 4096

#check @G1Mode.aRepairStart
#check @G1Mode.aRepairSeek
#check @G1Mode.aRepairWrite
#check @G1Mode.aRepairBack
#check @G1Mode.aRepairHop
#check @G1Mode.aRepairDone
#check @G1Mode.reject
#check @G1FramePosition.p3
#check @G1FramePosition.p2
#check @G1FramePosition.p1
#check @G1FramePosition.p0
#check @G1Frame.bof
#check @G1Frame.spent
#check @G1Frame.index
#check @G1ARepairStop
#check @g1ARepairStopState
#check @g1ARepairScanner
#check @g1ARepairCycle
#check @g1ARepairPassSteps
#check @g1ARepairSteps
#check @g1ARepairEntryConfig
#check @g1ARepairDoneConfig
#check @g1ARepairLiveSteps
#check @g1ABinaryRepairSteps
#check @G1ARepairExamples.reqFalse
#check @G1ARepairExamples.reqTrue
#check @G1ARepairExamples.reqZero
#check @G1PassATraceProbes.reqA

theorem check_g1ARepair_reverseFrame_runSafe {W base : Nat}
    (tape : Fin (G1M.tapeLength W) -> Bool) (ctx : G1Ctx)
    (hroom : base + 4 < gnLocalSpan W)
    (hfinal : 0 < base ∨
      G1ARepairStop (g1ARepairBackComplete
        (tape ⟨base, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 1, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 2, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 3, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩))) :
    G1RunSafe
      (g1AlignedConfig W (base + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .aRepairSeek .p3 false false false ctx) 4 :=
  g1ARepair_reverseFrame_runSafe tape ctx hroom hfinal

theorem check_g1CS_aRepair_scan_skip_runSafe {W : Nat}
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hpre : 0 < pre.length) (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hroom : 4 * (pre.length + skipped.length) + 3 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) - 1) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx) (4 * skipped.length) :=
  g1CS_aRepair_scan_skip_runSafe pre skipped suffix ctx hpre hskip hroom

theorem check_g1CS_aRepair_cycle_runSafe {W : Nat}
    (pre suffix : List G1Frame) (ctx : G1Ctx) (hpre : 1 < pre.length)
    (hroom : 4 * pre.length + 9 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * pre.length + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx) 13 :=
  g1CS_aRepair_cycle_runSafe pre suffix ctx hpre hroom

theorem check_g1CS_aRepair_spent_run_runSafe {W : Nat}
    (pre suffix : List G1Frame) (s : Nat) (ctx : G1Ctx)
    (hpre : 1 < pre.length)
    (hroom : 4 * (pre.length + s) + 5 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + s) - 1) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ List.replicate s G1Frame.spent ++ suffix).flatMap
          G1Frame.bits)) .aRepairSeek .p3 false false false ctx) (13 * s) :=
  g1CS_aRepair_spent_run_runSafe pre suffix s ctx hpre hroom

theorem check_g1CS_aRepair_finish_runSafe {W : Nat}
    (suffix : List G1Frame) (ctx : G1Ctx) (hroom : 4 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W 3 (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx) 4 :=
  g1CS_aRepair_finish_runSafe suffix ctx hroom

theorem check_g1CS_aRepair_pass_runSafe {W s : Nat}
    (left mid tail : List G1Frame) (ctx : G1Ctx)
    (hleftPos : 0 < left.length)
    (hleft : ∀ f ∈ left, G1RepairSkip f)
    (hmid : ∀ f ∈ mid, G1RepairSkip f)
    (hroom : 4 * (1 + left.length + s + mid.length) + 9 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (1 + left.length + s + mid.length) - 1)
        (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape (([G1Frame.bof] ++ left ++
          List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
          G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
      (g1ARepairPassSteps left.length s mid.length) :=
  g1CS_aRepair_pass_runSafe left mid tail ctx hleftPos hleft hmid hroom

theorem check_g1CS_aRepair_sweep_runSafe (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1ARepairEntryConfig r b v hm hv) (g1ARepairSteps r) :=
  g1CS_aRepair_sweep_runSafe r b v hm hv

theorem check_g1CS_aRepair_activation_runSafe (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkRepairStartConfig r b v hm hv) 1 :=
  g1CS_aRepair_activation_runSafe r b v hm hv

theorem check_g1CS_aRepair_live_trace_safe (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkRepairStartConfig r b v hm hv)
        (g1ARepairLiveSteps r) ∧
      TM.runConfig (M := G1M) (g1AWalkRepairStartConfig r b v hm hv)
          (g1ARepairLiveSteps r) = g1ARepairDoneConfig r b v :=
  g1CS_aRepair_live_trace_safe r b v hm hv

theorem check_g1CS_aRepair_live_structure (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    let out := TM.runConfig (M := G1M)
      (g1AWalkRepairStartConfig r b v hm hv) (g1ARepairLiveSteps r)
    out.tape = g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap
        G1Frame.bits) ∧
      (out.head : Nat) = 0 ∧
      out.state.snd = g1ARepairDoneState (g1AWalkCtx r b v) ∧
      out.state.snd.ctx = g1AWalkCtx r b v ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v ∧
      (encodeG1Frames r ++ [G1Frame.blank]).count .spent = 0 ∧
      (encodeG1Frames r ++ [G1Frame.blank]).count .cursor = 0 ∧
      (encodeG1Frames r ++ [G1Frame.blank]).count .index = r.arg1 + r.arg2 :=
  g1CS_aRepair_live_structure r b v hm hv

theorem check_g1ABinaryRepairSteps_trace_eq (r : G1Request) :
    g1ABinaryRepairSteps r =
      (g1ABinaryCursorSteps r +
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) +
      g1ARepairLiveSteps r :=
  g1ABinaryRepairSteps_trace_eq r

theorem check_g1CS_aRepair_binary_initial_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (v : Nat -> Bool) (hv : ∀ j, j ≤ r.arg1 -> r.vals[j]? = some (v j))
    (hvals : r.vals = bA :: rest) (hv0 : v 0 = bA) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryRepairSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ABinaryRepairSteps r) =
        g1ARepairDoneConfig r bB (v r.arg1) :=
  g1CS_aRepair_binary_initial_trace_safe r hc ht bA bB rest hB v hv hvals hv0

open Pnp3.Internal.PsubsetPpoly.TM.G1ARepairExamples
open Pnp3.Internal.PsubsetPpoly.TM.G1PassATraceProbes

theorem check_literal_false_local_trace_safe :
    G1RunSafe
        (g1ARepairEntryConfig reqFalse false false (by decide) (by decide)) 58 ∧
      TM.runConfig (M := G1M)
          (g1ARepairEntryConfig reqFalse false false (by decide) (by decide)) 58 =
        g1ARepairDoneConfig reqFalse false false :=
  G1ARepairTraceProbes.literal_false_local_trace_safe

theorem check_literal_true_local_trace_safe :
    G1RunSafe
        (g1ARepairEntryConfig reqTrue true true (by decide) (by decide)) 58 ∧
      TM.runConfig (M := G1M)
          (g1ARepairEntryConfig reqTrue true true (by decide) (by decide)) 58 =
        g1ARepairDoneConfig reqTrue true true :=
  G1ARepairTraceProbes.literal_true_local_trace_safe

theorem check_literal_zero_local_trace_safe :
    G1RunSafe
        (g1ARepairEntryConfig reqZero false true (by decide) (by decide)) 24 ∧
      TM.runConfig (M := G1M)
          (g1ARepairEntryConfig reqZero false true (by decide) (by decide)) 24 =
        g1ARepairDoneConfig reqZero false true :=
  G1ARepairTraceProbes.literal_zero_local_trace_safe

theorem check_literal_binary_steps : g1ABinaryRepairSteps reqA = 541 :=
  G1ARepairTraceProbes.literal_binary_steps

theorem check_literal_binary_initial_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqA))) 541 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqA))) 541 =
        g1ARepairDoneConfig reqA true true :=
  G1ARepairTraceProbes.literal_binary_initial_trace_safe

end Pnp3.Tests.TMGateOneARepairTraceSafetySurface
