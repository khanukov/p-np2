import Complexity.TMVerifier.TuringToolkit.GateOneOutputKernel

/-!
# S10a G1 output kernel: exact public surface

Definitions, constructors, and instances receive bare type checks.  Every
public theorem introduced by S10a has one exact named wrapper rooted directly
in that theorem; there are no anonymous examples.
-/

namespace Pnp3.Tests.TMGateOneOutputKernelSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

set_option maxRecDepth 4096

-- Six new control constructors.
#check @G1Mode.outSeek
#check @G1Mode.outTurn
#check @G1Mode.outWriteFalse
#check @G1Mode.outWriteTrue
#check @G1Mode.outputDoneFalse
#check @G1Mode.outputDoneTrue

-- Public control definitions and instance.
#check @g1OutSeekState
#check @g1OutTurnState
#check @g1OutWriteMode
#check @g1OutWriteState
#check @g1OutputDoneMode
#check @g1OutputDoneState
#check @G1OutputKernelMode
#check @instDecidablePredG1ModeG1OutputKernelMode

-- Public output-kernel definitions and instance.
#check @G1OutputSkip
#check @instDecidablePredG1FrameG1OutputSkip
#check @g1OutWriter
#check @g1OutputFrames
#check @g1OutputBase
#check @g1OutputExitHead
#check @g1OutputRoute
#check @g1OutputStartConfig
#check @g1OutputDoneConfig
#check @g1OutputKernelSteps
#check @G1OutputKernelProbes.req

/-! ## Control theorems -/

theorem check_g1Advance_outputKernel_predecessor (mode : G1Mode)
    (frame : G1Frame) :
    G1OutputKernelMode (g1Advance mode frame) → G1OutputKernelMode mode :=
  g1Advance_outputKernel_predecessor mode frame

theorem check_g1Complete_outputKernel_predecessor (mode : G1Mode)
    (b0 b1 b2 b3 : Bool) :
    G1OutputKernelMode (g1Complete mode b0 b1 b2 b3) →
      G1OutputKernelMode mode :=
  g1Complete_outputKernel_predecessor mode b0 b1 b2 b3

theorem check_g1Stuck_of_not_forward {mode : G1Mode}
    (hforward : ¬ G1ForwardMode mode) (hrewind : mode ≠ .rewindStart) :
    G1Stuck mode :=
  g1Stuck_of_not_forward hforward hrewind

theorem check_g1Transition_outTurn (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .outTurn position b0 b1 b2 ctx) scan =
      (0, g1OutWriteState ctx.vB ctx, scan, .left) :=
  g1Transition_outTurn phase position b0 b1 b2 scan ctx

theorem check_g1Transition_outWrite (phase : Fin 1) (res : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase
        (g1State (g1OutWriteMode res) position b0 b1 b2 ctx) scan =
      (0, match position with
          | .p3 => g1State (g1OutWriteMode res) .p2 false false false ctx
          | .p2 => g1State (g1OutWriteMode res) .p1 false false false ctx
          | .p1 => g1State (g1OutWriteMode res) .p0 false false false ctx
          | .p0 => g1OutputDoneState res,
        match position with
          | .p3 => res
          | .p2 => false
          | .p1 => false
          | .p0 => true,
        .left) :=
  g1Transition_outWrite phase res position b0 b1 b2 scan ctx

theorem check_g1Transition_outputDone_accept (phase : Fin 1)
    (res scan : Bool) :
    g1Transition phase (g1OutputDoneState res) scan =
      (0, g1AcceptState, scan, .stay) :=
  g1Transition_outputDone_accept phase res scan

/-! ## Strict scan grammar -/

theorem check_G1OutputSkip_ne_output {f : G1Frame} (h : G1OutputSkip f)
    (v : Bool) :
    f ≠ .output v :=
  G1OutputSkip_ne_output h v

theorem check_G1OutputSkip_ne_spent {f : G1Frame} (h : G1OutputSkip f) :
    f ≠ .spent :=
  G1OutputSkip_ne_spent h

theorem check_G1OutputSkip_ne_cursor {f : G1Frame} (h : G1OutputSkip f) :
    f ≠ .cursor :=
  G1OutputSkip_ne_cursor h

theorem check_g1Advance_outSeek_of_skip {f : G1Frame} (h : G1OutputSkip f) :
    g1Advance .outSeek f = .outSeek :=
  g1Advance_outSeek_of_skip h

theorem check_g1Advance_outSeek_output_false :
    g1Advance .outSeek (.output false) = .outTurn :=
  g1Advance_outSeek_output_false

theorem check_g1Advance_outSeek_reject_iff (f : G1Frame) :
    g1Advance .outSeek f = .reject ↔
      f = .blank ∨ f = .cursor ∨ f = .output true ∨
        f = .finish ∨ f = .spent :=
  g1Advance_outSeek_reject_iff f

theorem check_g1Advance_outSeek_forbidden :
    g1Advance .outSeek (.output true) = .reject ∧
      g1Advance .outSeek .spent = .reject ∧
      g1Advance .outSeek .cursor = .reject ∧
      g1Advance .outSeek .finish = .reject ∧
      g1Advance .outSeek .blank = .reject :=
  g1Advance_outSeek_forbidden

theorem check_g1Complete_outSeek_malformed_reserved
    {b0 b1 b2 b3 : Bool}
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    g1Complete .outSeek b0 b1 b2 b3 = .reject ∧
      g1Complete .outSeek true true false true = .reject ∧
      g1Complete .outSeek true true true false = .reject ∧
      g1Complete .outSeek true true true true = .reject :=
  g1Complete_outSeek_malformed_reserved hbad

theorem check_g1Transition_outputKernel_predecessor (phase : Fin 1)
    (s : G1State) (scan : Bool)
    (h : G1OutputKernelMode (g1Transition phase s scan).2.1.mode) :
    G1OutputKernelMode s.mode ∨ s.mode = .combineStart :=
  g1Transition_outputKernel_predecessor phase s scan h

theorem check_g1Transition_combineStart_output_mode (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    (g1Transition phase
      (g1State .combineStart position b0 b1 b2 ctx) scan).2.1.mode = .outSeek :=
  g1Transition_combineStart_output_mode phase position b0 b1 b2 scan ctx

/-! ## Exact caller-supplied atoms -/

theorem check_g1CS_out_scan (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1OutputSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length) (by omega)
          (g1ListTape
            ((pre ++ skipped ++ G1Frame.output false :: suffix).flatMap
              G1Frame.bits))
          .outSeek .p0 false false false ctx)
        (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.output false :: suffix).flatMap
            G1Frame.bits))
        .outTurn .p0 false false false ctx :=
  g1CS_out_scan n pre skipped suffix ctx hskip hsafe

theorem check_g1CS_out_turn (n h : Nat) (hh : h < G1M.tapeLength n)
    (hpos : 0 < h) (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .outTurn .p0 false false false ctx) 1 =
      g1AlignedConfigQ n (h - 1) (by omega) tape
        (g1OutWriteState ctx.vB ctx) :=
  g1CS_out_turn n h hh hpos tape ctx

theorem check_g1OutWriter_machine (res : Bool) :
    (g1OutWriter res).machine = G1M :=
  g1OutWriter_machine res

theorem check_g1CS_out_write (n : Nat) (pre suffix : List G1Frame)
    (res : Bool) (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfigQ n (4 * pre.length + 3) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
          (g1OutWriteState res ctx)) 4 =
      g1AlignedConfigQ n (4 * pre.length - 1) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.output res :: suffix).flatMap G1Frame.bits))
        (g1OutputDoneState res) :=
  g1CS_out_write n pre suffix res ctx hpre hsafe

/-! ## Canonical output layout -/

theorem check_g1OutputFrames_false (r : G1Request) :
    g1OutputFrames r false = g1ValidationFrames r :=
  g1OutputFrames_false r

theorem check_g1OutputFrames_length (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 :=
  g1OutputFrames_length r res

theorem check_g1OutputBase_eq (r : G1Request) :
    g1OutputBase r =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) :=
  g1OutputBase_eq r

theorem check_g1OutputPosition_eq_base (r : G1Request) :
    g1OutputPosition r = g1OutputBase r + 3 :=
  g1OutputPosition_eq_base r

theorem check_g1OutputBase_pos (r : G1Request) : 0 < g1OutputBase r :=
  g1OutputBase_pos r

theorem check_g1OutputBase_safe (r : G1Request) :
    g1OutputBase r + 4 < G1M.tapeLength (encodeG1 r).length :=
  g1OutputBase_safe r

theorem check_g1OutputExitHead_safe (r : G1Request) :
    g1OutputExitHead r < G1M.tapeLength (encodeG1 r).length :=
  g1OutputExitHead_safe r

theorem check_g1OutputTape_false (r : G1Request) :
    g1ListTape (n := (encodeG1 r).length)
        ((g1OutputFrames r false).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1OutputTape_false r

theorem check_g1OutputTape_eq_writeCell (r : G1Request) (res : Bool) :
    g1ListTape (n := (encodeG1 r).length)
        ((g1OutputFrames r res).flatMap G1Frame.bits) =
      writeCell (g1OutputPosition r) res
        (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1OutputTape_eq_writeCell r res

theorem check_g1OutputTape_at (r : G1Request) (res : Bool)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) i = res :=
  g1OutputTape_at r res i hi

theorem check_g1OutputTape_off (r : G1Request) (res : Bool)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) ≠ g1OutputPosition r) :
    g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) i =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape i :=
  g1OutputTape_off r res i hi

theorem check_g1OutputTape_true_ne_initial (r : G1Request)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    g1ListTape ((g1OutputFrames r true).flatMap G1Frame.bits) i ≠
      (G1M.initialConfig (g1Point (encodeG1 r))).tape i :=
  g1OutputTape_true_ne_initial r i hi

theorem check_g1OutputTape_false_identity (r : G1Request) :
    g1ListTape ((g1OutputFrames r false).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1OutputTape_false_identity r

theorem check_g1OutputFrames_count_spent (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count .spent = 0 :=
  g1OutputFrames_count_spent r res

theorem check_g1OutputFrames_count_cursor (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count .cursor = 0 :=
  g1OutputFrames_count_cursor r res

theorem check_g1OutputFrames_count_index (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count .index = r.arg1 + r.arg2 :=
  g1OutputFrames_count_index r res

theorem check_g1PrefixFrames_outSkip (r : G1Request) :
    ∀ f ∈ g1PrefixFrames r, G1OutputSkip f :=
  g1PrefixFrames_outSkip r

theorem check_g1PrefixFrames_ne_output (r : G1Request) (res : Bool) :
    ∀ f ∈ g1PrefixFrames r, f ≠ .output res :=
  g1PrefixFrames_ne_output r res

theorem check_g1OutputFrames_count_output (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count (.output res) = 1 :=
  g1OutputFrames_count_output r res

theorem check_g1OutputFrames_count_other_output (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count (.output (!res)) = 0 :=
  g1OutputFrames_count_other_output r res

/-! ## Canonical caller-supplied capstone -/

theorem check_g1OutputRoute_length (r : G1Request) :
    (g1OutputRoute r).length = (g1PrefixFrames r).length + 1 :=
  g1OutputRoute_length r

theorem check_g1OutputDoneConfig_state (r : G1Request) (res : Bool) :
    (g1OutputDoneConfig r res).state.snd = g1OutputDoneState res :=
  g1OutputDoneConfig_state r res

theorem check_g1OutputDoneConfig_head (r : G1Request) (res : Bool) :
    ((g1OutputDoneConfig r res).head : Nat) = g1OutputExitHead r :=
  g1OutputDoneConfig_head r res

theorem check_g1OutputDoneConfig_tape (r : G1Request) (res : Bool) :
    (g1OutputDoneConfig r res).tape =
      g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) :=
  g1OutputDoneConfig_tape r res

theorem check_g1OutputKernelSteps_eq (r : G1Request) :
    g1OutputKernelSteps r = 4 * ((g1PrefixFrames r).length + 1) + 5 :=
  g1OutputKernelSteps_eq r

theorem check_g1CS_output_scan_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1OutputStartConfig r res)
        (4 * ((g1PrefixFrames r).length + 1)) =
      g1AlignedConfig (encodeG1 r).length (g1OutputBase r + 4)
        (g1OutputBase_safe r)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .outTurn .p0 false false false (g1ResultCtx res) :=
  g1CS_output_scan_exact r res

theorem check_g1CS_output_turn_write_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig (encodeG1 r).length (g1OutputBase r + 4)
          (g1OutputBase_safe r)
          (G1M.initialConfig (g1Point (encodeG1 r))).tape
          .outTurn .p0 false false false (g1ResultCtx res)) 5 =
      g1OutputDoneConfig r res :=
  g1CS_output_turn_write_exact r res

theorem check_g1CS_output_kernel_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1OutputStartConfig r res)
        (g1OutputKernelSteps r) = g1OutputDoneConfig r res :=
  g1CS_output_kernel_exact r res

theorem check_g1CS_output_kernel_tape (r : G1Request) (res : Bool) :
    (TM.runConfig (M := G1M) (g1OutputStartConfig r res)
      (g1OutputKernelSteps r)).tape =
      writeCell (g1OutputPosition r) res
        (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1CS_output_kernel_tape r res

theorem check_g1CS_output_kernel_head (r : G1Request) (res : Bool) :
    ((TM.runConfig (M := G1M) (g1OutputStartConfig r res)
      (g1OutputKernelSteps r)).head : Nat) = g1OutputExitHead r :=
  g1CS_output_kernel_head r res

theorem check_g1CS_output_kernel_state (r : G1Request) (res : Bool) :
    (TM.runConfig (M := G1M) (g1OutputStartConfig r res)
      (g1OutputKernelSteps r)).state.snd = g1OutputDoneState res :=
  g1CS_output_kernel_state r res

theorem check_g1OutputDone_false_ne_reject :
    g1OutputDoneState false ≠ g1RejectState :=
  g1OutputDone_false_ne_reject

theorem check_g1OutputDone_false_ne_oob (ctx : G1Ctx) :
    g1OutputDoneState false ≠ g1OOBState ctx :=
  g1OutputDone_false_ne_oob ctx

theorem check_g1OutputDone_ne_combine (res : Bool) (ctx : G1Ctx) :
    g1OutputDoneState res ≠ g1CombineState ctx :=
  g1OutputDone_ne_combine res ctx

/-! ## Literal caller-supplied false/true probes -/

open G1OutputKernelProbes

theorem check_literal_frames_false :
    g1OutputFrames req false =
      [.bof, .tag, .tag, .argSep, .argSep, .separator,
        .output false, .finish, .blank] :=
  G1OutputKernelProbes.literal_frames_false

theorem check_literal_frames_true :
    g1OutputFrames req true =
      [.bof, .tag, .tag, .argSep, .argSep, .separator,
        .output true, .finish, .blank] :=
  G1OutputKernelProbes.literal_frames_true

theorem check_literal_steps :
    g1OutputKernelSteps req = 33 :=
  G1OutputKernelProbes.literal_steps

theorem check_literal_false_run :
    TM.runConfig (M := G1M) (g1OutputStartConfig req false) 33 =
      g1OutputDoneConfig req false :=
  G1OutputKernelProbes.literal_false_run

theorem check_literal_true_run :
    TM.runConfig (M := G1M) (g1OutputStartConfig req true) 33 =
      g1OutputDoneConfig req true :=
  G1OutputKernelProbes.literal_true_run

theorem check_literal_false_tape :
    (TM.runConfig (M := G1M) (g1OutputStartConfig req false) 33).tape =
      g1ListTape
        ([G1Frame.bof, .tag, .tag, .argSep, .argSep, .separator,
          .output false, .finish, .blank].flatMap G1Frame.bits) :=
  G1OutputKernelProbes.literal_false_tape

theorem check_literal_true_tape :
    (TM.runConfig (M := G1M) (g1OutputStartConfig req true) 33).tape =
      g1ListTape
        ([G1Frame.bof, .tag, .tag, .argSep, .argSep, .separator,
          .output true, .finish, .blank].flatMap G1Frame.bits) :=
  G1OutputKernelProbes.literal_true_tape

end Pnp3.Tests.TMGateOneOutputKernelSurface
