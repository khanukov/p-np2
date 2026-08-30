import Complexity.TMVerifier.TuringToolkit.GateOneARepair

/-!
# S8b live operand-A repair surface (2026-08-30)

Definitions are checked only.  Every public S8b theorem has one exact named
wrapper; there are no anonymous examples and no result/combine execution.
-/

namespace Pnp3.Tests.TMGateOneARepairSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open G1ARepairExamples

set_option maxRecDepth 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

#check @g1ARepairSeekState
#check @g1ARepairWriteState
#check @g1ARepairDoneState
#check @g1ARepairBackAdvance
#check @g1ARepairBackComplete
#check @G1ARepairControlMode
#check @G1ARepairScanMode
#check @G1ARepairStop
#check @g1ARepairStopState
#check @g1ARepairScanner
#check @g1ARepairCycle
#check @g1ARepairPassSteps
#check @g1ARepairLeft
#check @g1ARepairMid
#check @g1ARepairTail
#check @g1ARepairSteps
#check @g1ARepairEntryConfig
#check @g1ARepairDoneConfig
#check @g1ARepairLiveSteps
#check @g1AWalkRepairSteps
#check @g1AUnaryRepairSteps
#check @g1ABinaryRepairSteps
#check @g1ARepairLivePoly
#check @G1ARepairExamples.reqFalse
#check @G1ARepairExamples.reqTrue
#check @G1ARepairExamples.reqZero
theorem check_G1ForwardMode_not_aRepair :
    ¬ G1ForwardMode .aRepairSeek ∧ ¬ G1ForwardMode .aRepairWrite ∧
      ¬ G1ForwardMode .aRepairBack ∧ ¬ G1ForwardMode .aRepairHop ∧
      ¬ G1ForwardMode .aRepairDone := by
  apply G1ForwardMode.not_aRepair
theorem check_g1ARepairBackAdvance_of_skip {f : G1Frame} (h : G1RepairSkip f) :
    g1ARepairBackAdvance f = .aRepairSeek := by
  apply g1ARepairBackAdvance_of_skip <;> assumption
theorem check_g1ARepairBackComplete_some {b0 b1 b2 b3 : Bool} {f : G1Frame}
    (h : decodeG1Frame? [b0, b1, b2, b3] = some f) :
    g1ARepairBackComplete b0 b1 b2 b3 = g1ARepairBackAdvance f := by
  apply g1ARepairBackComplete_some <;> assumption
theorem check_g1ARepairBackComplete_none {b0 b1 b2 b3 : Bool}
    (h : decodeG1Frame? [b0, b1, b2, b3] = none) :
    g1ARepairBackComplete b0 b1 b2 b3 = .reject := by
  apply g1ARepairBackComplete_none <;> assumption
theorem check_g1ARepairBackComplete_reserved :
    g1ARepairBackComplete true true false true = .reject ∧
      g1ARepairBackComplete true true true false = .reject ∧
      g1ARepairBackComplete true true true true = .reject := by
  apply g1ARepairBackComplete_reserved <;> assumption
theorem check_g1ARepairBackComplete_forbidden :
    g1ARepairBackComplete false false false false = .reject ∧
      g1ARepairBackComplete false true true true = .reject := by
  apply g1ARepairBackComplete_forbidden <;> assumption
theorem check_g1Advance_aRepair_predecessor_closure
    (mode : G1Mode) (frame : G1Frame) :
    G1ARepairControlMode (g1Advance mode frame) → G1ARepairControlMode mode := by
  apply g1Advance_aRepair_predecessor_closure <;> assumption
theorem check_g1Complete_aRepair_predecessor_closure
    (mode : G1Mode) (b0 b1 b2 b3 : Bool) :
    G1ARepairControlMode (g1Complete mode b0 b1 b2 b3) →
      G1ARepairControlMode mode := by
  apply g1Complete_aRepair_predecessor_closure <;> assumption
theorem check_g1ARepairStart_not_control :
    ¬ G1ARepairControlMode .aRepairStart := by
  apply g1ARepairStart_not_control <;> assumption
theorem check_g1Transition_aRepairSeek_p3 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairSeek .p3 b0 b1 b2 ctx) scan =
      (0, g1State .aRepairSeek .p2 false false scan ctx, scan, .left) := by
  apply g1Transition_aRepairSeek_p3 <;> assumption
theorem check_g1Transition_aRepairSeek_p2 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairSeek .p2 b0 b1 b2 ctx) scan =
      (0, g1State .aRepairSeek .p1 false scan b2 ctx, scan, .left) := by
  apply g1Transition_aRepairSeek_p2 <;> assumption
theorem check_g1Transition_aRepairSeek_p1 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairSeek .p1 b0 b1 b2 ctx) scan =
      (0, g1State .aRepairSeek .p0 scan b1 b2 ctx, scan, .left) := by
  apply g1Transition_aRepairSeek_p1 <;> assumption
theorem check_g1Transition_aRepairSeek_p0_spent (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (h : decodeG1Frame? [scan, b0, b1, b2] = some .spent) :
    g1Transition phase (g1State .aRepairSeek .p0 b0 b1 b2 ctx) scan =
      (0, g1ARepairWriteState ctx, scan, .stay) := by
  apply g1Transition_aRepairSeek_p0_spent <;> assumption
theorem check_g1Transition_aRepairSeek_p0_bof (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (h : decodeG1Frame? [scan, b0, b1, b2] = some .bof) :
    g1Transition phase (g1State .aRepairSeek .p0 b0 b1 b2 ctx) scan =
      (0, g1ARepairDoneState ctx, scan, .stay) := by
  apply g1Transition_aRepairSeek_p0_bof <;> assumption
theorem check_g1Transition_aRepairSeek_p0_skip (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx) (frame : G1Frame)
    (hdec : decodeG1Frame? [scan, b0, b1, b2] = some frame)
    (hskip : G1RepairSkip frame) :
    g1Transition phase (g1State .aRepairSeek .p0 b0 b1 b2 ctx) scan =
      (0, g1ARepairSeekState ctx, scan, .left) := by
  apply g1Transition_aRepairSeek_p0_skip <;> assumption
theorem check_g1Transition_aRepairSeek_p0_bad (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (h : g1ARepairBackComplete scan b0 b1 b2 = .reject) :
    g1Transition phase (g1State .aRepairSeek .p0 b0 b1 b2 ctx) scan =
      (0, g1RejectState, scan, .stay) := by
  apply g1Transition_aRepairSeek_p0_bad <;> assumption
theorem check_g1Transition_aRepairSeek_p0_reserved_bad (phase : Fin 1)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairSeek .p0 true false true ctx) true =
        (0, g1RejectState, true, .stay) ∧
      g1Transition phase (g1State .aRepairSeek .p0 true true false ctx) true =
        (0, g1RejectState, true, .stay) ∧
      g1Transition phase (g1State .aRepairSeek .p0 true true true ctx) true =
        (0, g1RejectState, true, .stay) := by
  apply g1Transition_aRepairSeek_p0_reserved_bad <;> assumption
theorem check_g1Transition_aRepairWrite (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairWrite position b0 b1 b2 ctx) scan =
      (0, match position with
          | .p0 => g1State .aRepairWrite .p1 false false false ctx
          | .p1 => g1State .aRepairWrite .p2 false false false ctx
          | .p2 => g1State .aRepairWrite .p3 false false false ctx
          | .p3 => g1State .aRepairBack .p0 false false false ctx,
        match position with
          | .p0 | .p1 => false
          | .p2 | .p3 => true,
        .right) := by
  apply g1Transition_aRepairWrite <;> assumption
theorem check_g1Transition_aRepairBack (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairBack position b0 b1 b2 ctx) scan =
      (0, match position with
          | .p0 => g1State .aRepairBack .p1 false false false ctx
          | .p1 => g1State .aRepairBack .p2 false false false ctx
          | .p2 => g1State .aRepairBack .p3 false false false ctx
          | .p3 => g1State .aRepairHop .p0 false false false ctx,
        scan, .left) := by
  apply g1Transition_aRepairBack <;> assumption
theorem check_g1Transition_aRepairHop (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairHop position b0 b1 b2 ctx) scan =
      (0, g1ARepairSeekState ctx, scan, .left) := by
  apply g1Transition_aRepairHop <;> assumption
theorem check_g1Transition_aRepairDone_idle (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairDone position b0 b1 b2 ctx) scan =
      (0, g1ARepairDoneState ctx, scan, .stay) := by
  apply g1Transition_aRepairDone_idle <;> assumption
theorem check_g1Transition_aRepair_entry_closure (phase : Fin 1) (s : G1State)
    (scan : Bool)
    (h : G1ARepairControlMode (g1Transition phase s scan).2.1.mode) :
    G1ARepairControlMode s.mode ∨ s.mode = .aRepairStart := by
  apply g1Transition_aRepair_entry_closure <;> assumption
theorem check_g1Transition_aRepair_unique_external_door (phase : Fin 1)
    (s : G1State) (scan : Bool)
    (hnext : G1ARepairControlMode (g1Transition phase s scan).2.1.mode)
    (hprev : ¬ G1ARepairControlMode s.mode) : s.mode = .aRepairStart := by
  apply g1Transition_aRepair_unique_external_door <;> assumption
theorem check_g1Transition_aRepairStart_entry (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    G1ARepairControlMode
      (g1Transition phase
        (g1State .aRepairStart position b0 b1 b2 ctx) scan).2.1.mode := by
  apply g1Transition_aRepairStart_entry <;> assumption
theorem check_g1Transition_aRepair_external_entry_iff (phase : Fin 1)
    (s : G1State) (scan : Bool) (hprev : ¬ G1ARepairControlMode s.mode) :
    G1ARepairControlMode (g1Transition phase s scan).2.1.mode ↔
      s.mode = .aRepairStart := by
  apply g1Transition_aRepair_external_entry_iff <;> assumption
theorem check_G1ARepairScanMode_eq {m : G1Mode} (h : G1ARepairScanMode m) :
    m = .aRepairSeek := by
  apply G1ARepairScanMode.eq <;> assumption
theorem check_g1ARepairStopState_write (ctx : G1Ctx) :
    g1ARepairStopState .aRepairWrite ctx = g1ARepairWriteState ctx := by
  apply g1ARepairStopState_write <;> assumption
theorem check_g1ARepairStopState_done (ctx : G1Ctx) :
    g1ARepairStopState .aRepairDone ctx = g1ARepairDoneState ctx := by
  apply g1ARepairStopState_done <;> assumption
theorem check_g1ARepairStopState_reject (ctx : G1Ctx) :
    g1ARepairStopState .reject ctx = g1RejectState := by
  apply g1ARepairStopState_reject <;> assumption
theorem check_g1ARepairScanner_machine : g1ARepairScanner.machine = G1M := by
  apply g1ARepairScanner_machine <;> assumption
theorem check_g1CS_aRepair_cycle_onList (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
          .aRepairSeek .p3 false false false ctx) 13 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx := by
  apply g1CS_aRepair_cycle_onList <;> assumption
theorem check_g1CS_aRepair_seek_and_repair (n : Nat)
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hpre : 0 < pre.length) (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.spent :: skipped ++ suffix).flatMap
            G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
        (4 * skipped.length + 13) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap
          G1Frame.bits)) .aRepairSeek .p3 false false false ctx := by
  apply g1CS_aRepair_seek_and_repair <;> assumption
theorem check_g1CS_aRepair_frame_skip (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : G1RepairSkip f) (hbits : physicalBitsAt hsafe tape = f.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n (base - 1) (by omega) tape .aRepairSeek .p3
        false false false ctx := by
  apply g1CS_aRepair_frame_skip <;> assumption
theorem check_g1CS_aRepair_frame_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : f = .blank ∨ f = .cursor)
    (hbits : physicalBitsAt hsafe tape = f.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  apply g1CS_aRepair_frame_reject <;> assumption
theorem check_g1CS_aRepair_frame_reject_idle (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : f = .blank ∨ f = .cursor)
    (hbits : physicalBitsAt hsafe tape = f.bits) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) (4 + k) =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  apply g1CS_aRepair_frame_reject_idle <;> assumption
theorem check_g1CS_aRepair_reserved_1101_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  apply g1CS_aRepair_reserved_1101_reject <;> assumption
theorem check_g1CS_aRepair_reserved_1101_reject_idle (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) (4 + k) =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  apply g1CS_aRepair_reserved_1101_reject_idle <;> assumption
theorem check_g1CS_aRepair_scan_skip (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hsafe : 4 * (pre.length + skipped.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) - 1) (by omega)
          (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
          .aRepairSeek .p3 false false false ctx) (4 * skipped.length) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx := by
  apply g1CS_aRepair_scan_skip <;> assumption
theorem check_g1CS_aRepair_spent_run (n : Nat) (pre suffix : List G1Frame) (s : Nat)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * (pre.length + s) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + s) - 1) (by omega)
          (g1ListTape ((pre ++ List.replicate s G1Frame.spent ++
            suffix).flatMap G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
        (13 * s) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ List.replicate s G1Frame.index ++
          suffix).flatMap G1Frame.bits)) .aRepairSeek .p3 false false false ctx := by
  apply g1CS_aRepair_spent_run <;> assumption
theorem check_g1CS_aRepair_finish (n : Nat) (suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 3 (by omega)
          (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
          .aRepairSeek .p3 false false false ctx) 4 =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .aRepairDone .p0 false false false ctx := by
  apply g1CS_aRepair_finish <;> assumption
theorem check_g1CS_runConfig_aRepairDone_idle (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aRepairDone .p0 false false false ctx) k =
      g1AlignedConfig n h hh tape .aRepairDone .p0 false false false ctx := by
  apply g1CS_runConfig_aRepairDone_idle <;> assumption
theorem check_g1ARepairPassSteps_eq (a s m : Nat) :
    g1ARepairPassSteps a s m + 1 = g1RepairPassSteps a s m := by
  apply g1ARepairPassSteps_eq <;> assumption
theorem check_g1CS_aRepair_pass_exact (n s : Nat) (left mid tail : List G1Frame)
    (ctx : G1Ctx) (hleft : ∀ f ∈ left, G1RepairSkip f)
    (hmid : ∀ f ∈ mid, G1RepairSkip f)
    (hsafe : 4 * (1 + left.length + s + mid.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (1 + left.length + s + mid.length) - 1)
          (by omega) (g1ListTape (([G1Frame.bof] ++ left ++
            List.replicate s G1Frame.spent ++ mid ++ tail).flatMap G1Frame.bits))
          .aRepairSeek .p3 false false false ctx)
        (g1ARepairPassSteps left.length s mid.length) =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape (([G1Frame.bof] ++ left ++
          List.replicate s G1Frame.index ++ mid ++ tail).flatMap G1Frame.bits))
        .aRepairDone .p0 false false false ctx := by
  apply g1CS_aRepair_pass_exact <;> assumption
theorem check_g1ARepairLeft_length (r : G1Request) :
    (g1ARepairLeft r).length = r.tag.units + 1 := by
  apply g1ARepairLeft_length <;> assumption
theorem check_g1ARepairMid_length (r : G1Request) (hm : r.arg1 < r.vals.length) :
    (g1ARepairMid r).length = r.arg1 + r.arg2 + 3 := by
  apply g1ARepairMid_length <;> assumption
theorem check_g1ARepair_split_of (r : G1Request) (X : List G1Frame) :
    [G1Frame.bof] ++ g1ARepairLeft r ++ X ++ g1ARepairMid r ++
        g1ARepairTail r =
      g1TagRouteFrames r ++ X ++ [G1Frame.argSep] ++ g1AWalkOperand2 r ++
        [G1Frame.separator] ++ r.vals.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] := by
  apply g1ARepair_split_of <;> assumption
theorem check_g1AWalkDoneFrames_repair_split (r : G1Request) :
    g1AWalkDoneFrames r =
      [G1Frame.bof] ++ g1ARepairLeft r ++
        List.replicate r.arg1 G1Frame.spent ++ g1ARepairMid r ++
        g1ARepairTail r := by
  apply g1AWalkDoneFrames_repair_split <;> assumption
theorem check_g1ARepairLeft_skip (r : G1Request) :
    ∀ f ∈ g1ARepairLeft r, G1RepairSkip f := by
  apply g1ARepairLeft_skip <;> assumption
theorem check_g1ARepairMid_skip (r : G1Request) :
    ∀ f ∈ g1ARepairMid r, G1RepairSkip f := by
  apply g1ARepairMid_skip <;> assumption
theorem check_g1ARepairFrames_repaired (r : G1Request) :
    [G1Frame.bof] ++ g1ARepairLeft r ++ List.replicate r.arg1 G1Frame.index ++
        g1ARepairMid r ++ g1ARepairTail r =
      encodeG1Frames r ++ [G1Frame.blank] := by
  apply g1ARepairFrames_repaired <;> assumption
theorem check_g1ARepairCanonical_fields (r : G1Request) :
    encodeG1Frames r ++ [G1Frame.blank] =
      g1TagRouteFrames r ++ List.replicate r.arg1 G1Frame.index ++
        [G1Frame.argSep] ++ g1AWalkOperand2 r ++ [G1Frame.separator] ++
        r.vals.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] := by
  apply g1ARepairCanonical_fields <;> assumption
theorem check_g1ARepairCanonical_count_spent (r : G1Request) :
    (encodeG1Frames r ++ [G1Frame.blank]).count G1Frame.spent = 0 := by
  apply g1ARepairCanonical_count_spent <;> assumption
theorem check_g1ARepairCanonical_count_cursor (r : G1Request) :
    (encodeG1Frames r ++ [G1Frame.blank]).count G1Frame.cursor = 0 := by
  apply g1ARepairCanonical_count_cursor <;> assumption
theorem check_g1ARepairCanonical_count_index (r : G1Request) :
    (encodeG1Frames r ++ [G1Frame.blank]).count G1Frame.index =
      r.arg1 + r.arg2 := by
  apply g1ARepairCanonical_count_index <;> assumption
theorem check_g1ARepairSteps_eq (r : G1Request) (hm : r.arg1 < r.vals.length) :
    g1ARepairSteps r =
      g1ARepairPassSteps (g1ARepairLeft r).length r.arg1
        (g1ARepairMid r).length := by
  apply g1ARepairSteps_eq <;> assumption
theorem check_g1CS_aRepair_canonical_exact (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
        (g1ARepairSteps r) = g1ARepairDoneConfig r b v := by
  apply g1CS_aRepair_canonical_exact <;> assumption
theorem check_g1CS_aRepair_canonical_head (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    ((TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).head : Nat) = 0 := by
  apply g1CS_aRepair_canonical_head <;> assumption
theorem check_g1CS_aRepair_canonical_tape (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).tape =
      g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits) := by
  apply g1CS_aRepair_canonical_tape <;> assumption
theorem check_g1CS_aRepair_canonical_state (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).state.snd =
      g1ARepairDoneState (g1AWalkCtx r b v) := by
  apply g1CS_aRepair_canonical_state <;> assumption
theorem check_g1CS_aRepair_canonical_res (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).state.snd.ctx.res = g1Residual r.tag b := by
  apply g1CS_aRepair_canonical_res <;> assumption
theorem check_g1CS_aRepair_canonical_vB (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).state.snd.ctx.vB = v := by
  apply g1CS_aRepair_canonical_vB <;> assumption
theorem check_g1ARepairLiveSteps_eq (r : G1Request) :
    g1ARepairLiveSteps r =
      4 * r.tag.units + 17 * r.arg1 + 4 * r.arg2 + 21 := by
  apply g1ARepairLiveSteps_eq
theorem check_g1CS_aRepair_activation_exact (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    TM.runConfig (M := G1M) (g1AWalkRepairStartConfig r b v hm hv) 1 =
      g1ARepairEntryConfig r b v hm hv := by
  apply g1CS_aRepair_activation_exact <;> assumption
theorem check_g1CS_aRepair_live_exact (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    TM.runConfig (M := G1M) (g1AWalkRepairStartConfig r b v hm hv)
        (g1ARepairLiveSteps r) = g1ARepairDoneConfig r b v := by
  apply g1CS_aRepair_live_exact <;> assumption
theorem check_g1CS_aRepair_live_done_stable (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) (k : Nat) :
    TM.runConfig (M := G1M) (g1AWalkRepairStartConfig r b v hm hv)
        (g1ARepairLiveSteps r + k) = g1ARepairDoneConfig r b v := by
  apply g1CS_aRepair_live_done_stable <;> assumption
theorem check_g1CS_aRepair_live_endpoint (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    let out := TM.runConfig (M := G1M)
      (g1AWalkRepairStartConfig r b v hm hv) (g1ARepairLiveSteps r)
    out.tape =
        g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap
          G1Frame.bits) ∧
      (out.head : Nat) = 0 ∧
      out.state.snd = g1ARepairDoneState (g1AWalkCtx r b v) ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v ∧
      (encodeG1Frames r ++ [G1Frame.blank]).count .spent = 0 ∧
      (encodeG1Frames r ++ [G1Frame.blank]).count .cursor = 0 ∧
      out.state.snd.mode = .aRepairDone ∧
      out.state.snd.mode ≠ .readAStart ∧
      out.state.snd.mode ≠ .combineStart ∧
      out.state.snd.mode ≠ .accept ∧ out.state.snd.mode ≠ .reject ∧
      out.state.snd.mode ≠ .bOOB := by
  apply g1CS_aRepair_live_endpoint <;> assumption
theorem check_g1AWalkRepairSteps_eq (r : G1Request) :
    g1AWalkRepairSteps r =
      8 * r.arg1 ^ 2 + (8 * r.arg2 + 70) * r.arg1 +
        4 * r.tag.units + 12 * r.arg2 + 57 := by
  apply g1AWalkRepairSteps_eq
theorem check_g1CS_aWalk_repair_driver_exact (r : G1Request) (b : Bool)
    (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega))) (g1AWalkRepairSteps r) =
      g1ARepairDoneConfig r b (v r.arg1) := by
  apply g1CS_aWalk_repair_driver_exact <;> assumption
theorem check_g1CS_aRepair_unary_initial_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (rest : List Bool) (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryRepairSteps r) =
      g1ARepairDoneConfig r false (v r.arg1) := by
  apply g1CS_aRepair_unary_initial_exact <;> assumption
theorem check_g1CS_aRepair_binary_initial_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (bB : Bool)
    (hB : r.vals[r.arg2]? = some bB) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (rest : List Bool) (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryRepairSteps r) =
      g1ARepairDoneConfig r bB (v r.arg1) := by
  apply g1CS_aRepair_binary_initial_exact <;> assumption
theorem check_g1CS_aRepair_unary_arg1_zero_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (hzero : r.arg1 = 0) (v : Bool) (rest : List Bool)
    (hvals : r.vals = v :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryRepairSteps r) = g1ARepairDoneConfig r false v := by
  apply g1CS_aRepair_unary_arg1_zero_exact <;> assumption
theorem check_g1AWalkRepairSteps_le_poly (r : G1Request) :
    g1AWalkRepairSteps r ≤ g1ARepairLivePoly r := by
  apply g1AWalkRepairSteps_le_poly
theorem check_g1AUnaryRepairSteps_le_poly (r : G1Request) :
    g1AUnaryRepairSteps r ≤ g1ARepairLivePoly r := by
  apply g1AUnaryRepairSteps_le_poly
theorem check_g1ABinaryRepairSteps_le_poly (r : G1Request) :
    g1ABinaryRepairSteps r ≤ g1ARepairLivePoly r := by
  apply g1ABinaryRepairSteps_le_poly
theorem check_g1ARepairLivePoly_le_clock (r : G1Request) :
    g1ARepairLivePoly r ≤ g1Clock (encodeG1 r).length := by
  apply g1ARepairLivePoly_le_clock
theorem check_g1AUnaryRepairSteps_le_clock (r : G1Request) :
    g1AUnaryRepairSteps r ≤ g1Clock (encodeG1 r).length := by
  apply g1AUnaryRepairSteps_le_clock
theorem check_g1ABinaryRepairSteps_le_clock (r : G1Request) :
    g1ABinaryRepairSteps r ≤ g1Clock (encodeG1 r).length := by
  apply g1ABinaryRepairSteps_le_clock
theorem check_g1CS_aWalk_oob_driver_stable (r : G1Request) (b : Bool)
    (t : Nat) (ht1 : t < r.arg1) (hlast : t + 1 = r.vals.length)
    (v : Nat → Bool) (hv : ∀ j, j ≤ t → r.vals[j]? = some (v j))
    (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega)))
        (g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t + k) =
      g1AWalkOOBConfig r b t ht1 (by omega) (v t)
        (hv t (Nat.le_refl _)) := by
  apply g1CS_aWalk_oob_driver_stable <;> assumption
theorem check_g1AWalkOOBConfig_ne_aRepairDone (r : G1Request) (b v w : Bool)
    (t : Nat) (ht1 : t < r.arg1) (ht : t < r.vals.length)
    (hv : r.vals[t]? = some v) :
    g1AWalkOOBConfig r b t ht1 ht v hv ≠ g1ARepairDoneConfig r b w := by
  apply g1AWalkOOBConfig_ne_aRepairDone <;> assumption
theorem check_literal_steps : g1ARepairSteps reqFalse = 58 ∧
    g1ARepairSteps reqTrue = 58 ∧
    g1ARepairSteps reqZero = 24 := by
  apply G1ARepairExamples.literal_steps <;> assumption
theorem check_literal_false_repair_exact :
    TM.runConfig (M := G1M)
        (g1ARepairEntryConfig reqFalse false false (by decide) (by decide)) 58 =
      g1ARepairDoneConfig reqFalse false false := by
  apply G1ARepairExamples.literal_false_repair_exact <;> assumption
theorem check_literal_true_repair_exact :
    TM.runConfig (M := G1M)
        (g1ARepairEntryConfig reqTrue true true (by decide) (by decide)) 58 =
      g1ARepairDoneConfig reqTrue true true := by
  apply G1ARepairExamples.literal_true_repair_exact <;> assumption
theorem check_literal_zero_arg1_repair_exact :
    TM.runConfig (M := G1M)
        (g1ARepairEntryConfig reqZero false true (by decide) (by decide)) 24 =
      g1ARepairDoneConfig reqZero false true := by
  apply G1ARepairExamples.literal_zero_arg1_repair_exact <;> assumption
theorem check_literal_live_steps : g1AUnaryRepairSteps reqFalse = 404 ∧
    g1AUnaryRepairSteps reqTrue = 404 ∧
    g1AUnaryRepairSteps reqZero = 192 := by
  apply G1ARepairExamples.literal_live_steps
theorem check_literal_false_live_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqFalse))) 404 =
      g1ARepairDoneConfig reqFalse false false := by
  apply G1ARepairExamples.literal_false_live_exact
theorem check_literal_true_live_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqTrue))) 404 =
      g1ARepairDoneConfig reqTrue false true := by
  apply G1ARepairExamples.literal_true_live_exact
theorem check_literal_zero_live_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqZero))) 192 =
      g1ARepairDoneConfig reqZero false true := by
  apply G1ARepairExamples.literal_zero_live_exact
theorem check_literal_false_endpoint_word :
    encodeG1Frames reqFalse ++ [G1Frame.blank] =
      [.bof, .tag, .argSep, .index, .index, .argSep, .separator,
        .data true, .data true, .data false, .output false, .finish, .blank] := by
  apply G1ARepairExamples.literal_false_endpoint_word <;> assumption
theorem check_literal_true_endpoint_word :
    encodeG1Frames reqTrue ++ [G1Frame.blank] =
      [.bof, .tag, .argSep, .index, .index, .argSep, .separator,
        .data false, .data false, .data true, .output false, .finish, .blank] := by
  apply G1ARepairExamples.literal_true_endpoint_word <;> assumption
theorem check_literal_zero_endpoint_word :
    encodeG1Frames reqZero ++ [G1Frame.blank] =
      [.bof, .tag, .argSep, .argSep, .separator, .data true,
        .output false, .finish, .blank] := by
  apply G1ARepairExamples.literal_zero_endpoint_word <;> assumption

end Pnp3.Tests.TMGateOneARepairSurface
