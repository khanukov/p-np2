import Complexity.TMVerifier.TuringToolkit.GateOneAWalkKernel

/-!
# S3b2a/S3b2b dormant operand-A walk surface

Dated 2026-08-29.  The normal/terminal runs remain caller-supplied; S4 stops at
their `aSeekOut .p3` entry boundary, terminal cleanup stops at stationary
`aRepairStart`, and no repair executes.
-/

namespace Pnp3.Tests.TMGateOneAWalkSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! Declaration probes are definitions only. -/

#check @G1AWalkMode
#check @g1ASeekOutState
#check @g1ASeekInState
#check @g1ADecState
#check @g1AFwdState
#check @g1AExhState
#check @g1ARestoreMode
#check @g1AFinMode
#check @g1ARepairStartState
#check @g1ASeekRevAdvance
#check @g1ASeekRevComplete
#check @G1ASeekOutSkip
#check @G1ASeekInSkip
#check @G1AWalkSkip
#check @G1ASeekStop
#check @G1ASeekMode
#check @g1ASeekStopState
#check @g1AWalkScanner
#check @g1ADecWriter
#check @g1ARestoreWriter
#check @g1AFinWriter

/-! Every new public source theorem has an exact named direct-root wrapper. -/

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]
variable {F Mode Aux : Type v}

theorem check_revWindowStop
    (K : ReverseFrameScanner S F Mode Aux) (n base : Nat)
    (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (a : Aux)
    (hm : K.Reverse m)
    (hstop : K.Stop (K.revComplete m (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩))) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (base + 3) (by omega) tape m a) 4 =
      K.alignedConfigQ n base (by omega) tape
        (K.stopState (K.revComplete m (tape ⟨base, by omega⟩)
          (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
          (tape ⟨base + 3, by omega⟩)) a) :=
  K.revWindowStop n base hsafe tape m a hm hstop

theorem check_g1Advance_aWalk_dormant (mode : G1Mode) (frame : G1Frame) :
    G1AWalkMode (g1Advance mode frame) → G1AWalkMode mode :=
  g1Advance_aWalk_dormant mode frame

theorem check_g1Complete_aWalk_dormant
    (mode : G1Mode) (b0 b1 b2 b3 : Bool) :
    G1AWalkMode (g1Complete mode b0 b1 b2 b3) → G1AWalkMode mode :=
  g1Complete_aWalk_dormant mode b0 b1 b2 b3

theorem check_g1Complete_aWalk_reserved (mode : G1Mode) :
    g1Complete mode true true false true = .reject ∧
      g1Complete mode true true true false = .reject ∧
      g1Complete mode true true true true = .reject :=
  g1Complete_aWalk_reserved mode

theorem check_g1Advance_aFwd_cursor :
    g1Advance .aFwd .cursor = .aTurn :=
  g1Advance_aFwd_cursor

theorem check_g1ASeekRevComplete_some
    {mode : G1Mode} {b0 b1 b2 b3 : Bool} {frame : G1Frame}
    (h : decodeG1Frame? [b0, b1, b2, b3] = some frame) :
    g1ASeekRevComplete mode b0 b1 b2 b3 = g1ASeekRevAdvance mode frame :=
  g1ASeekRevComplete_some h

theorem check_g1ASeekRevComplete_none
    {mode : G1Mode} {b0 b1 b2 b3 : Bool}
    (h : decodeG1Frame? [b0, b1, b2, b3] = none) :
    g1ASeekRevComplete mode b0 b1 b2 b3 = .reject :=
  g1ASeekRevComplete_none h

theorem check_g1ASeekRevComplete_reserved (mode : G1Mode) :
    g1ASeekRevComplete mode true true false true = .reject ∧
      g1ASeekRevComplete mode true true true false = .reject ∧
      g1ASeekRevComplete mode true true true true = .reject :=
  g1ASeekRevComplete_reserved mode

theorem check_g1ASeekRevAdvance_blank_cursor :
    g1ASeekRevAdvance .aSeekOut .blank = .reject ∧
      g1ASeekRevAdvance .aSeekOut .cursor = .reject ∧
      g1ASeekRevAdvance .aSeekIn .blank = .reject ∧
      g1ASeekRevAdvance .aSeekIn .cursor = .reject :=
  g1ASeekRevAdvance_blank_cursor

theorem check_g1AFinMode_ne_restore (b b' : Bool) :
    g1AFinMode b ≠ g1ARestoreMode b' :=
  g1AFinMode_ne_restore b b'

theorem check_g1Advance_aTerminal_rows :
    g1Advance .aExh .argSep = .aRet ∧
      g1Advance .aRet .spent = .aRet ∧
      g1Advance .aRet .argSep = .aRet ∧
      g1Advance .aRet .index = .aRet ∧
      g1Advance .aRet .separator = .aRet ∧
      g1Advance .aRet (.data false) = .aRet ∧
      g1Advance .aRet (.data true) = .aRet ∧
      g1Advance .aRet .cursor = .aTurnFin :=
  g1Advance_aTerminal_rows

theorem check_g1Transition_aRepairStart_idle (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aRepairStart position b0 b1 b2 ctx) scan =
      (0, g1ARepairStartState ctx, scan, .stay) :=
  g1Transition_aRepairStart_idle phase position b0 b1 b2 scan ctx

theorem check_g1Transition_aSeekOut_p3
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aSeekOut .p3 b0 b1 b2 ctx) scan =
      (0, g1State .aSeekOut .p2 false false scan ctx, scan, .left) :=
  g1Transition_aSeekOut_p3 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aSeekOut_p2
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aSeekOut .p2 b0 b1 b2 ctx) scan =
      (0, g1State .aSeekOut .p1 false scan b2 ctx, scan, .left) :=
  g1Transition_aSeekOut_p2 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aSeekOut_p1
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aSeekOut .p1 b0 b1 b2 ctx) scan =
      (0, g1State .aSeekOut .p0 scan b1 b2 ctx, scan, .left) :=
  g1Transition_aSeekOut_p1 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aSeekOut_p0_seekIn (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hnext : g1ASeekRevComplete .aSeekOut scan b0 b1 b2 = .aSeekIn) :
    g1Transition phase (g1State .aSeekOut .p0 b0 b1 b2 ctx) scan =
      (0, g1ASeekInState ctx, scan, .left) :=
  g1Transition_aSeekOut_p0_seekIn phase b0 b1 b2 scan ctx hnext

theorem check_g1Transition_aSeekOut_p0_argSep (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (heq : decodeG1Frame? [scan, b0, b1, b2] = some .argSep) :
    g1Transition phase (g1State .aSeekOut .p0 b0 b1 b2 ctx) scan =
      (0, g1ASeekInState ctx, scan, .left) :=
  g1Transition_aSeekOut_p0_argSep phase b0 b1 b2 scan ctx heq

theorem check_g1Transition_aSeekOut_p0_other (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hnext : g1ASeekRevComplete .aSeekOut scan b0 b1 b2 = .aSeekOut) :
    g1Transition phase (g1State .aSeekOut .p0 b0 b1 b2 ctx) scan =
      (0, g1ASeekOutState ctx, scan, .left) :=
  g1Transition_aSeekOut_p0_other phase b0 b1 b2 scan ctx hnext

theorem check_g1Transition_aSeekOut_p0_bad (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hbad : g1ASeekRevComplete .aSeekOut scan b0 b1 b2 = .reject) :
    g1Transition phase (g1State .aSeekOut .p0 b0 b1 b2 ctx) scan =
      (0, g1RejectState, scan, .stay) :=
  g1Transition_aSeekOut_p0_bad phase b0 b1 b2 scan ctx hbad

theorem check_g1Transition_aSeekOut_p0_none_bad (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hdec : decodeG1Frame? [scan, b0, b1, b2] = none) :
    g1Transition phase (g1State .aSeekOut .p0 b0 b1 b2 ctx) scan =
      (0, g1RejectState, scan, .stay) :=
  g1Transition_aSeekOut_p0_none_bad phase b0 b1 b2 scan ctx hdec

theorem check_g1Transition_aSeekIn_p3
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aSeekIn .p3 b0 b1 b2 ctx) scan =
      (0, g1State .aSeekIn .p2 false false scan ctx, scan, .left) :=
  g1Transition_aSeekIn_p3 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aSeekIn_p2
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aSeekIn .p2 b0 b1 b2 ctx) scan =
      (0, g1State .aSeekIn .p1 false scan b2 ctx, scan, .left) :=
  g1Transition_aSeekIn_p2 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aSeekIn_p1
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aSeekIn .p1 b0 b1 b2 ctx) scan =
      (0, g1State .aSeekIn .p0 scan b1 b2 ctx, scan, .left) :=
  g1Transition_aSeekIn_p1 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aSeekIn_p0_dec (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hnext : g1ASeekRevComplete .aSeekIn scan b0 b1 b2 = .aDec) :
    g1Transition phase (g1State .aSeekIn .p0 b0 b1 b2 ctx) scan =
      (0, g1ADecState ctx, scan, .stay) :=
  g1Transition_aSeekIn_p0_dec phase b0 b1 b2 scan ctx hnext

theorem check_g1Transition_aSeekIn_p0_exh (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hnext : g1ASeekRevComplete .aSeekIn scan b0 b1 b2 = .aExh) :
    g1Transition phase (g1State .aSeekIn .p0 b0 b1 b2 ctx) scan =
      (0, g1AExhState ctx, scan, .stay) :=
  g1Transition_aSeekIn_p0_exh phase b0 b1 b2 scan ctx hnext

theorem check_g1Transition_aSeekIn_p0_index (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (heq : decodeG1Frame? [scan, b0, b1, b2] = some .index) :
    g1Transition phase (g1State .aSeekIn .p0 b0 b1 b2 ctx) scan =
      (0, g1ADecState ctx, scan, .stay) :=
  g1Transition_aSeekIn_p0_index phase b0 b1 b2 scan ctx heq

theorem check_g1Transition_aSeekIn_p0_argSep (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (heq : decodeG1Frame? [scan, b0, b1, b2] = some .argSep) :
    g1Transition phase (g1State .aSeekIn .p0 b0 b1 b2 ctx) scan =
      (0, g1AExhState ctx, scan, .stay) :=
  g1Transition_aSeekIn_p0_argSep phase b0 b1 b2 scan ctx heq

theorem check_g1Transition_aSeekIn_p0_other (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hnext : g1ASeekRevComplete .aSeekIn scan b0 b1 b2 = .aSeekIn) :
    g1Transition phase (g1State .aSeekIn .p0 b0 b1 b2 ctx) scan =
      (0, g1ASeekInState ctx, scan, .left) :=
  g1Transition_aSeekIn_p0_other phase b0 b1 b2 scan ctx hnext

theorem check_g1Transition_aSeekIn_p0_bad (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hbad : g1ASeekRevComplete .aSeekIn scan b0 b1 b2 = .reject) :
    g1Transition phase (g1State .aSeekIn .p0 b0 b1 b2 ctx) scan =
      (0, g1RejectState, scan, .stay) :=
  g1Transition_aSeekIn_p0_bad phase b0 b1 b2 scan ctx hbad

theorem check_g1Transition_aSeekIn_p0_none_bad (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hdec : decodeG1Frame? [scan, b0, b1, b2] = none) :
    g1Transition phase (g1State .aSeekIn .p0 b0 b1 b2 ctx) scan =
      (0, g1RejectState, scan, .stay) :=
  g1Transition_aSeekIn_p0_none_bad phase b0 b1 b2 scan ctx hdec

theorem check_g1Transition_aSeek_p0_reserved_bad
    (phase : Fin 1) (ctx : G1Ctx) :
    (g1Transition phase (g1State .aSeekOut .p0 true false true ctx) true =
        (0, g1RejectState, true, .stay) ∧
      g1Transition phase (g1State .aSeekIn .p0 true false true ctx) true =
        (0, g1RejectState, true, .stay)) ∧
    (g1Transition phase (g1State .aSeekOut .p0 true true false ctx) true =
        (0, g1RejectState, true, .stay) ∧
      g1Transition phase (g1State .aSeekIn .p0 true true false ctx) true =
        (0, g1RejectState, true, .stay)) ∧
    (g1Transition phase (g1State .aSeekOut .p0 true true true ctx) true =
        (0, g1RejectState, true, .stay) ∧
      g1Transition phase (g1State .aSeekIn .p0 true true true ctx) true =
        (0, g1RejectState, true, .stay)) :=
  g1Transition_aSeek_p0_reserved_bad phase ctx

theorem check_g1Transition_aDec (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aDec position b0 b1 b2 ctx) scan =
      (0, match position with
          | .p0 => g1State .aDec .p1 false false false ctx
          | .p1 => g1State .aDec .p2 false false false ctx
          | .p2 => g1State .aDec .p3 false false false ctx
          | .p3 => g1AFwdState ctx,
        match position with | .p0 | .p1 => true | .p2 | .p3 => false,
        .right) :=
  g1Transition_aDec phase position b0 b1 b2 scan ctx

theorem check_g1Transition_aTurn (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aTurn position b0 b1 b2 ctx) scan =
      (0, match position with
          | .p0 => g1State .aTurn .p1 false false false ctx
          | .p1 => g1State .aTurn .p2 false false false ctx
          | .p2 => g1State .aTurn .p3 false false false ctx
          | .p3 => g1State (g1ARestoreMode ctx.vB) .p0 false false false ctx,
        scan, .left) :=
  g1Transition_aTurn phase position b0 b1 b2 scan ctx

theorem check_g1Transition_aRestore (phase : Fin 1) (b : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1ARestoreMode b) position b0 b1 b2 ctx) scan =
      (0, match position with
          | .p0 => g1State (g1ARestoreMode b) .p1 false false false ctx
          | .p1 => g1State (g1ARestoreMode b) .p2 false false false ctx
          | .p2 => g1State (g1ARestoreMode b) .p3 false false false ctx
          | .p3 => g1AProbeState ctx,
        match position with | .p0 => false | .p1 => true | .p2 => b | .p3 => !b,
        .right) :=
  g1Transition_aRestore phase b position b0 b1 b2 scan ctx

theorem check_g1Transition_aTurnFin (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aTurnFin position b0 b1 b2 ctx) scan =
      (0, match position with
          | .p0 => g1State .aTurnFin .p1 false false false ctx
          | .p1 => g1State .aTurnFin .p2 false false false ctx
          | .p2 => g1State .aTurnFin .p3 false false false ctx
          | .p3 => g1State (g1AFinMode ctx.vB) .p0 false false false ctx,
        scan, .left) :=
  g1Transition_aTurnFin phase position b0 b1 b2 scan ctx

theorem check_g1Transition_aFin (phase : Fin 1) (b : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1AFinMode b) position b0 b1 b2 ctx) scan =
      (0, match position with
          | .p0 => g1State (g1AFinMode b) .p1 false false false ctx
          | .p1 => g1State (g1AFinMode b) .p2 false false false ctx
          | .p2 => g1State (g1AFinMode b) .p3 false false false ctx
          | .p3 => g1ARepairStartState ctx,
        match position with
          | .p0 => false
          | .p1 => true
          | .p2 => b
          | .p3 => !b,
        .right) :=
  g1Transition_aFin phase b position b0 b1 b2 scan ctx

theorem check_g1Transition_aWalk_entry_closure
    (phase : Fin 1) (s : G1State) (scan : Bool)
    (h : G1AWalkMode (g1Transition phase s scan).2.1.mode) :
    G1AWalkMode s.mode ∨ s.mode = .aInstallStart :=
  g1Transition_aWalk_entry_closure phase s scan h

theorem check_g1Advance_aFwd_of_skip {f : G1Frame} (h : G1AWalkSkip f) :
    g1Advance .aFwd f = .aFwd :=
  g1Advance_aFwd_of_skip h

theorem check_g1Advance_aRet_of_skip {f : G1Frame} (h : G1AWalkSkip f) :
    g1Advance .aRet f = .aRet :=
  g1Advance_aRet_of_skip h

theorem check_G1ASeekOutSkip_ne_argSep
    {f : G1Frame} (h : G1ASeekOutSkip f) :
    f ≠ .argSep :=
  G1ASeekOutSkip_ne_argSep h

theorem check_G1ASeekInSkip_ne_index
    {f : G1Frame} (h : G1ASeekInSkip f) :
    f ≠ .index :=
  G1ASeekInSkip_ne_index h

theorem check_G1ASeekInSkip_ne_argSep
    {f : G1Frame} (h : G1ASeekInSkip f) :
    f ≠ .argSep :=
  G1ASeekInSkip_ne_argSep h

theorem check_G1ASeekMode_eq {m : G1Mode} (h : G1ASeekMode m) :
    m = .aSeekOut ∨ m = .aSeekIn :=
  G1ASeekMode.eq h

theorem check_g1ASeekRevAdvance_out_of_skip {f : G1Frame}
    (h : G1ASeekOutSkip f) : g1ASeekRevAdvance .aSeekOut f = .aSeekOut :=
  g1ASeekRevAdvance_out_of_skip h

theorem check_g1ASeekRevAdvance_in_of_skip {f : G1Frame}
    (h : G1ASeekInSkip f) : g1ASeekRevAdvance .aSeekIn f = .aSeekIn :=
  g1ASeekRevAdvance_in_of_skip h

theorem check_g1CS_aWalk_reserved_1101_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode) (ctx : G1Ctx)
    (hmode : G1ASeekMode mode)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape mode .p3
          false false false ctx) 4 =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 :=
  g1CS_aWalk_reserved_1101_reject n base hsafe tape mode ctx hmode hbits

theorem check_g1CS_aWalk_reserved_1101_reject_idle (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode) (ctx : G1Ctx)
    (hmode : G1ASeekMode mode)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape mode .p3
          false false false ctx) (4 + k) =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 :=
  g1CS_aWalk_reserved_1101_reject_idle
    n base hsafe tape mode ctx hmode hbits k

theorem check_g1AWalkScanner_machine : g1AWalkScanner.machine = G1M :=
  g1AWalkScanner_machine

theorem check_g1CS_aWalk_seek_index
    (n : Nat) (pre inner outer suffix : List G1Frame)
    (ctx : G1Ctx) (houter : ∀ f ∈ outer, G1ASeekOutSkip f)
    (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hsafe : 4 * (pre.length + (inner.length + outer.length + 1)) + 4 <
      G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.index :: inner ++ G1Frame.argSep ::
            outer ++ suffix).flatMap G1Frame.bits))
          .aSeekOut .p3 false false false ctx)
        (4 * (inner.length + outer.length + 1) + 4) =
      g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: inner ++ G1Frame.argSep ::
          outer ++ suffix).flatMap G1Frame.bits))
        .aDec .p0 false false false ctx :=
  g1CS_aWalk_seek_index n pre inner outer suffix ctx houter hinner hsafe

theorem check_g1CS_aWalk_seek_exhaust (n : Nat)
    (pre inner outer suffix : List G1Frame) (ctx : G1Ctx)
    (houter : ∀ f ∈ outer, G1ASeekOutSkip f)
    (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hsafe : 4 * (pre.length + (inner.length + outer.length + 1)) + 4 <
      G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.argSep :: inner ++ G1Frame.argSep ::
            outer ++ suffix).flatMap G1Frame.bits))
          .aSeekOut .p3 false false false ctx)
        (4 * (inner.length + outer.length + 1) + 4) =
      g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.argSep :: inner ++ G1Frame.argSep ::
          outer ++ suffix).flatMap G1Frame.bits))
        .aExh .p0 false false false ctx :=
  g1CS_aWalk_seek_exhaust n pre inner outer suffix ctx houter hinner hsafe

theorem check_g1CS_aWalk_mark
    (n : Nat) (pre suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
        .aDec .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .aFwd .p0 false false false ctx :=
  g1CS_aWalk_mark n pre suffix ctx hsafe

theorem check_g1CS_aWalk_fwd_to_cursor
    (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1AWalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .aFwd .p0 false false false ctx) (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .aTurn .p0 false false false ctx :=
  g1CS_aWalk_fwd_to_cursor n pre skipped suffix ctx hskip hsafe

theorem check_g1CS_aWalk_turn
    (n k : Nat) (hsafe : k + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (k + 4) hsafe tape .aTurn .p0 false false false ctx) 4 =
      g1AlignedConfig n k (by omega) tape
        (g1ARestoreMode ctx.vB) .p0 false false false ctx :=
  g1CS_aWalk_turn n k hsafe tape ctx

theorem check_g1CS_aWalk_restore
    (n : Nat) (pre suffix : List G1Frame) (b : Bool)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        (g1ARestoreMode b) .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data b :: suffix).flatMap G1Frame.bits))
        .aProbe .p0 false false false ctx :=
  g1CS_aWalk_restore n pre suffix b ctx hsafe

theorem check_g1CS_aWalk_exh_to_cursor
    (n : Nat) (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1AWalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 2)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
            suffix).flatMap G1Frame.bits))
        .aExh .p0 false false false ctx) (4 * (skipped.length + 2)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 2))) hsafe
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
            suffix).flatMap G1Frame.bits))
        .aTurnFin .p0 false false false ctx :=
  g1CS_aWalk_exh_to_cursor n pre skipped suffix ctx hskip hsafe

theorem check_g1CS_aWalk_turn_fin
    (n k : Nat) (hsafe : k + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (k + 4) hsafe tape .aTurnFin .p0 false false false ctx)
        4 =
      g1AlignedConfig n k (by omega) tape
        (g1AFinMode ctx.vB) .p0 false false false ctx :=
  g1CS_aWalk_turn_fin n k hsafe tape ctx

theorem check_g1CS_aWalk_fin_restore
    (n : Nat) (pre suffix : List G1Frame) (b : Bool) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        (g1AFinMode b) .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data b :: suffix).flatMap G1Frame.bits))
        .aRepairStart .p0 false false false ctx :=
  g1CS_aWalk_fin_restore n pre suffix b ctx hsafe

theorem check_g1CS_aWalk_terminal_exact
    (n : Nat) (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1AWalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 2)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
            suffix).flatMap G1Frame.bits))
        .aExh .p0 false false false ctx) (4 * (skipped.length + 4)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 2))) hsafe
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.data ctx.vB ::
            suffix).flatMap G1Frame.bits))
        .aRepairStart .p0 false false false ctx :=
  g1CS_aWalk_terminal_exact n pre skipped suffix ctx hskip hsafe

theorem check_g1CS_runConfig_aRepairStart_idle
    (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aRepairStart .p0 false false false ctx) k =
      g1AlignedConfig n h hh tape .aRepairStart .p0 false false false ctx :=
  g1CS_runConfig_aRepairStart_idle n h hh tape ctx k

/-! Literal normal, terminal and malformed caller-supplied probes. -/

theorem literal_normal_mark (n : Nat) (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 0 (by omega)
          (g1ListTape ([G1Frame.index].flatMap G1Frame.bits))
          .aDec .p0 false false false g1Ctx0) 4 =
      g1AlignedConfig n 4 hsafe
        (g1ListTape ([G1Frame.spent].flatMap G1Frame.bits))
        .aFwd .p0 false false false g1Ctx0 := by
  simpa using g1CS_aWalk_mark n [] [] g1Ctx0 hsafe

theorem literal_normal_restore (n : Nat) (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 0 (by omega)
          (g1ListTape ([G1Frame.cursor].flatMap G1Frame.bits))
          .aRestoreTrue .p0 false false false g1Ctx0) 4 =
      g1AlignedConfig n 4 hsafe
        (g1ListTape ([G1Frame.data true].flatMap G1Frame.bits))
        .aProbe .p0 false false false g1Ctx0 := by
  simpa using g1CS_aWalk_restore n [] [] true g1Ctx0 hsafe

theorem literal_terminal_false (n : Nat) (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 0 (by omega)
          (g1ListTape ([G1Frame.cursor].flatMap G1Frame.bits))
          .aFinFalse .p0 false false false
          ((g1Ctx0.withRes .notA).withVB false)) 4 =
      g1AlignedConfig n 4 hsafe
        (g1ListTape ([G1Frame.data false].flatMap G1Frame.bits))
        .aRepairStart .p0 false false false
        ((g1Ctx0.withRes .notA).withVB false) := by
  simpa using g1CS_aWalk_fin_restore n [] [] false
    ((g1Ctx0.withRes .notA).withVB false) hsafe

theorem literal_terminal_true (n : Nat) (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 0 (by omega)
          (g1ListTape ([G1Frame.cursor].flatMap G1Frame.bits))
          .aFinTrue .p0 false false false
          ((g1Ctx0.withRes .notA).withVB true)) 4 =
      g1AlignedConfig n 4 hsafe
        (g1ListTape ([G1Frame.data true].flatMap G1Frame.bits))
        .aRepairStart .p0 false false false
        ((g1Ctx0.withRes .notA).withVB true) := by
  simpa using g1CS_aWalk_fin_restore n [] [] true
    ((g1Ctx0.withRes .notA).withVB true) hsafe

theorem literal_exhaustion_repair_boundary
    (n : Nat) (hsafe : 8 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 0 (by omega)
          (g1ListTape ([G1Frame.argSep, G1Frame.cursor].flatMap G1Frame.bits))
          .aExh .p0 false false false
          ((g1Ctx0.withRes .notA).withVB true)) 16 =
      g1AlignedConfig n 8 hsafe
        (g1ListTape ([G1Frame.argSep, G1Frame.data true].flatMap G1Frame.bits))
        .aRepairStart .p0 false false false
        ((g1Ctx0.withRes .notA).withVB true) := by
  simpa using g1CS_aWalk_terminal_exact n [] [] []
    ((g1Ctx0.withRes .notA).withVB true) (by simp) hsafe

theorem literal_malformed_reserved_row (phase : Fin 1) (ctx : G1Ctx) :
    g1Transition phase (g1State .aSeekOut .p0 true false true ctx) true =
      (0, g1RejectState, true, .stay) :=
  (g1Transition_aSeek_p0_reserved_bad phase ctx).1.1

theorem literal_malformed_reserved_run (n : Nat)
    (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 3 (by omega)
          (g1ListTape [true, true, false, true])
          .aSeekOut .p3 false false false g1Ctx0) 4 =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape [true, true, false, true])
        .reject .p0 false false false g1Ctx0 := by
  exact g1CS_aWalk_reserved_1101_reject n 0 hsafe _ .aSeekOut g1Ctx0 trivial rfl

theorem check_aInstallStart_live_entry (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .aInstallStart position b0 b1 b2 ctx) scan =
      (0, g1AInsSeekState ctx, scan, .stay) :=
  g1Transition_aInstallStart_live phase position b0 b1 b2 scan ctx

end Pnp3.Tests.TMGateOneAWalkSurface
