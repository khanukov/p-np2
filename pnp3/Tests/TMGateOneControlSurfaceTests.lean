import Complexity.TMVerifier.TuringToolkit.GateOneScanner

/-!
# G1 one-gate interpreter, fixed control layer: surface tests

Import-side type probes for the T2a control surface: the one fixed
zero-parameter program, the frame-level language its forward table decides,
the proved correspondence between that language and the pure parser, the named
noncanonical-rejection witnesses, and the program as a genuine instance of the
generic frame-scanner kernel.

This layer exposes frame-word/table correspondence and the generic kernel's
exact four-step and multi-frame `TM.runConfig` primitives.  It also pins the
fourteen transition tuples of the retired destructive index round
(`bRoundStart` bridge, `bWalk`, `bMark`, `bBack`, `bHop`) and the thirty-one
transition tuples of the cursor walk (the reverse seek `bSeek` with its three
outcomes, the `index ↦ spent` writer `bDec`, the two turns, the two
cursor-restore writers, the two **terminal** restore writers, the two latch
dispatches and the leftward cursor writer `bIns`).  It also pins the eleven
transition tuples of the **operand-2 repair sweep** (the reverse scan
`bRepairSeek` with its **four** outcomes — the `spent` write handoff, the `bof`
terminal handoff, a `G1RepairSkip` frame continuing the scan, and the `reject`
sink for every window it may not cross — the `spent ↦ index` writer
`bRepairWrite`, its back-walk `bRepairBack`, its hop `bRepairHop` and the anchor
dispatch `bRepairDone` into `readAStart`), together with its
reverse frame table `g1RepairBackAdvance`/`g1RepairBackComplete` and the literal
codewords that reject it — no *frame-table* row enters those five modes, and the
only row that does is the `readAResetStart` bridge
(`check_g1Transition_readAResetStart_bridge`), which is **not** idle any more.
The
five *forward* walk modes — `bInsSeek`, `bProbe2`, `bFwd`, `bExh` and `bRet` —
have no transition blocks of their own.  Execution lives in separate layers with
their own surface entries.  End-to-end physical validation, rejection, rewind,
and `readBStart` composition remain in their separate execution surface.

S1b1 introduced the then-dormant pass-A control ABI: the twelve pass-A modes, their
frame rows, the residual view of the two spare context bits, the result
convention and the operation latch.  Every one of those entries is pinned below,
together with the frame-table closure and the executed one-door theorem
(`g1Advance_passA`, `g1Transition_passA_door`).
S1b2a re-points the two unary rows and both constant tuples through
`readAResetStart`.  S1b2b activates `readAStart`; no frame-table row produces
it and the repair terminal is its unique predecessor.

This is an audit surface: it pins public signatures, it does not prove
anything new.
-/

namespace Pnp3.Tests.TMGateOneControlSurface

open Pnp3.Internal.PsubsetPpoly.TM

-- The one fixed zero-parameter machine.
#check @G1State
#check @G1Mode
#check @G1FramePosition
#check @G1Ctx
#check @g1Ctx0
#check @g1State
#check @g1AcceptState
#check @g1RejectState
#check @g1ReadBState
#check @g1ReadAState
#check @g1CombineState
#check @g1ReadAResetState
#check @g1RoundState
#check @g1WalkState
#check @g1MarkState
#check @g1OOBState
#check @G1Ctx.withVB
#check @g1ConstMode
#check @g1StoreMode
#check @g1Clock
#check @g1CS
#check @g1CS_runTime
#check @g1Transition
#check @g1Transition_forward_p0
#check @g1Transition_forward_p1
#check @g1Transition_forward_p2
#check @g1Transition_forward_p3_advance
#check @g1Transition_forward_p3_reject
#check @g1Transition_rewindStart
#check @g1Transition_rewind_p3
#check @g1Transition_rewind_p2
#check @g1Transition_rewind_p1
#check @g1Transition_rewind_p0_bof
#check @g1Transition_rewind_p0_other
#check @g1Transition_combineStart_idle
#check @g1Transition_readAResetStart_bridge
#check @g1Transition_bOOB_stable
#check @g1Transition_constLit
#check @g1Transition_store
-- The fourteen tuples of the destructive index round.
#check @g1Transition_bRoundStart_bridge
#check @g1Transition_bWalk_p3
#check @g1Transition_bWalk_p2
#check @g1Transition_bWalk_p1
#check @g1Transition_bWalk_p0_index
#check @g1Transition_bWalk_p0_other
#check @g1Transition_bMark_p0
#check @g1Transition_bMark_p1
#check @g1Transition_bMark_p2
#check @g1Transition_bMark_p3
#check @g1Transition_bBack_p0
#check @g1Transition_bBack_p1
#check @g1Transition_bBack_p2
#check @g1Transition_bBack_p3
#check @g1Transition_bHop
-- The entry states, the three selectors and the thirty-one transition tuples of
-- the cursor walk.  `bInsSeek`/`bProbe2`/`bFwd`/`bExh`/`bRet` are forward modes,
-- so none of the five has transition rows of its own.
#check @g1InsSeekState
#check @g1Probe2State
#check @g1InsState
#check @g1SeekState
#check @g1DecState
#check @g1FwdState
#check @g1ExhState
#check @g1LatchMode
#check @g1RestoreMode
#check @g1FinMode
#check @g1FinMode_ne_restore
#check @g1Transition_bLatch
#check @g1Transition_bIns_p3
#check @g1Transition_bIns_p2
#check @g1Transition_bIns_p1
#check @g1Transition_bIns_p0
#check @g1Transition_bSeek_p3
#check @g1Transition_bSeek_p2
#check @g1Transition_bSeek_p1
#check @g1Transition_bSeek_p0_index
#check @g1Transition_bSeek_p0_argSep
#check @g1Transition_bSeek_p0_other
#check @g1Transition_bDec_p0
#check @g1Transition_bDec_p1
#check @g1Transition_bDec_p2
#check @g1Transition_bDec_p3
#check @g1Transition_bTurn_p0
#check @g1Transition_bTurn_p1
#check @g1Transition_bTurn_p2
#check @g1Transition_bTurn_p3
#check @g1Transition_bTurnFin_p0
#check @g1Transition_bTurnFin_p1
#check @g1Transition_bTurnFin_p2
#check @g1Transition_bTurnFin_p3
#check @g1Transition_bRestore_p0
#check @g1Transition_bRestore_p1
#check @g1Transition_bRestore_p2
#check @g1Transition_bRestore_p3
#check @g1Transition_bFin_p0
#check @g1Transition_bFin_p1
#check @g1Transition_bFin_p2
#check @g1Transition_bFin_p3
#check @g1RejectState_ne_readB
#check @g1OOBState_ne_readAReset
#check @g1ExhState_ne_dec

-- The three entry states of the operand-2 repair sweep; its eleven transition
-- tuples are pinned as exact equations by the `check_g1Transition_bRepair*`
-- theorems below.  No `g1Advance` row enters them; the sole live entry is the
-- Repair-2a `readAResetStart` bridge.
#check @g1RepairSeekState
#check @g1RepairWriteState
#check @g1RepairDoneState
#check @g1Transition_bRepairWrite
#check @g1Transition_bRepairBack
#check @g1Transition_bRepairHop

-- The frame-level language of the fixed forward control.
#check @g1Advance
#check @g1Complete
#check @G1ForwardMode
#check @G1ForwardMode.not_reject
#check @G1ForwardMode.not_rewindStart
#check @G1Stuck
#check @g1Advance_range
#check @g1AdvanceList_ne_rewindStart_of_stuck
#check @g1AdvanceList
#check @g1AdvanceList_append
#check @G1ValidPath
#check @G1RejectPath
#check @G1RejectPath.forward
#check @g1ValidPath_of_accepts
#check @g1AdvanceList_encode
#check @g1AdvanceList_encode_reject
#check @g1RejectPath_encode
#check @encodeG1Frames_blank_shape
#check @g1_structure_of_accepts
#check @g1Automaton_accepts_iff_decode
#check @g1CanonicalEncoderAutomatonTrace_iff
#check @g1_example_control_and_accepts
#check @g1_example_control_const_rejects

-- Named rejection witnesses: wrong tag counts, the `const` operand
-- convention, and the unused operand-2 field of every arity-1 tag.
#check @g1_reject_tagRun_zero
#check @g1_reject_tagRun_six
#check @g1_reject_const_arg1_ge_two
#check @g1_reject_unusedField_input
#check @g1_reject_unusedField_not
#check @g1_reject_unusedField_const
#check @g1_rejectPath_vArg2Zero
#check @g1_rejectPath_vArg1Unary
#check @g1_rejectPath_vConst0_arg1
#check @g1_rejectPath_vConst0_arg2

-- The generic frame-scanner kernel, instantiated at G1.
#check @G1M
#check @g1FrameCodec
#check @g1FrameScanner
#check @g1FrameScanner_codec
#check @g1FrameScanner_frameMacrostep
#check @g1FrameScanner_scanFrames
#check @g1FrameScanner_advanceList
#check @g1FrameScanner_validPath
#check @g1FrameScanner_frameLanguage_iff_decode

-- The pass-A control ABI and its S1b2b activation.  The residual view of the two spare
-- context bits and the result convention, the two named pass-A states, the
-- twelve-mode family predicate with its frame-table closure and executed door,
-- the operation latch, the idle install handoff and the live two-way
-- `readAStart` dispatch.
#check @g1ResPass
#check @g1ResCrossed
#check @G1Ctx.res
#check @G1Ctx.withRes
#check @G1Ctx.res_withRes
#check @G1Ctx.withRes_vB
#check @G1Ctx.withVB_res
#check @G1Ctx.withRes_res
#check @g1ResultCtx
#check @g1ResultCtx_pass
#check @g1ResultCtx_vB
#check @g1ResultCtx_ne_entry
#check @g1ResultCtx_eq_andFalse_res
#check @g1ResultCtx_pass_eq_orTrue_res
#check @g1ABofState
#check @g1AInstallState
#check @G1PassAMode
#check @G1PassAMode.not_reject
#check @g1Advance_passA
#check @g1Complete_passA
#check @g1_readAStart_unreachable
#check @g1_aInstallStart_unreachable
#check @g1Complete_ne_readAStart
#check @g1Complete_ne_aInstallStart
#check @g1AOpMode
#check @g1AOpMode_const
#check @g1Transition_aOp
#check @g1Transition_aInstallStart_idle
#check @g1Transition_passA_door

/-! ## Exact theorem-contract pins -/

theorem check_g1CS_runTime (N : Nat) :
    g1CS.toPhased.toTM.runTime N = 512 * (N + 1) ^ 2 + 512 :=
  g1CS_runTime N

/-- **The re-pointed row.**  The positive-index branch of the operand-2 walk
enters the installation scan, not the retired rewrite-cycle bridge. -/
theorem check_g1Advance_bScan_index :
    g1Advance .bScan .index = .bInsSeek := rfl

/-- **The complete installation-scan table.** -/
theorem check_g1Advance_bInsSeek :
    g1Advance .bInsSeek .index = .bInsSeek ∧
      g1Advance .bInsSeek .spent = .bInsSeek ∧
      g1Advance .bInsSeek .separator = .bProbe2 :=
  ⟨rfl, rfl, rfl⟩

/-- **The complete probe table and the walk's right-running scan.**  `bProbe2`
latches the data bit it reads or hands off to the stable
out-of-range boundary; `bFwd` crosses consumed units, the separator and data and
stops on the `cursor`.  The
`bScan + data` row stays absent: a data frame before the separator is still
malformed and still rejects. -/
theorem check_g1Advance_probe (b : Bool) :
    (g1Advance .bProbe2 (.data b) = g1LatchMode b ∧
        g1Advance .bProbe2 (.output false) = .bOOB) ∧
      (g1Advance .bFwd (.data b) = .bFwd ∧ g1Advance .bFwd .cursor = .bTurn) ∧
      g1Advance .bScan (.data b) = .reject := by
  cases b <;> exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

/-- **The complete terminal exhaustion table.**  `bExh` has exactly one row —
it re-reads the `argSep` that opens the operand-2 field and enters `bRet` — and
`bRet` crosses consumed units, the separator and data and stops on the `cursor`
at the terminal turn.  Every other frame at either mode enters `reject`. -/
theorem check_g1Advance_exhaustion (b : Bool) :
    (g1Advance .bExh .argSep = .bRet ∧
        g1Advance .bExh .cursor = .reject) ∧
      (g1Advance .bRet .spent = .bRet ∧ g1Advance .bRet .separator = .bRet ∧
        g1Advance .bRet (.data b) = .bRet ∧
        g1Advance .bRet .cursor = .bTurnFin ∧
        g1Advance .bRet .argSep = .reject) := by
  cases b <;> exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- **The writers and the turns never read a frame forward.**  Each of the eight
non-forward walk modes of the round and the three of the terminal path is
`G1Stuck`: they move under
`g1Transition` alone.  `bSeek` is among them because it reads **right to left**,
not because it is a boundary; its three outcomes are
`check_g1Transition_bSeek`. -/
theorem check_g1Advance_walk_nonforward :
    G1Stuck .bSeek ∧ G1Stuck .bDec ∧ G1Stuck .bTurn ∧
      G1Stuck .bRestoreFalse ∧ G1Stuck .bRestoreTrue ∧
      G1Stuck .bLatchFalse ∧ G1Stuck .bLatchTrue ∧ G1Stuck .bIns ∧
      G1Stuck .bTurnFin ∧ G1Stuck .bFinFalse ∧ G1Stuck .bFinTrue := by decide

/-- **The reverse seek's three outcomes, pinned exactly.**  An `index` stops it
at the write handoff and an `argSep` at the exhaustion handoff, both *without*
moving; every other frame continues it one frame further left.  The literal
`argSep` stop row is pinned exactly. -/
theorem check_g1Transition_bSeek (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    (decodeG1Frame? [scan, b0, b1, b2] = some .index →
        g1Transition phase (g1State .bSeek .p0 b0 b1 b2 ctx) scan =
          (0, g1DecState ctx, scan, .stay)) ∧
      (decodeG1Frame? [scan, b0, b1, b2] = some .argSep →
        g1Transition phase (g1State .bSeek .p0 b0 b1 b2 ctx) scan =
          (0, g1ExhState ctx, scan, .stay)) ∧
      (decodeG1Frame? [scan, b0, b1, b2] ≠ some .index →
        decodeG1Frame? [scan, b0, b1, b2] ≠ some .argSep →
        g1Transition phase (g1State .bSeek .p0 b0 b1 b2 ctx) scan =
          (0, g1SeekState ctx, scan, .left)) :=
  ⟨g1Transition_bSeek_p0_index phase b0 b1 b2 scan ctx,
    g1Transition_bSeek_p0_argSep phase b0 b1 b2 scan ctx,
    g1Transition_bSeek_p0_other phase b0 b1 b2 scan ctx⟩

/-- **The latch, pinned exactly.**  One step stores the probed bit in the fixed
Boolean field `vB` and steps left; it writes back the cell it scans. -/
theorem check_g1Transition_bLatch (phase : Fin 1) (b : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1LatchMode b) position b0 b1 b2 ctx) scan =
      (0, g1InsState (ctx.withVB b), scan, .left) :=
  g1Transition_bLatch phase b position b0 b1 b2 scan ctx

/-- **The terminal turn, pinned exactly.**  Four hold-and-move-left steps that
write back what they scan, exiting into the *terminal* writer selected by the
latched bit — never into the round writer. -/
theorem check_g1Transition_bTurnFin (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bTurnFin .p0 b0 b1 b2 ctx) scan =
        (0, g1State .bTurnFin .p1 false false false ctx, scan, .left) ∧
      g1Transition phase (g1State .bTurnFin .p1 b0 b1 b2 ctx) scan =
        (0, g1State .bTurnFin .p2 false false false ctx, scan, .left) ∧
      g1Transition phase (g1State .bTurnFin .p2 b0 b1 b2 ctx) scan =
        (0, g1State .bTurnFin .p3 false false false ctx, scan, .left) ∧
      g1Transition phase (g1State .bTurnFin .p3 b0 b1 b2 ctx) scan =
        (0, g1State (g1FinMode ctx.vB) .p0 false false false ctx, scan, .left) ∧
      g1FinMode ctx.vB ≠ g1RestoreMode ctx.vB :=
  ⟨g1Transition_bTurnFin_p0 phase b0 b1 b2 scan ctx,
    g1Transition_bTurnFin_p1 phase b0 b1 b2 scan ctx,
    g1Transition_bTurnFin_p2 phase b0 b1 b2 scan ctx,
    g1Transition_bTurnFin_p3 phase b0 b1 b2 scan ctx,
    g1FinMode_ne_restore ctx.vB ctx.vB⟩

/-- **The terminal restore, pinned exactly.**  The four cells it writes are
literally `(G1Frame.data b).bits`, and the fourth step hands off to
`readAResetStart` — the row that leaves no cursor on the tape. -/
theorem check_g1Transition_bFin (phase : Fin 1) (b : Bool)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1FinMode b) .p0 b0 b1 b2 ctx) scan =
        (0, g1State (g1FinMode b) .p1 false false false ctx, false, .right) ∧
      g1Transition phase (g1State (g1FinMode b) .p1 b0 b1 b2 ctx) scan =
        (0, g1State (g1FinMode b) .p2 false false false ctx, true, .right) ∧
      g1Transition phase (g1State (g1FinMode b) .p2 b0 b1 b2 ctx) scan =
        (0, g1State (g1FinMode b) .p3 false false false ctx, b, .right) ∧
      g1Transition phase (g1State (g1FinMode b) .p3 b0 b1 b2 ctx) scan =
        (0, g1ReadAResetState ctx, !b, .right) ∧
      (G1Frame.data b).bits = [false, true, b, !b] :=
  ⟨g1Transition_bFin_p0 phase b b0 b1 b2 scan ctx,
    g1Transition_bFin_p1 phase b b0 b1 b2 scan ctx,
    g1Transition_bFin_p2 phase b b0 b1 b2 scan ctx,
    g1Transition_bFin_p3 phase b b0 b1 b2 scan ctx,
    by cases b <;> rfl⟩

/-- **The reverse repair scan, pinned exactly.**  Three buffering steps and a
**four-way** decision at frame position `0`: a `spent` unit is the write handoff,
the `bof` anchor the terminal handoff, a crossable interior frame continues the
scan one frame further left, and a window the scan may not cross enters the
`reject` sink.  All three non-continuing rows *stay*. -/
theorem check_g1Transition_bRepairSeek (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) (frame : G1Frame) :
    g1Transition phase (g1State .bRepairSeek .p3 b0 b1 b2 ctx) scan =
        (0, g1State .bRepairSeek .p2 false false scan ctx, scan, .left) ∧
      g1Transition phase (g1State .bRepairSeek .p2 b0 b1 b2 ctx) scan =
        (0, g1State .bRepairSeek .p1 false scan b2 ctx, scan, .left) ∧
      g1Transition phase (g1State .bRepairSeek .p1 b0 b1 b2 ctx) scan =
        (0, g1State .bRepairSeek .p0 scan b1 b2 ctx, scan, .left) ∧
      (decodeG1Frame? [scan, b0, b1, b2] = some .spent →
        g1Transition phase (g1State .bRepairSeek .p0 b0 b1 b2 ctx) scan =
          (0, g1RepairWriteState ctx, scan, .stay)) ∧
      (decodeG1Frame? [scan, b0, b1, b2] = some .bof →
        g1Transition phase (g1State .bRepairSeek .p0 b0 b1 b2 ctx) scan =
          (0, g1RepairDoneState ctx, scan, .stay)) ∧
      (decodeG1Frame? [scan, b0, b1, b2] = some frame → G1RepairSkip frame →
        g1Transition phase (g1State .bRepairSeek .p0 b0 b1 b2 ctx) scan =
          (0, g1RepairSeekState ctx, scan, .left)) ∧
      (g1RepairBackComplete scan b0 b1 b2 = .reject →
        g1Transition phase (g1State .bRepairSeek .p0 b0 b1 b2 ctx) scan =
          (0, g1RejectState, scan, .stay)) :=
  ⟨g1Transition_bRepairSeek_p3 phase b0 b1 b2 scan ctx,
    g1Transition_bRepairSeek_p2 phase b0 b1 b2 scan ctx,
    g1Transition_bRepairSeek_p1 phase b0 b1 b2 scan ctx,
    g1Transition_bRepairSeek_p0_spent phase b0 b1 b2 scan ctx,
    g1Transition_bRepairSeek_p0_bof phase b0 b1 b2 scan ctx,
    g1Transition_bRepairSeek_p0_skip phase b0 b1 b2 scan ctx frame,
    g1Transition_bRepairSeek_p0_bad phase b0 b1 b2 scan ctx⟩

/-- **The malformed windows, pinned literally.**  `G1RepairSkip` is *exactly*
the crossable interior frame kinds, and the two forbidden decodable codewords
`blank = 0000` and `cursor = 0111`, together with the three reserved codes
`1101`, `1110`, `1111` that decode to nothing, all send the frame-position-`0`
row of `bRepairSeek` into the `reject` sink without moving.  The reserved codes
have no `G1Frame` at all, so they are pinned at the bit level — there is no
frame-level run to state for them. -/
theorem check_g1Transition_bRepairSeek_malformed (phase : Fin 1) (ctx : G1Ctx) :
    (decodeG1Frame? [true, true, false, true] = none ∧
        decodeG1Frame? [true, true, true, false] = none ∧
        decodeG1Frame? [true, true, true, true] = none) ∧
      (∀ f : G1Frame, G1RepairSkip f → g1RepairBackAdvance f = .bRepairSeek) ∧
      (g1RepairBackAdvance .spent = .bRepairWrite ∧
        g1RepairBackAdvance .bof = .bRepairDone ∧
        g1RepairBackAdvance .blank = .reject ∧
        g1RepairBackAdvance .cursor = .reject) ∧
      g1Transition phase (g1State .bRepairSeek .p0 false false false ctx)
          false = (0, g1RejectState, false, .stay) ∧
      g1Transition phase (g1State .bRepairSeek .p0 true true true ctx)
          false = (0, g1RejectState, false, .stay) ∧
      g1Transition phase (g1State .bRepairSeek .p0 true false true ctx)
          true = (0, g1RejectState, true, .stay) ∧
      g1Transition phase (g1State .bRepairSeek .p0 true true false ctx)
          true = (0, g1RejectState, true, .stay) ∧
      g1Transition phase (g1State .bRepairSeek .p0 true true true ctx)
          true = (0, g1RejectState, true, .stay) :=
  ⟨decodeG1Frame_reserved, fun _ h => g1RepairBackAdvance_of_skip h,
    ⟨rfl, rfl, rfl, rfl⟩,
    g1Transition_bRepairSeek_p0_bad phase false false false false ctx
      g1RepairBackComplete_forbidden.1,
    g1Transition_bRepairSeek_p0_bad phase true true true false ctx
      g1RepairBackComplete_forbidden.2,
    g1Transition_bRepairSeek_p0_bad phase true false true true ctx
      g1RepairBackComplete_reserved.1,
    g1Transition_bRepairSeek_p0_bad phase true true false true ctx
      g1RepairBackComplete_reserved.2.1,
    g1Transition_bRepairSeek_p0_bad phase true true true true ctx
      g1RepairBackComplete_reserved.2.2⟩

/-- **The `spent ↦ index` writer, its back-walk and its hop, pinned exactly.**
The four cells the writer lays down are literally `G1Frame.index.bits`, the
back-walk writes back what it scans and the hop re-enters the scan one frame
further left. -/
theorem check_g1Transition_bRepairWrite (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bRepairWrite .p0 b0 b1 b2 ctx) scan =
        (0, g1State .bRepairWrite .p1 false false false ctx, false, .right) ∧
      g1Transition phase (g1State .bRepairWrite .p1 b0 b1 b2 ctx) scan =
        (0, g1State .bRepairWrite .p2 false false false ctx, false, .right) ∧
      g1Transition phase (g1State .bRepairWrite .p2 b0 b1 b2 ctx) scan =
        (0, g1State .bRepairWrite .p3 false false false ctx, true, .right) ∧
      g1Transition phase (g1State .bRepairWrite .p3 b0 b1 b2 ctx) scan =
        (0, g1State .bRepairBack .p0 false false false ctx, true, .right) ∧
      g1Transition phase (g1State .bRepairBack .p3 b0 b1 b2 ctx) scan =
        (0, g1State .bRepairHop .p0 false false false ctx, scan, .left) ∧
      g1Transition phase (g1State .bRepairHop .p0 b0 b1 b2 ctx) scan =
        (0, g1RepairSeekState ctx, scan, .left) ∧
      G1Frame.index.bits = [false, false, true, true] :=
  ⟨g1Transition_bRepairWrite phase .p0 b0 b1 b2 scan ctx,
    g1Transition_bRepairWrite phase .p1 b0 b1 b2 scan ctx,
    g1Transition_bRepairWrite phase .p2 b0 b1 b2 scan ctx,
    g1Transition_bRepairWrite phase .p3 b0 b1 b2 scan ctx,
    g1Transition_bRepairBack phase .p3 b0 b1 b2 scan ctx,
    g1Transition_bRepairHop phase .p0 b0 b1 b2 scan ctx, rfl⟩

/-- **The repair terminal, pinned exactly.** -/
theorem check_g1Transition_bRepairDone (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .bRepairDone position b0 b1 b2 ctx) scan =
      (0, g1ReadAState ctx, scan, .stay) :=
  g1Transition_bRepairDone phase position b0 b1 b2 scan ctx

/-- **The bridge into the sweep, pinned exactly.**  `readAResetStart` is the
one and only row outside the five repair modes that enters one: it writes back
the cell it scans — so the tape is unchanged — steps one cell **left**, and
lands in the reverse-read entry shape `bRepairSeek .p3` with an empty frame
buffer and the whole `G1Ctx`, latch included, preserved.  `readAStart` and
`combineStart` remain idle beside it. -/
theorem check_g1Transition_readAResetStart_bridge (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .readAResetStart position b0 b1 b2 ctx) scan =
        (0, g1RepairSeekState ctx, scan, .left) ∧
      g1RepairSeekState ctx = g1State .bRepairSeek .p3 false false false ctx ∧
      g1Transition phase (g1State .combineStart position b0 b1 b2 ctx) scan =
        (0, g1CombineState ctx, scan, .stay) :=
  ⟨g1Transition_readAResetStart_bridge phase position b0 b1 b2 scan ctx, rfl,
    g1Transition_combineStart_idle phase position b0 b1 b2 scan ctx⟩

theorem check_g1AdvanceList_encode_reject (r : G1Request)
    (hc : ¬ r.Canonical) :
    g1AdvanceList .vBof (encodeG1Frames r ++ [.blank]) = .reject :=
  g1AdvanceList_encode_reject r hc

theorem check_g1_reject_tagRun_zero (rest : List G1Frame) :
    g1AdvanceList .vBof (.bof :: .argSep :: rest) = .reject :=
  g1_reject_tagRun_zero rest

theorem check_g1_reject_tagRun_six (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .tag :: .tag :: .tag :: .tag :: rest) =
      .reject :=
  g1_reject_tagRun_six rest

theorem check_g1_reject_const_arg1_ge_two (a1 : Nat) (h : 2 ≤ a1)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .argSep ::
          (List.replicate a1 .index ++ rest)) = .reject :=
  g1_reject_const_arg1_ge_two a1 h rest

theorem check_g1_reject_unusedField_input (a1 a2 : Nat) (h : a2 ≠ 0)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1_reject_unusedField_input a1 a2 h rest

theorem check_g1_reject_unusedField_not (a1 a2 : Nat) (h : a2 ≠ 0)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1_reject_unusedField_not a1 a2 h rest

theorem check_g1_reject_unusedField_const (a1 a2 : Nat) (h1 : a1 ≤ 1)
    (h2 : a2 ≠ 0) (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1_reject_unusedField_const a1 a2 h1 h2 rest

theorem check_g1Automaton_accepts_iff_decode (fs : List G1Frame) :
    g1AdvanceList .vBof (fs ++ [.blank]) = .rewindStart ↔
      ∃ r : G1Request, decodeG1FrameList? fs = some r :=
  g1Automaton_accepts_iff_decode fs

theorem check_g1CanonicalEncoderAutomatonTrace_iff (r : G1Request) :
    g1AdvanceList .vBof (encodeG1Frames r ++ [.blank]) = .rewindStart ↔
      r.Canonical :=
  g1CanonicalEncoderAutomatonTrace_iff r

theorem check_g1FrameScanner_frameLanguage_iff_decode (fs : List G1Frame) :
    g1FrameScanner.advanceList .vBof (fs ++ [.blank]) = .rewindStart ↔
      ∃ r : G1Request, decodeG1FrameList? fs = some r :=
  g1FrameScanner_frameLanguage_iff_decode fs

theorem check_g1FrameScanner_frameMacrostep (n h : Nat)
    (hsafe : h + 4 < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (mode : G1Mode) (frame : G1Frame) (ctx : G1Ctx)
    (hmode : G1ForwardMode mode) (hnext : g1Advance mode frame ≠ .reject)
    (hbits : FrameScan.physicalBitsAt hsafe tape = frame.bits) :
    G1M.runConfig
        (g1FrameScanner.alignedFrame n h
          (by rw [g1FrameScanner_machine]; omega) tape mode ctx) 4 =
      g1FrameScanner.alignedFrame n (h + 4) hsafe tape
        (g1Advance mode frame) ctx :=
  g1FrameScanner_frameMacrostep n h hsafe tape mode frame ctx hmode hnext hbits

theorem check_g1FrameScanner_scanFrames (n : Nat)
    (pre frames suffix : List G1Frame) (mode : G1Mode) (ctx : G1Ctx)
    (hpath : g1FrameScanner.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < G1M.tapeLength n) :
    G1M.runConfig
        (g1FrameScanner.alignedFrame n (4 * pre.length)
          (by rw [g1FrameScanner_machine]; omega)
          (FrameScan.frameListTape
            ((pre ++ frames ++ suffix).flatMap G1Frame.bits)) mode ctx)
        (4 * frames.length) =
      g1FrameScanner.alignedFrame n (4 * (pre.length + frames.length)) hsafe
        (FrameScan.frameListTape
          ((pre ++ frames ++ suffix).flatMap G1Frame.bits))
        (g1FrameScanner.advanceList mode frames) ctx :=
  g1FrameScanner_scanFrames n pre frames suffix mode ctx hpath hsafe

/-! ## The live pass-A control ABI (S1b2b)

Every row of the twelve-mode family, its closure against frame-table entry from
outside, and its sole executed external door through live `readAStart`. -/

/-- **The complete pass-A frame table.**  The anchor read, the five
counter rows and the four `argSep` rows that select an operation latch — and the
`aTag2` gap, which is why `const` rejects and why the `const` filler row of
`g1Residual` is never consumed. -/
theorem check_g1Advance_passA_table :
    (g1Advance .aBof .bof = .aTag0 ∧ g1Advance .aTag0 .tag = .aTag1 ∧
        g1Advance .aTag1 .tag = .aTag2 ∧ g1Advance .aTag2 .tag = .aTag3 ∧
        g1Advance .aTag3 .tag = .aTag4 ∧ g1Advance .aTag4 .tag = .aTag5) ∧
      (g1Advance .aTag1 .argSep = .aOpInput ∧
        g1Advance .aTag3 .argSep = .aOpNot ∧
        g1Advance .aTag4 .argSep = .aOpAnd ∧
        g1Advance .aTag5 .argSep = .aOpOr) ∧
      (g1Advance .aTag2 .argSep = .reject ∧
        g1Advance .aTag5 .tag = .reject ∧
        g1AOpMode .const = .reject) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The two unary pass-B rows enter the common rewind. -/
theorem check_g1Advance_unary_repoint :
    g1Advance .rTag1 .argSep = .readAResetStart ∧
      g1Advance .rTag3 .argSep = .readAResetStart :=
  ⟨rfl, rfl⟩

/-- **The four latches read nothing forward, and the install handoff is
stuck.**  The pass-A anchor read and its counters, by contrast, are genuine
forward modes. -/
theorem check_g1Advance_passA_forward :
    (G1ForwardMode .aBof ∧ G1ForwardMode .aTag0 ∧ G1ForwardMode .aTag5) ∧
      (G1Stuck .aOpInput ∧ G1Stuck .aOpNot ∧ G1Stuck .aOpAnd ∧
        G1Stuck .aOpOr ∧ G1Stuck .aInstallStart) := by
  refine ⟨⟨trivial, trivial, trivial⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The frame table is closed and the executed family has only the live
`readAStart` door. -/
theorem check_g1_passA_door :
    (∀ (mode : G1Mode) (frame : G1Frame),
        G1PassAMode (g1Advance mode frame) → G1PassAMode mode) ∧
      (∀ (phase : Fin 1) (s : G1State) (scan : Bool),
        G1PassAMode (g1Transition phase s scan).2.1.mode →
          G1PassAMode s.mode ∨ s.mode = .readAStart) :=
  ⟨g1Advance_passA, g1Transition_passA_door⟩

/-- The live entry branch preserves the scanned cell and context and keeps the
head stationary while entering the A-specific anchor state. -/
theorem check_g1Transition_readAStart_entry (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hpass : ctx.pass = false) :
    g1Transition phase (g1State .readAStart position b0 b1 b2 ctx) scan =
      (0, g1ABofState ctx, scan, .stay) :=
  g1Transition_readAStart_entry phase position b0 b1 b2 scan ctx hpass

/-- The live result branch preserves the scanned cell and context and keeps the
head stationary while entering the combine boundary. -/
theorem check_g1Transition_readAStart_result (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx)
    (hpass : ctx.pass = true) :
    g1Transition phase (g1State .readAStart position b0 b1 b2 ctx) scan =
      (0, g1CombineState ctx, scan, .stay) :=
  g1Transition_readAStart_result phase position b0 b1 b2 scan ctx hpass

/-- The repair terminal is the exact and only predecessor of `readAStart`. -/
theorem check_g1Transition_readAStart_unique (phase : Fin 1) (s : G1State)
    (scan : Bool) (h : (g1Transition phase s scan).2.1.mode = .readAStart) :
    s.mode = .bRepairDone :=
  g1Transition_readAStart_unique phase s scan h

/-- The four operation latches and the stationary boundary are the exact
predecessors of `aInstallStart`. -/
theorem check_g1Transition_aInstallStart_unique (phase : Fin 1) (s : G1State)
    (scan : Bool) (h : (g1Transition phase s scan).2.1.mode = .aInstallStart) :
    s.mode = .aOpInput ∨ s.mode = .aOpNot ∨ s.mode = .aOpAnd ∨
      s.mode = .aOpOr ∨ s.mode = .aInstallStart :=
  g1Transition_aInstallStart_unique phase s scan h

/-- **The operation latch and the idle install handoff, pinned exactly.**  One
stationary step writes the residual of `(t, ctx.vB)` into the two spare context
bits and installs it in a state that never moves again. -/
theorem check_g1Transition_aOp (phase : Fin 1) (t : G1Tag) (ht : t ≠ .const)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1AOpMode t) position b0 b1 b2 ctx) scan =
        (0, g1AInstallState (ctx.withRes (g1Residual t ctx.vB)), scan, .stay) ∧
      g1Transition phase (g1State .aInstallStart position b0 b1 b2 ctx) scan =
        (0, g1AInstallState ctx, scan, .stay) :=
  ⟨g1Transition_aOp phase t ht position b0 b1 b2 scan ctx,
    g1Transition_aInstallStart_idle phase position b0 b1 b2 scan ctx⟩

/-- **The residual view is a faithful two-bit encoding that leaves `vB`
alone.**  No field is added to `G1Ctx`: `res`/`withRes` read and write the
existing `pass`/`crossed` pair. -/
theorem check_G1Ctx_res_roundTrip (ctx : G1Ctx) (res : G1Residual) (b : Bool) :
    (ctx.withRes res).res = res ∧ (ctx.withRes res).vB = ctx.vB ∧
      ctx.withRes ctx.res = ctx ∧ (ctx.withVB b).res = ctx.res :=
  ⟨G1Ctx.res_withRes ctx res, G1Ctx.withRes_vB ctx res, G1Ctx.withRes_res ctx,
    G1Ctx.withVB_res ctx b⟩

/-- **The result convention, and the aliasing it creates.**  An entry context is
never a result context, but a *latched* one can be: the absorbing
`and`/`vB = false` residual is literally `g1ResultCtx false`.  Harmless while
`aInstallStart` self-loops and cannot return to `readAStart`; it is the constraint S1b2
and the deferred operand-1 walk inherit. -/
theorem check_g1ResultCtx_aliasing (b b' : Bool) :
    g1ResultCtx b ≠ g1Ctx0.withVB b' ∧
      (g1Ctx0.withVB false).withRes (g1Residual .and false) = g1ResultCtx false ∧
      ((g1Ctx0.withVB true).withRes (g1Residual .or true)).pass =
        (g1ResultCtx true).pass :=
  ⟨g1ResultCtx_ne_entry b b', g1ResultCtx_eq_andFalse_res,
    g1ResultCtx_pass_eq_orTrue_res⟩

end Pnp3.Tests.TMGateOneControlSurface
