import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycle
import Complexity.TMVerifier.TuringToolkit.FrameScannerReverseInstances

/-!
# T1 and G1 against the generic mutation kernel

`FrameRewriteCycle` proves the thirteen-step rewrite cycle once, generically.
This module instantiates it — and the leftward writer and the seek driver — at
the *existing* controls.

## T1

`t1RepairScanner` presents the `repairSeek` pass as a `ReverseFrameScanner`
whose stop modes are the three outcomes of T1's own frame decision
(`repairWrite`, `repairDone`, the grammar sink), and `t1RepairCycle` puts the
`repairWrite`/`repairBack`/`repairHop` rows on top of it.
`t1RepairCycle_repair_cycle` re-derives `t1CS_repair_cycle` — same statement,
`spent ↦ index` in thirteen genuine steps, head `base + 3 ↦ base - 1` — from the
generic composition instead of four hand-chained T1 macro lemmas, and
`t1RepairCycle_repair_cycle_onList` states it on an arbitrary frame list.
`t1OutWriter` presents T1's output write as a `ReverseFrameWriter` — a genuine
*leftward* writer whose installed frame `output latch` depends on the carried
context — and `t1OutWriter_outWriteOut_frame` matches
`t1CS_outWriteOut_frame`.

## G1

`g1RevScanner_seek_bof` instantiates the new seek-until-marker driver at G1's
**existing** rewind modes: an arbitrary run of non-anchor frames is crossed and
the anchor read in exactly `4 * tail.length + 4` steps, landing at head `0` in
the `readBStart` handoff.  No control table is touched and `bRoundStart` stays
idle.

`g1CS` has **no** destructive walk modes — no write, walk-back or hop rows exist
for it — so **no G1 rewrite cycle is claimed here**.  What is provided instead
is the exact obligation: `G1RewriteCycleObligation` is the data the next G1
slice must build (a `FrameRewriteCycle` whose scanner's program *is* `g1CS`,
whose codec is `g1FrameCodec`, with the `index ↦ spent` direction fixed),
`machine_eq` records that such a cycle's machine is literally `G1M`, and
`rewrite_cycle` derives the thirteen-step `index ↦ spent` run from it by the
generic theorem verbatim.  Both are conditional on data that does not exist
yet; nothing below executes `g1CS` past `bRoundStart`.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## T1: the repair pass as a reverse scanner -/
/-- The single T1 mode that reads frames right to left in the repair pass. -/
def T1RepairMode : T1Mode → Prop
  | .repairSeek => True
  | _ => False

theorem T1RepairMode.eq {m : T1Mode} (h : T1RepairMode m) : m = .repairSeek := by
  cases m <;> simp_all [T1RepairMode]

/-- The repair scan continues only while the decided mode is the scan itself:
the write handoff, the final dispatch and the grammar sink all stop it. -/
def T1RepairStop (mode : T1Mode) : Prop := mode ≠ .repairSeek

/-- T1's repair table, as a mode-indexed reverse frame table.  The mode
argument is inert: the repair pass has one reverse mode. -/
def t1RepairRevAdvance (_mode : T1Mode) (frame : T1Frame) : T1Mode :=
  t1RepairBackAdvance frame

/-- The bit-level form of `t1RepairRevAdvance`, as `t1Transition` computes it. -/
def t1RepairRevComplete (_mode : T1Mode) (b0 b1 b2 b3 : Bool) : T1Mode :=
  t1RepairBackComplete b0 b1 b2 b3

/-- The three states T1's repair scan can stop in.  The grammar sink clears the
latch, which is why this is a case distinction and not a uniform record. -/
def t1RepairStopState (mode : T1Mode) (latch : Bool) : T1State :=
  match mode with
  | .repairWrite => t1State .repairWrite .p0 false false false latch
  | .repairDone => t1State .repairDone .p0 false false false latch
  | _ => t1RejectState

/-- **T1's repair scan is an instance of the generic reverse kernel.** -/
def t1RepairScanner : ReverseFrameScanner T1State T1Frame T1Mode Bool where
  program := t1CS
  phase := t1CS.startPhase
  codec := t1FrameCodec
  Stop := T1RepairStop
  revAdvance := t1RepairRevAdvance
  revComplete := t1RepairRevComplete
  Reverse := T1RepairMode
  rst3 := fun m latch => t1State m .p3 false false false latch
  rst2 := fun m latch b3 => t1State m .p2 false false b3 latch
  rst1 := fun m latch b2 b3 => t1State m .p1 false b2 b3 latch
  rst0 := fun m latch b1 b2 b3 => t1State m .p0 b1 b2 b3 latch
  stopState := t1RepairStopState
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    have h' : decodeT1Frame? [b0, b1, b2, b3] = some f := h
    unfold t1RepairRevComplete t1RepairBackComplete t1RepairRevAdvance
    rw [h']
  rstep_p3 := by
    intro m hm latch scan
    obtain rfl := hm.eq
    exact t1Transition_repairSeek_p3 t1CS.startPhase false false false latch scan
  rstep_p2 := by
    intro m hm latch b3 scan
    obtain rfl := hm.eq
    exact t1Transition_repairSeek_p2 t1CS.startPhase false false b3 latch scan
  rstep_p1 := by
    intro m hm latch b2 b3 scan
    obtain rfl := hm.eq
    exact t1Transition_repairSeek_p1 t1CS.startPhase false b2 b3 latch scan
  rstep_p0 := by
    intro m hm latch b1 b2 b3 scan hne
    obtain rfl := hm.eq
    have hseek : t1RepairBackComplete scan b1 b2 b3 = T1Mode.repairSeek := by
      by_contra hc
      exact hne hc
    rw [show t1RepairRevComplete T1Mode.repairSeek scan b1 b2 b3 =
      T1Mode.repairSeek from hseek]
    unfold t1RepairBackComplete at hseek
    cases hd : decodeT1Frame? [scan, b1, b2, b3] with
    | none => rw [hd] at hseek; simp at hseek
    | some f =>
        rw [hd] at hseek
        refine t1Transition_repairSeek_p0_skip t1CS.startPhase b1 b2 b3 latch
          scan f hd ?_
        cases f with
        | index => exact Or.inl rfl
        | separator => exact Or.inr (Or.inl rfl)
        | finish => exact Or.inr (Or.inr (Or.inl rfl))
        | data v => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩)))
        | output v => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩)))
        | spent | bof | blank | cursor => simp [t1RepairBackAdvance] at hseek
  rstep_p0_stop := by
    intro m hm latch b1 b2 b3 scan hstop
    obtain rfl := hm.eq
    cases hd : decodeT1Frame? [scan, b1, b2, b3] with
    | none =>
        have hc : t1RepairBackComplete scan b1 b2 b3 = T1Mode.reject := by
          simp [t1RepairBackComplete, hd]
        rw [show t1RepairRevComplete T1Mode.repairSeek scan b1 b2 b3 =
          T1Mode.reject from hc]
        exact t1Transition_repairSeek_p0_bad t1CS.startPhase b1 b2 b3 latch scan
          hc
    | some f =>
        have hc : t1RepairBackComplete scan b1 b2 b3 = t1RepairBackAdvance f := by
          simp [t1RepairBackComplete, hd]
        rw [show t1RepairRevComplete T1Mode.repairSeek scan b1 b2 b3 =
          t1RepairBackAdvance f from hc]
        cases f with
        | spent =>
            exact t1Transition_repairSeek_p0_write t1CS.startPhase b1 b2 b3 latch
              scan hd
        | bof =>
            exact t1Transition_repairSeek_p0_done t1CS.startPhase b1 b2 b3 latch
              scan hd
        | blank | cursor =>
            exact t1Transition_repairSeek_p0_bad t1CS.startPhase b1 b2 b3 latch
              scan (by simp [hc, t1RepairBackAdvance])
        | index | separator | finish | data _ | output _ =>
            exact absurd (show t1RepairRevComplete T1Mode.repairSeek scan b1 b2 b3 =
              T1Mode.repairSeek by
                simp [t1RepairRevComplete, hc, t1RepairBackAdvance]) hstop

/-- **T1's repair cycle is an instance of the generic rewrite cycle.**  All ten
cycle tuples are the *existing* standalone table lemmas of `TrueUniformSeek`;
`t1Transition` is not unfolded here and no control table is modified. -/
def t1RepairCycle : FrameRewriteCycle T1State T1Frame T1Mode Bool where
  scanner := t1RepairScanner
  seekMode := .repairSeek
  stopMode := .repairWrite
  marker := .spent
  target := .index
  w0 := false
  w1 := false
  w2 := true
  w3 := false
  wst1 := fun latch => t1State .repairWrite .p1 false false false latch
  wst2 := fun latch => t1State .repairWrite .p2 false false false latch
  wst3 := fun latch => t1State .repairWrite .p3 false false false latch
  bst0 := fun latch => t1State .repairBack .p0 false false false latch
  bst1 := fun latch => t1State .repairBack .p1 false false false latch
  bst2 := fun latch => t1State .repairBack .p2 false false false latch
  bst3 := fun latch => t1State .repairBack .p3 false false false latch
  hopState := fun latch => t1State .repairHop .p0 false false false latch
  seek_reverse := trivial
  seek_nostop := by simp [t1RepairScanner, T1RepairStop]
  marker_stop := rfl
  stop_stops := by simp [t1RepairScanner, T1RepairStop]
  target_bits := rfl
  wstep_p0 := fun latch scan =>
    t1Transition_repairWrite t1CS.startPhase .p0 false false false latch scan
  wstep_p1 := fun latch scan =>
    t1Transition_repairWrite t1CS.startPhase .p1 false false false latch scan
  wstep_p2 := fun latch scan =>
    t1Transition_repairWrite t1CS.startPhase .p2 false false false latch scan
  wstep_p3 := fun latch scan =>
    t1Transition_repairWrite t1CS.startPhase .p3 false false false latch scan
  bstep_p0 := fun latch scan =>
    t1Transition_repairBack t1CS.startPhase .p0 false false false latch scan
  bstep_p1 := fun latch scan =>
    t1Transition_repairBack t1CS.startPhase .p1 false false false latch scan
  bstep_p2 := fun latch scan =>
    t1Transition_repairBack t1CS.startPhase .p2 false false false latch scan
  bstep_p3 := fun latch scan =>
    t1Transition_repairBack t1CS.startPhase .p3 false false false latch scan
  hop_step := fun latch scan =>
    t1Transition_repairHop t1CS.startPhase .p0 false false false latch scan

/-- The T1 four-cell overwrite of an `index` frame is the generic one. -/
private theorem t1WriteFrame_index_eq {L : Nat} (base : Nat)
    (tape : Fin L → Bool) :
    t1WriteFrame base T1Frame.index.bits tape =
      writeFrame4 base false false true false tape :=
  (t1WriteFrame_ascending base false false true false tape).symm

/-- **T1 regression: the repair cycle.**  The statement is
`t1CS_repair_cycle`'s and the proof is the generic
`FrameRewriteCycle.rewriteCycle` at `t1RepairCycle`: thirteen genuine TM steps
turn a single `spent` marker back into an `index` frame and return the control
to the repair scan's entry shape one frame to the left. -/
theorem t1RepairCycle_repair_cycle (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = T1Frame.spent.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base + 3) (by omega) tape .repairSeek .p3
          false false false latch) 13 =
      t1AlignedConfig n (base - 1) (by omega)
        (t1WriteFrame base T1Frame.index.bits tape) .repairSeek .p3
        false false false latch := by
  have h := t1RepairCycle.rewriteCycle n base hpos hsafe tape latch
    (by simpa using hbits)
  rw [t1WriteFrame_index_eq]
  simpa [t1RepairCycle, t1RepairScanner] using h

/-- **T1 regression: the repair cycle on an arbitrary frame list.**  Thirteen
genuine TM steps replace one `spent` frame of an arbitrary surrounding word by
`index`, with the exact resulting tape and the head on the last cell of the
preceding frame. -/
theorem t1RepairCycle_repair_cycle_onList (n : Nat)
    (pre suffix : List T1Frame) (latch : Bool) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < T1M.tapeLength n) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * pre.length + 3) (by omega)
          (t1ListTape ((pre ++ T1Frame.spent :: suffix).flatMap T1Frame.bits))
          .repairSeek .p3 false false false latch) 13 =
      t1AlignedConfig n (4 * pre.length - 1) (by omega)
        (t1ListTape ((pre ++ T1Frame.index :: suffix).flatMap T1Frame.bits))
        .repairSeek .p3 false false false latch := by
  have h := t1RepairCycle.rewriteCycleOnList n pre suffix latch hpre hsafe
  simpa [t1RepairCycle, t1RepairScanner] using h

/-! ## T1: the output write as a leftward frame writer -/
/-- **T1's output write is an instance of the generic leftward writer.**  The
installed frame `output latch` genuinely depends on the carried context. -/
def t1OutWriter : ReverseFrameWriter T1State T1Frame Bool where
  program := t1CS
  phase := t1CS.startPhase
  codec := t1FrameCodec
  target := fun latch => .output latch
  w0 := fun _ => true
  w1 := fun _ => false
  w2 := fun _ => false
  w3 := fun latch => latch
  lst3 := fun latch => t1State .outWriteOut .p3 false false false latch
  lst2 := fun latch => t1State .outWriteOut .p2 false false false latch
  lst1 := fun latch => t1State .outWriteOut .p1 false false false latch
  lst0 := fun latch => t1State .outWriteOut .p0 false false false latch
  exitState := fun _ => t1State .repairSeek .p3 false false false true
  target_bits := by intro latch; cases latch <;> rfl
  lstep_p3 := fun latch scan =>
    t1Transition_outWriteOut t1CS.startPhase .p3 false false false latch scan
  lstep_p2 := fun latch scan =>
    t1Transition_outWriteOut t1CS.startPhase .p2 false false false latch scan
  lstep_p1 := fun latch scan =>
    t1Transition_outWriteOut t1CS.startPhase .p1 false false false latch scan
  lstep_p0 := fun latch scan =>
    t1Transition_outWriteOut t1CS.startPhase .p0 false false false latch scan

private theorem t1WriteFrame_output_eq {L : Nat} (base : Nat) (latch : Bool)
    (tape : Fin L → Bool) :
    t1WriteFrame base (T1Frame.output latch).bits tape =
      writeFrame4 base true false false latch tape := by
  cases latch <;> exact (t1WriteFrame_ascending base true false false _ tape).symm

/-- **T1 regression: the output write.**  The statement is
`t1CS_outWriteOut_frame`'s and the proof is the generic
`ReverseFrameWriter.writeMacrostepLeft` at `t1OutWriter`: four genuine
right-to-left steps install `output latch` and leave the head on the last cell
of the preceding frame, in the repair scan, with the latch set. -/
theorem t1OutWriter_outWriteOut_frame (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base + 3) (by omega) tape .outWriteOut .p3
          false false false latch) 4 =
      t1AlignedConfig n (base - 1) (by omega)
        (t1WriteFrame base (T1Frame.output latch).bits tape) .repairSeek .p3
        false false false true := by
  have h := t1OutWriter.writeMacrostepLeft n base hpos hsafe tape latch
  rw [t1WriteFrame_output_eq]
  simpa [t1OutWriter] using h

/-! ## G1: the seek driver at the existing rewind modes -/
/-- **The generic seek-until-marker at G1's existing rewind.**  An arbitrary run
of non-anchor frames is crossed right to left and the anchor read, in exactly
`4 * tail.length + 4` genuine TM steps, landing at head `0` in the pass-B
handoff with the list-backed tape and the whole `G1Ctx` untouched.  No control
table is touched; `bRoundStart` stays idle. -/
theorem g1RevScanner_seek_bof (n : Nat) (tail suffix : List G1Frame)
    (ctx : G1Ctx) (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * tail.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * tail.length + 3) (by omega)
          (g1ListTape ((.bof :: tail ++ suffix).flatMap G1Frame.bits))
          .rewind .p3 false false false ctx) (4 * tail.length + 4) =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape ((.bof :: tail ++ suffix).flatMap G1Frame.bits))
        .readBStart .p0 false false false ctx := by
  have hskip : ∀ f ∈ tail, g1RevScanner.revAdvance .rewind f = .rewind := by
    intro f hf
    have hfne := hne f hf
    cases f <;> simp_all [g1RevAdvance]
  have h := g1RevScanner.revSeekToMarker n [] .bof tail suffix .rewind ctx
    trivial (by simp [G1RewindStop]) hskip rfl (by simpa using hsafe)
  simpa [g1RevScanner] using h

/-! ## G1: the exact obligation of the deferred destructive walk -/
/-- **What the next G1 slice must build.**  A rewrite cycle *of the fixed
control `g1CS`*: the program equation is the whole content, since a cycle at
any other program says nothing about `G1M`.  `g1CS` has no write, walk-back or
hop rows today, so this structure has no inhabitant in this development and
nothing below claims one. -/
structure G1RewriteCycleObligation where
  cycle : FrameRewriteCycle G1State G1Frame G1Mode G1Ctx
  program_eq : cycle.scanner.program = g1CS
  codec_eq : cycle.scanner.codec = g1FrameCodec
  marker_eq : cycle.marker = G1Frame.index
  target_eq : cycle.target = G1Frame.spent

/-- Such a cycle's machine is literally the fixed G1 machine. -/
theorem G1RewriteCycleObligation.machine_eq (O : G1RewriteCycleObligation) :
    O.cycle.scanner.machine = G1M :=
  congrArg (fun U : ConstStatePhasedProgram G1State => U.toPhased.toTM)
    O.program_eq

/-- **The obligation, discharged forward.**  Given the missing cycle, the
thirteen-step `index ↦ spent` rewrite on an arbitrary G1 frame list is the
generic theorem verbatim.  This is a *conditional* statement: no G1 execution
past `bRoundStart` is claimed anywhere, because `G1RewriteCycleObligation` is
not inhabited here. -/
theorem G1RewriteCycleObligation.rewrite_cycle (O : G1RewriteCycleObligation)
    (n : Nat) (pre suffix : List G1Frame) (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < O.cycle.scanner.machine.tapeLength n) :
    TM.runConfig (M := O.cycle.scanner.machine)
        (O.cycle.scanner.revAligned n (4 * pre.length + 3) (by omega)
          (frameListTape
            ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
          O.cycle.seekMode ctx) 13 =
      O.cycle.scanner.revAligned n (4 * pre.length - 1) (by omega)
        (frameListTape
          ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        O.cycle.seekMode ctx := by
  have h := O.cycle.rewriteCycleOnList n pre suffix ctx hpre hsafe
  rw [O.marker_eq, O.target_eq, O.codec_eq] at h
  exact h

end Pnp3.Internal.PsubsetPpoly.TM
