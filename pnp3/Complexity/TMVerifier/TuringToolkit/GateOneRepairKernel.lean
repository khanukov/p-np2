import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycle
import Complexity.TMVerifier.TuringToolkit.GateOneWalkDriver

/-!
# G1 operand-2 repair sweep: the kernel instances and the generic pass

**Progress classification: Infrastructure.**

The executable half of the Repair-1 slice.  `GateOneControl` supplies the repair
rows and their tuple lemmas; this module turns them into **two concrete
instances of the generic frame kernels** — `g1RepairScanner`
(`ReverseFrameScanner`: the reverse repair scan, stopping on a `spent` unit at
the write handoff or on the `bof` anchor at the terminal handoff) and
`g1RepairCycle` (`FrameRewriteCycle`: `spent ↦ index`, the exact mirror of T1's
`t1RepairCycle`) — and into exact `TM.runConfig` macros on an **arbitrary
surrounding frame list**: the thirteen-step cycle (`g1CS_repair_cycle_onList`,
`4 + 4 + 4 + 1`, head `4p + 3 ↦ 4p - 1`), the combined seek/repair step
(`g1CS_repair_seek_and_repair`), the single skipped frame
(`g1CS_repair_frame_skip`), the read-only skip of a whole run
(`g1CS_repair_scan_skip`), the **iteration** turning a contiguous run of `s`
consumed units back into `s` `index` frames in exactly `13 * s` steps
(`g1CS_repair_spent_run`), and the anchor read plus dispatch
(`g1CS_repair_finish`).  `g1CS_repair_pass_exact` composes them into the generic
repair pass, with the same closed cost `g1RepairPassSteps a s m =
4m + 13s + 4a + 5` as T1's `t1RepairSteps`.

**Everything here is caller-supplied.**  Every statement below takes the
caller's `n`, head-safety bound, frame list and `G1Ctx`, and **no route of the
machine reaches the sweep in this slice**: `g1_repair_unreachable_forward` shows
no `g1Advance` row produces a repair mode, `g1_repair_modes_stuck` shows all
five are stuck at the frame table, and `readAResetStart` is still the idle
handoff `GateOneControl` leaves it.

**Explicit deferrals.**  Wiring the sweep behind the operand-2 read, the
request-specific layout split and the composed `initialConfig` capstones are
**Repair-2**; no statement of this module mentions `G1M.initialConfig`, a
request, a repair driver, `readAStart` doing any work, pass A, the combine step,
the output write, `TM.accepts`, a full-clock theorem or the gate-semantics
correctness statement.  The out-of-range boundary `bOOB` is untouched: it is
still the stable sink of `GateOneReadB`, and no repair or rejection is claimed
for it.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- **The five repair modes are unreachable from the forward frame table.**  No
mode/frame pair completes into any of them, so the sweep is never entered by a
frame read.  The mirror of `GateOneRouting.g1_bRoundStart_unreachable`. -/
theorem g1_repair_unreachable_forward (mode : G1Mode) (frame : G1Frame) :
    g1Advance mode frame ≠ .bRepairSeek ∧
      g1Advance mode frame ≠ .bRepairWrite ∧
      g1Advance mode frame ≠ .bRepairBack ∧
      g1Advance mode frame ≠ .bRepairHop ∧
      g1Advance mode frame ≠ .bRepairDone := by
  revert mode frame; decide

/-- **All five repair modes are stuck at the frame table.**  They read right to
left or write; none of them has a successful `g1Advance` row, so the validation
grammar is untouched by their addition. -/
theorem g1_repair_modes_stuck :
    G1Stuck .bRepairSeek ∧ G1Stuck .bRepairWrite ∧ G1Stuck .bRepairBack ∧
      G1Stuck .bRepairHop ∧ G1Stuck .bRepairDone := by decide

/-- Frames the repair scan crosses: **everything except** a consumed operand-2
unit and the anchor — on the canonical layout, every nonspent frame (the tag
run, both `argSep`s, both index fields, the `separator`, the data region, the
destination frame, the terminator and the trailing blank). -/
def G1RepairSkip : G1Frame → Prop
  | .spent => False
  | .bof => False
  | _ => True

instance : DecidablePred G1RepairSkip := fun f => by
  cases f <;> first | exact isTrue trivial | exact isFalse id

/-- G1's right-to-left repair table: a `spent` unit stops the pass at the write
handoff, the `bof` anchor stops it at the terminal handoff, every other frame
continues it one frame further left. -/
def g1RepairRevAdvance : G1Mode → G1Frame → G1Mode
  | _, .spent => .bRepairWrite
  | _, .bof => .bRepairDone
  | _, _ => .bRepairSeek

/-- The bit-level form of `g1RepairRevAdvance`, as `g1Transition` computes it. -/
def g1RepairRevComplete (_mode : G1Mode) (b0 b1 b2 b3 : Bool) : G1Mode :=
  match decodeG1Frame? [b0, b1, b2, b3] with
  | some .spent => .bRepairWrite
  | some .bof => .bRepairDone
  | _ => .bRepairSeek

/-- The single G1 mode of the repair sweep that reads frames right to left. -/
def G1RepairMode : G1Mode → Prop
  | .bRepairSeek => True
  | _ => False

theorem G1RepairMode.eq {m : G1Mode} (h : G1RepairMode m) : m = .bRepairSeek := by
  cases m <;> simp_all [G1RepairMode]

/-- The repair scan stops at the write handoff or at the terminal handoff. -/
def G1RepairStop (mode : G1Mode) : Prop :=
  mode = .bRepairWrite ∨ mode = .bRepairDone

theorem g1RepairRevAdvance_of_skip {m : G1Mode} {f : G1Frame}
    (h : G1RepairSkip f) : g1RepairRevAdvance m f = .bRepairSeek := by
  cases f <;> first | rfl | exact (show False from h).elim

private theorem g1RepairRevComplete_cases (m : G1Mode) (b0 b1 b2 b3 : Bool) :
    (g1RepairRevComplete m b0 b1 b2 b3 = .bRepairWrite ∧
        decodeG1Frame? [b0, b1, b2, b3] = some .spent) ∨
      (g1RepairRevComplete m b0 b1 b2 b3 = .bRepairDone ∧
        decodeG1Frame? [b0, b1, b2, b3] = some .bof) ∨
      (g1RepairRevComplete m b0 b1 b2 b3 = .bRepairSeek ∧
        decodeG1Frame? [b0, b1, b2, b3] ≠ some .spent ∧
        decodeG1Frame? [b0, b1, b2, b3] ≠ some .bof) := by
  unfold g1RepairRevComplete
  cases hd : decodeG1Frame? [b0, b1, b2, b3] with
  | none => exact Or.inr (Or.inr ⟨rfl, by simp, by simp⟩)
  | some f => cases f <;> simp_all

/-- **G1's repair scan is an instance of the generic reverse kernel.**  The
carried `G1Ctx` triple is threaded through unchanged, so whatever the caller
latched in `vB` survives the whole sweep.  All six obligations are standalone
tuple lemmas of `GateOneControl`; `g1Transition` is not unfolded here. -/
def g1RepairScanner : ReverseFrameScanner G1State G1Frame G1Mode G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  Stop := G1RepairStop
  revAdvance := g1RepairRevAdvance
  revComplete := g1RepairRevComplete
  Reverse := G1RepairMode
  rst3 := fun m ctx => g1State m .p3 false false false ctx
  rst2 := fun m ctx b3 => g1State m .p2 false false b3 ctx
  rst1 := fun m ctx b2 b3 => g1State m .p1 false b2 b3 ctx
  rst0 := fun m ctx b1 b2 b3 => g1State m .p0 b1 b2 b3 ctx
  stopState := fun m ctx => g1State m .p0 false false false ctx
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    have h' : decodeG1Frame? [b0, b1, b2, b3] = some f := h
    unfold g1RepairRevComplete
    rw [h']
    cases f <;> rfl
  rstep_p3 := by
    intro m hm ctx scan
    obtain rfl := hm.eq
    exact g1Transition_bRepairSeek_p3 g1CS.startPhase false false false scan ctx
  rstep_p2 := by
    intro m hm ctx b3 scan
    obtain rfl := hm.eq
    exact g1Transition_bRepairSeek_p2 g1CS.startPhase false false b3 scan ctx
  rstep_p1 := by
    intro m hm ctx b2 b3 scan
    obtain rfl := hm.eq
    exact g1Transition_bRepairSeek_p1 g1CS.startPhase false b2 b3 scan ctx
  rstep_p0 := by
    intro m hm ctx b1 b2 b3 scan hne
    obtain rfl := hm.eq
    rcases g1RepairRevComplete_cases .bRepairSeek scan b1 b2 b3 with
      ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, hs, hb⟩
    · exact absurd (he ▸ Or.inl rfl : G1RepairStop _) hne
    · exact absurd (he ▸ Or.inr rfl : G1RepairStop _) hne
    · rw [he]
      exact g1Transition_bRepairSeek_p0_other g1CS.startPhase b1 b2 b3 scan ctx
        hs hb
  rstep_p0_stop := by
    intro m hm ctx b1 b2 b3 scan hstop
    obtain rfl := hm.eq
    rcases g1RepairRevComplete_cases .bRepairSeek scan b1 b2 b3 with
      ⟨he, hd⟩ | ⟨he, hd⟩ | ⟨he, -, -⟩
    · rw [he]
      exact g1Transition_bRepairSeek_p0_spent g1CS.startPhase b1 b2 b3 scan ctx hd
    · rw [he]
      exact g1Transition_bRepairSeek_p0_bof g1CS.startPhase b1 b2 b3 scan ctx hd
    · rw [he] at hstop
      rcases hstop with h | h <;> exact absurd h (by decide)

@[simp] theorem g1RepairScanner_machine : g1RepairScanner.machine = G1M := rfl

/-- **G1's `spent ↦ index` repair is an instance of the generic rewrite
cycle.**  The nine cycle tuples are the standalone `g1Transition_bRepairWrite`,
`g1Transition_bRepairBack` and `g1Transition_bRepairHop` lemmas; the write half
is entered at the scanner's own stop state, so the two halves are glued by
definitional equality.  The exact mirror of `t1RepairCycle`. -/
def g1RepairCycle : FrameRewriteCycle G1State G1Frame G1Mode G1Ctx where
  scanner := g1RepairScanner
  seekMode := .bRepairSeek
  stopMode := .bRepairWrite
  marker := .spent
  target := .index
  w0 := false
  w1 := false
  w2 := true
  w3 := true
  wst1 := fun ctx => g1State .bRepairWrite .p1 false false false ctx
  wst2 := fun ctx => g1State .bRepairWrite .p2 false false false ctx
  wst3 := fun ctx => g1State .bRepairWrite .p3 false false false ctx
  bst0 := fun ctx => g1State .bRepairBack .p0 false false false ctx
  bst1 := fun ctx => g1State .bRepairBack .p1 false false false ctx
  bst2 := fun ctx => g1State .bRepairBack .p2 false false false ctx
  bst3 := fun ctx => g1State .bRepairBack .p3 false false false ctx
  hopState := fun ctx => g1State .bRepairHop .p0 false false false ctx
  seek_reverse := trivial
  seek_nostop := by simp [g1RepairScanner, G1RepairStop]
  marker_stop := rfl
  stop_stops := Or.inl rfl
  target_bits := rfl
  wstep_p0 := fun ctx scan =>
    g1Transition_bRepairWrite g1CS.startPhase .p0 false false false scan ctx
  wstep_p1 := fun ctx scan =>
    g1Transition_bRepairWrite g1CS.startPhase .p1 false false false scan ctx
  wstep_p2 := fun ctx scan =>
    g1Transition_bRepairWrite g1CS.startPhase .p2 false false false scan ctx
  wstep_p3 := fun ctx scan =>
    g1Transition_bRepairWrite g1CS.startPhase .p3 false false false scan ctx
  bstep_p0 := fun ctx scan =>
    g1Transition_bRepairBack g1CS.startPhase .p0 false false false scan ctx
  bstep_p1 := fun ctx scan =>
    g1Transition_bRepairBack g1CS.startPhase .p1 false false false scan ctx
  bstep_p2 := fun ctx scan =>
    g1Transition_bRepairBack g1CS.startPhase .p2 false false false scan ctx
  bstep_p3 := fun ctx scan =>
    g1Transition_bRepairBack g1CS.startPhase .p3 false false false scan ctx
  hop_step := fun ctx scan =>
    g1Transition_bRepairHop g1CS.startPhase .p0 false false false scan ctx

/-- **The thirteen-step `spent ↦ index` cycle on an arbitrary frame list.**
Thirteen genuine steps turn `pre ++ spent :: suffix` into `pre ++ index ::
suffix` — nothing outside those four cells changes — with the head going from
the last cell of the repaired frame to the last cell of the one before it, the
control back in the reverse-read entry shape and the `G1Ctx` preserved. -/
theorem g1CS_repair_cycle_onList (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false ctx) 13 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx :=
  g1RepairCycle.rewriteCycleOnList n pre suffix ctx hpre hsafe

/-- **Seek, then repair.**  From the last cell of the last frame of an arbitrary
run that needs no repair, `4 * skipped.length + 13` genuine steps cross the run
right to left, turn the `spent` unit that ends it back into an `index`, and
return to the scan's entry shape one frame further left. -/
theorem g1CS_repair_seek_and_repair (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.spent :: skipped ++ suffix).flatMap
            G1Frame.bits))
          .bRepairSeek .p3 false false false ctx)
        (4 * skipped.length + 13) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap
          G1Frame.bits))
        .bRepairSeek .p3 false false false ctx :=
  g1RepairCycle.seekAndRewrite n pre skipped suffix ctx hpre
    (fun f hf => g1RepairRevAdvance_of_skip (hskip f hf)) hsafe

/-- **One skipped frame.**  Four genuine steps read a frame that needs no repair
right to left, leaving the head on the last cell of its predecessor. -/
theorem g1CS_repair_frame_skip (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : G1RepairSkip f) (hbits : physicalBitsAt hsafe tape = f.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .bRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n (base - 1) (by omega) tape .bRepairSeek .p3
        false false false ctx := by
  have hns : ¬ g1RepairScanner.Stop
      (g1RepairScanner.revAdvance .bRepairSeek f) := by
    show ¬ G1RepairStop (g1RepairRevAdvance .bRepairSeek f)
    rw [g1RepairRevAdvance_of_skip hf]
    simp [G1RepairStop]
  have h := g1RepairScanner.revFrameMacrostep n base hpos hsafe tape
    .bRepairSeek f ctx trivial hns hbits
  rw [show g1RepairScanner.revAdvance .bRepairSeek f = .bRepairSeek from
    g1RepairRevAdvance_of_skip hf] at h
  exact h

/-- **Backward multi-frame skip.**  A whole run of frames that need no repair is
crossed in exactly four genuine steps per frame, tape and context untouched.
Structurally the mirror of `t1CS_repair_scan_skip`. -/
theorem g1CS_repair_scan_skip (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hsafe : 4 * (pre.length + skipped.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) - 1) (by omega)
          (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false ctx)
        (4 * skipped.length) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx := by
  induction skipped generalizing pre with
  | nil => simp
  | cons f rest ih =>
      have hf : G1RepairSkip f := hskip f (by simp)
      have hrest : ∀ g ∈ rest, G1RepairSkip g :=
        fun g hg => hskip g (by simp [hg])
      have hlen : (pre ++ [f]).length = pre.length + 1 := by simp
      have hsafe' : 4 * ((pre ++ [f]).length + rest.length) <
          G1M.tapeLength n := by
        rw [hlen]
        simp only [List.length_cons] at hsafe
        omega
      have hbase : 4 * pre.length + 4 < G1M.tapeLength n := by
        simp only [List.length_cons] at hsafe
        omega
      have hIH := ih (pre ++ [f]) (by omega) hrest hsafe'
      simp only [hlen, show 4 * (pre.length + 1 + rest.length) - 1 =
          4 * (pre.length + (rest.length + 1)) - 1 from by omega,
        show 4 * (pre.length + 1) - 1 = 4 * pre.length + 3 from by omega,
        List.append_assoc, List.nil_append, List.cons_append] at hIH
      have hbits : physicalBitsAt hbase
          (g1ListTape (n := n)
            ((pre ++ f :: (rest ++ suffix)).flatMap G1Frame.bits)) = f.bits :=
        physicalBitsAt_flatMap g1FrameCodec pre (rest ++ suffix) f hbase
      have hstep := g1CS_repair_frame_skip n (4 * pre.length) (by omega) hbase
        (g1ListTape (n := n)
          ((pre ++ f :: (rest ++ suffix)).flatMap G1Frame.bits))
        ctx f hf hbits
      rw [show 4 * (f :: rest).length = 4 * rest.length + 4 by simp; omega,
        runConfig_add]
      simp only [List.length_cons, List.append_assoc, List.cons_append]
      rw [hIH, hstep]

/-- **The repair induction.**  A contiguous run of `s` consumed units is turned
back into `s` `index` frames in exactly `13 * s` genuine steps, the head ending
on the last cell of the frame preceding the run.  Nothing else is touched. -/
theorem g1CS_repair_spent_run (n : Nat) (pre suffix : List G1Frame) (s : Nat)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * (pre.length + s) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + s) - 1) (by omega)
          (g1ListTape ((pre ++ List.replicate s G1Frame.spent ++
            suffix).flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false ctx) (13 * s) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ List.replicate s G1Frame.index ++
          suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx := by
  induction s generalizing pre with
  | zero => simp
  | succ s ih =>
      have hlen : (pre ++ [G1Frame.spent]).length = pre.length + 1 := by simp
      have hsafe' : 4 * ((pre ++ [G1Frame.spent]).length + s) <
          G1M.tapeLength n := by
        rw [hlen]; omega
      have hbase : 4 * pre.length + 4 < G1M.tapeLength n := by omega
      have hIH := ih (pre ++ [G1Frame.spent]) (by omega) hsafe'
      simp only [hlen,
        show 4 * (pre.length + 1 + s) - 1 = 4 * (pre.length + (s + 1)) - 1
          from by omega,
        show 4 * (pre.length + 1) - 1 = 4 * pre.length + 3 from by omega,
        List.append_assoc, List.cons_append, List.nil_append] at hIH
      have hcycle := g1CS_repair_cycle_onList n pre
        (List.replicate s G1Frame.index ++ suffix) ctx hpre hbase
      rw [show 13 * (s + 1) = 13 * s + 13 from by omega, runConfig_add]
      simp only [List.replicate_succ, List.append_assoc, List.cons_append]
        at hIH hcycle ⊢
      rw [hIH, hcycle]

/-- **The terminal dispatch of the repair sweep, executed.**  One stationary
step on the anchor's first cell hands off to the existing idle `readAStart` with
the tape, the head and the whole `G1Ctx` untouched. -/
theorem g1CS_step_repairDone (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .bRepairDone .p0 false false false ctx) 1 =
      g1AlignedConfig n h hh tape .readAStart .p0 false false false ctx := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape (g1RepairDoneState ctx)
    (g1ReadAState ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_bRepairDone phase .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-- **The end of the sweep.**  The anchor read plus the terminal dispatch: four
genuine steps read the `bof` frame right to left — the anchor stops the pass, so
the fourth *stays* on physical cell zero — and one more dispatches, so five
steps put the head on cell zero and the control in `readAStart`, with the tape
and the whole `G1Ctx` — in particular whatever the caller latched in `vB` —
unchanged. -/
theorem g1CS_repair_finish (n : Nat) (suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 3 (by omega)
          (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false ctx) 5 =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .readAStart .p0 false false false ctx := by
  have hsafe0 : (0 : Nat) + 4 < G1M.tapeLength n := by omega
  have hbits : physicalBitsAt hsafe0
      (g1ListTape (n := n) ((G1Frame.bof :: suffix).flatMap G1Frame.bits)) =
      G1Frame.bof.bits := by
    have h := physicalBitsAt_flatMap g1FrameCodec ([] : List G1Frame) suffix
      G1Frame.bof (by simpa using hsafe0)
    simpa using h
  have hanchor : TM.runConfig (M := G1M)
      (g1AlignedConfig n 3 (by omega)
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx) 4 =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .bRepairDone .p0 false false false ctx := by
    have h := g1RepairScanner.revAnchorStep n 0 hsafe0
      (g1ListTape (n := n) ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
      .bRepairSeek G1Frame.bof ctx trivial (Or.inr rfl) hbits
    simpa using h
  rw [show (5 : Nat) = 4 + 1 from rfl, runConfig_add, hanchor]
  exact g1CS_step_repairDone n 0 (by omega) _ ctx

/-- **The cost of one repair pass.**  `m` frames skipped to the right of the
consumed run, `s` units repaired, `a` frames skipped between the anchor and the
run, plus the anchor read and the terminal dispatch.  Literally T1's
`t1RepairSteps`. -/
def g1RepairPassSteps (a s m : Nat) : Nat := 4 * m + 13 * s + 4 * a + 5

/-- **The generic repair pass, end to end.**  From the repair scan's entry shape
on the last cell of the rightmost frame it has to visit, the machine skips
`mid`, repairs the whole consumed run, skips `left`, reads the anchor and
dispatches — landing on head `0` in `readAStart` with the carried context `ctx`
**unchanged**.  The tape statement is exact: the only change is
`spent^s ↦ index^s`, so `left`, `mid` and `tail` are bit-for-bit preserved and
no designated consumed unit remains in the swept run.  This is the exact mirror of
`t1CS_repair_pass_exact`, at a different fixed control and with an untouched
context instead of a cleared latch.

The frame list, `n`, the safety bound and `ctx` are all the **caller's**: no
request, no layout split and no run from `G1M.initialConfig` occurs here. -/
theorem g1CS_repair_pass_exact (n s : Nat) (left mid tail : List G1Frame)
    (ctx : G1Ctx) (hleft : ∀ f ∈ left, G1RepairSkip f)
    (hmid : ∀ f ∈ mid, G1RepairSkip f)
    (hsafe : 4 * (1 + left.length + s + mid.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (1 + left.length + s + mid.length) - 1)
          (by omega)
          (g1ListTape (([G1Frame.bof] ++ left ++
            List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
            G1Frame.bits))
          .bRepairSeek .p3 false false false ctx)
        (g1RepairPassSteps left.length s mid.length) =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape (([G1Frame.bof] ++ left ++
          List.replicate s G1Frame.index ++ mid ++ tail).flatMap G1Frame.bits))
        .readAStart .p0 false false false ctx := by
  have hlenA : ([G1Frame.bof] ++ left ++
      List.replicate s G1Frame.spent).length = 1 + left.length + s := by
    simp only [List.length_append, List.length_replicate, List.length_singleton]
  have hlenB : ([G1Frame.bof] ++ left).length = 1 + left.length := by
    simp only [List.length_append, List.length_singleton]
  have hlenC : ([G1Frame.bof] : List G1Frame).length = 1 := rfl
  -- Phase A: skip `mid`, right to left.
  have hA := g1CS_repair_scan_skip n
    ([G1Frame.bof] ++ left ++ List.replicate s G1Frame.spent) mid tail ctx
    (by simp only [hlenA]; omega) hmid (by simp only [hlenA]; exact hsafe)
  simp only [hlenA] at hA
  -- Phase B: repair the whole consumed run.
  have hB := g1CS_repair_spent_run n ([G1Frame.bof] ++ left) (mid ++ tail) s ctx
    (by simp only [hlenB]; omega) (by simp only [hlenB]; omega)
  simp only [hlenB] at hB
  -- Phase C: skip everything between the anchor and the run.
  have hC := g1CS_repair_scan_skip n [G1Frame.bof] left
    (List.replicate s G1Frame.index ++ mid ++ tail) ctx (by simp) hleft
    (by simp only [hlenC]; omega)
  simp only [hlenC, show 4 * 1 - 1 = 3 from rfl] at hC
  -- Phase D: the anchor read and the terminal dispatch.
  have hD := g1CS_repair_finish n
    (left ++ List.replicate s G1Frame.index ++ mid ++ tail) ctx (by omega)
  have hsplit : g1RepairPassSteps left.length s mid.length =
      4 * mid.length + (13 * s + (4 * left.length + 5)) := by
    simp only [g1RepairPassSteps]; omega
  rw [hsplit, runConfig_add, runConfig_add, runConfig_add]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
    at hA hB hC hD ⊢
  rw [hA, hB, hC, hD]

end Pnp3.Internal.PsubsetPpoly.TM
