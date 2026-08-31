import Complexity.TMVerifier.TuringToolkit.GateOnePassBTraceSafety

/-!
# GN-3B2c2: terminal pass-B cleanup and one repair-cycle trace safety (2026-08-31)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module starts at the existing successful terminal walk configuration
`g1WalkConfig r r.arg2 ...`.  It follows the already-proved schedule

`(8a + 8) + (8a + 12) + 4 + 4`

through exhaustion detection, the read-only return to the cursor, terminal
turn and `cursor ↦ data` cleanup.  The resulting exact
`readAResetStart` boundary is then followed through the existing repair
schedule

`1 + 4 * mid.length + 13 * s + 4 * left.length + 5`

to the canonical head-zero `readAStart` boundary.  No new execution schedule
or endpoint is introduced.

The structural records below expose the actual cursor/spent/index words, the
reverse and forward empty-buffer relations, the unchanged context, and the
successful repair path.  They contain no reachability, run-index, safety, or
target-machine field.  Local safety is proved at the scanner/macro boundary;
in particular the final `bof` read is stationary and never relies on the tape
head's left clamp.  `blank` and leftover `cursor` remain the repair scanner's
existing reject outcomes; the successful driver path excludes them via
`G1RepairSkip` exactly where the existing repair theorem does.

There is no induction over arbitrary operand-2 rounds here.  The real-initial
literal capstone uses the already-proved one-round `arg2 = 1` execution and
stops exactly at `readAStart`.  Pass A, the full gate, `ShiftRunSafe`, a GN
controller/clock, output, verdict and acceptance are outside this module.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

private theorem g1Terminal_getn {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) (hj : j < l.length) : l[j] = v := by
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

private theorem g1Terminal_drop_cons (l : List Bool) (j : Nat)
    (hj : j < l.length) : l.drop j = l[j] :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
      cases j with
      | zero => simp
      | succ j => exact ih j (by simpa using hj)

private theorem g1Terminal_runSafe_one {W : Nat}
    (c : Configuration (M := G1M) W) (h : G1LocalStepSafe c) :
    G1RunSafe c 1 := by
  simpa using G1RunSafe.succ (G1RunSafe.empty c) h

private theorem g1Terminal_step_head_le_next_add_one {W : Nat}
    (c : Configuration (M := G1M) W) :
    (c.head : Nat) ≤ ((TM.stepConfig (M := G1M) c).head : Nat) + 1 := by
  rw [stepConfig_head]
  generalize hm : (G1M.step c.state (c.tape c.head)).snd.snd = move
  cases move with
  | stay => simp
  | left =>
      by_cases hzero : (c.head : Nat) = 0
      · simp [hzero]
      · rw [Configuration.moveHead_left_val_of_pos c (by omega)]
        omega
  | right =>
      by_cases hright : (c.head : Nat) + 1 < G1M.tapeLength W
      · rw [Configuration.moveHead_right_lt c hright]
        change (c.head : Nat) ≤ (c.head : Nat) + 1 + 1
        omega
      · rw [Configuration.moveHead_right_clamp c hright]
        exact Nat.le_succ _

private theorem g1Terminal_run_head_start_le_add {W k : Nat}
    (c : Configuration (M := G1M) W) :
    (c.head : Nat) ≤ ((TM.runConfig (M := G1M) c k).head : Nat) + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [runConfig_succ]
      have hs := g1Terminal_step_head_le_next_add_one
        (TM.runConfig (M := G1M) c k)
      omega

/-! ## Structural terminal and repair paths -/

/-- The successful terminal-B word split at its unique cursor.  The buffer
fields pin the actual empty entry buffers of the merged reverse/forward
scanner APIs; all other fields are physical frame, tape and context facts. -/
structure G1TerminalBShape (r : G1Request) (v : Bool) where
  pre : List G1Frame
  skipped : List G1Frame
  tail : List G1Frame
  walk_split : g1WalkFrames r r.arg2 =
    pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor :: tail
  pre_length : pre.length = r.tag.units + r.arg1 + 2
  skipped_length : skipped.length = 2 * r.arg2 + 1
  cursor_length : pre.length + skipped.length + 1 = g1WalkCursor r r.arg2
  skipped_path : ∀ f ∈ skipped, G1WalkSkip f
  reverse_buffer : G1ReverseBufferCoherent G1Frame.cursor .p3 false false false
  forward_buffer : G1ForwardBufferCoherent G1Frame.argSep .p0 false false false
  context : (g1Ctx0.withVB v).vB = v

/-- The successful repair path over the exact driver split.  `pending` and
`repaired` explicitly relate the `spent` and `index` runs; the clean fields
exclude precisely the two reserved decoded frames that would take the merged
scanner's reject row. -/
structure G1RepairSweepShape (r : G1Request) (s : Nat) where
  left : List G1Frame
  mid : List G1Frame
  tail : List G1Frame
  pending : g1BSpentFrames r s =
    [G1Frame.bof] ++ left ++ List.replicate s G1Frame.spent ++ mid ++ tail
  repaired : [G1Frame.bof] ++ left ++ List.replicate s G1Frame.index ++
      mid ++ tail = encodeG1Frames r ++ [G1Frame.blank]
  left_path : ∀ f ∈ left, G1RepairSkip f
  mid_path : ∀ f ∈ mid, G1RepairSkip f
  left_clean : G1Frame.blank ∉ left ∧ G1Frame.cursor ∉ left
  mid_clean : G1Frame.blank ∉ mid ∧ G1Frame.cursor ∉ mid
  reverse_buffer : G1ReverseBufferCoherent G1Frame.bof .p3 false false false
  spent_count : (g1BSpentFrames r s).count G1Frame.spent = s
  cursor_count : (g1BSpentFrames r s).count G1Frame.cursor = 0
  index_count : (g1BSpentFrames r s).count G1Frame.index =
    r.arg1 + (r.arg2 - s)

/-- The exact terminal shape, obtained from the existing walk layout. -/
def G1TerminalBShape.of_request (r : G1Request) (v : Bool)
    (hm : r.arg2 ≤ r.vals.length) :
    G1TerminalBShape r v := by
  let pre := g1ExhPre r
  let skipped := List.replicate r.arg2 G1Frame.spent ++
    [G1Frame.separator] ++ (r.vals.take r.arg2).map G1Frame.data
  let tail := (r.vals.drop (r.arg2 + 1)).map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]
  refine ⟨pre, skipped, tail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pre, skipped, tail, g1WalkFrames, g1ExhPre,
      g1FieldRouteFrames, List.append_assoc]
  · simp [pre]
  · simp [skipped, List.length_take, Nat.min_eq_left hm]
    omega
  · simp [pre, skipped, g1WalkCursor, List.length_take, Nat.min_eq_left hm]
    omega
  · simpa [skipped] using g1WalkSkipRun_mem r.arg2 r.vals
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · rfl

/-- The driver's repair split inhabits the successful structural repair path. -/
def G1RepairSweepShape.of_request (r : G1Request) (s : Nat)
    (hs : s ≤ r.arg2) : G1RepairSweepShape r s := by
  refine ⟨g1RepairLeft r s, g1RepairMid r, g1RepairTail r,
    g1BSpentFrames_repair_split r s, g1RepairFrames_repaired r s hs,
    g1RepairLeft_skip r s, g1RepairMid_skip r, g1RepairLeft_clean r s,
    g1RepairMid_clean r, ⟨rfl, rfl, rfl⟩, g1BSpentFrames_count_spent r s,
    g1BSpentFrames_count_cursor r s, g1BSpentFrames_count_index r s⟩

/-! ## Terminal cleanup safety -/

/-- Safety of the existing reverse exhaustion seek.  This is the merged
right-to-left buffer proof specialised to the terminal `argSep` stop row. -/
theorem g1CS_walk_seek_exhaust_runSafe (r : G1Request)
    (hm : r.arg2 < r.vals.length) (v : Bool)
    (hv : r.vals[r.arg2]? = some v) :
    G1RunSafe (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
      (8 * r.arg2 + 8) := by
  let shape := G1TerminalBShape.of_request r v (by omega)
  have hroom : 4 * (shape.pre.length + shape.skipped.length) + 8 <
      gnLocalSpan (encodeG1 r).length := by
    simp [shape, G1TerminalBShape.of_request, gnLocalSpan, encodeG1_length,
      List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)]
    omega
  have hs := g1Walk_seekToMarker_runSafe
    (W := (encodeG1 r).length) shape.pre .argSep shape.skipped
    (.cursor :: shape.tail) (g1Ctx0.withVB v)
    (fun f hf => g1WalkRevAdvance_of_skip (shape.skipped_path f hf))
    (Or.inr rfl) hroom
  rw [← shape.walk_split] at hs
  have hhead : 4 * (shape.pre.length + shape.skipped.length) + 3 =
      4 * g1WalkCursor r r.arg2 - 1 := by
    have hc := shape.cursor_length
    omega
  have hsteps : 4 * shape.skipped.length + 4 = 8 * r.arg2 + 8 := by
    rw [shape.skipped_length]
    omega
  simpa only [g1WalkConfig, hhead, hsteps] using hs

/-- Safety of the exact exhaustion return from the opening `argSep` through
the spent/data run and the cursor.  `G1ForwardScannerMicrostate` supplies the
forward buffer/path invariant used by `g1Forward_scanFrom_runSafe`. -/
theorem g1CS_walk_exh_to_cursor_runSafe (r : G1Request)
    (hm : r.arg2 < r.vals.length) (v : Bool) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + 2)) (by
          exact lt_of_lt_of_le (by
            simp [gnLocalSpan, encodeG1_length]
            omega) (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
        (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        .bExh .p0 false false false (g1Ctx0.withVB v))
      (8 * r.arg2 + 12) := by
  let shape := G1TerminalBShape.of_request r v (by omega)
  let frames := G1Frame.argSep :: (shape.skipped ++ [G1Frame.cursor])
  have hpath : G1ValidPath .bExh frames := by
    have hfix : ∀ f ∈ shape.skipped, g1Advance .bRet f = .bRet :=
      fun f hf => g1Advance_bRet_of_skip (shape.skipped_path f hf)
    exact ⟨trivial, by decide,
      g1ValidPath_fix (mode := .bRet) trivial [.cursor]
        ⟨trivial, by decide, trivial⟩ shape.skipped hfix⟩
  have hroom : 4 * (shape.pre.length + frames.length) <
      gnLocalSpan (encodeG1 r).length := by
    simp [shape, frames, G1TerminalBShape.of_request, gnLocalSpan,
      encodeG1_length, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hm)]
    omega
  have hs := g1Forward_scanFrom_runSafe
    (W := (encodeG1 r).length) shape.pre frames shape.tail .bExh
    (g1Ctx0.withVB v) hpath hroom
  have hlist : shape.pre ++ frames ++ shape.tail = g1WalkFrames r r.arg2 := by
    rw [shape.walk_split]
    simp [frames, List.append_assoc]
  rw [hlist] at hs
  have hhead : 4 * shape.pre.length = 4 * (r.tag.units + r.arg1 + 2) := by
    rw [shape.pre_length]
  have hsteps : 4 * frames.length = 8 * r.arg2 + 12 := by
    simp [frames, shape.skipped_length]
    omega
  simpa only [hhead, hsteps] using hs

/-- Safety of the four-cell terminal turn and four-cell cursor cleanup. -/
theorem g1CS_walk_terminal_turn_restore_runSafe (r : G1Request)
    (hm : r.arg2 < r.vals.length) (v : Bool) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1WalkCursor r r.arg2 + 1)) (by
          have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
          omega)
        (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        .bTurnFin .p0 false false false (g1Ctx0.withVB v)) 8 := by
  apply g1RunSafe_of_margins
  · simp [g1WalkCursor]
    omega
  · simp [g1WalkCursor, gnLocalSpan, encodeG1_length]
    omega

set_option maxHeartbeats 1000000 in
/-- The complete existing terminal cleanup schedule is safe and reaches its
existing exact `readAResetStart` endpoint. -/
theorem g1CS_walk_terminal_trace_safe (r : G1Request)
    (hm : r.arg2 < r.vals.length) (v : Bool)
    (hv : r.vals[r.arg2]? = some v) :
    G1RunSafe (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
        (16 * r.arg2 + 28) ∧
      TM.runConfig (M := G1M)
          (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
          (16 * r.arg2 + 28) =
        g1AlignedConfig (encodeG1 r).length
          (4 * (g1WalkCursor r r.arg2 + 1)) (by
            have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
            omega)
          (g1ListTape ((g1BSpentFrames r r.arg2).flatMap G1Frame.bits))
          .readAResetStart .p0 false false false (g1Ctx0.withVB v) := by
  have hA := g1CS_walk_seek_exhaust_runSafe r hm v hv
  let shape := G1TerminalBShape.of_request r v (by omega)
  have hAexact := g1CS_walk_seek_exhaust (encodeG1 r).length shape.pre
    shape.skipped (.cursor :: shape.tail) (g1Ctx0.withVB v)
    shape.skipped_path (by
      apply lt_of_lt_of_le (b := gnLocalSpan (encodeG1 r).length)
      · rw [shape.pre_length, shape.skipped_length]
        simp [gnLocalSpan, encodeG1_length]
        omega
      · exact gnLocalSpan_le_g1_tapeLength (encodeG1 r).length)
  rw [← shape.walk_split] at hAexact
  have hAstart : 4 * (shape.pre.length + shape.skipped.length) + 3 =
      4 * g1WalkCursor r r.arg2 - 1 := by
    have hc := shape.cursor_length
    omega
  have hAsteps : 4 * shape.skipped.length + 4 = 8 * r.arg2 + 8 := by
    rw [shape.skipped_length]
    omega
  have hAfinish : 4 * shape.pre.length =
      4 * (r.tag.units + r.arg1 + 2) := by rw [shape.pre_length]
  have hAendpoint : TM.runConfig (M := G1M)
      (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv) (8 * r.arg2 + 8) =
    g1AlignedConfig (encodeG1 r).length
      (4 * (r.tag.units + r.arg1 + 2)) (by
        apply lt_of_lt_of_le (b := gnLocalSpan (encodeG1 r).length)
        · simp [gnLocalSpan, encodeG1_length]
          omega
        · exact gnLocalSpan_le_g1_tapeLength (encodeG1 r).length)
      (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
      .bExh .p0 false false false (g1Ctx0.withVB v) := by
    simpa only [g1WalkConfig, hAstart, hAsteps, hAfinish] using hAexact
  have hB0 := g1CS_walk_exh_to_cursor_runSafe r hm v
  have hB : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
        (8 * r.arg2 + 8)) (8 * r.arg2 + 12) := by
    rw [hAendpoint]
    exact hB0
  have hAB := G1RunSafe.add hA hB
  have hABendpoint : TM.runConfig (M := G1M)
      (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
      ((8 * r.arg2 + 8) + (8 * r.arg2 + 12)) =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1WalkCursor r r.arg2 + 1)) (by
        have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
        omega)
      (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
      .bTurnFin .p0 false false false (g1Ctx0.withVB v) := by
    rw [runConfig_add, hAendpoint]
    have h := g1CS_walk_exh_to_cursor (encodeG1 r).length shape.pre
      shape.skipped shape.tail (g1Ctx0.withVB v) shape.skipped_path (by
        simp [shape, G1TerminalBShape.of_request, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hm)]
        have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
        omega)
    have hlist : shape.pre ++ .argSep :: shape.skipped ++ .cursor :: shape.tail =
        g1WalkFrames r r.arg2 := shape.walk_split.symm
    rw [hlist] at h
    have hstart : 4 * shape.pre.length =
        4 * (r.tag.units + r.arg1 + 2) := by rw [shape.pre_length]
    have hfinish : 4 * (shape.pre.length + (shape.skipped.length + 2)) =
        4 * (g1WalkCursor r r.arg2 + 1) := by
      have hc := shape.cursor_length
      omega
    have hsteps : 4 * (shape.skipped.length + 2) = 8 * r.arg2 + 12 := by
      rw [shape.skipped_length]
      omega
    simpa only [List.length_cons, List.length_append, List.length_singleton,
      hstart, hfinish, hsteps] using h
  have hCD0 := g1CS_walk_terminal_turn_restore_runSafe r hm v
  have hCD : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
        ((8 * r.arg2 + 8) + (8 * r.arg2 + 12))) 8 := by
    rw [hABendpoint]
    exact hCD0
  have hall := G1RunSafe.add hAB hCD
  constructor
  · simpa only [show (8 * r.arg2 + 8) + (8 * r.arg2 + 12) + 8 =
        16 * r.arg2 + 28 by omega] using hall
  · exact g1CS_walk_terminal_exact r hm v hv

/-! ## Repair macro safety -/

/-- Four reverse-buffer microsteps on an interior repair frame are safe.  The
buffer positions are the exact `p3 → p2 → p1 → p0` relation; successful
skip, spent-stop and reject-stop rows are all covered because the frame base is
strictly positive. -/
theorem g1Repair_reverseFrame_runSafe {W base : Nat}
    (tape : Fin (G1M.tapeLength W) → Bool) (ctx : G1Ctx)
    (hroom : base + 4 < gnLocalSpan W)
    (hfinal : 0 < base ∨
      G1RepairStop (g1RepairRevComplete .bRepairSeek
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
        .bRepairSeek .p3 false false false ctx) 4 := by
  let hb0 : base < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb1 : base + 1 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb2 : base + 2 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb3 : base + 3 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let b3 := tape ⟨base + 3, hb3⟩
  let b2 := tape ⟨base + 2, hb2⟩
  let b1 := tape ⟨base + 1, hb1⟩
  let b0 := tape ⟨base, hb0⟩
  let c3 := g1AlignedConfig W (base + 3) hb3 tape .bRepairSeek .p3
    false false false ctx
  let c2 := g1AlignedConfig W (base + 2) hb2 tape .bRepairSeek .p2
    false false b3 ctx
  let c1 := g1AlignedConfig W (base + 1) hb1 tape .bRepairSeek .p1
    false b2 b3 ctx
  let c0 := g1AlignedConfig W base hb0 tape .bRepairSeek .p0 b1 b2 b3 ctx
  have hs3 : TM.stepConfig (M := G1M) c3 = c2 := by
    have h := g1CS_aligned_step_left W (base + 3) hb3 (by omega) tape
      (g1State .bRepairSeek .p3 false false false ctx)
      (g1State .bRepairSeek .p2 false false b3 ctx) _
      (fun phase => g1Transition_bRepairSeek_p3 phase false false false _ ctx)
    rw [writeCell_self] at h
    simpa [c3, c2, b3] using h
  have hs2 : TM.stepConfig (M := G1M) c2 = c1 := by
    have h := g1CS_aligned_step_left W (base + 2) hb2 (by omega) tape
      (g1State .bRepairSeek .p2 false false b3 ctx)
      (g1State .bRepairSeek .p1 false b2 b3 ctx) _
      (fun phase => g1Transition_bRepairSeek_p2 phase false false b3 _ ctx)
    rw [writeCell_self] at h
    simpa [c2, c1, b2] using h
  have hs1 : TM.stepConfig (M := G1M) c1 = c0 := by
    have h := g1CS_aligned_step_left W (base + 1) hb1 (by omega) tape
      (g1State .bRepairSeek .p1 false b2 b3 ctx)
      (g1State .bRepairSeek .p0 b1 b2 b3 ctx) _
      (fun phase => g1Transition_bRepairSeek_p1 phase false b2 b3 _ ctx)
    rw [writeCell_self] at h
    simpa [c1, c0, b1] using h
  have hl3 : G1LocalStepSafe c3 := by
    apply g1LocalStepSafe_of_interior
    all_goals simp [c3] at hroom ⊢
    all_goals omega
  have hl2 : G1LocalStepSafe c2 := by
    apply g1LocalStepSafe_of_interior
    all_goals simp [c2] at hroom ⊢
    all_goals omega
  have hl1 : G1LocalStepSafe c1 := by
    apply g1LocalStepSafe_of_interior
    all_goals simp [c1] at hroom ⊢
    all_goals omega
  have hl0 : G1LocalStepSafe c0 := by
    simp only [G1LocalStepSafe, c0, g1AlignedConfig_head_val,
      g1AlignedConfig_state, g1AlignedConfig_tape]
    refine ⟨by omega, ?_, ?_⟩
    · intro hleft
      by_cases hstop : G1RepairStop
          (g1RepairRevComplete .bRepairSeek b0 b1 b2 b3)
      · change (g1Transition (0 : Fin 1)
          (g1State .bRepairSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
            Move.left at hleft
        have htr := g1RepairScanner.rstep_p0_stop (m := .bRepairSeek) trivial
          ctx b1 b2 b3 b0 hstop
        change g1Transition 0
            (g1State .bRepairSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1RepairStopState
            (g1RepairRevComplete .bRepairSeek b0 b1 b2 b3) ctx,
            b0, Move.stay) at htr
        rw [htr] at hleft
        exact Move.noConfusion hleft
      · rcases hfinal with hpos | hstop'
        · simpa [c0] using hpos
        · exact (hstop (by simpa [b0, b1, b2, b3] using hstop')).elim
    · intro hright
      by_cases hstop : G1RepairStop
          (g1RepairRevComplete .bRepairSeek b0 b1 b2 b3)
      · change (g1Transition (0 : Fin 1)
          (g1State .bRepairSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
            Move.right at hright
        have htr := g1RepairScanner.rstep_p0_stop (m := .bRepairSeek) trivial
          ctx b1 b2 b3 b0 hstop
        change g1Transition 0
            (g1State .bRepairSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1RepairStopState
            (g1RepairRevComplete .bRepairSeek b0 b1 b2 b3) ctx,
            b0, Move.stay) at htr
        rw [htr] at hright
        exact Move.noConfusion hright
      · change (g1Transition (0 : Fin 1)
          (g1State .bRepairSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
            Move.right at hright
        have htr := g1RepairScanner.rstep_p0 (m := .bRepairSeek) trivial ctx
          b1 b2 b3 b0 hstop
        have htr' : g1Transition 0
            (g1State .bRepairSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1State (g1RepairRevComplete .bRepairSeek b0 b1 b2 b3) .p3
            false false false ctx, b0, Move.left) := by
          simpa [g1RepairScanner] using htr
        rw [htr'] at hright
        exact Move.noConfusion hright
  have hr1 : TM.runConfig (M := G1M) c3 1 = c2 := by
    simpa only [runConfig_one] using hs3
  have hr2 : TM.runConfig (M := G1M) c3 2 = c1 := by
    rw [show (2 : Nat) = 1 + 1 by omega, runConfig_add, hr1, runConfig_one,
      hs2]
  have hr3 : TM.runConfig (M := G1M) c3 3 = c0 := by
    rw [show (3 : Nat) = 2 + 1 by omega, runConfig_add, hr2, runConfig_one,
      hs1]
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with
    rfl | rfl | rfl | rfl
  · exact hl3
  · rw [hr1]; exact hl2
  · rw [hr2]; exact hl1
  · rw [hr3]; exact hl0

/-- A whole successful `G1RepairSkip` run is safe.  Exact macro preservation
comes from `g1CS_repair_scan_skip`; the induction merely composes its concrete
four-cell frame steps. -/
theorem g1CS_repair_scan_skip_runSafe {W : Nat}
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hpre : 0 < pre.length) (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hroom : 4 * (pre.length + skipped.length) + 3 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) - 1) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx) (4 * skipped.length) := by
  induction skipped using List.reverseRecOn generalizing suffix with
  | nil => exact G1RunSafe.empty _
  | append_singleton rest frame ih =>
      have hrest : ∀ f ∈ rest, G1RepairSkip f :=
        fun f hf => hskip f (by simp [hf])
      have hlocal : 4 * (pre.length + rest.length) + 4 < gnLocalSpan W := by
        simp only [List.length_append, List.length_singleton] at hroom
        omega
      have hsafe : 4 * (pre.length + rest.length) + 4 <
          G1M.tapeLength W :=
        lt_of_lt_of_le hlocal (gnLocalSpan_le_g1_tapeLength W)
      have hfirst := g1Repair_reverseFrame_runSafe
        (W := W) (base := 4 * (pre.length + rest.length))
        (g1ListTape ((pre ++ (rest ++ [frame]) ++ suffix).flatMap
          G1Frame.bits)) ctx hlocal (Or.inl (by omega))
      have hexact := g1CS_repair_frame_skip W
        (4 * (pre.length + rest.length)) (by omega)
        hsafe
        (g1ListTape ((pre ++ (rest ++ [frame]) ++ suffix).flatMap
          G1Frame.bits)) ctx frame (hskip frame (by simp)) (by
          have h := physicalBitsAt_flatMap (L := G1M.tapeLength W)
            g1FrameCodec (pre ++ rest) suffix frame (by simpa using hsafe)
          simpa [List.append_assoc] using h)
      have htail := ih (suffix := frame :: suffix) hrest (by
        simp only [List.length_append, List.length_singleton] at hroom ⊢
        omega)
      have htail' : G1RunSafe
          (TM.runConfig (M := G1M)
            (g1AlignedConfig W (4 * (pre.length + (rest ++ [frame]).length) - 1)
              (by
                apply lt_of_lt_of_le (b := gnLocalSpan W)
                · simp only [List.length_append, List.length_singleton] at hroom ⊢
                  omega
                · exact gnLocalSpan_le_g1_tapeLength W)
              (g1ListTape ((pre ++ (rest ++ [frame]) ++ suffix).flatMap
                G1Frame.bits)) .bRepairSeek .p3 false false false ctx) 4)
          (4 * rest.length) := by
        have ht : G1RunSafe
            (TM.runConfig (M := G1M)
              (g1AlignedConfig W (4 * (pre.length + rest.length) + 3) (by
                apply lt_of_lt_of_le (b := gnLocalSpan W)
                · omega
                · exact gnLocalSpan_le_g1_tapeLength W)
                (g1ListTape ((pre ++ (rest ++ [frame]) ++ suffix).flatMap
                  G1Frame.bits)) .bRepairSeek .p3 false false false ctx) 4)
            (4 * rest.length) := by
          apply G1RunSafe.transport hexact.symm
          simpa [List.append_assoc] using htail
        simpa only [List.length_append, List.length_singleton] using ht
      have hadd := G1RunSafe.add (by
        simpa only [List.length_append, List.length_singleton,
          show 4 * (pre.length + (rest.length + 1)) - 1 =
            4 * (pre.length + rest.length) + 3 by omega] using hfirst) htail'
      simpa [Nat.mul_add, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hadd

/-- One exact thirteen-step `spent ↦ index` cycle is safe when instantiated
inside the driver footprint. -/
theorem g1CS_repair_cycle_runSafe {W : Nat} (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hleft : 13 < 4 * pre.length + 3)
    (hright : 4 * pre.length + 16 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * pre.length + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx) 13 := by
  apply g1RunSafe_of_margins
  · simpa only [g1AlignedConfig_head_val] using hleft
  · simpa only [g1AlignedConfig_head_val] using hright

/-- The contiguous spent run is safe and macro-preserves the exact
already-repaired `index` suffix after each cycle. -/
theorem g1CS_repair_spent_run_runSafe {W : Nat}
    (pre suffix : List G1Frame) (s : Nat) (ctx : G1Ctx)
    (hpre : 13 < 4 * pre.length + 3)
    (hroom : 4 * (pre.length + s) + 12 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + s) - 1) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ List.replicate s G1Frame.spent ++ suffix).flatMap
          G1Frame.bits)) .bRepairSeek .p3 false false false ctx) (13 * s) := by
  induction s generalizing pre with
  | zero => exact G1RunSafe.empty _
  | succ s ih =>
      have hpre' : 13 < 4 * (pre ++ [G1Frame.spent]).length + 3 := by
        simp
        omega
      let start := g1AlignedConfig W
        (4 * ((pre ++ [G1Frame.spent]).length + s) - 1) (by
          apply lt_of_lt_of_le (b := gnLocalSpan W)
          · simp at hroom ⊢
            omega
          · exact gnLocalSpan_le_g1_tapeLength W)
        (g1ListTape (((pre ++ [G1Frame.spent]) ++
          List.replicate s G1Frame.spent ++ suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx
      have hIH : G1RunSafe start (13 * s) := by
        simpa [start] using
          ih (pre ++ [G1Frame.spent]) hpre' (by simp at hroom ⊢; omega)
      have hIHExact0 := g1CS_repair_spent_run W
        (pre ++ [G1Frame.spent]) suffix s ctx
        (by simp) (by
          exact lt_of_lt_of_le (by simp at hroom ⊢; omega)
            (gnLocalSpan_le_g1_tapeLength W))
      have hIHExact : TM.runConfig (M := G1M) start (13 * s) =
          g1AlignedConfig W (4 * pre.length + 3) (by
            exact lt_of_lt_of_le (by omega)
              (gnLocalSpan_le_g1_tapeLength W))
            (g1ListTape ((pre ++ G1Frame.spent ::
              (List.replicate s G1Frame.index ++ suffix)).flatMap
              G1Frame.bits)) .bRepairSeek .p3 false false false ctx := by
        simpa [start, List.append_assoc] using hIHExact0
      have hcycle := g1CS_repair_cycle_runSafe (W := W) pre
        (List.replicate s G1Frame.index ++ suffix) ctx hpre (by omega)
      have hcycle' : G1RunSafe (TM.runConfig (M := G1M) start (13 * s)) 13 := by
        rw [hIHExact]
        exact hcycle
      have hadd := G1RunSafe.add hIH hcycle'
      simpa [start, List.replicate_succ, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hadd

/-- The anchor read and dispatch are safe.  The fourth reverse-buffer row on
`bof` is stationary, and the fifth `bRepairDone` row is stationary, so this
proof has no left-clamp premise at head zero. -/
theorem g1CS_repair_finish_runSafe {W : Nat} (suffix : List G1Frame)
    (ctx : G1Ctx) (hroom : 7 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W 3 (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx) 5 := by
  let tape := g1ListTape (n := W) ((G1Frame.bof :: suffix).flatMap G1Frame.bits)
  have hsafe : 4 < G1M.tapeLength W := by
    apply lt_of_lt_of_le (b := gnLocalSpan W)
    · omega
    · exact gnLocalSpan_le_g1_tapeLength W
  have hbits : physicalBitsAt hsafe tape = G1Frame.bof.bits := by
    simpa [tape] using physicalBitsAt_flatMap (L := G1M.tapeLength W)
      g1FrameCodec ([] : List G1Frame) suffix G1Frame.bof hsafe
  have hcomplete : g1RepairRevComplete .bRepairSeek
      (tape ⟨0, by omega⟩) (tape ⟨1, by omega⟩)
      (tape ⟨2, by omega⟩) (tape ⟨3, by omega⟩) =
      .bRepairDone := by
    have h := g1RepairScanner.revComplete_of_bits .bRepairSeek .bof hbits
    simpa [g1RepairScanner] using h
  have hanchor : TM.runConfig (M := G1M)
      (g1AlignedConfig W 3 (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .bRepairSeek .p3 false false false ctx) 4 =
    g1AlignedConfig W 0 (by omega) tape .bRepairDone .p0 false false false ctx := by
    simpa using g1RepairScanner.revAnchorStep W 0 hsafe tape
      .bRepairSeek .bof ctx trivial (Or.inr (Or.inl rfl)) hbits
  have hfirst : G1RunSafe
        (g1AlignedConfig W 3 (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
          .bRepairSeek .p3 false false false ctx) 4 := by
    have hfinal : 0 < 0 ∨
        G1RepairStop (g1RepairRevComplete .bRepairSeek
          (tape ⟨0, by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
          (tape ⟨0 + 1, by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
          (tape ⟨0 + 2, by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
          (tape ⟨0 + 3, by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)) := by
      right
      rw [hcomplete]
      exact Or.inr (Or.inl rfl)
    have h := g1Repair_reverseFrame_runSafe (W := W) (base := 0) tape ctx
      (by omega) hfinal
    simpa using h
  have hlast : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W 3 (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
          .bRepairSeek .p3 false false false ctx) 4) 1 := by
    rw [hanchor]
    apply g1Terminal_runSafe_one
    apply g1LocalStepSafe_at_zero_of_not_left
    · rfl
    · intro hleft
      change (g1Transition (0 : Fin 1)
        (g1State .bRepairDone .p0 false false false ctx) _).snd.snd.snd =
          Move.left at hleft
      rw [g1Transition_bRepairDone] at hleft
      exact Move.noConfusion hleft
  simpa [tape] using G1RunSafe.add hfirst hlast

/-! ## Exact repair sweep and capstones -/

set_option maxHeartbeats 1000000 in
/-- The exact request-specific repair sweep is safe from the existing
`readAResetStart` boundary through the canonical `readAStart` handoff. -/
theorem g1CS_repair_sweep_runSafe (r : G1Request) (s : Nat)
    (hs : s ≤ r.arg2) (hm : r.arg2 < r.vals.length) (ctx : G1Ctx) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1WalkCursor r r.arg2 + 1)) (by
          have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
          omega)
        (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false ctx) (g1RepairSteps r s) := by
  let shape := G1RepairSweepShape.of_request r s hs
  have hspan : 4 * (1 + shape.left.length + s + shape.mid.length) + 12 <
      gnLocalSpan (encodeG1 r).length := by
    simp [shape, G1RepairSweepShape.of_request, g1RepairLeft_length,
      g1RepairMid_length r hm, gnLocalSpan, encodeG1_length]
    omega
  have hTL : 4 * (1 + shape.left.length + s + shape.mid.length) + 12 <
      G1M.tapeLength (encodeG1 r).length :=
    lt_of_lt_of_le hspan
      (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length)
  have hbridgeSafe : G1RunSafe
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1WalkCursor r r.arg2 + 1)) (by
          have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
          omega)
        (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false ctx) 1 := by
    apply g1Terminal_runSafe_one
    apply g1LocalStepSafe_of_interior
    · simp [g1WalkCursor]
    · simp [g1WalkCursor, gnLocalSpan, encodeG1_length]
      omega
  have hbridge := g1CS_step_readAReset_bridge (encodeG1 r).length
    (4 * (g1WalkCursor r r.arg2 + 1)) (by
      have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
      omega) (by simp [g1WalkCursor])
    (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits)) ctx
  have hcursor : 1 + shape.left.length + s + shape.mid.length =
      g1WalkCursor r r.arg2 + 1 := by
    simp [shape, G1RepairSweepShape.of_request, g1RepairLeft_length,
      g1RepairMid_length r hm, g1WalkCursor]
    omega
  have hstart : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1WalkCursor r r.arg2 + 1)) (by
          have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
          omega)
        (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false ctx) 1 =
    g1AlignedConfig (encodeG1 r).length
      (4 * (1 + shape.left.length + s + shape.mid.length) - 1) (by omega)
      (g1ListTape (([G1Frame.bof] ++ shape.left ++
        List.replicate s G1Frame.spent ++
        shape.mid ++ shape.tail).flatMap G1Frame.bits))
      .bRepairSeek .p3 false false false ctx := by
    rw [shape.pending] at hbridge
    rw [shape.pending]
    simpa [hcursor] using hbridge
  have hmid0 := g1CS_repair_scan_skip_runSafe
    (W := (encodeG1 r).length)
    ([G1Frame.bof] ++ shape.left ++ List.replicate s G1Frame.spent)
    shape.mid shape.tail ctx
    (by simp) shape.mid_path (by
      simp only [List.length_append, List.length_singleton,
        List.length_replicate] at hspan ⊢
      omega)
  have hmid : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig (encodeG1 r).length
          (4 * (g1WalkCursor r r.arg2 + 1)) (by
            have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
            omega)
          (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
          .readAResetStart .p0 false false false ctx) 1)
      (4 * shape.mid.length) := by
    rw [hstart]
    simpa only [List.length_append, List.length_singleton,
      List.length_replicate] using hmid0
  have hprefix := G1RunSafe.add hbridgeSafe hmid
  have hmidExact := g1CS_repair_scan_skip (encodeG1 r).length
    ([G1Frame.bof] ++ shape.left ++ List.replicate s G1Frame.spent)
    shape.mid shape.tail ctx
    (by simp) shape.mid_path (by
      simp only [List.length_append, List.length_singleton,
        List.length_replicate] at hTL ⊢
      omega)
  have hafterMid : TM.runConfig (M := G1M)
      (TM.runConfig (M := G1M)
        (g1AlignedConfig (encodeG1 r).length
          (4 * (g1WalkCursor r r.arg2 + 1)) (by
            have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
            omega)
          (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
          .readAResetStart .p0 false false false ctx) 1)
      (4 * shape.mid.length) =
    g1AlignedConfig (encodeG1 r).length
      (4 * (1 + shape.left.length + s) - 1) (by omega)
      (g1ListTape (([G1Frame.bof] ++ shape.left ++
        List.replicate s G1Frame.spent ++
        shape.mid ++ shape.tail).flatMap G1Frame.bits))
      .bRepairSeek .p3 false false false ctx := by
    rw [hstart]
    simpa only [List.length_append, List.length_singleton,
      List.length_replicate] using hmidExact
  have hspent0 := g1CS_repair_spent_run_runSafe
    (W := (encodeG1 r).length) ([G1Frame.bof] ++ shape.left)
    (shape.mid ++ shape.tail) s ctx (by
      simp [shape, G1RepairSweepShape.of_request, g1RepairLeft_length]
      omega) (by
        simp only [List.length_append, List.length_singleton] at hspan ⊢
        omega)
  have hspent : G1RunSafe
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (g1AlignedConfig (encodeG1 r).length
            (4 * (g1WalkCursor r r.arg2 + 1)) (by
              have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
              omega)
            (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
            .readAResetStart .p0 false false false ctx) 1)
        (4 * shape.mid.length)) (13 * s) := by
    rw [hafterMid]
    simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hspent0
  have hprefix2 := G1RunSafe.add hprefix (by
    simpa only [runConfig_add] using hspent)
  have hspentExact := g1CS_repair_spent_run (encodeG1 r).length
    ([G1Frame.bof] ++ shape.left) (shape.mid ++ shape.tail) s ctx (by simp) (by
      simp only [List.length_append, List.length_singleton] at hTL ⊢
      omega)
  have hafterSpent : TM.runConfig (M := G1M)
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (g1AlignedConfig (encodeG1 r).length
            (4 * (g1WalkCursor r r.arg2 + 1)) (by
              have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
              omega)
            (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
            .readAResetStart .p0 false false false ctx) 1)
        (4 * shape.mid.length)) (13 * s) =
    g1AlignedConfig (encodeG1 r).length
      (4 * (1 + shape.left.length) - 1) (by omega)
      (g1ListTape (([G1Frame.bof] ++ shape.left ++
        List.replicate s G1Frame.index ++
        shape.mid ++ shape.tail).flatMap G1Frame.bits))
      .bRepairSeek .p3 false false false ctx := by
    rw [hafterMid]
    simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hspentExact
  have hleft0 := g1CS_repair_scan_skip_runSafe
    (W := (encodeG1 r).length) [G1Frame.bof] shape.left
    (List.replicate s G1Frame.index ++ shape.mid ++ shape.tail) ctx (by simp)
    shape.left_path (by
      simp only [List.length_singleton] at hspan ⊢
      omega)
  have hleft : G1RunSafe
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (TM.runConfig (M := G1M)
            (g1AlignedConfig (encodeG1 r).length
              (4 * (g1WalkCursor r r.arg2 + 1)) (by
                have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
                omega)
              (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
              .readAResetStart .p0 false false false ctx) 1)
          (4 * shape.mid.length)) (13 * s)) (4 * shape.left.length) := by
    rw [hafterSpent]
    simpa [List.append_assoc] using hleft0
  have hprefix3 := G1RunSafe.add hprefix2 (by
    simpa only [runConfig_add, Nat.add_assoc] using hleft)
  have hleftExact := g1CS_repair_scan_skip (encodeG1 r).length [G1Frame.bof]
    shape.left (List.replicate s G1Frame.index ++ shape.mid ++ shape.tail) ctx
    (by simp) shape.left_path (by
      simp only [List.length_singleton] at hTL ⊢
      omega)
  have hafterLeft : TM.runConfig (M := G1M)
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (TM.runConfig (M := G1M)
            (g1AlignedConfig (encodeG1 r).length
              (4 * (g1WalkCursor r r.arg2 + 1)) (by
                have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
                omega)
              (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
              .readAResetStart .p0 false false false ctx) 1)
          (4 * shape.mid.length)) (13 * s)) (4 * shape.left.length) =
    g1AlignedConfig (encodeG1 r).length 3 (by omega)
      (g1ListTape (([G1Frame.bof] ++ shape.left ++
        List.replicate s G1Frame.index ++
        shape.mid ++ shape.tail).flatMap G1Frame.bits))
      .bRepairSeek .p3 false false false ctx := by
    rw [hafterSpent]
    simpa [List.append_assoc] using hleftExact
  have hfinish0 := g1CS_repair_finish_runSafe
    (W := (encodeG1 r).length)
    (shape.left ++ List.replicate s G1Frame.index ++ shape.mid ++ shape.tail) ctx
    (by simp [gnLocalSpan, encodeG1_length]; omega)
  have hfinish : G1RunSafe
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (TM.runConfig (M := G1M)
            (TM.runConfig (M := G1M)
              (g1AlignedConfig (encodeG1 r).length
                (4 * (g1WalkCursor r r.arg2 + 1)) (by
                  have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
                  omega)
                (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
                .readAResetStart .p0 false false false ctx) 1)
            (4 * shape.mid.length)) (13 * s)) (4 * shape.left.length)) 5 := by
    rw [hafterLeft]
    simpa [List.append_assoc] using hfinish0
  have hall := G1RunSafe.add hprefix3 (by
    simpa only [runConfig_add, Nat.add_assoc] using hfinish)
  have hsteps := g1RepairSteps_eq r s hs hm
  rw [hsteps]
  simpa [shape, G1RepairSweepShape.of_request, g1RepairPassSteps,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hall

/-- Arbitrary-terminal-state capstone: terminal exhaustion/cleanup and one
complete reject-aware repair cycle are safe and reach the existing canonical
pass-A handoff. -/
theorem g1CS_walk_terminal_repair_trace_safe (r : G1Request)
    (hm : r.arg2 < r.vals.length) (v : Bool)
    (hv : r.vals[r.arg2]? = some v) :
    G1RunSafe (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
        ((16 * r.arg2 + 28) + g1RepairSteps r r.arg2) ∧
      TM.runConfig (M := G1M)
          (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
          ((16 * r.arg2 + 28) + g1RepairSteps r r.arg2) =
        g1ReadAConfig r v := by
  rcases g1CS_walk_terminal_trace_safe r hm v hv with ⟨hterm, hexact⟩
  have hrepair0 := g1CS_repair_sweep_runSafe r r.arg2 (Nat.le_refl _) hm
    (g1Ctx0.withVB v)
  have hrepair : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv)
        (16 * r.arg2 + 28)) (g1RepairSteps r r.arg2) := by
    rw [hexact]
    exact hrepair0
  refine ⟨G1RunSafe.add hterm hrepair, ?_⟩
  rw [runConfig_add, g1CS_walk_terminal_exact r hm v hv]
  exact g1CS_repair_sweep_readAConfig r r.arg2 (Nat.le_refl _) hm v

/-! ## Real-initial nonvacuous literal capstone -/

namespace G1PassBTerminalRepairTraceProbes

/-- One-round positive-B request: the existing B2c1 literal reaches `Σ(1)`,
so no arbitrary-round induction is used below. -/
def reqAnd : G1Request := ⟨.and, 0, 1, [true, false]⟩

theorem reqAnd_canonical : reqAnd.Canonical := by decide

theorem literal_terminal_repair_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqAnd)))
        (g1BPassASteps reqAnd) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqAnd)))
          (g1BPassASteps reqAnd) = g1ReadAConfig reqAnd false := by
  have hone := g1CS_walk_one_round_trace_safe reqAnd reqAnd_canonical
    (Or.inl rfl) 0 rfl true false (by decide) (by decide)
  have htail := g1CS_walk_terminal_repair_trace_safe reqAnd
    (by decide) false (by decide)
  have hsuffix : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAnd)))
        (g1WalkInstallSteps reqAnd + 37))
      ((16 * reqAnd.arg2 + 28) + g1RepairSteps reqAnd reqAnd.arg2) := by
    rw [hone.2]
    exact htail.1
  have hs := G1RunSafe.add hone.1 hsuffix
  have hsteps : g1BPassASteps reqAnd =
      (g1WalkInstallSteps reqAnd + 37) +
        ((16 * reqAnd.arg2 + 28) + g1RepairSteps reqAnd reqAnd.arg2) := by
    rw [g1BPassASteps, g1BReadSteps_eq]
    simp [reqAnd, g1BLoopSteps]
    omega
  constructor
  · rwa [hsteps]
  · exact g1CS_readB_positive_repaired_exact reqAnd reqAnd_canonical
      (Or.inl rfl) (by decide) false (by decide)

end G1PassBTerminalRepairTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
