import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycle
import Complexity.TMVerifier.TuringToolkit.FrameScannerReverseProbe

/-!
# A non-T1 instance of the rewrite cycle (genericity probe)

This module witnesses that `FrameRewriteCycle` and `FrameScannerWriteLeft` are
genuinely generic and not `T1` wrappers.  With **no T1 import** it reuses the
`RevFrame` alphabet of `FrameScannerReverseProbe` — whose five codewords all lie
*outside* the eleven codes `T1Frame` uses, so no theorem below can be a
disguised T1 fact — and puts a *new* finite control on it: seven modes, a
carried context that is a **pair** of Booleans, a rightward write mode, a
walk-back mode, a hop mode and a separate **leftward** write mode.  It then
applies the generic layers unchanged and ends in four fully concrete executable
runs, for **every** input length `n` and with no side hypothesis:

* `cycProbeCS_rewrite_cycle` — the full **thirteen-step** rewrite cycle:
  `spent ↦ cell true` inside the four-frame word `anchor · mark · spent ·
  cell false`, head `11 ↦ 7`, with the exact resulting tape;
* `cycProbeCS_seek_rewrite` — the seek driver in front of it: two skippable
  frames crossed and the marker rewritten in `8 + 13 = 21` steps, head
  `19 ↦ 7`;
* `cycProbeCS_write_left` — the **leftward** four-cell writer replacing
  `cell false` by `mark`, head `15 ↦ 11`, with the exact resulting tape;
* `cycProbeCS_seek_marker` — the seek-until-marker driver alone, stopping on
  the first cell of the marker in the write handoff.

Nothing downstream depends on this module; it is an audit surface.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

open Pnp3.Internal.PsubsetPpoly.TM

/-! ## A control with cycle modes -/
/-- The probe's modes.  `cSeek` is the single reverse mode, `cWrite` the
rightward writer entered at the marker, `cBack`/`cHop` the return walk and the
hop that re-enters the scan, `cWriteL` an independent *leftward* writer, and
`cHalt`/`cBad` the two sinks. -/
inductive CycMode
  | cSeek | cWrite | cBack | cHop | cWriteL | cHalt | cBad
  deriving Fintype, DecidableEq, Repr

set_option synthInstance.maxSize 1024 in
/-- The probe's control state.  Its carried context is a *pair* of Booleans. -/
structure CycState where
  mode : CycMode
  position : RevPos
  b0 : Bool
  b1 : Bool
  b2 : Bool
  ctx : Bool × Bool
  deriving Fintype, DecidableEq, Repr

def cycState (mode : CycMode) (position : RevPos)
    (b0 := false) (b1 := false) (b2 := false)
    (ctx : Bool × Bool := (false, false)) : CycState :=
  ⟨mode, position, b0, b1, b2, ctx⟩

/-- **The right-to-left frame table.**  `rvSpent` is the marker that starts a
rewrite, `rvAnchor` ends the pass, and `rvMark`/`rvCell` are skippable. -/
def cycAdvance : CycMode → RevFrame → CycMode
  | .cSeek, .rvSpent => .cWrite
  | .cSeek, .rvAnchor => .cHalt
  | .cSeek, .rvMark => .cSeek
  | .cSeek, .rvCell _ => .cSeek
  | _, _ => .cBad

def cycComplete (mode : CycMode) (b0 b1 b2 b3 : Bool) : CycMode :=
  match decodeRevFrame? [b0, b1, b2, b3] with
  | some frame => cycAdvance mode frame
  | none => .cBad

/-- The modes at which the reverse pass stops, as a Boolean test the finite
control can perform: everything except the one reverse mode. -/
def cycStops : CycMode → Bool
  | .cSeek => false
  | _ => true

def CycStop (mode : CycMode) : Prop := cycStops mode = true

def CycReverse : CycMode → Prop
  | .cSeek => True
  | _ => False

theorem CycReverse.eq {mode : CycMode} (h : CycReverse mode) :
    mode = .cSeek := by
  cases mode <;> simp_all [CycReverse]

/-- The probe's transition table.  `cWrite` installs `rvCell true`
(`1101`) left to right; `cWriteL` installs `rvMark` (`1011`) right to left. -/
def cycTransition (_phase : Fin 1) (s : CycState) (scan : Bool) :
    Fin 1 × CycState × Bool × Move :=
  match s.mode with
  | .cSeek =>
      match s.position with
      | .q3 => (0, cycState .cSeek .q2 false false scan s.ctx, scan, .left)
      | .q2 => (0, cycState .cSeek .q1 false scan s.b2 s.ctx, scan, .left)
      | .q1 => (0, cycState .cSeek .q0 scan s.b1 s.b2 s.ctx, scan, .left)
      | .q0 =>
          let next := cycComplete .cSeek scan s.b0 s.b1 s.b2
          if cycStops next then
            (0, cycState next .q0 false false false s.ctx, scan, .stay)
          else (0, cycState next .q3 false false false s.ctx, scan, .left)
  | .cWrite =>
      match s.position with
      | .q0 => (0, cycState .cWrite .q1 false false false s.ctx, true, .right)
      | .q1 => (0, cycState .cWrite .q2 false false false s.ctx, true, .right)
      | .q2 => (0, cycState .cWrite .q3 false false false s.ctx, false, .right)
      | .q3 => (0, cycState .cBack .q0 false false false s.ctx, true, .right)
  | .cBack =>
      match s.position with
      | .q0 => (0, cycState .cBack .q1 false false false s.ctx, scan, .left)
      | .q1 => (0, cycState .cBack .q2 false false false s.ctx, scan, .left)
      | .q2 => (0, cycState .cBack .q3 false false false s.ctx, scan, .left)
      | .q3 => (0, cycState .cHop .q0 false false false s.ctx, scan, .left)
  | .cHop => (0, cycState .cSeek .q3 false false false s.ctx, scan, .left)
  | .cWriteL =>
      match s.position with
      | .q3 => (0, cycState .cWriteL .q2 false false false s.ctx, true, .left)
      | .q2 => (0, cycState .cWriteL .q1 false false false s.ctx, true, .left)
      | .q1 => (0, cycState .cWriteL .q0 false false false s.ctx, false, .left)
      | .q0 => (0, cycState .cHalt .q0 false false false s.ctx, true, .left)
  | .cHalt => (0, cycState .cHalt .q0 false false false s.ctx, scan, .stay)
  | .cBad => (0, cycState .cBad .q0 false false false s.ctx, scan, .stay)

def cycProbeClock (N : Nat) : Nat := 64 * (N + 1)

/-- The probe program: zero parameters, one phase, its own clock. -/
def cycProbeCS : ConstStatePhasedProgram CycState where
  numPhases := 1
  startPhase := 0
  startState := cycState .cSeek .q3
  acceptPhase := 0
  acceptState := cycState .cHalt .q0
  transition := cycTransition
  timeBound := cycProbeClock

/-- The compiled probe machine. -/
abbrev CycProbeM := cycProbeCS.toPhased.toTM

/-- Every position the concrete runs below visit is far inside the tape, for
*every* input length: that is what makes them unconditional in `n`. -/
theorem cycProbe_lt_tapeLength {n k : Nat} (h : k ≤ 64) :
    k < CycProbeM.tapeLength n := by
  show k < n + cycProbeClock n + 1
  rw [cycProbeClock]; omega

/-! ### Standalone table lemmas (the only place `cycTransition` reduces) -/
theorem cycTransition_p3 {mode : CycMode} (hm : CycReverse mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool) :
    cycTransition phase (cycState mode .q3 b0 b1 b2 ctx) scan =
      (0, cycState mode .q2 false false scan ctx, scan, .left) := by
  obtain rfl := hm.eq; rfl

theorem cycTransition_p2 {mode : CycMode} (hm : CycReverse mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool) :
    cycTransition phase (cycState mode .q2 b0 b1 b2 ctx) scan =
      (0, cycState mode .q1 false scan b2 ctx, scan, .left) := by
  obtain rfl := hm.eq; rfl

theorem cycTransition_p1 {mode : CycMode} (hm : CycReverse mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool) :
    cycTransition phase (cycState mode .q1 b0 b1 b2 ctx) scan =
      (0, cycState mode .q0 scan b1 b2 ctx, scan, .left) := by
  obtain rfl := hm.eq; rfl

/-- The frame-position-0 branch, before the stop test is decided. -/
theorem cycTransition_p0_raw {mode : CycMode} (hm : CycReverse mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool) :
    cycTransition phase (cycState mode .q0 b0 b1 b2 ctx) scan =
      (if cycStops (cycComplete mode scan b0 b1 b2) then
          (0, cycState (cycComplete mode scan b0 b1 b2) .q0 false false false
            ctx, scan, .stay)
        else
          (0, cycState (cycComplete mode scan b0 b1 b2) .q3 false false false
            ctx, scan, .left)) := by
  obtain rfl := hm.eq; rfl

/-! ## The instances -/
/-- **A non-T1 reverse scanner** whose stop modes include a write handoff. -/
def cycProbeScanner : ReverseFrameScanner CycState RevFrame CycMode
    (Bool × Bool) where
  program := cycProbeCS
  phase := cycProbeCS.startPhase
  codec := revProbeCodec
  Stop := CycStop
  revAdvance := cycAdvance
  revComplete := cycComplete
  Reverse := CycReverse
  rst3 := fun mode a => cycState mode .q3 false false false a
  rst2 := fun mode a b3 => cycState mode .q2 false false b3 a
  rst1 := fun mode a b2 b3 => cycState mode .q1 false b2 b3 a
  rst0 := fun mode a b1 b2 b3 => cycState mode .q0 b1 b2 b3 a
  stopState := fun mode a => cycState mode .q0 false false false a
  revComplete_decode := fun _ _ _ _ _ _ h => by
    simp [cycComplete, revProbeCodec] at h ⊢; rw [h]
  rstep_p3 := fun hm a scan =>
    cycTransition_p3 hm cycProbeCS.startPhase false false false scan a
  rstep_p2 := fun hm a b3 scan =>
    cycTransition_p2 hm cycProbeCS.startPhase false false b3 scan a
  rstep_p1 := fun hm a b2 b3 scan =>
    cycTransition_p1 hm cycProbeCS.startPhase false b2 b3 scan a
  rstep_p0 := fun hm a b1 b2 b3 scan hne =>
    (cycTransition_p0_raw hm cycProbeCS.startPhase b1 b2 b3 scan a).trans
      (if_neg hne)
  rstep_p0_stop := fun hm a b1 b2 b3 scan hstop =>
    (cycTransition_p0_raw hm cycProbeCS.startPhase b1 b2 b3 scan a).trans
      (if_pos hstop)

/-- **A non-T1 rewrite cycle**: `rvSpent ↦ rvCell true`, with the write
entered at the scanner's own stop state. -/
def cycProbeCycle : FrameRewriteCycle CycState RevFrame CycMode (Bool × Bool) where
  scanner := cycProbeScanner
  seekMode := .cSeek
  stopMode := .cWrite
  marker := .rvSpent
  target := .rvCell true
  w0 := true
  w1 := true
  w2 := false
  w3 := true
  wst1 := fun a => cycState .cWrite .q1 false false false a
  wst2 := fun a => cycState .cWrite .q2 false false false a
  wst3 := fun a => cycState .cWrite .q3 false false false a
  bst0 := fun a => cycState .cBack .q0 false false false a
  bst1 := fun a => cycState .cBack .q1 false false false a
  bst2 := fun a => cycState .cBack .q2 false false false a
  bst3 := fun a => cycState .cBack .q3 false false false a
  hopState := fun a => cycState .cHop .q0 false false false a
  seek_reverse := trivial
  seek_nostop := by simp [cycProbeScanner, CycStop, cycStops]
  marker_stop := rfl
  stop_stops := rfl
  target_bits := rfl
  -- the nine cycle tuples are single `rfl` facts of `cycTransition`
  wstep_p0 := fun _ _ => rfl
  wstep_p1 := fun _ _ => rfl
  wstep_p2 := fun _ _ => rfl
  wstep_p3 := fun _ _ => rfl
  bstep_p0 := fun _ _ => rfl
  bstep_p1 := fun _ _ => rfl
  bstep_p2 := fun _ _ => rfl
  bstep_p3 := fun _ _ => rfl
  hop_step := fun _ _ => rfl

/-- **A non-T1 leftward writer**: the control that installs `rvMark` over
whatever frame it is standing on, walking right to left. -/
def cycProbeWriterL : ReverseFrameWriter CycState RevFrame (Bool × Bool) where
  program := cycProbeCS
  phase := cycProbeCS.startPhase
  codec := revProbeCodec
  target := fun _ => .rvMark
  w0 := fun _ => true
  w1 := fun _ => false
  w2 := fun _ => true
  w3 := fun _ => true
  lst3 := fun a => cycState .cWriteL .q3 false false false a
  lst2 := fun a => cycState .cWriteL .q2 false false false a
  lst1 := fun a => cycState .cWriteL .q1 false false false a
  lst0 := fun a => cycState .cWriteL .q0 false false false a
  exitState := fun a => cycState .cHalt .q0 false false false a
  target_bits := fun _ => rfl
  lstep_p3 := fun _ _ => rfl
  lstep_p2 := fun _ _ => rfl
  lstep_p1 := fun _ _ => rfl
  lstep_p0 := fun _ _ => rfl

/-- `cycProbe_lt_tapeLength`, phrased at the scanner's own machine, so that the
head-safety side goals of the generic layers see one atom. -/
theorem cycProbeScanner_lt_tapeLength {n k : Nat} (h : k ≤ 64) :
    k < cycProbeScanner.machine.tapeLength n := cycProbe_lt_tapeLength h

/-- `cycProbe_lt_tapeLength`, phrased at the leftward writer's own machine. -/
theorem cycProbeWriterL_lt_tapeLength {n k : Nat} (h : k ≤ 64) :
    k < cycProbeWriterL.machine.tapeLength n := cycProbe_lt_tapeLength h

/-! ### Four fully concrete non-T1 runs -/
/-- `anchor · mark · spent · cell false`: a four-frame word with the marker in
the middle. -/
def cycProbeWord : List RevFrame :=
  [.rvAnchor, .rvMark, .rvSpent, .rvCell false]

/-- **Concrete non-T1 rewrite cycle.**  Thirteen genuine TM steps replace the
`spent` marker of `cycProbeWord` by `cell true`: head `11 ↦ 7`, control back in
the reverse scan's entry shape, the two-Boolean context surviving, and the tape
exactly that of the rewritten word.  Unconditional in `n`. -/
theorem cycProbeCS_rewrite_cycle (n : Nat) (a : Bool × Bool) :
    TM.runConfig (M := cycProbeScanner.machine)
        (cycProbeScanner.revAligned n 11
          (cycProbeScanner_lt_tapeLength (by omega))
          (frameListTape (cycProbeWord.flatMap RevFrame.bits)) .cSeek a) 13 =
      cycProbeScanner.revAligned n 7
        (cycProbeScanner_lt_tapeLength (by omega))
        (frameListTape
          (([RevFrame.rvAnchor, .rvMark, .rvCell true, .rvCell false]).flatMap
            RevFrame.bits)) .cSeek a := by
  have h := cycProbeCycle.rewriteCycleOnList n [RevFrame.rvAnchor, .rvMark]
    [RevFrame.rvCell false] a (by simp)
    (by simpa using cycProbeScanner_lt_tapeLength (n := n) (k := 12) (by omega))
  simpa [cycProbeWord, cycProbeCycle] using h

/-- **Concrete non-T1 seek-and-rewrite.**  Two skippable frames are crossed
right to left and the marker they end at is rewritten, in `8 + 13 = 21` genuine
TM steps: head `19 ↦ 7`, with the exact resulting tape.  Unconditional in
`n`. -/
theorem cycProbeCS_seek_rewrite (n : Nat) (a : Bool × Bool) :
    TM.runConfig (M := cycProbeScanner.machine)
        (cycProbeScanner.revAligned n 19
          (cycProbeScanner_lt_tapeLength (by omega))
          (frameListTape
            (([RevFrame.rvAnchor, .rvMark, .rvSpent, .rvCell false,
              .rvCell true]).flatMap RevFrame.bits)) .cSeek a)
        21 =
      cycProbeScanner.revAligned n 7
        (cycProbeScanner_lt_tapeLength (by omega))
        (frameListTape
          (([RevFrame.rvAnchor, .rvMark, .rvCell true, .rvCell false,
            .rvCell true]).flatMap RevFrame.bits)) .cSeek a := by
  have hskip : ∀ f ∈ [RevFrame.rvCell false, RevFrame.rvCell true],
      cycProbeCycle.scanner.revAdvance cycProbeCycle.seekMode f =
        cycProbeCycle.seekMode := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · rfl
    · rcases List.mem_cons.mp hf with rfl | hf
      · rfl
      · exact absurd hf (by simp)
  have h := cycProbeCycle.seekAndRewrite n [RevFrame.rvAnchor, .rvMark]
    [RevFrame.rvCell false, .rvCell true] [] a (by simp) hskip
    (by simpa using cycProbeScanner_lt_tapeLength (n := n) (k := 20) (by omega))
  simpa [cycProbeCycle] using h

/-- **Concrete non-T1 leftward frame replacement.**  Four genuine TM steps
replace the `cell false` frame of `cycProbeWord` by `mark` while the head walks
*left*: head `15 ↦ 11`, control in the `cHalt` exit, context surviving, and the
tape exactly that of the rewritten word.  Unconditional in `n`. -/
theorem cycProbeCS_write_left (n : Nat) (a : Bool × Bool) :
    TM.runConfig (M := cycProbeWriterL.machine)
        (cycProbeWriterL.alignedConfigQ n 15
          (cycProbeWriterL_lt_tapeLength (by omega))
          (frameListTape (cycProbeWord.flatMap RevFrame.bits))
          (cycState .cWriteL .q3 false false false a)) 4 =
      cycProbeWriterL.alignedConfigQ n 11
        (cycProbeWriterL_lt_tapeLength (by omega))
        (frameListTape
          (([RevFrame.rvAnchor, .rvMark, .rvSpent, .rvMark]).flatMap
            RevFrame.bits))
        (cycState .cHalt .q0 false false false a) := by
  have h := cycProbeWriterL.writeFrameOnListLeft n
    [RevFrame.rvAnchor, .rvMark, .rvSpent] [] (.rvCell false) a (by simp)
    (by simpa using cycProbeWriterL_lt_tapeLength (n := n) (k := 16) (by omega))
  simpa [cycProbeWord, cycProbeWriterL] using h

/-- **Concrete non-T1 seek-until-marker.**  Twelve genuine TM steps cross the
two skippable frames right to left and read the marker, stopping on its first
cell in the write handoff, with the tape and the context untouched.
Unconditional in `n`. -/
theorem cycProbeCS_seek_marker (n : Nat) (a : Bool × Bool) :
    TM.runConfig (M := cycProbeScanner.machine)
        (cycProbeScanner.revAligned n 19
          (cycProbeScanner_lt_tapeLength (by omega))
          (frameListTape
            (([RevFrame.rvAnchor, .rvMark, .rvSpent, .rvCell false,
              .rvCell true]).flatMap RevFrame.bits)) .cSeek a)
        12 =
      cycProbeScanner.alignedConfigQ n 8
        (cycProbeScanner_lt_tapeLength (by omega))
        (frameListTape
          (([RevFrame.rvAnchor, .rvMark, .rvSpent, .rvCell false,
            .rvCell true]).flatMap RevFrame.bits))
        (cycState .cWrite .q0 false false false a) := by
  have hskip : ∀ f ∈ [RevFrame.rvCell false, RevFrame.rvCell true],
      cycProbeScanner.revAdvance .cSeek f = .cSeek := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · rfl
    · rcases List.mem_cons.mp hf with rfl | hf
      · rfl
      · exact absurd hf (by simp)
  have h := cycProbeScanner.revSeekToMarker n [RevFrame.rvAnchor, .rvMark]
    .rvSpent [RevFrame.rvCell false, .rvCell true] [] .cSeek a trivial
    (by simp [cycProbeScanner, CycStop, cycStops]) hskip rfl
    (by simpa using cycProbe_lt_tapeLength (n := n) (k := 20) (by omega))
  simpa [cycProbeScanner] using h

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
