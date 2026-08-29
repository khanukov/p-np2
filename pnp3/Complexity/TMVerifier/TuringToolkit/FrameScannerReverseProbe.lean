import Complexity.TMVerifier.TuringToolkit.FrameScannerSeek
import Complexity.TMVerifier.TuringToolkit.FrameScannerWrite
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma

/-!
# A non-T1 instance of the reverse and write kernels (genericity probe)

No T1 or G1 import: five disjoint codewords, two visited reverse modes, a
Boolean triple context, an independent executable program/clock, and exact
unconditional 20-step reverse, 20-step mixed-boundary seek, and 4-step
replacement runs.  This is an audit-only genericity probe.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## A four-bit alphabet disjoint from T1's -/
/-- Five frames whose codewords are exactly the five bit patterns `T1Frame`
leaves unused. -/
inductive RevFrame
  | rvMark | rvCell (value : Bool) | rvSpent | rvAnchor
  deriving DecidableEq, Repr

def RevFrame.bits : RevFrame → List Bool
  | .rvMark       => [true, false, true,  true ]
  | .rvCell false => [true, true,  false, false]
  | .rvCell true  => [true, true,  false, true ]
  | .rvSpent      => [true, true,  true,  false]
  | .rvAnchor     => [true, true,  true,  true ]

def decodeRevFrame? : List Bool → Option RevFrame
  | [true, false, true,  true ] => some .rvMark
  | [true, true,  false, false] => some (.rvCell false)
  | [true, true,  false, true ] => some (.rvCell true)
  | [true, true,  true,  false] => some .rvSpent
  | [true, true,  true,  true ] => some .rvAnchor
  | _ => none

/-- The probe alphabet as a fixed-width codec. -/
def revProbeCodec : FrameCodec RevFrame where
  bits := RevFrame.bits
  decode? := decodeRevFrame?
  bits_length := by
    intro f; cases f with
    | rvCell b => cases b <;> rfl
    | rvMark | rvSpent | rvAnchor => rfl
  decode_bits := by
    intro f; cases f with
    | rvCell b => cases b <;> rfl
    | rvMark | rvSpent | rvAnchor => rfl

/-! ## A different control table -/
/-- Probe modes.  `rScan` and `rMark` are two *distinct* reverse modes — the
reverse table switches at a `rvMark` frame, so the mode argument of
`revAdvance` is genuinely used.  `wCell` is the destructive writer, `rHalt` the
anchor sink, `rBad` the grammar sink. -/
inductive RevMode
  | rScan | rMark | wCell | wDone | rHalt | rBad
  deriving Fintype, DecidableEq, Repr

inductive RevPos | q0 | q1 | q2 | q3
  deriving Fintype, DecidableEq, Repr

set_option synthInstance.maxSize 1024 in
/-- The probe's control state.  Its carried context is a *triple* of Booleans —
neither T1's single latch nor the forward probe's pair. -/
structure RevState where
  mode : RevMode
  position : RevPos
  b0 : Bool
  b1 : Bool
  b2 : Bool
  ctx : Bool × Bool × Bool
  deriving Fintype, DecidableEq, Repr

def revState (mode : RevMode) (position : RevPos)
    (b0 := false) (b1 := false) (b2 := false)
    (ctx : Bool × Bool × Bool := (false, false, false)) : RevState :=
  ⟨mode, position, b0, b1, b2, ctx⟩

/-- **The right-to-left frame table.**  `rvMark` switches the reverse mode;
`rvAnchor` ends the pass; a `rvMark` met a second time is a grammar violation. -/
def revProbeAdvance : RevMode → RevFrame → RevMode
  | .rScan, .rvAnchor => .rHalt
  | .rScan, .rvMark => .rMark
  | .rScan, _ => .rScan
  | .rMark, .rvAnchor => .rHalt
  | .rMark, .rvMark => .rBad
  | .rMark, _ => .rMark
  | _, _ => .rBad

def revProbeComplete (mode : RevMode) (b0 b1 b2 b3 : Bool) : RevMode :=
  match decodeRevFrame? [b0, b1, b2, b3] with
  | some frame => revProbeAdvance mode frame
  | none => .rBad

/-- The two sinks, as a Boolean test the finite control can perform. -/
def revProbeStops : RevMode → Bool
  | .rHalt | .rBad => true
  | _ => false

def RevProbeStop (mode : RevMode) : Prop := revProbeStops mode = true

def RevProbeReverse : RevMode → Prop
  | .rScan | .rMark => True
  | _ => False

theorem RevProbeReverse.cases {mode : RevMode} (h : RevProbeReverse mode) :
    mode = .rScan ∨ mode = .rMark := by
  cases mode <;> simp_all [RevProbeReverse]

def revProbeTransition (_phase : Fin 1) (s : RevState) (scan : Bool) :
    Fin 1 × RevState × Bool × Move :=
  match s.mode with
  | .rHalt => (0, revState .rHalt .q0 false false false s.ctx, scan, .stay)
  | .rBad => (0, revState .rBad .q0 false false false s.ctx, scan, .stay)
  | .wDone => (0, revState .wDone .q0 false false false s.ctx, scan, .stay)
  | .wCell =>
      match s.position with
      | .q0 => (0, revState .wCell .q1 false false false s.ctx, true, .right)
      | .q1 => (0, revState .wCell .q2 false false false s.ctx, true, .right)
      | .q2 => (0, revState .wCell .q3 false false false s.ctx, true, .right)
      | .q3 => (0, revState .wDone .q0 false false false s.ctx, false, .right)
  | mode =>
      match s.position with
      | .q3 => (0, revState mode .q2 false false scan s.ctx, scan, .left)
      | .q2 => (0, revState mode .q1 false scan s.b2 s.ctx, scan, .left)
      | .q1 => (0, revState mode .q0 scan s.b1 s.b2 s.ctx, scan, .left)
      | .q0 =>
          let next := revProbeComplete mode scan s.b0 s.b1 s.b2
          if revProbeStops next then
            (0, revState next .q0 false false false s.ctx, scan, .stay)
          else (0, revState next .q3 false false false s.ctx, scan, .left)

def revProbeClock (N : Nat) : Nat := 64 * (N + 1)

/-- The probe program: zero parameters, one phase, its own clock. -/
def revProbeCS : ConstStatePhasedProgram RevState where
  numPhases := 1
  startPhase := 0
  startState := revState .rScan .q3
  acceptPhase := 0
  acceptState := revState .rHalt .q0
  transition := revProbeTransition
  timeBound := revProbeClock

/-- The compiled probe machine. -/
abbrev RevProbeM := revProbeCS.toPhased.toTM

/-- Every position the concrete probe runs visit is far inside the tape, for
*every* input length.  This is what makes the concrete theorems below
unconditional, hence non-vacuous. -/
theorem revProbe_lt_tapeLength {n k : Nat} (h : k ≤ 64) :
    k < RevProbeM.tapeLength n := by
  show k < n + revProbeClock n + 1
  rw [revProbeClock]; omega

/-! ### Standalone table lemmas (the only place `revProbeTransition` reduces) -/
theorem revProbeTransition_p3 {mode : RevMode} (hm : RevProbeReverse mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool × Bool) :
    revProbeTransition phase (revState mode .q3 b0 b1 b2 ctx) scan =
      (0, revState mode .q2 false false scan ctx, scan, .left) := by
  rcases hm.cases with rfl | rfl <;> rfl

theorem revProbeTransition_p2 {mode : RevMode} (hm : RevProbeReverse mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool × Bool) :
    revProbeTransition phase (revState mode .q2 b0 b1 b2 ctx) scan =
      (0, revState mode .q1 false scan b2 ctx, scan, .left) := by
  rcases hm.cases with rfl | rfl <;> rfl

theorem revProbeTransition_p1 {mode : RevMode} (hm : RevProbeReverse mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool × Bool) :
    revProbeTransition phase (revState mode .q1 b0 b1 b2 ctx) scan =
      (0, revState mode .q0 scan b1 b2 ctx, scan, .left) := by
  rcases hm.cases with rfl | rfl <;> rfl

/-- The frame-position-0 branch, before the stop test is decided. -/
theorem revProbeTransition_p0_raw {mode : RevMode}
    (hm : RevProbeReverse mode) (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : Bool × Bool × Bool) :
    revProbeTransition phase (revState mode .q0 b0 b1 b2 ctx) scan =
      (if revProbeStops (revProbeComplete mode scan b0 b1 b2) then
          (0, revState (revProbeComplete mode scan b0 b1 b2) .q0 false false
            false ctx, scan, .stay)
        else
          (0, revState (revProbeComplete mode scan b0 b1 b2) .q3 false false
            false ctx, scan, .left)) := by
  rcases hm.cases with rfl | rfl <;> rfl

/-! ## The two instances -/
/-- **A non-T1 instance of the reverse kernel.** -/
def revProbeScanner : ReverseFrameScanner RevState RevFrame RevMode
    (Bool × Bool × Bool) where
  program := revProbeCS
  phase := revProbeCS.startPhase
  codec := revProbeCodec
  Stop := RevProbeStop
  revAdvance := revProbeAdvance
  revComplete := revProbeComplete
  Reverse := RevProbeReverse
  rst3 := fun mode a => revState mode .q3 false false false a
  rst2 := fun mode a b3 => revState mode .q2 false false b3 a
  rst1 := fun mode a b2 b3 => revState mode .q1 false b2 b3 a
  rst0 := fun mode a b1 b2 b3 => revState mode .q0 b1 b2 b3 a
  stopState := fun mode a => revState mode .q0 false false false a
  revComplete_decode := fun _ _ _ _ _ _ h => by
    simp [revProbeComplete, revProbeCodec] at h ⊢; rw [h]
  rstep_p3 := fun hm a scan =>
    revProbeTransition_p3 hm revProbeCS.startPhase false false false scan a
  rstep_p2 := fun hm a b3 scan =>
    revProbeTransition_p2 hm revProbeCS.startPhase false false b3 scan a
  rstep_p1 := fun hm a b2 b3 scan =>
    revProbeTransition_p1 hm revProbeCS.startPhase false b2 b3 scan a
  rstep_p0 := fun hm a b1 b2 b3 scan hne =>
    (revProbeTransition_p0_raw hm revProbeCS.startPhase b1 b2 b3 scan a).trans
      (if_neg hne)
  rstep_p0_stop := fun hm a b1 b2 b3 scan hstop =>
    (revProbeTransition_p0_raw hm revProbeCS.startPhase b1 b2 b3 scan a).trans
      (if_pos hstop)

/-- **A non-T1 instance of the write kernel**: the control that installs the
`rvSpent` marker over whatever frame it is standing on. -/
def revProbeWriter : FrameWriter RevState RevFrame (Bool × Bool × Bool) where
  program := revProbeCS
  phase := revProbeCS.startPhase
  codec := revProbeCodec
  target := .rvSpent
  w0 := true
  w1 := true
  w2 := true
  w3 := false
  wst0 := fun a => revState .wCell .q0 false false false a
  wst1 := fun a => revState .wCell .q1 false false false a
  wst2 := fun a => revState .wCell .q2 false false false a
  wst3 := fun a => revState .wCell .q3 false false false a
  exitState := fun a => revState .wDone .q0 false false false a
  target_bits := rfl
  -- the four write tuples are single `rfl` facts of `revProbeTransition`
  wstep_p0 := fun _ _ => rfl
  wstep_p1 := fun _ _ => rfl
  wstep_p2 := fun _ _ => rfl
  wstep_p3 := fun _ _ => rfl

@[simp] theorem revProbeScanner_Stop : revProbeScanner.Stop = RevProbeStop := rfl

@[simp] theorem revProbeScanner_revAdvance :
    revProbeScanner.revAdvance = revProbeAdvance := rfl

/-- `revProbe_lt_tapeLength`, phrased at the scanner's own machine so that the
head-safety side goals of the generic kernel see one atom. -/
theorem revProbeScanner_lt_tapeLength {n k : Nat} (h : k ≤ 64) :
    k < revProbeScanner.machine.tapeLength n := revProbe_lt_tapeLength h

/-- `revProbe_lt_tapeLength`, phrased at the writer's own machine. -/
theorem revProbeWriter_lt_tapeLength {n k : Nat} (h : k ≤ 64) :
    k < revProbeWriter.machine.tapeLength n := revProbe_lt_tapeLength h

/-! ### Two fully concrete non-T1 runs -/
/-- `anchor · cell true · mark · cell false · spent`: a five-frame word shaped
like a marked operand field. -/
def revProbeWord : List RevFrame :=
  [.rvAnchor, .rvCell true, .rvMark, .rvCell false, .rvSpent]

/-- The four frames read by the rewind, left to right. -/
def revProbeTail : List RevFrame :=
  [.rvCell true, .rvMark, .rvCell false, .rvSpent]

theorem revProbeTail_validPath :
    revProbeScanner.RevValidPath .rScan revProbeTail := by
  refine ⟨trivial, ?_, trivial, ?_, trivial, ?_, trivial, ?_, trivial⟩ <;>
    simp [RevProbeStop, revProbeAdvance, revProbeStops]

/-- The rewind genuinely switches reverse mode at the `mark` frame. -/
theorem revProbeTail_advanceList :
    revProbeScanner.revAdvanceList .rScan revProbeTail = .rMark := rfl

/-- Unconditional concrete non-T1 20-step reverse-to-anchor run. -/
theorem revProbeCS_scan_word (n : Nat) (a : Bool × Bool × Bool) :
    TM.runConfig (M := revProbeScanner.machine)
        (revProbeScanner.revAligned n 19
          (revProbeScanner_lt_tapeLength (by omega))
          (frameListTape (revProbeWord.flatMap RevFrame.bits)) .rScan a) 20 =
      revProbeScanner.alignedConfigQ n 0
        (revProbeScanner_lt_tapeLength (by omega))
        (frameListTape (revProbeWord.flatMap RevFrame.bits))
        (revState .rHalt .q0 false false false a) := by
  have h := revProbeScanner.revScanToAnchor n .rvAnchor revProbeTail []
    .rScan a revProbeTail_validPath trivial rfl
    (by simpa [revProbeTail] using
      revProbeScanner_lt_tapeLength (n := n) (k := 20) (by omega))
  simpa [revProbeTail, revProbeWord, revProbeScanner] using h

/-- **Concrete non-T1/non-G1 mixed-boundary seek.**  Twenty genuine steps of
the fixed probe machine cross `cell false · spent` in `rScan`, read `rvMark`
and switch to `rMark` without stopping, cross `cell true` in `rMark`, and stop
on `rvAnchor` at head `0`.  The literal list-backed tape and the complete
three-Boolean context are unchanged, for every input length. -/
theorem revProbeCS_seek_across_mark (n : Nat) (a : Bool × Bool × Bool) :
    TM.runConfig (M := revProbeScanner.machine)
        (revProbeScanner.revAligned n 19
          (revProbeScanner_lt_tapeLength (by omega))
          (frameListTape (revProbeWord.flatMap RevFrame.bits)) .rScan a) 20 =
      revProbeScanner.alignedConfigQ n 0
        (revProbeScanner_lt_tapeLength (by omega))
        (frameListTape (revProbeWord.flatMap RevFrame.bits))
        (revState .rHalt .q0 false false false a) := by
  have hskip : ∀ (m : RevMode) (fs : List RevFrame),
      (∀ f ∈ fs, revProbeAdvance m f = m) →
      ∀ f ∈ fs, revProbeScanner.revAdvance m f = m := fun _ _ h => h
  have h := revProbeScanner.revSeekAcrossBoundary n [] .rvAnchor
    [RevFrame.rvCell true] .rvMark [RevFrame.rvCell false, .rvSpent] []
    .rScan .rMark a trivial
    (by simp [revProbeScanner, RevProbeStop, revProbeStops]) trivial
    (by simp [revProbeScanner, RevProbeStop, revProbeStops])
    (hskip .rScan _ (by decide)) rfl (hskip .rMark _ (by decide)) rfl
    (by simpa using revProbeScanner_lt_tapeLength (n := n) (k := 20) (by omega))
  simpa [revProbeWord, revProbeScanner] using h

/-- Unconditional concrete non-T1 four-step frame replacement. -/
theorem revProbeCS_write_cell (n : Nat) (a : Bool × Bool × Bool) :
    TM.runConfig (M := revProbeWriter.machine)
        (revProbeWriter.alignedConfigQ n 12
          (revProbeWriter_lt_tapeLength (by omega))
          (frameListTape (revProbeWord.flatMap RevFrame.bits))
          (revState .wCell .q0 false false false a)) 4 =
      revProbeWriter.alignedConfigQ n 16
        (revProbeWriter_lt_tapeLength (by omega))
        (frameListTape
          (([RevFrame.rvAnchor, .rvCell true, .rvMark, .rvSpent,
            .rvSpent]).flatMap RevFrame.bits))
        (revState .wDone .q0 false false false a) := by
  have h := revProbeWriter.writeFrameOnList n
    [RevFrame.rvAnchor, .rvCell true, .rvMark] [RevFrame.rvSpent]
    (.rvCell false) a
    (by simpa using revProbeWriter_lt_tapeLength (n := n) (k := 16) (by omega))
  simpa [revProbeWord, revProbeWriter] using h

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
