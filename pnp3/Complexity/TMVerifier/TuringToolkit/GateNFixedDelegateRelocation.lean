import Complexity.TMVerifier.TuringToolkit.GateOneFiveTagTraceSafety
import Complexity.TMVerifier.TuringToolkit.FrameScannerKernel
import Complexity.TMVerifier.TuringToolkit.FrameScannerReverse
import Complexity.TMVerifier.TuringToolkit.FrameShuttle
import Complexity.TMVerifier.TuringToolkit.GateNRuntimeGrammar
import Complexity.TMVerifier.TuringToolkit.GateNLocateGrammar

/-!
# Fixed GN delegate, relocation, and E1b scratch-entry scan (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module defines one closed finite outer control.  Its delegated states carry
only the already-finite complete `G1M.state`; every outer state remains finite.
There is no request, result, natural number, base, width, offset, index, or
runtime datum in the control.  GN-E1a adds one finite four-cell lexical scan
payload and a fixed `wordEnd` state; GN-E1b reuses that public arrival to read
exactly the next four physical cells, require the blank frame `0000`, return
four cells left, and enter fixed `scratchEntry`.  The old `idle` state remains
an inert regression sink, while the real start state is the aligned scanner
entry.

Ordinary delegated states execute the exact `G1M.step` tuple.  The only two
interceptions are the complete canonical states `g1DoneQ false` and
`g1DoneQ true`, including both the unique phase and the complete `G1State`.
Malformed output modes, buffers, positions, and contexts therefore continue to
delegate.  The successful five-tag source trace cannot reach either intercepted
state at a proper prefix; that source fact is proved from the live
`outputDone -> accept` row, the stable accept sink, and the exact merged
output-done endpoint, without target delegation, relocation, or `G1RunSafe`.

The capstone overlays exactly `[0,W+5)` into a caller-supplied ambient target
tape, relocates the complete safe source trace, preserves every outside cell at
every prefix, and executes one further stationary target step into the fixed
result-indexed returned state.  It adds no exact-list parser, copier, installer,
runtime base discovery, commit sweep, multi-gate loop, total clock-adequacy
theorem, verdict, or acceptance result.  The scan is lexical only: it does not
compare slot and record counts or enforce semantic index bounds, and it is not
equivalent to `decodeGN?`.  The blank-padded tape cannot distinguish an exact
word from a trailing-zero extension.  E1b rejects nonblank decoded or reserved
windows in the inspected frame, but makes no trailing-zero rejection claim.
The exported E1b endpoint is exact `scratchEntry`.  GN-E2-1c now activates that
row into the strict read-only reverse locator in this same control owner;
`firstRecord` and `noGate` are the new dormant arrivals.  GN-E2-1b's separate
caller-supplied `install` states remain unconnected.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Closed finite outer machine -/

/-- The complete one-phase source state at the canonical output-done boundary. -/
def g1DoneQ (b : Bool) : G1M.state :=
  ⟨(0 : Fin 1), g1OutputDoneState b⟩

/-- The complete one-phase source accept state. -/
def g1AcceptQ : G1M.state := ⟨(0 : Fin 1), g1AcceptState⟩

/-- Four physical positions of the finite read-only frame buffer. -/
inductive GNScanBuffer where
  | p0
  | p1 (b0 : Bool)
  | p2 (b0 b1 : Bool)
  | p3 (b0 b1 b2 : Bool)
  deriving Fintype, DecidableEq, Repr

/-- The sole scanning payload: one finite grammar mode and at most three bits. -/
structure GNScanState where
  mode : GNDiscoveryMode
  buffer : GNScanBuffer
  deriving Fintype, DecidableEq, Repr

/-- Finite modes of the dormant GN identity-copy shuttle.  They contain no
runtime geometry; the later bootstrap/record driver owns all boundary
translations and entry selection. -/
inductive GNInstallMode where
  | probe | turnBack | mark | seek | destinationTurn | destination
  | reverse | reverseStop | restore | exit | reject
  deriving Fintype, DecidableEq, Repr

/-- Four physical positions used by every installer reader/writer. -/
inductive GNInstallBuffer where
  | p0
  | p1 (b0 : Bool)
  | p2 (b0 b1 : Bool)
  | p3 (b0 b1 b2 : Bool)
  | r3
  | r2 (b3 : Bool)
  | r1 (b2 b3 : Bool)
  | r0 (b1 b2 b3 : Bool)
  deriving Fintype, DecidableEq, Repr

/-- The only installer auxiliary payload: either empty or one decoded frame. -/
inductive GNInstallAux where
  | empty
  | carried (frame : G1Frame)
  deriving Fintype, DecidableEq, Repr

/-- Total projection used by dormant rows; live probe completion always
replaces the initial payload with `carried source`. -/
def GNInstallAux.frame : GNInstallAux → G1Frame
  | .empty => .blank
  | .carried frame => frame

def gnInstallLatch (_ : GNInstallAux) (frame : G1Frame) : GNInstallAux :=
  .carried frame

def gnInstallBit0 (a : GNInstallAux) : Bool := a.frame.bits.getD 0 false
def gnInstallBit1 (a : GNInstallAux) : Bool := a.frame.bits.getD 1 false
def gnInstallBit2 (a : GNInstallAux) : Bool := a.frame.bits.getD 2 false
def gnInstallBit3 (a : GNInstallAux) : Bool := a.frame.bits.getD 3 false

/-- Identity-copy admissibility.  Blank is the destination frontier and
`output true` is the temporary source marker, so neither may be a source. -/
def GNInstallAdmissible (frame : G1Frame) : Prop :=
  frame ≠ .blank ∧ frame ≠ .output true

set_option synthInstance.maxSize 8192 in
/-- Fixed GN outer control.  The delegated payload is itself a closed finite
G1 control state; none of the constructors contains runtime geometry or data. -/
inductive GNState where
  | delegated (q : G1M.state)
  | returnedFalse
  | returnedTrue
  | scanning (scan : GNScanState)
  | wordEnd
  | blankConfirm (buffer : GNScanBuffer)
  | blankSeen
  | return3
  | return2
  | return1
  | return0
  | install (mode : GNInstallMode) (buffer : GNInstallBuffer)
      (aux : GNInstallAux)
  | scratchEntry
  | locating (locate : GNLocateState)
  | firstRecord
  | noGate
  | idle
  | accept
  | reject
  deriving Fintype, DecidableEq

/-- Installer rejection is the already-existing stable outer reject sink. -/
def gnInstallControl (mode : GNInstallMode) (buffer : GNInstallBuffer)
    (aux : GNInstallAux) : GNState :=
  match mode with
  | .reject => .reject
  | _ => .install mode buffer aux

/-- Collapse the two terminal discovery modes to fixed outer states. -/
def gnScanControl (mode : GNDiscoveryMode) (buffer : GNScanBuffer) : GNState :=
  match mode with
  | .wordEnd => .wordEnd
  | .reject => .reject
  | _ => .scanning ⟨mode, buffer⟩

/-- Result-indexed fixed returned state. -/
def gnReturnedState : Bool → GNState
  | false => .returnedFalse
  | true => .returnedTrue

/-- The exact outer transition table.  Equality tests intercept only the two
complete canonical `g1DoneQ` values. -/
def gnTransition (_phase : Fin 1) (s : GNState) (scan : Bool) :
    Fin 1 × GNState × Bool × Move :=
  match s with
  | .delegated q =>
      if q = g1DoneQ false then (0, .returnedFalse, scan, .stay)
      else if q = g1DoneQ true then (0, .returnedTrue, scan, .stay)
      else
        let out := G1M.step q scan
        (0, .delegated out.fst, out.snd.fst, out.snd.snd)
  | .returnedFalse => (0, .returnedFalse, scan, .stay)
  | .returnedTrue => (0, .returnedTrue, scan, .stay)
  | .scanning q =>
      match q.buffer with
      | .p0 => (0, .scanning ⟨q.mode, .p1 scan⟩, scan, .right)
      | .p1 b0 => (0, .scanning ⟨q.mode, .p2 b0 scan⟩, scan, .right)
      | .p2 b0 b1 =>
          (0, .scanning ⟨q.mode, .p3 b0 b1 scan⟩, scan, .right)
      | .p3 b0 b1 b2 =>
          let next := gnDiscoveryComplete q.mode b0 b1 b2 scan
          (0, gnScanControl next .p0, scan,
            if next = .reject then .stay else .right)
  | .wordEnd => (0, .blankConfirm (.p1 scan), scan, .right)
  | .blankConfirm buffer =>
      match buffer with
      -- Totality only: live `wordEnd` entry starts at `p1`; no row targets `p0`.
      | .p0 => (0, .blankConfirm (.p1 scan), scan, .right)
      | .p1 b0 => (0, .blankConfirm (.p2 b0 scan), scan, .right)
      | .p2 b0 b1 =>
          (0, .blankConfirm (.p3 b0 b1 scan), scan, .right)
      | .p3 b0 b1 b2 =>
          if b0 = false ∧ b1 = false ∧ b2 = false ∧ scan = false then
            (0, .blankSeen, scan, .right)
          else (0, .reject, scan, .stay)
  | .blankSeen => (0, .return3, scan, .left)
  | .return3 => (0, .return2, scan, .left)
  | .return2 => (0, .return1, scan, .left)
  | .return1 => (0, .return0, scan, .left)
  | .return0 => (0, .scratchEntry, scan, .stay)
  | .install .probe .p0 a =>
      (0, .install .probe (.p1 scan) a, scan, .right)
  | .install .probe (.p1 b0) a =>
      (0, .install .probe (.p2 b0 scan) a, scan, .right)
  | .install .probe (.p2 b0 b1) a =>
      (0, .install .probe (.p3 b0 b1 scan) a, scan, .right)
  | .install .probe (.p3 b0 b1 b2) a =>
      match decodeG1Frame? [b0, b1, b2, scan] with
      | some frame =>
          if frame = .blank ∨ frame = .output true then
            (0, .reject, scan, .stay)
          else
            (0, .install .turnBack (.p3 false false false)
              (gnInstallLatch a frame), scan, .right)
      | none => (0, .reject, scan, .stay)
  | .install .turnBack (.p3 _ _ _) a =>
      (0, .install .turnBack (.p2 false false) a, scan, .left)
  | .install .turnBack (.p2 _ _) a =>
      (0, .install .turnBack (.p1 false) a, scan, .left)
  | .install .turnBack (.p1 _) a =>
      (0, .install .turnBack .p0 a, scan, .left)
  | .install .turnBack .p0 a =>
      (0, .install .mark .p0 a, scan, .left)
  | .install .mark .p0 a =>
      (0, .install .mark (.p1 true) a, true, .right)
  | .install .mark (.p1 _) a =>
      (0, .install .mark (.p2 true false) a, false, .right)
  | .install .mark (.p2 _ _) a =>
      (0, .install .mark (.p3 true false false) a, false, .right)
  | .install .mark (.p3 _ _ _) a =>
      (0, .install .seek .p0 a, true, .right)
  | .install .seek .p0 a =>
      (0, .install .seek (.p1 scan) a, scan, .right)
  | .install .seek (.p1 b0) a =>
      (0, .install .seek (.p2 b0 scan) a, scan, .right)
  | .install .seek (.p2 b0 b1) a =>
      (0, .install .seek (.p3 b0 b1 scan) a, scan, .right)
  | .install .seek (.p3 b0 b1 b2) a =>
      match decodeG1Frame? [b0, b1, b2, scan] with
      | some .blank => (0, .install .destinationTurn .p0 a, scan, .right)
      | some (.output true) => (0, .reject, scan, .stay)
      | some _ => (0, .install .seek .p0 a, scan, .right)
      | none => (0, .reject, scan, .stay)
  | .install .destinationTurn .p0 a =>
      (0, .install .destination (.p3 false false false) a, scan, .left)
  | .install .destination (.p3 _ _ _) a =>
      (0, .install .destination (.p2 false false) a, gnInstallBit3 a, .left)
  | .install .destination (.p2 _ _) a =>
      (0, .install .destination (.p1 false) a, gnInstallBit2 a, .left)
  | .install .destination (.p1 _) a =>
      (0, .install .destination .p0 a, gnInstallBit1 a, .left)
  | .install .reverse .r3 a =>
      (0, .install .reverse (.r2 scan) a, scan, .left)
  | .install .reverse (.r2 b3) a =>
      (0, .install .reverse (.r1 scan b3) a, scan, .left)
  | .install .reverse (.r1 b2 b3) a =>
      (0, .install .reverse (.r0 scan b2 b3) a, scan, .left)
  | .install .reverse (.r0 b1 b2 b3) a =>
      match decodeG1Frame? [scan, b1, b2, b3] with
      | some (.output true) =>
          (0, .install .reverseStop .p0 a, scan, .stay)
      | some _ => (0, .install .reverse .r3 a, scan, .left)
      | none => (0, .reject, scan, .stay)
  | .install .destination .p0 a =>
      (0, .install .reverse .r3 a, gnInstallBit0 a, .left)
  | .install .reverseStop .p0 a =>
      (0, .install .restore (.p1 (gnInstallBit0 a)) a,
        gnInstallBit0 a, .right)
  | .install .restore (.p1 _) a =>
      (0, .install .restore (.p2 (gnInstallBit0 a) (gnInstallBit1 a)) a,
        gnInstallBit1 a, .right)
  | .install .restore (.p2 _ _) a =>
      (0, .install .restore
        (.p3 (gnInstallBit0 a) (gnInstallBit1 a) (gnInstallBit2 a)) a,
        gnInstallBit2 a, .right)
  | .install .restore (.p3 _ _ _) a =>
      (0, .install .exit .p0 .empty, gnInstallBit3 a, .right)
  | .install .exit buffer a => (0, .install .exit buffer a, scan, .stay)
  | .install _ _ _ => (0, .reject, scan, .stay)
  | .scratchEntry =>
      (0, .locating ⟨.tailFinish, .r3⟩, scan, .left)
  | .locating ⟨mode, .r3⟩ =>
      (0, .locating ⟨mode, .r2 scan⟩, scan, .left)
  | .locating ⟨mode, .r2 b3⟩ =>
      (0, .locating ⟨mode, .r1 scan b3⟩, scan, .left)
  | .locating ⟨mode, .r1 b2 b3⟩ =>
      (0, .locating ⟨mode, .r0 scan b2 b3⟩, scan, .left)
  | .locating ⟨mode, .r0 b1 b2 b3⟩ =>
      let next := gnLocateComplete mode scan b1 b2 b3
      if next = .firstRecord then (0, .firstRecord, scan, .stay)
      else if next = .noGate then (0, .noGate, scan, .stay)
      else if next = .reject then (0, .reject, scan, .stay)
      else (0, .locating ⟨next, .r3⟩, scan, .left)
  | .firstRecord => (0, .firstRecord, scan, .stay)
  | .noGate => (0, .noGate, scan, .stay)
  | .idle => (0, .idle, scan, .stay)
  | .accept => (0, .accept, scan, .stay)
  | .reject => (0, .reject, scan, .stay)

/-- Closed outer clock declaration.  No adequacy claim is made here. -/
def gnClock (N : Nat) : Nat := g1Clock N

/-- One fixed GN outer program.  Its real initial state is the aligned scan. -/
def gnCS : ConstStatePhasedProgram GNState where
  numPhases := 1
  startPhase := 0
  startState := gnScanControl .start .p0
  acceptPhase := 0
  acceptState := .accept
  transition := gnTransition
  timeBound := gnClock

/-- The fixed compiled outer machine. -/
abbrev GNM := gnCS.toPhased.toTM

/-- Embed one complete source state into the delegated outer region. -/
def gnEmbed (q : G1M.state) : GNM.state :=
  ⟨(0 : Fin 1), .delegated q⟩

/-- Complete target state reached when the shell intercepts a result. -/
def gnReturnedQ (b : Bool) : GNM.state :=
  ⟨(0 : Fin 1), gnReturnedState b⟩

/-- Exact-list Boolean-cube point used by the real GN initial configuration. -/
def gnPoint (bits : List Bool) : Boolcube.Point bits.length := fun i => bits.get i

@[simp] theorem gnCS_startState : gnCS.startState = gnScanControl .start .p0 := rfl

@[simp] theorem gnTransition_idle (phase : Fin 1) (scan : Bool) :
    gnTransition phase .idle scan = (0, .idle, scan, .stay) := rfl

@[simp] theorem gnTransition_returnedFalse (phase : Fin 1) (scan : Bool) :
    gnTransition phase .returnedFalse scan =
      (0, .returnedFalse, scan, .stay) := rfl

@[simp] theorem gnTransition_returnedTrue (phase : Fin 1) (scan : Bool) :
    gnTransition phase .returnedTrue scan =
      (0, .returnedTrue, scan, .stay) := rfl

@[simp] theorem gnTransition_accept (phase : Fin 1) (scan : Bool) :
    gnTransition phase .accept scan = (0, .accept, scan, .stay) := rfl

@[simp] theorem gnTransition_reject (phase : Fin 1) (scan : Bool) :
    gnTransition phase .reject scan = (0, .reject, scan, .stay) := rfl

/-- The public E1a `wordEnd` arrival is the p0 row of E1b confirmation. -/
theorem gnTransition_wordEnd (phase : Fin 1) (scan : Bool) :
    gnTransition phase .wordEnd scan =
      (0, .blankConfirm (.p1 scan), scan, .right) := rfl

/-- The two remaining buffering rows of blank-frame confirmation. -/
theorem gnTransition_blankConfirm_buffer (phase : Fin 1)
    (b0 b1 scan : Bool) :
    gnTransition phase (.blankConfirm (.p1 b0)) scan =
        (0, .blankConfirm (.p2 b0 scan), scan, .right) ∧
      gnTransition phase (.blankConfirm (.p2 b0 b1)) scan =
        (0, .blankConfirm (.p3 b0 b1 scan), scan, .right) := by
  exact ⟨rfl, rfl⟩

/-- Exactly `0000` completes confirmation and advances to the post-frame
landing cell. -/
theorem gnTransition_blankConfirm_zero (phase : Fin 1) :
    gnTransition phase (.blankConfirm (.p3 false false false)) false =
      (0, .blankSeen, false, .right) := rfl

/-- Representative nonblank decoded (`0001`, `bof`) and reserved (`1101`)
confirmation windows reject stationarily at p3 and write back the scan. -/
theorem gnTransition_blankConfirm_rejections (phase : Fin 1) :
    gnTransition phase (.blankConfirm (.p3 false false false)) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.blankConfirm (.p3 true true false)) true =
        (0, .reject, true, .stay) := by
  exact ⟨rfl, rfl⟩

/-- The five fixed post-confirmation rows: four read-only left moves followed
by one stationary entry into `scratchEntry`. -/
theorem gnTransition_blankReturn_rows (phase : Fin 1) (scan : Bool) :
    gnTransition phase .blankSeen scan = (0, .return3, scan, .left) ∧
      gnTransition phase .return3 scan = (0, .return2, scan, .left) ∧
      gnTransition phase .return2 scan = (0, .return1, scan, .left) ∧
      gnTransition phase .return1 scan = (0, .return0, scan, .left) ∧
      gnTransition phase .return0 scan =
        (0, .scratchEntry, scan, .stay) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gnTransition_delegate_ordinary (phase : Fin 1) (q : G1M.state)
    (scan : Bool) (hf : q ≠ g1DoneQ false) (ht : q ≠ g1DoneQ true) :
    gnTransition phase (.delegated q) scan =
      (0, .delegated (G1M.step q scan).fst,
        (G1M.step q scan).snd.fst, (G1M.step q scan).snd.snd) := by
  simp [gnTransition, hf, ht]

theorem gnTransition_intercept_false (phase : Fin 1) (scan : Bool) :
    gnTransition phase (.delegated (g1DoneQ false)) scan =
      (0, .returnedFalse, scan, .stay) := by
  simp [gnTransition]

theorem gnTransition_intercept_true (phase : Fin 1) (scan : Bool) :
    gnTransition phase (.delegated (g1DoneQ true)) scan =
      (0, .returnedTrue, scan, .stay) := by
  have hne : g1DoneQ true ≠ g1DoneQ false := by
    intro h
    exact G1Mode.noConfusion (congrArg (fun q : G1M.state => q.snd.mode) h)
  simp [gnTransition, hne]

theorem g1M_step_done (b scan : Bool) :
    G1M.step (g1DoneQ b) scan = (g1AcceptQ, scan, .stay) := by
  cases b <;> rfl

theorem g1M_step_accept (scan : Bool) :
    G1M.step g1AcceptQ scan = (g1AcceptQ, scan, .stay) := rfl

theorem gnM_step_embed_ordinary (q : G1M.state) (scan : Bool)
    (hf : q ≠ g1DoneQ false) (ht : q ≠ g1DoneQ true) :
    GNM.step (gnEmbed q) scan =
      (gnEmbed (G1M.step q scan).fst,
        (G1M.step q scan).snd.fst, (G1M.step q scan).snd.snd) := by
  simp [gnEmbed, gnCS, ConstStatePhasedProgram.toPhased,
    PhasedProgram.toTM, gnTransition, hf, ht]

theorem gnM_step_embed_done (b scan : Bool) :
    GNM.step (gnEmbed (g1DoneQ b)) scan =
      (gnReturnedQ b, scan, .stay) := by
  cases b
  · simp [gnEmbed, gnReturnedQ, gnReturnedState, gnCS,
      ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, gnTransition]
  · have hne : g1DoneQ true ≠ g1DoneQ false := by
      intro h
      exact G1Mode.noConfusion (congrArg (fun q : G1M.state => q.snd.mode) h)
    simp [gnEmbed, gnReturnedQ, gnReturnedState, gnCS,
      ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, gnTransition, hne]

/-! ## GN-E1a live lexical scan -/

/-- The GN outer machine as an instance of the shared four-cell scanner. -/
def gnFrameScanner : FrameScanner GNState G1Frame GNDiscoveryMode Unit where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  rejectMode := .reject
  advance := gnDiscoveryAdvance
  complete := gnDiscoveryComplete
  Forward := GNDiscoveryMode.Forward
  st0 := fun mode _ => gnScanControl mode .p0
  st1 := fun mode _ b0 => gnScanControl mode (.p1 b0)
  st2 := fun mode _ b0 b1 => gnScanControl mode (.p2 b0 b1)
  st3 := fun mode _ b0 b1 b2 => gnScanControl mode (.p3 b0 b1 b2)
  complete_decode := fun m b0 b1 b2 b3 => by
    cases h : decodeG1Frame? [b0, b1, b2, b3] <;>
      simp [gnDiscoveryComplete, g1FrameCodec, h]
  step_p0 := fun {m} hm _ scan => by
    cases m <;> simp [GNDiscoveryMode.Forward] at hm ⊢ <;>
      rfl
  step_p1 := fun {m} hm _ b0 scan => by
    cases m <;> simp [GNDiscoveryMode.Forward] at hm ⊢ <;>
      rfl
  step_p2 := fun {m} hm _ b0 b1 scan => by
    cases m <;> simp [GNDiscoveryMode.Forward] at hm ⊢ <;>
      rfl
  step_p3 := fun {m} hm _ b0 b1 b2 scan hne => by
    cases m <;> simp [GNDiscoveryMode.Forward] at hm ⊢ <;>
      simp [gnCS, gnTransition, gnScanControl, hne]

private theorem gnFrameScanner_program : gnFrameScanner.program = gnCS := rfl

private theorem gnFrameScanner_codec : gnFrameScanner.codec = g1FrameCodec := rfl

private theorem gnFrameScanner_machine : gnFrameScanner.machine = GNM := by
  rfl

private theorem gnFrameScanner_advanceList (m : GNDiscoveryMode)
    (fs : List G1Frame) :
    gnFrameScanner.advanceList m fs = gnDiscoveryAdvanceList m fs := by
  induction fs generalizing m with
  | nil => rfl
  | cons f fs ih =>
      change gnFrameScanner.advanceList (gnDiscoveryAdvance m f) fs =
        gnDiscoveryAdvanceList (gnDiscoveryAdvance m f) fs
      exact ih (gnDiscoveryAdvance m f)

private theorem gnFrameScanner_validPath (m : GNDiscoveryMode)
    (fs : List G1Frame) :
    gnFrameScanner.ValidPath m fs ↔ GNDiscoveryValidPath m fs := by
  induction fs generalizing m with
  | nil => exact Iff.rfl
  | cons f fs ih =>
      change (m.Forward ∧ gnDiscoveryAdvance m f ≠ .reject ∧
        gnFrameScanner.ValidPath (gnDiscoveryAdvance m f) fs) ↔
          (m.Forward ∧ gnDiscoveryAdvance m f ≠ .reject ∧
            GNDiscoveryValidPath (gnDiscoveryAdvance m f) fs)
      rw [ih (gnDiscoveryAdvance m f)]

/-- Initial GN tape equals the shared list-backed, blank-padded tape. -/
theorem gnInitialTape_eq_frameListTape (bits : List Bool) :
    (GNM.initialConfig (gnPoint bits)).tape = frameListTape bits := by
  funext i
  simp only [TM.initialConfig, gnPoint, frameListTape]
  split <;> rename_i h
  · simp [List.getD, h]
  · have hi : bits.length ≤ i.val := Nat.le_of_not_gt h
    simp [List.getD, h]

/-- Exact dormant E1b handoff: fixed word-end state, physical head at the
logical GN word length, and the unchanged real initial tape. -/
def gnWordEndConfig (r : GNProgram) :
    Configuration (M := GNM) (encodeGN r).length where
  state := ⟨(0 : Fin 1), .wordEnd⟩
  head := ⟨(encodeGN r).length, by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]
    omega⟩
  tape := (GNM.initialConfig (gnPoint (encodeGN r))).tape

/-- GN-E1a real-input capstone.  The read-only live scan stops immediately
after terminal `finish`; no blank cell is read and no exact-list parser
equivalence is claimed. -/
theorem gnCS_encodeGN_wordEnd (r : GNProgram) :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN r)))
      (encodeGN r).length = gnWordEndConfig r := by
  have hpath : gnFrameScanner.ValidPath .start (encodeGNFrames r) :=
    (gnFrameScanner_validPath _ _).2 (gnDiscovery_encodeGNFrames r).2
  have hsafe : 4 * (([] : List G1Frame).length + (encodeGNFrames r).length) <
      GNM.tapeLength (encodeGN r).length := by
    change 4 * (([] : List G1Frame).length + (encodeGNFrames r).length) <
      (encodeGN r).length + gnClock (encodeGN r).length + 1
    simp only [List.length_nil, Nat.zero_add]
    rw [encodeGN_length]
    omega
  have hscan := gnFrameScanner.scanFrames (encodeGN r).length []
    (encodeGNFrames r) [] .start () hpath (by
      simpa [gnFrameScanner_machine] using hsafe)
  rw [gnFrameScanner_advanceList, (gnDiscovery_encodeGNFrames r).1] at hscan
  have hinit : GNM.initialConfig (gnPoint (encodeGN r)) =
      gnFrameScanner.alignedFrame (encodeGN r).length 0
        (by simpa [gnFrameScanner_machine] using
          TM.tapeLength_pos GNM (encodeGN r).length)
        (frameListTape (encodeGN r)) .start () := by
    apply Configuration.ext_of_components
    · rfl
    · rfl
    · change (GNM.initialConfig (gnPoint (encodeGN r))).tape =
        frameListTape (encodeGN r)
      exact gnInitialTape_eq_frameListTape _
  rw [hinit]
  have hscan' :
      TM.runConfig (M := GNM)
        (gnFrameScanner.alignedFrame (encodeGN r).length 0
          (by simpa [gnFrameScanner_machine] using
            TM.tapeLength_pos GNM (encodeGN r).length)
          (frameListTape (encodeGN r)) .start ())
        (encodeGN r).length =
      gnFrameScanner.alignedFrame (encodeGN r).length
        (4 * (encodeGNFrames r).length) (by
          simpa [gnFrameScanner_machine] using hsafe)
        (frameListTape (encodeGN r)) .wordEnd () := by
    simpa only [gnFrameScanner_machine, gnFrameScanner_codec,
      g1FrameCodec_bits, List.nil_append, List.append_nil, List.length_nil,
      Nat.zero_add, encodeGN_length] using hscan
  rw [hscan']
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    change 4 * (encodeGNFrames r).length = (encodeGN r).length
    exact (encodeGN_length r).symm
  · change frameListTape (encodeGN r) =
      (GNM.initialConfig (gnPoint (encodeGN r))).tape
    exact (gnInitialTape_eq_frameListTape _).symm

/-! ## GN-E1b blank-frame confirmation and scratch entry -/

/-- The complete fixed state at the E1b/E2 scratch-entry boundary. -/
def gnScratchEntryQ : GNM.state := ⟨(0 : Fin 1), .scratchEntry⟩

/-- Exact E1b endpoint: scratch-entry control, physical head at the logical
word end, and the unchanged real initial tape. -/
def gnScratchEntryConfig (r : GNProgram) :
    Configuration (M := GNM) (encodeGN r).length where
  state := gnScratchEntryQ
  head := ⟨(encodeGN r).length, by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]
    omega⟩
  tape := (GNM.initialConfig (gnPoint (encodeGN r))).tape

/-- E1a scan plus the fixed E1b nine-row segment. -/
def gnValidateSteps (r : GNProgram) : Nat := (encodeGN r).length + 9

private theorem gnCS_wordEnd_blankFrame_macro (n h : Nat)
    (hsafe : h + 4 < (Phased.machine gnCS).tapeLength n)
    (tape : Fin ((Phased.machine gnCS).tapeLength n) → Bool)
    (h0 : tape ⟨h, by omega⟩ = false)
    (h1 : tape ⟨h + 1, by omega⟩ = false)
    (h2 : tape ⟨h + 2, by omega⟩ = false)
    (h3 : tape ⟨h + 3, by omega⟩ = false) :
    TM.runConfig (M := Phased.machine gnCS)
        (Phased.alignedAt gnCS gnCS.startPhase n h (by omega) tape .wordEnd) 9 =
      Phased.alignedAt gnCS gnCS.startPhase n h (by omega) tape .scratchEntry := by
  have s0 := Phased.stepRight gnCS gnCS.startPhase n h (by omega) (by omega) tape
    GNState.wordEnd (.blankConfirm (.p1 (tape ⟨h, by omega⟩)))
    (tape ⟨h, by omega⟩) (by rfl)
  rw [writeCell_self, h0] at s0
  have s1 := Phased.stepRight gnCS gnCS.startPhase n (h + 1) (by omega) (by omega) tape
    (.blankConfirm (.p1 false))
    (.blankConfirm (.p2 false (tape ⟨h + 1, by omega⟩)))
    (tape ⟨h + 1, by omega⟩) (by rfl)
  rw [writeCell_self, h1] at s1
  have s2 := Phased.stepRight gnCS gnCS.startPhase n (h + 2) (by omega) (by omega) tape
    (.blankConfirm (.p2 false false))
    (.blankConfirm (.p3 false false (tape ⟨h + 2, by omega⟩)))
    (tape ⟨h + 2, by omega⟩) (by rfl)
  rw [writeCell_self, h2] at s2
  have s3 := Phased.stepRight gnCS gnCS.startPhase n (h + 3) (by omega) hsafe tape
    (.blankConfirm (.p3 false false false)) .blankSeen
    (tape ⟨h + 3, by omega⟩) (by simpa [h3] using
      gnTransition_blankConfirm_zero (0 : Fin 1))
  rw [writeCell_self] at s3
  have hread : TM.runConfig (M := Phased.machine gnCS)
      (Phased.alignedAt gnCS gnCS.startPhase n h (by omega) tape .wordEnd) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n (h + 4) hsafe tape .blankSeen := by
    show TM.runConfig (M := Phased.machine gnCS)
      (Phased.alignedAt gnCS gnCS.startPhase n h (by omega) tape .wordEnd)
      (1 + 1 + 1 + 1) = _
    rw [runConfig_add, runConfig_add, runConfig_add]
    simp only [runConfig_one]
    rw [s0, s1, s2, s3]
  have hback := Phased.holdWalk4 gnCS gnCS.startPhase n h hsafe tape
    GNState.blankSeen .return3 .return2 .return1 .return0
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hentry := Phased.stepStay gnCS gnCS.startPhase n h (by omega) tape
    GNState.return0 .scratchEntry (tape ⟨h, by omega⟩) (by rfl)
  rw [writeCell_self] at hentry
  have hreturn : TM.runConfig (M := Phased.machine gnCS)
      (Phased.alignedAt gnCS gnCS.startPhase n (h + 4) hsafe tape .blankSeen) 5 =
      Phased.alignedAt gnCS gnCS.startPhase n h (by omega) tape .scratchEntry := by
    show TM.runConfig (M := Phased.machine gnCS)
      (Phased.alignedAt gnCS gnCS.startPhase n (h + 4) hsafe tape .blankSeen) (4 + 1) = _
    rw [runConfig_add, hback, runConfig_one, hentry]
  show TM.runConfig (M := Phased.machine gnCS)
    (Phased.alignedAt gnCS gnCS.startPhase n h (by omega) tape .wordEnd) (4 + 5) = _
  rw [runConfig_add, hread, hreturn]

/-- Exact nonblank-first-cell confirmation probe.  Starting at `wordEnd`, a
nonzero first padding cell is buffered, the remaining three cells are read,
and p3 enters stationary reject after exactly four rows, with unchanged tape. -/
theorem gnCS_wordEnd_nonblank_first_reject (n h : Nat)
    (hsafe : h + 4 < (Phased.machine gnCS).tapeLength n)
    (tape : Fin ((Phased.machine gnCS).tapeLength n) → Bool)
    (hfirst : tape ⟨h, by omega⟩ = true) :
    TM.runConfig (M := Phased.machine gnCS)
        (Phased.alignedAt gnCS gnCS.startPhase n h (by omega) tape .wordEnd) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n (h + 3) (by omega) tape .reject := by
  have s0 := Phased.stepRight gnCS gnCS.startPhase n h (by omega) (by omega)
    tape GNState.wordEnd (.blankConfirm (.p1 (tape ⟨h, by omega⟩)))
    (tape ⟨h, by omega⟩) (by rfl)
  rw [writeCell_self, hfirst] at s0
  let b1 := tape ⟨h + 1, by omega⟩
  have s1 := Phased.stepRight gnCS gnCS.startPhase n (h + 1) (by omega)
    (by omega) tape (.blankConfirm (.p1 true)) (.blankConfirm (.p2 true b1))
    b1 (by rfl)
  rw [writeCell_self] at s1
  let b2 := tape ⟨h + 2, by omega⟩
  have s2 := Phased.stepRight gnCS gnCS.startPhase n (h + 2) (by omega)
    (by omega) tape (.blankConfirm (.p2 true b1))
    (.blankConfirm (.p3 true b1 b2)) b2 (by rfl)
  rw [writeCell_self] at s2
  let b3 := tape ⟨h + 3, by omega⟩
  have s3 := Phased.stepStay gnCS gnCS.startPhase n (h + 3) (by omega) tape
    (.blankConfirm (.p3 true b1 b2)) .reject b3 (by
      dsimp [b1, b2, b3]
      cases tape ⟨h + 1, by omega⟩ <;>
        cases tape ⟨h + 2, by omega⟩ <;>
          cases tape ⟨h + 3, by omega⟩ <;> rfl)
  rw [writeCell_self] at s3
  show TM.runConfig (M := Phased.machine gnCS)
    (Phased.alignedAt gnCS gnCS.startPhase n h (by omega) tape .wordEnd)
    (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [s0, s1, s2, s3]

/-- Local E1b capstone.  From the public E1a arrival, exactly four blank reads
and five return/entry rows restore head `N`, preserve the tape exactly, and
enter fixed `scratchEntry` in nine steps. -/
theorem gnCS_wordEnd_to_scratchEntry_exact (r : GNProgram) :
    TM.runConfig (M := GNM) (gnWordEndConfig r) 9 =
      gnScratchEntryConfig r := by
  let N := (encodeGN r).length
  let tape := (GNM.initialConfig (gnPoint (encodeGN r))).tape
  have hsafe : N + 4 < GNM.tapeLength N := by
    simp [N, TM.tapeLength, gnCS, gnClock, g1Clock]
    omega
  have hblank (j : Nat) (hj : N ≤ j) (hfit : j < GNM.tapeLength N) :
      tape ⟨j, hfit⟩ = false := by
    exact GNM.initial_tape_blank (gnPoint (encodeGN r)) hj
  have hmacro := gnCS_wordEnd_blankFrame_macro N N hsafe tape
    (hblank N (by omega) (by omega))
    (hblank (N + 1) (by omega) (by omega))
    (hblank (N + 2) (by omega) (by omega))
    (hblank (N + 3) (by omega) (by omega))
  have hN : N < (Phased.machine gnCS).tapeLength N := by
    exact lt_trans (by omega) hsafe
  have hword : gnWordEndConfig r =
      Phased.alignedAt gnCS gnCS.startPhase N N hN tape .wordEnd := by
    apply Configuration.ext_of_components <;> rfl
  have hscratch : gnScratchEntryConfig r =
      Phased.alignedAt gnCS gnCS.startPhase N N hN tape .scratchEntry := by
    apply Configuration.ext_of_components <;> rfl
  rw [hword, hmacro, hscratch]

/-- Full E1a+E1b capstone from the real encoded input. -/
theorem gnCS_encodeGN_scratchEntry (r : GNProgram) :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN r))) (gnValidateSteps r) =
        gnScratchEntryConfig r := by
  rw [gnValidateSteps, runConfig_add, gnCS_encodeGN_wordEnd,
    gnCS_wordEnd_to_scratchEntry_exact]

/-- Explicit endpoint projections for E2: fixed state, physical head at `N`,
and tape identical to the real initial tape. -/
theorem gnScratchEntryConfig_structure (r : GNProgram) :
    (gnScratchEntryConfig r).state = gnScratchEntryQ ∧
      ((gnScratchEntryConfig r).head : Nat) = (encodeGN r).length ∧
      (gnScratchEntryConfig r).tape =
        (GNM.initialConfig (gnPoint (encodeGN r))).tape := by
  exact ⟨rfl, rfl, rfl⟩

/-- Schedule provenance: E1a's `N` scan, four confirmation reads, and five
fixed return/entry rows. -/
theorem gnValidateSteps_provenance (r : GNProgram) :
    gnValidateSteps r = (encodeGN r).length + 4 + 5 := by
  simp [gnValidateSteps]

/-- Only a bound for the scan/confirmation/return segment, not adequacy for a
future installer, delegated run, loop, or the machine's full clock. -/
theorem gnScanValidateSegment_le_gnClock (N : Nat) :
    N + 9 ≤ gnClock N := by
  have hsquare : N + 1 ≤ (N + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ (by omega)
  unfold gnClock g1Clock
  omega

/-- GN-2's generic `W+16≤N` capacity leaves enough physical GNM room to place
the exact local G1 span at scratch base `N`.  This is arithmetic only; it does
not identify a selected request or install/copy it. -/
theorem gnScratch_room_of_add_sixteen {W N : Nat} (hWN : W + 16 ≤ N) :
    N + gnLocalSpan W ≤ GNM.tapeLength N := by
  have hsegment := gnScanValidateSegment_le_gnClock N
  change N + (W + 5) ≤ N + gnClock N + 1
  omega

/-- Four raw physical reads ending in a rejecting completion.  The first
three rows move right; the p3 completion is stationary, and every row writes
back the bit it scanned. -/
theorem gnFrameScanner_rejectMacrostep (n h : Nat)
    (hsafe : h + 4 < gnFrameScanner.machine.tapeLength n)
    (tape : Fin (gnFrameScanner.machine.tapeLength n) → Bool)
    (m : GNDiscoveryMode)
    (hm : m.Forward)
    (hbad : gnDiscoveryComplete m
      (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩)
      (tape ⟨h + 2, by omega⟩) (tape ⟨h + 3, by omega⟩) = .reject) :
    TM.runConfig (M := gnFrameScanner.machine)
        (gnFrameScanner.alignedFrame n h (by omega) tape m ()) 4 =
      gnFrameScanner.alignedConfigQ n (h + 3) (by omega) tape .reject := by
  show TM.runConfig (M := gnFrameScanner.machine)
      (gnFrameScanner.alignedConfigQ n h (by omega) tape
        (gnFrameScanner.st0 m ())) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have hp0 := gnFrameScanner.alignedStepRight n h (by omega) (by omega) tape
    (gnFrameScanner.st0 m ())
    (gnFrameScanner.st1 m () (tape ⟨h, by omega⟩))
    (tape ⟨h, by omega⟩) (gnFrameScanner.step_p0 hm () _)
  rw [FrameScan.writeCell_self] at hp0
  rw [hp0]
  have hp1 := gnFrameScanner.alignedStepRight n (h + 1) (by omega) (by omega)
    tape (gnFrameScanner.st1 m () (tape ⟨h, by omega⟩))
    (gnFrameScanner.st2 m () (tape ⟨h, by omega⟩)
      (tape ⟨h + 1, by omega⟩))
    (tape ⟨h + 1, by omega⟩)
    (gnFrameScanner.step_p1 hm () _ _)
  rw [FrameScan.writeCell_self] at hp1
  rw [hp1]
  have hp2 := gnFrameScanner.alignedStepRight n (h + 2) (by omega) (by omega)
    tape (gnFrameScanner.st2 m () (tape ⟨h, by omega⟩)
      (tape ⟨h + 1, by omega⟩))
    (gnFrameScanner.st3 m () (tape ⟨h, by omega⟩)
      (tape ⟨h + 1, by omega⟩) (tape ⟨h + 2, by omega⟩))
    (tape ⟨h + 2, by omega⟩)
    (gnFrameScanner.step_p2 hm () _ _ _)
  rw [FrameScan.writeCell_self] at hp2
  rw [hp2]
  have hp3 := gnFrameScanner.alignedStepStay n (h + 3) (by omega) tape
    (gnFrameScanner.st3 m () (tape ⟨h, by omega⟩)
      (tape ⟨h + 1, by omega⟩) (tape ⟨h + 2, by omega⟩))
    GNState.reject (tape ⟨h + 3, by omega⟩) (by
      cases m <;> simp [GNDiscoveryMode.Forward] at hm ⊢ <;>
        simp [gnFrameScanner, gnCS, gnTransition, gnScanControl, hbad])
  rwa [FrameScan.writeCell_self] at hp3

def gnReserved1101Bits : List Bool := [true, true, false, true]

/-- Literal rejecting endpoint for the raw reserved `1101` window. -/
def gnReserved1101RejectConfig : Configuration (M := GNM) 4 where
  state := ⟨(0 : Fin 1), .reject⟩
  head := ⟨3, by
    change 3 < 4 + gnClock 4 + 1
    omega⟩
  tape := (GNM.initialConfig (gnPoint gnReserved1101Bits)).tape

/-- Raw exact four-step reserved-code rejection, with head left at p3 and the
entire blank-padded tape unchanged. -/
theorem gnCS_reserved1101_reject_four :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint gnReserved1101Bits)) 4 =
        gnReserved1101RejectConfig := by
  have hsafe : 0 + 4 < GNM.tapeLength 4 := by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]
  have hmacro := gnFrameScanner_rejectMacrostep 4 0 hsafe
    (GNM.initialConfig (gnPoint gnReserved1101Bits)).tape .start (by trivial)
    (by rfl)
  have hinit : GNM.initialConfig (gnPoint gnReserved1101Bits) =
      gnFrameScanner.alignedFrame 4 0 (by
        simpa [gnFrameScanner_machine] using hsafe)
        (GNM.initialConfig (gnPoint gnReserved1101Bits)).tape .start () := by
    apply Configuration.ext_of_components <;> rfl
  have hmacro' : TM.runConfig (M := GNM)
      (gnFrameScanner.alignedFrame 4 0 (by
        simpa [gnFrameScanner_machine] using hsafe)
        (GNM.initialConfig (gnPoint gnReserved1101Bits)).tape .start ()) 4 =
      gnFrameScanner.alignedConfigQ 4 3 (by
        simpa [gnFrameScanner_machine] using (show 3 < GNM.tapeLength 4 by
          change 3 < 4 + gnClock 4 + 1
          omega))
        (GNM.initialConfig (gnPoint gnReserved1101Bits)).tape .reject := by
    simpa only [gnFrameScanner_machine, Nat.zero_add] using hmacro
  rw [hinit, hmacro']
  apply Configuration.ext_of_components <;> rfl

/-- Literal reserved completions in the machine table: `1101`, `1110`, and
`1111` all enter the fixed GN reject state without moving from p3. -/
theorem gnTransition_reserved_windows (m : GNDiscoveryMode) :
    gnTransition 0 (.scanning ⟨m, .p3 true true false⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition 0 (.scanning ⟨m, .p3 true true true⟩) false =
        (0, .reject, false, .stay) ∧
      gnTransition 0 (.scanning ⟨m, .p3 true true true⟩) true =
        (0, .reject, true, .stay) := by
  cases m <;> simp [gnTransition, gnDiscoveryComplete, decodeG1Frame?,
    gnScanControl]

/-- Representative decoded but misplaced frames also take the literal reject
row at the initial lexical mode. -/
theorem gnTransition_start_malformed_windows :
    gnTransition 0 (.scanning ⟨.start, .p3 false false false⟩) false =
        (0, .reject, false, .stay) ∧
      gnTransition 0 (.scanning ⟨.start, .p3 true true false⟩) false =
        (0, .reject, false, .stay) ∧
      gnTransition 0 (.scanning ⟨.start, .p3 true false false⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition 0 (.scanning ⟨.start, .p3 false true false⟩) false =
        (0, .reject, false, .stay) ∧
      gnTransition 0 (.scanning ⟨.start, .p3 false true true⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition 0 (.scanning ⟨.assignments, .p3 false false false⟩) true =
        (0, .reject, true, .stay) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem gnM_step_reject (scan : Bool) :
    GNM.step ⟨(0 : Fin 1), GNState.reject⟩ scan =
      (⟨(0 : Fin 1), GNState.reject⟩, scan, .stay) := rfl

/-- Reject is a stationary read-only sink under arbitrary physical padding. -/
theorem gnCS_reject_stable {n : Nat} (c : Configuration (M := GNM) n)
    (hstate : c.state = ⟨(0 : Fin 1), GNState.reject⟩) (k : Nat) :
    TM.runConfig (M := GNM) c k = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [runConfig_succ, ih]
      apply Configuration.ext_of_components
      · change (GNM.step c.state (c.tape c.head)).fst = c.state
        rw [hstate]
        rfl
      · rw [stepConfig_head, hstate, gnM_step_reject]
        rfl
      · rw [stepConfig_tape, hstate, gnM_step_reject]
        funext i
        by_cases hi : i = c.head
        · subst i
          exact Configuration.write_self _ _ _
        · exact Configuration.write_other _ hi _

/-! ## Source-only proper-prefix exclusion and concrete delegation -/

private theorem g1_runConfig_accept_state {W : Nat}
    (c : Configuration (M := G1M) W) (hstate : c.state = g1AcceptQ)
    (k : Nat) :
    (TM.runConfig (M := G1M) c k).state = g1AcceptQ := by
  induction k with
  | zero => simpa using hstate
  | succ k ih =>
      rw [runConfig_succ, stepConfig_state, ih, g1M_step_accept]

/-- A successful canonical source run reaches neither exact output-done state
at a proper prefix.  This proof uses only source transition rows, source accept
stability, and the merged exact source endpoint. -/
theorem g1CS_gate_done_no_early_outputDone (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    (j : Nat) (hj : j < g1GateDoneSteps r) (b : Bool) :
    (TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) j).state ≠ g1DoneQ b := by
  intro hearly
  let c0 := G1M.initialConfig (g1Point (encodeG1 r))
  have hnext : (TM.runConfig (M := G1M) c0 (j + 1)).state = g1AcceptQ := by
    rw [runConfig_succ, stepConfig_state, hearly, g1M_step_done]
  have hsplit : g1GateDoneSteps r =
      (j + 1) + (g1GateDoneSteps r - (j + 1)) := by omega
  have haccept :
      (TM.runConfig (M := G1M) c0 (g1GateDoneSteps r)).state = g1AcceptQ := by
    rw [hsplit, runConfig_add]
    exact g1_runConfig_accept_state _ hnext _
  have hdone :
      (TM.runConfig (M := G1M) c0 (g1GateDoneSteps r)).state =
        g1DoneQ res := by
    rw [g1CS_gate_done_exact r hc res hs]
    rfl
  rw [hdone] at haccept
  have hm := congrArg (fun q : G1M.state => q.snd.mode) haccept
  cases res <;> exact G1Mode.noConfusion hm

/-- The concrete shell delegates the complete successful canonical five-tag
source prefix, and only that proper prefix. -/
theorem gn_g1_gate_done_delegates (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    G1RunDelegates GNM gnEmbed
      (G1M.initialConfig (g1Point (encodeG1 r))) (g1GateDoneSteps r) := by
  intro j hj
  let c := TM.runConfig (M := G1M)
    (G1M.initialConfig (g1Point (encodeG1 r))) j
  have hf : c.state ≠ g1DoneQ false :=
    g1CS_gate_done_no_early_outputDone r hc res hs j hj false
  have ht : c.state ≠ g1DoneQ true :=
    g1CS_gate_done_no_early_outputDone r hc res hs j hj true
  unfold G1StepDelegates
  exact gnM_step_embed_ordinary c.state (c.tape c.head) hf ht

/-- Delegation genuinely fails at either intercepted output-done endpoint. -/
theorem gn_g1_outputDone_not_delegates {W : Nat}
    (c : Configuration (M := G1M) W) (b : Bool)
    (hstate : c.state = g1DoneQ b) :
    ¬ G1StepDelegates GNM gnEmbed c := by
  intro h
  unfold G1StepDelegates at h
  rw [hstate, gnM_step_embed_done, g1M_step_done] at h
  have hq := congrArg (fun out => out.fst.snd) h
  cases b <;> exact GNState.noConfusion hq

/-! ## Minimal endpoint geometry -/

/-- The real G1 initial head lies in its exact local relocation span. -/
theorem g1InitialConfig_head_lt_gnLocalSpan (r : G1Request) :
    ((G1M.initialConfig (g1Point (encodeG1 r))).head : Nat) <
      gnLocalSpan (encodeG1 r).length := by
  simp [gnLocalSpan]

/-- The exact output-done exit head lies in the same local span. -/
theorem g1OutputDoneConfig_head_lt_gnLocalSpan (r : G1Request) (res : Bool) :
    ((g1OutputDoneConfig r res).head : Nat) <
      gnLocalSpan (encodeG1 r).length := by
  simp [g1OutputExitHead, g1OutputBase_eq, gnLocalSpan, encodeG1_length]
  omega

/-! ## Concrete shifted source run and intercepted endpoint -/

/-- Overlay the exact `W+5` source footprint into a caller ambient tape. -/
def gnGateShiftConfig (r : G1Request) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    Configuration (M := GNM) N :=
  gnShiftConfig GNM base gnEmbed ambient
    (G1M.initialConfig (g1Point (encodeG1 r))) hroom
    (g1InitialConfig_head_lt_gnLocalSpan r)

private theorem gnShiftConfig_congr {W N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan W ≤ GNM.tapeLength N)
    {c d : Configuration (M := G1M) W} (hcd : c = d)
    (hc : (c.head : Nat) < gnLocalSpan W)
    (hd : (d.head : Nat) < gnLocalSpan W) :
    gnShiftConfig GNM base gnEmbed ambient c hroom hc =
      gnShiftConfig GNM base gnEmbed ambient d hroom hd := by
  subst d
  rfl

/-- Exact relocation conjugacy from the shifted real source initial
configuration through the complete successful output-done prefix. -/
theorem gnCS_gate_shift_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
        (g1GateDoneSteps r) =
      gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
        (g1OutputDoneConfig_head_lt_gnLocalSpan r res) := by
  unfold gnGateShiftConfig
  rw [gn_delegate_run_shift gnEmbed ambient _ hroom
    (g1InitialConfig_head_lt_gnLocalSpan r)
    (g1CS_gate_done_trace_safe r hc res hs).1
    (gn_g1_gate_done_delegates r hc res hs)]
  exact gnShiftConfig_congr ambient hroom
    (g1CS_gate_done_trace_safe r hc res hs).2 _ _

/-- Every target prefix through output-done preserves every cell outside the
shifted exact local footprint. -/
theorem gnCS_gate_shift_outside_every_prefix (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base j : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N)
    (hj : j ≤ g1GateDoneSteps r) (i : Fin (GNM.tapeLength N))
    (hout : (i : Nat) < base ∨
      base + gnLocalSpan (encodeG1 r).length ≤ (i : Nat)) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom) j).tape i =
      ambient i := by
  unfold gnGateShiftConfig
  exact gn_delegate_run_shift_outside_prefix gnEmbed ambient _ hroom
    (g1InitialConfig_head_lt_gnLocalSpan r)
    (g1CS_gate_done_trace_safe r hc res hs).1
    (gn_g1_gate_done_delegates r hc res hs) hj i hout

/-- Replace only the control state of a target configuration by the fixed
result-indexed returned state. -/
def gnReturnConfig {N : Nat} (res : Bool) (c : Configuration (M := GNM) N) :
    Configuration (M := GNM) N :=
  { c with state := gnReturnedQ res }

private theorem gnCS_step_outputDone {N : Nat}
    (c : Configuration (M := GNM) N) (res : Bool)
    (hstate : c.state = gnEmbed (g1DoneQ res)) :
    TM.runConfig (M := GNM) c 1 = gnReturnConfig res c := by
  rw [runConfig_one]
  apply Configuration.ext_of_components
  · rw [stepConfig_state, hstate, gnM_step_embed_done]
    rfl
  · rw [stepConfig_head, hstate, gnM_step_embed_done]
    rfl
  · rw [stepConfig_tape, hstate, gnM_step_embed_done]
    funext i
    by_cases hi : i = c.head
    · subst i
      exact Configuration.write_self c c.head (c.tape c.head)
    · exact Configuration.write_other c hi (c.tape c.head)

/-- One target step intercepts an exact shifted output-done source state.  It
is stationary and writes back the scanned bit, hence preserves head and tape. -/
theorem gnCS_step_shifted_outputDone (r : G1Request) (res : Bool)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM)
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) 1 =
      gnReturnConfig res
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) := by
  apply gnCS_step_outputDone
  rfl

/-- Concrete relocation capstone: the safe shifted G1 run reaches exact
shifted output-done, and the one additional target row returns its result. -/
theorem gnCS_gate_shift_intercept_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
        (g1GateDoneSteps r + 1) =
      gnReturnConfig res
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) := by
  rw [runConfig_add, gnCS_gate_shift_exact r hc res hs ambient hroom]
  exact gnCS_step_shifted_outputDone r res ambient hroom

/-- Exact result-indexed target state after the intercepted shifted run. -/
theorem gnCS_gate_shift_intercept_state (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)).state = gnReturnedQ res := by
  rw [gnCS_gate_shift_intercept_exact r hc res hs ambient hroom]
  rfl

/-- Exact fixed outer mode after the intercepted shifted run. -/
theorem gnCS_gate_shift_intercept_mode (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)).state.snd = gnReturnedState res := by
  rw [gnCS_gate_shift_intercept_exact r hc res hs ambient hroom]
  rfl

/-- The same capstone exposed at the outer-mode level, with exact unchanged
head and tape relative to the shifted source endpoint. -/
theorem gnCS_gate_shift_intercept_structure (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    let out := TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)
    let shifted := gnShiftConfig GNM base gnEmbed ambient
      (g1OutputDoneConfig r res) hroom
      (g1OutputDoneConfig_head_lt_gnLocalSpan r res)
    out.state.snd = gnReturnedState res ∧
      out.head = shifted.head ∧ out.tape = shifted.tape := by
  dsimp only
  rw [gnCS_gate_shift_intercept_exact r hc res hs ambient hroom]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Concrete schedule probes -/

namespace GNFixedDelegateProbes

open G1AResultProbes

def emptyProgram : GNProgram := ⟨[], ⟨[]⟩⟩

def oneConstFalseProgram : GNProgram :=
  ⟨[], ⟨[.const false]⟩⟩

theorem literal_encodeGN_lengths :
    (encodeGN emptyProgram).length = 20 ∧
      (encodeGN oneConstFalseProgram).length = 48 := by
  decide

/-- Literal empty-program scan: five frames, twenty physical steps. -/
theorem literal_empty_wordEnd :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN emptyProgram))) 20 =
        gnWordEndConfig emptyProgram := by
  simpa only [literal_encodeGN_lengths.1] using
    gnCS_encodeGN_wordEnd emptyProgram

/-- Literal nonempty scan: one constant record, twelve frames, forty-eight
physical steps. -/
theorem literal_oneConstFalse_wordEnd :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 48 =
        gnWordEndConfig oneConstFalseProgram := by
  simpa only [literal_encodeGN_lengths.2] using
    gnCS_encodeGN_wordEnd oneConstFalseProgram

/-- Literal empty-program E1a+E1b schedule: `20 + 9 = 29`. -/
theorem literal_empty_scratchEntry :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN emptyProgram))) 29 =
        gnScratchEntryConfig emptyProgram := by
  have h := gnCS_encodeGN_scratchEntry emptyProgram
  simpa [gnValidateSteps, literal_encodeGN_lengths.1] using h

/-- Literal one-constant-false E1a+E1b schedule: `48 + 9 = 57`. -/
theorem literal_oneConstFalse_scratchEntry :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 57 =
        gnScratchEntryConfig oneConstFalseProgram := by
  have h := gnCS_encodeGN_scratchEntry oneConstFalseProgram
  simpa [gnValidateSteps, literal_encodeGN_lengths.2] using h

/-- Literal true probe: `N=64`, `base=7`, all-true ambient, `229+1=230`. -/
theorem literal_input_true_shifted_intercept :
    TM.runConfig (M := GNM)
      (gnGateShiftConfig (N := 64) (base := 7) reqInputT (fun _ => true) (by decide))
      230 =
    gnReturnConfig true
      (gnShiftConfig GNM 7 gnEmbed (fun _ => true)
        (g1OutputDoneConfig reqInputT true) (by decide)
        (g1OutputDoneConfig_head_lt_gnLocalSpan reqInputT true)) := by
  have h := gnCS_gate_shift_intercept_exact reqInputT
    literal_canonical.1 true literal_specs.1
    (N := 64) (base := 7) (fun _ => true) (by decide)
  rw [G1FiveTagTraceProbes.literal_done_steps.1] at h
  simpa using h

/-- Literal false probe: `N=64`, `base=7`, all-true ambient, `151+1=152`. -/
theorem literal_const_false_shifted_intercept :
    TM.runConfig (M := GNM)
      (gnGateShiftConfig (N := 64) (base := 7) reqConstF (fun _ => true) (by decide))
      152 =
    gnReturnConfig false
      (gnShiftConfig GNM 7 gnEmbed (fun _ => true)
        (g1OutputDoneConfig reqConstF false) (by decide)
        (g1OutputDoneConfig_head_lt_gnLocalSpan reqConstF false)) := by
  have h := gnCS_gate_shift_intercept_exact reqConstF
    literal_canonical.2.2.2.2.1 false literal_specs.2.2.2.2.1
    (N := 64) (base := 7) (fun _ => true) (by decide)
  rw [G1FiveTagTraceProbes.literal_done_steps.2.1] at h
  simpa using h

end GNFixedDelegateProbes

end Pnp3.Internal.PsubsetPpoly.TM
