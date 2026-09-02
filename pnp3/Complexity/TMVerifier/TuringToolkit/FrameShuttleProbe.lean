import Complexity.TMVerifier.TuringToolkit.FrameShuttle
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma

/-!
# Fresh executable probe for the generic frame shuttle

This alphabet, control, auxiliary latch and program are unrelated to T1/G1.
The positive run has two middle frames and takes exactly 45 steps.  A separate
negative theorem shows that inserting the decoded marker destroys the forward
valid path required by the kernel.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

open Pnp3.Internal.PsubsetPpoly.TM

inductive ShuttleProbeFrame
  | blank | marker | source (b : Bool) | middle (b : Bool) | image (b : Bool)
  deriving Fintype, DecidableEq, Repr

def ShuttleProbeFrame.bits : ShuttleProbeFrame → List Bool
  | .blank => [false, false, false, false]
  | .marker => [false, false, false, true]
  | .source b => [false, false, true, b]
  | .middle b => [false, true, false, b]
  | .image b => [false, true, true, b]

def decodeShuttleProbeFrame? : List Bool → Option ShuttleProbeFrame
  | [false, false, false, false] => some .blank
  | [false, false, false, true] => some .marker
  | [false, false, true, false] => some (.source false)
  | [false, false, true, true] => some (.source true)
  | [false, true, false, false] => some (.middle false)
  | [false, true, false, true] => some (.middle true)
  | [false, true, true, false] => some (.image false)
  | [false, true, true, true] => some (.image true)
  | _ => none

def shuttleProbeCodec : FrameCodec ShuttleProbeFrame where
  bits := ShuttleProbeFrame.bits
  decode? := decodeShuttleProbeFrame?
  bits_length := by intro f; cases f <;> rfl
  decode_bits := by
    intro f
    cases f with
    | blank => rfl
    | marker => rfl
    | source b => cases b <;> rfl
    | middle b => cases b <;> rfl
    | image b => cases b <;> rfl

def shuttleProbePayload : ShuttleProbeFrame → Bool
  | .source b | .middle b | .image b => b
  | .blank | .marker => false

def shuttleProbeImage (f : ShuttleProbeFrame) : ShuttleProbeFrame :=
  .image (shuttleProbePayload f)

structure ShuttleProbeAux where
  flag : Bool
  held : ShuttleProbeFrame
  deriving Fintype, DecidableEq, Repr

def shuttleProbeLatch (a : ShuttleProbeAux) (f : ShuttleProbeFrame) :
    ShuttleProbeAux := ⟨a.flag, f⟩

inductive ShuttleProbeMode | seek | dest | rev | revStop | reject
  deriving Fintype, DecidableEq, Repr

inductive ShuttleProbePos | q0 | q1 | q2 | q3
  deriving Fintype, DecidableEq, Repr

inductive ShuttleProbeTag
  | probe | turn | mark | forward (m : ShuttleProbeMode) | destWrite
  | reverse (m : ShuttleProbeMode) | restore | exit | bad
  deriving Fintype, DecidableEq, Repr

set_option synthInstance.maxSize 2048 in
structure ShuttleProbeState where
  tag : ShuttleProbeTag
  pos : ShuttleProbePos
  b0 : Bool
  b1 : Bool
  b2 : Bool
  aux : ShuttleProbeAux
  deriving Fintype, DecidableEq, Repr

abbrev shuttleProbeState (tag : ShuttleProbeTag) (pos : ShuttleProbePos)
    (b0 b1 b2 : Bool) (a : ShuttleProbeAux) : ShuttleProbeState :=
  ⟨tag, pos, b0, b1, b2, a⟩

def shuttleProbeAdvance : ShuttleProbeMode → ShuttleProbeFrame → ShuttleProbeMode
  | .seek, .blank => .dest
  | .seek, .marker => .reject
  | .seek, _ => .seek
  | _, _ => .reject

def shuttleProbeComplete (m : ShuttleProbeMode) (b0 b1 b2 b3 : Bool) :
    ShuttleProbeMode :=
  match decodeShuttleProbeFrame? [b0, b1, b2, b3] with
  | some f => shuttleProbeAdvance m f
  | none => .reject

def ShuttleProbeForward : ShuttleProbeMode → Prop
  | .seek => True
  | _ => False

theorem ShuttleProbeForward.eq {m} (h : ShuttleProbeForward m) : m = .seek := by
  cases m <;> simp_all [ShuttleProbeForward]

def shuttleProbeRevAdvance : ShuttleProbeMode → ShuttleProbeFrame →
    ShuttleProbeMode
  | .rev, .marker => .revStop
  | .rev, .blank => .reject
  | .rev, _ => .rev
  | _, _ => .reject

def shuttleProbeRevComplete (m : ShuttleProbeMode) (b0 b1 b2 b3 : Bool) :
    ShuttleProbeMode :=
  match decodeShuttleProbeFrame? [b0, b1, b2, b3] with
  | some f => shuttleProbeRevAdvance m f
  | none => .reject

def ShuttleProbeReverse : ShuttleProbeMode → Prop
  | .rev => True
  | _ => False

theorem ShuttleProbeReverse.eq {m} (h : ShuttleProbeReverse m) : m = .rev := by
  cases m <;> simp_all [ShuttleProbeReverse]

def ShuttleProbeStop (m : ShuttleProbeMode) : Prop := m = .revStop

def shuttleProbeCode0 : ShuttleProbeFrame → Bool := fun _ => false
def shuttleProbeCode1 : ShuttleProbeFrame → Bool
  | .blank | .marker | .source _ => false
  | .middle _ | .image _ => true
def shuttleProbeCode2 : ShuttleProbeFrame → Bool
  | .source _ | .image _ => true
  | _ => false
def shuttleProbeCode3 : ShuttleProbeFrame → Bool
  | .blank | .source false | .middle false | .image false => false
  | _ => true

theorem shuttleProbe_bits_components (f : ShuttleProbeFrame) :
    f.bits = [shuttleProbeCode0 f, shuttleProbeCode1 f,
      shuttleProbeCode2 f, shuttleProbeCode3 f] := by
  cases f with
  | blank => rfl
  | marker => rfl
  | source b => cases b <;> rfl
  | middle b => cases b <;> rfl
  | image b => cases b <;> rfl

def shuttleProbeTransition (_ : Fin 1) (s : ShuttleProbeState) (scan : Bool) :
    Fin 1 × ShuttleProbeState × Bool × Move :=
  match s.tag with
  | .probe =>
      match s.pos with
      | .q0 => (0, shuttleProbeState .probe .q1 scan false false s.aux,
          scan, .right)
      | .q1 => (0, shuttleProbeState .probe .q2 s.b0 scan false s.aux,
          scan, .right)
      | .q2 => (0, shuttleProbeState .probe .q3 s.b0 s.b1 scan s.aux,
          scan, .right)
      | .q3 =>
          match decodeShuttleProbeFrame? [s.b0, s.b1, s.b2, scan] with
          | some f => (0, shuttleProbeState .turn .q3 false false false
              (shuttleProbeLatch s.aux f), scan, .right)
          | none => (0, shuttleProbeState .bad .q0 false false false s.aux,
              scan, .right)
  | .turn =>
      match s.pos with
      | .q3 => (0, shuttleProbeState .turn .q2 false false false s.aux,
          scan, .left)
      | .q2 => (0, shuttleProbeState .turn .q1 false false false s.aux,
          scan, .left)
      | .q1 => (0, shuttleProbeState .turn .q0 false false false s.aux,
          scan, .left)
      | .q0 => (0, shuttleProbeState .mark .q0 false false false s.aux,
          scan, .left)
  | .mark =>
      match s.pos with
      | .q0 => (0, shuttleProbeState .mark .q1 false false false s.aux,
          false, .right)
      | .q1 => (0, shuttleProbeState .mark .q2 false false false s.aux,
          false, .right)
      | .q2 => (0, shuttleProbeState .mark .q3 false false false s.aux,
          false, .right)
      | .q3 => (0, shuttleProbeState (.forward .seek) .q0 false false false s.aux,
          true, .right)
  | .forward .seek =>
      match s.pos with
      | .q0 => (0, shuttleProbeState (.forward .seek) .q1 scan false false s.aux,
          scan, .right)
      | .q1 => (0, shuttleProbeState (.forward .seek) .q2 s.b0 scan false s.aux,
          scan, .right)
      | .q2 => (0, shuttleProbeState (.forward .seek) .q3 s.b0 s.b1 scan s.aux,
          scan, .right)
      | .q3 =>
          let next := shuttleProbeComplete .seek s.b0 s.b1 s.b2 scan
          (0, shuttleProbeState (.forward next) .q0 false false false s.aux,
            scan, .right)
  | .forward .dest =>
      (0, shuttleProbeState .destWrite .q3 false false false s.aux,
        scan, .left)
  | .forward _ =>
      (0, shuttleProbeState .bad .q0 false false false s.aux, scan, .stay)
  | .destWrite =>
      let b := shuttleProbePayload s.aux.held
      match s.pos with
      | .q3 => (0, shuttleProbeState .destWrite .q2 false false false s.aux,
          b, .left)
      | .q2 => (0, shuttleProbeState .destWrite .q1 false false false s.aux,
          true, .left)
      | .q1 => (0, shuttleProbeState .destWrite .q0 false false false s.aux,
          true, .left)
      | .q0 => (0, shuttleProbeState (.reverse .rev) .q3 false false false s.aux,
          false, .left)
  | .reverse .rev =>
      match s.pos with
      | .q3 => (0, shuttleProbeState (.reverse .rev) .q2 false false scan s.aux,
          scan, .left)
      | .q2 => (0, shuttleProbeState (.reverse .rev) .q1 false scan s.b2 s.aux,
          scan, .left)
      | .q1 => (0, shuttleProbeState (.reverse .rev) .q0 scan s.b1 s.b2 s.aux,
          scan, .left)
      | .q0 =>
          let next := shuttleProbeRevComplete .rev scan s.b0 s.b1 s.b2
          if next = .revStop then
            (0, shuttleProbeState .restore .q0 false false false s.aux,
              scan, .stay)
          else
            (0, shuttleProbeState (.reverse next) .q3 false false false s.aux,
              scan, .left)
  | .reverse _ =>
      (0, shuttleProbeState .bad .q0 false false false s.aux, scan, .stay)
  | .restore =>
      match s.pos with
      | .q0 => (0, shuttleProbeState .restore .q1 false false false s.aux,
          shuttleProbeCode0 s.aux.held, .right)
      | .q1 => (0, shuttleProbeState .restore .q2 false false false s.aux,
          shuttleProbeCode1 s.aux.held, .right)
      | .q2 => (0, shuttleProbeState .restore .q3 false false false s.aux,
          shuttleProbeCode2 s.aux.held, .right)
      | .q3 => (0, shuttleProbeState .exit .q0 false false false s.aux,
          shuttleProbeCode3 s.aux.held, .right)
  | .exit => (0, s, scan, .stay)
  | .bad => (0, s, scan, .stay)

def shuttleProbeClock (n : Nat) : Nat := 128 * (n + 1)

def shuttleProbeCS : ConstStatePhasedProgram ShuttleProbeState where
  numPhases := 1
  startPhase := 0
  startState := shuttleProbeState .probe .q0 false false false ⟨false, .blank⟩
  acceptPhase := 0
  acceptState := shuttleProbeState .exit .q0 false false false ⟨false, .blank⟩
  transition := shuttleProbeTransition
  timeBound := shuttleProbeClock

def shuttleProbeCore : FrameScanner ShuttleProbeState ShuttleProbeFrame
    ShuttleProbeMode ShuttleProbeAux where
  program := shuttleProbeCS
  phase := shuttleProbeCS.startPhase
  codec := shuttleProbeCodec
  rejectMode := .reject
  advance := shuttleProbeAdvance
  complete := shuttleProbeComplete
  Forward := ShuttleProbeForward
  st0 := fun m a => shuttleProbeState (.forward m) .q0 false false false a
  st1 := fun m a b0 => shuttleProbeState (.forward m) .q1 b0 false false a
  st2 := fun m a b0 b1 => shuttleProbeState (.forward m) .q2 b0 b1 false a
  st3 := fun m a b0 b1 b2 => shuttleProbeState (.forward m) .q3 b0 b1 b2 a
  complete_decode := by
    intro m b0 b1 b2 b3
    rw [show shuttleProbeCodec.decode? [b0, b1, b2, b3] =
      decodeShuttleProbeFrame? [b0, b1, b2, b3] by rfl]
    unfold shuttleProbeComplete
    cases decodeShuttleProbeFrame? [b0, b1, b2, b3] <;> rfl
  step_p0 := by intro m hm a scan; obtain rfl := hm.eq; rfl
  step_p1 := by intro m hm a b0 scan; obtain rfl := hm.eq; rfl
  step_p2 := by intro m hm a b0 b1 scan; obtain rfl := hm.eq; rfl
  step_p3 := by intro m hm a b0 b1 b2 scan _; obtain rfl := hm.eq; rfl

def shuttleProbe : FrameShuttle ShuttleProbeState ShuttleProbeFrame
    ShuttleProbeMode ShuttleProbeAux where
  core := shuttleProbeCore
  blank := .blank
  marker := .marker
  image := shuttleProbeImage
  latch := shuttleProbeLatch
  carry := ShuttleProbeAux.held
  carry_latch := by intro a f; rfl
  blank_bits := rfl
  blank_ne_marker := by decide
  image_ne_blank := by intro f; cases f <;> simp [shuttleProbeImage]
  image_ne_marker := by intro f; cases f <;> simp [shuttleProbeImage]
  pst0 := fun a => shuttleProbeState .probe .q0 false false false a
  pst1 := fun a b0 => shuttleProbeState .probe .q1 b0 false false a
  pst2 := fun a b0 b1 => shuttleProbeState .probe .q2 b0 b1 false a
  pst3 := fun a b0 b1 b2 => shuttleProbeState .probe .q3 b0 b1 b2 a
  turnBack3 := fun a => shuttleProbeState .turn .q3 false false false a
  probe_p0 := by intro a scan; rfl
  probe_p1 := by intro a b0 scan; rfl
  probe_p2 := by intro a b0 b1 scan; rfl
  probe_p3 := by
    intro a b0 b1 b2 scan f h
    have h' : decodeShuttleProbeFrame? [b0, b1, b2, scan] = some f := by
      simpa [shuttleProbeCore, shuttleProbeCodec] using h
    simp [shuttleProbeCore, shuttleProbeCS, shuttleProbeTransition, h']
  turnBack2 := fun a => shuttleProbeState .turn .q2 false false false a
  turnBack1 := fun a => shuttleProbeState .turn .q1 false false false a
  turnBack0 := fun a => shuttleProbeState .turn .q0 false false false a
  mark0 := fun a => shuttleProbeState .mark .q0 false false false a
  turnBack_p3 := by intro a scan; rfl
  turnBack_p2 := by intro a scan; rfl
  turnBack_p1 := by intro a scan; rfl
  turnBack_p0 := by intro a scan; rfl
  mark1 := fun a => shuttleProbeState .mark .q1 false false false a
  mark2 := fun a => shuttleProbeState .mark .q2 false false false a
  mark3 := fun a => shuttleProbeState .mark .q3 false false false a
  mw0 := false
  mw1 := false
  mw2 := false
  mw3 := true
  marker_bits := rfl
  seekMode := .seek
  destMode := .dest
  seek_forward := trivial
  seek_blank := rfl
  seek_marker := rfl
  seek_other := by
    intro f hb hm
    cases f <;> simp_all [shuttleProbeCore, shuttleProbeAdvance]
  seek_not_reject := by decide
  dest_not_reject := by decide
  mark_p0 := by intro a scan; rfl
  mark_p1 := by intro a scan; rfl
  mark_p2 := by intro a scan; rfl
  mark_p3 := by intro a scan; rfl
  revStop := ShuttleProbeStop
  revAdvance := shuttleProbeRevAdvance
  revComplete := shuttleProbeRevComplete
  revReverse := ShuttleProbeReverse
  rst3 := fun m a => shuttleProbeState (.reverse m) .q3 false false false a
  rst2 := fun m a b3 => shuttleProbeState (.reverse m) .q2 false false b3 a
  rst1 := fun m a b2 b3 => shuttleProbeState (.reverse m) .q1 false b2 b3 a
  rst0 := fun m a b1 b2 b3 => shuttleProbeState (.reverse m) .q0 b1 b2 b3 a
  revStopState := fun _ a => shuttleProbeState .restore .q0 false false false a
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    have h' : decodeShuttleProbeFrame? [b0, b1, b2, b3] = some f := by
      simpa [shuttleProbeCore, shuttleProbeCodec] using h
    simp [shuttleProbeRevComplete, h']
  rev_p3 := by intro m hm a scan; obtain rfl := hm.eq; rfl
  rev_p2 := by intro m hm a b3 scan; obtain rfl := hm.eq; rfl
  rev_p1 := by intro m hm a b2 b3 scan; obtain rfl := hm.eq; rfl
  rev_p0 := by
    intro m hm a b1 b2 b3 scan hn
    obtain rfl := hm.eq
    change shuttleProbeRevComplete .rev scan b1 b2 b3 ≠ .revStop at hn
    simp only [shuttleProbeCore, shuttleProbeCS, shuttleProbeTransition]
    rw [if_neg hn]
  rev_p0_stop := by
    intro m hm a b1 b2 b3 scan hs
    obtain rfl := hm.eq
    change shuttleProbeRevComplete .rev scan b1 b2 b3 = .revStop at hs
    simp only [shuttleProbeCore, shuttleProbeCS, shuttleProbeTransition]
    rw [if_pos hs]
  revMode := .rev
  revStopMode := .revStop
  rev_mode := trivial
  rev_nostop := by simp [ShuttleProbeStop]
  rev_marker := rfl
  rev_marker_stops := rfl
  rev_other := by
    intro f hb hm
    cases f <;> simp_all [shuttleProbeRevAdvance]
  dest3 := fun a => shuttleProbeState .destWrite .q3 false false false a
  turn_destination := by intro a scan; rfl
  dest2 := fun a => shuttleProbeState .destWrite .q2 false false false a
  dest1 := fun a => shuttleProbeState .destWrite .q1 false false false a
  dest0 := fun a => shuttleProbeState .destWrite .q0 false false false a
  dw0 := fun _ => false
  dw1 := fun _ => true
  dw2 := fun _ => true
  dw3 := fun a => shuttleProbePayload a.held
  dest_bits := by
    intro a
    cases h : a.held <;> rfl
  dest_p3 := by intro a scan; rfl
  dest_p2 := by intro a scan; rfl
  dest_p1 := by intro a scan; rfl
  dest_p0 := by intro a scan; rfl
  restore1 := fun a => shuttleProbeState .restore .q1 false false false a
  restore2 := fun a => shuttleProbeState .restore .q2 false false false a
  restore3 := fun a => shuttleProbeState .restore .q3 false false false a
  exitState := fun a => shuttleProbeState .exit .q0 false false false a
  rw0 := fun a => shuttleProbeCode0 a.held
  rw1 := fun a => shuttleProbeCode1 a.held
  rw2 := fun a => shuttleProbeCode2 a.held
  rw3 := fun a => shuttleProbeCode3 a.held
  restore_bits := fun a => shuttleProbe_bits_components a.held
  restore_p0 := by intro a scan; rfl
  restore_p1 := by intro a scan; rfl
  restore_p2 := by intro a scan; rfl
  restore_p3 := by intro a scan; rfl

theorem shuttleProbe_lt_tapeLength {n k : Nat} (h : k ≤ 64) :
    k < shuttleProbe.machine.tapeLength n := by
  show k < n + shuttleProbeClock n + 1
  rw [shuttleProbeClock]
  omega

def shuttleProbeInput : List ShuttleProbeFrame :=
  [.source true, .middle false, .middle true, .blank, .blank]

def shuttleProbeOutput : List ShuttleProbeFrame :=
  [.source true, .middle false, .middle true, .image true, .blank]

/-- Fresh nonempty `d=2` run: exactly 45 genuine steps restore the source,
preserve both middle frames, install its image, retain the next blank frontier,
and finish at head 4 in the exact exit state. -/
theorem shuttleProbe_run45 (n : Nat) :
    TM.runConfig (M := shuttleProbe.machine)
        (shuttleProbe.cfg n 0 (shuttleProbe_lt_tapeLength (by omega))
          (frameListTape (shuttleProbeInput.flatMap ShuttleProbeFrame.bits))
          (shuttleProbeState .probe .q0 false false false ⟨false, .blank⟩)) 45 =
      shuttleProbe.cfg n 4 (shuttleProbe_lt_tapeLength (by omega))
        (frameListTape (shuttleProbeOutput.flatMap ShuttleProbeFrame.bits))
        (shuttleProbeState .exit .q0 false false false ⟨false, .source true⟩) := by
  have hmid : ∀ g ∈ [ShuttleProbeFrame.middle false, .middle true],
      g ≠ ShuttleProbeFrame.blank ∧ g ≠ ShuttleProbeFrame.marker := by
    intro g hg
    simp at hg
    rcases hg with rfl | rfl <;> decide
  have h := shuttleProbe.shuttleOnList_nextBlank n [] (.source true)
    [.middle false, .middle true] [] ⟨false, .blank⟩ hmid
    (shuttleProbe_lt_tapeLength (n := n) (k := 16) (by omega))
  simpa [shuttleProbeInput, shuttleProbeOutput, FrameShuttle.shuttleSteps,
    FrameShuttle.shuttleSegments, shuttleProbe, shuttleProbeLatch] using h

/-- Necessity probe: a decoded marker in the middle is not a valid forward
path; it takes the exact marker row into `reject`. -/
theorem shuttleProbe_marker_middle_rejected :
    ¬ shuttleProbe.core.ValidPath shuttleProbe.seekMode
      [ShuttleProbeFrame.marker] :=
  shuttleProbe.marker_breaks_forwardPath

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
