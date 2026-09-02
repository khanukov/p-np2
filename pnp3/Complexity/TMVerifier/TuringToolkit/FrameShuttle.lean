import Complexity.TMVerifier.TuringToolkit.FrameScannerKernel
import Complexity.TMVerifier.TuringToolkit.FrameScannerSeek
import Complexity.TMVerifier.TuringToolkit.FrameScannerWriteCtx
import Complexity.TMVerifier.TuringToolkit.FrameScannerWriteLeft

/-!
# Generic source-restoring frame shuttle

One decoded source frame is latched in finite auxiliary control, temporarily
replaced by a marker, copied as `image source` to the first aligned blank, and
then restored after a reverse seek to the first marker in the traversed interval.
All derived scanners and writers use `core.program`, `core.phase`, and
`core.codec` definitionally; there is no second machine or prose-only coherence
assumption.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

universe v

open Pnp3.Internal.PsubsetPpoly.TM

/-- Complete row-level obligations for the shuttle.  `core` is the sole
program/phase/codec source.  Every other machine component below is derived
from these rows, so component entry and exit states are executable glue. -/
structure FrameShuttle (S : Type v) [Fintype S] [DecidableEq S]
    (F Mode Aux : Type v) [Fintype Mode] [Fintype Aux] where
  core : FrameScanner S F Mode Aux
  blank : F
  marker : F
  /-- Source frames for which `image` is a genuine nonblank, nonmarker
  payload.  This is explicit because useful specializations (notably the GN
  boundary-image shuttle) cannot satisfy those freshness facts for every
  alphabet element. -/
  admissible : F → Prop
  image : F → F
  latch : Aux → F → Aux
  carry : Aux → F
  carry_latch : ∀ a f, carry (latch a f) = f
  blank_bits : core.codec.bits blank = [false, false, false, false]
  blank_ne_marker : blank ≠ marker
  image_ne_blank : ∀ f, admissible f → image f ≠ blank
  image_ne_marker : ∀ f, admissible f → image f ≠ marker

  /- Source probe: decode the source and latch it on the fourth right step. -/
  pst0 : Aux → S
  pst1 : Aux → Bool → S
  pst2 : Aux → Bool → Bool → S
  pst3 : Aux → Bool → Bool → Bool → S
  turnBack3 : Aux → S
  probe_p0 : ∀ a scan, core.program.transition core.phase (pst0 a) scan =
    (core.phase, pst1 a scan, scan, Move.right)
  probe_p1 : ∀ a b0 scan, core.program.transition core.phase (pst1 a b0) scan =
    (core.phase, pst2 a b0 scan, scan, Move.right)
  probe_p2 : ∀ a b0 b1 scan,
    core.program.transition core.phase (pst2 a b0 b1) scan =
      (core.phase, pst3 a b0 b1 scan, scan, Move.right)
  probe_p3 : ∀ a b0 b1 b2 scan f, admissible f →
    core.codec.decode? [b0, b1, b2, scan] = some f →
    core.program.transition core.phase (pst3 a b0 b1 b2) scan =
      (core.phase, turnBack3 (latch a f), scan, Move.right)

  /- Four exact rows return from the post-source cell to source p0. -/
  turnBack2 : Aux → S
  turnBack1 : Aux → S
  turnBack0 : Aux → S
  mark0 : Aux → S
  turnBack_p3 : ∀ a scan,
    core.program.transition core.phase (turnBack3 a) scan =
      (core.phase, turnBack2 a, scan, Move.left)
  turnBack_p2 : ∀ a scan,
    core.program.transition core.phase (turnBack2 a) scan =
      (core.phase, turnBack1 a, scan, Move.left)
  turnBack_p1 : ∀ a scan,
    core.program.transition core.phase (turnBack1 a) scan =
      (core.phase, turnBack0 a, scan, Move.left)
  turnBack_p0 : ∀ a scan,
    core.program.transition core.phase (turnBack0 a) scan =
      (core.phase, mark0 a, scan, Move.left)

  /- Marker writer, glued to the forward seek entry. -/
  mark1 : Aux → S
  mark2 : Aux → S
  mark3 : Aux → S
  mw0 : Bool
  mw1 : Bool
  mw2 : Bool
  mw3 : Bool
  marker_bits : core.codec.bits marker = [mw0, mw1, mw2, mw3]
  seekMode : Mode
  destMode : Mode
  seek_forward : core.Forward seekMode
  seek_blank : core.advance seekMode blank = destMode
  seek_marker : core.advance seekMode marker = core.rejectMode
  seek_other : ∀ f, f ≠ blank → f ≠ marker →
    core.advance seekMode f = seekMode
  seek_not_reject : seekMode ≠ core.rejectMode
  dest_not_reject : destMode ≠ core.rejectMode
  mark_p0 : ∀ a scan, core.program.transition core.phase (mark0 a) scan =
    (core.phase, mark1 a, mw0, Move.right)
  mark_p1 : ∀ a scan, core.program.transition core.phase (mark1 a) scan =
    (core.phase, mark2 a, mw1, Move.right)
  mark_p2 : ∀ a scan, core.program.transition core.phase (mark2 a) scan =
    (core.phase, mark3 a, mw2, Move.right)
  mark_p3 : ∀ a scan, core.program.transition core.phase (mark3 a) scan =
    (core.phase, core.st0 seekMode a, mw3, Move.right)

  /- Reverse seek rows, also derived over the shared core. -/
  revStop : Mode → Prop
  revAdvance : Mode → F → Mode
  revComplete : Mode → Bool → Bool → Bool → Bool → Mode
  revReverse : Mode → Prop
  rst3 : Mode → Aux → S
  rst2 : Mode → Aux → Bool → S
  rst1 : Mode → Aux → Bool → Bool → S
  rst0 : Mode → Aux → Bool → Bool → Bool → S
  revStopState : Mode → Aux → S
  revComplete_decode : ∀ m f b0 b1 b2 b3,
    core.codec.decode? [b0, b1, b2, b3] = some f →
      revComplete m b0 b1 b2 b3 = revAdvance m f
  rev_p3 : ∀ {m}, revReverse m → ∀ a scan,
    core.program.transition core.phase (rst3 m a) scan =
      (core.phase, rst2 m a scan, scan, Move.left)
  rev_p2 : ∀ {m}, revReverse m → ∀ a b3 scan,
    core.program.transition core.phase (rst2 m a b3) scan =
      (core.phase, rst1 m a scan b3, scan, Move.left)
  rev_p1 : ∀ {m}, revReverse m → ∀ a b2 b3 scan,
    core.program.transition core.phase (rst1 m a b2 b3) scan =
      (core.phase, rst0 m a scan b2 b3, scan, Move.left)
  rev_p0 : ∀ {m}, revReverse m → ∀ a b1 b2 b3 scan,
    ¬ revStop (revComplete m scan b1 b2 b3) →
    core.program.transition core.phase (rst0 m a b1 b2 b3) scan =
      (core.phase, rst3 (revComplete m scan b1 b2 b3) a, scan, Move.left)
  rev_p0_stop : ∀ {m}, revReverse m → ∀ a b1 b2 b3 scan,
    revStop (revComplete m scan b1 b2 b3) →
    core.program.transition core.phase (rst0 m a b1 b2 b3) scan =
      (core.phase, revStopState (revComplete m scan b1 b2 b3) a,
        scan, Move.stay)
  revMode : Mode
  revStopMode : Mode
  rev_mode : revReverse revMode
  rev_nostop : ¬ revStop revMode
  rev_marker : revAdvance revMode marker = revStopMode
  rev_marker_stops : revStop revStopMode
  rev_other : ∀ f, f ≠ blank → f ≠ marker →
    revAdvance revMode f = revMode

  /- One left row turns from just after the blank into its p3 writer. -/
  dest3 : Aux → S
  turn_destination : ∀ a scan,
    core.program.transition core.phase (core.st0 destMode a) scan =
      (core.phase, dest3 a, scan, Move.left)

  /- Destination writer: target = image(carry a), exit = reverse seek. -/
  dest2 : Aux → S
  dest1 : Aux → S
  dest0 : Aux → S
  dw0 : Aux → Bool
  dw1 : Aux → Bool
  dw2 : Aux → Bool
  dw3 : Aux → Bool
  dest_bits : ∀ a, core.codec.bits (image (carry a)) =
    [dw0 a, dw1 a, dw2 a, dw3 a]
  dest_p3 : ∀ a scan, core.program.transition core.phase (dest3 a) scan =
    (core.phase, dest2 a, dw3 a, Move.left)
  dest_p2 : ∀ a scan, core.program.transition core.phase (dest2 a) scan =
    (core.phase, dest1 a, dw2 a, Move.left)
  dest_p1 : ∀ a scan, core.program.transition core.phase (dest1 a) scan =
    (core.phase, dest0 a, dw1 a, Move.left)
  dest_p0 : ∀ a scan, core.program.transition core.phase (dest0 a) scan =
    (core.phase, rst3 revMode a, dw0 a, Move.left)

  /- Restore writer: target = carry a, starts at the reverse stop and exits. -/
  restore1 : Aux → S
  restore2 : Aux → S
  restore3 : Aux → S
  exitState : Aux → S
  rw0 : Aux → Bool
  rw1 : Aux → Bool
  rw2 : Aux → Bool
  rw3 : Aux → Bool
  restore_bits : ∀ a, core.codec.bits (carry a) =
    [rw0 a, rw1 a, rw2 a, rw3 a]
  restore_p0 : ∀ a scan,
    core.program.transition core.phase (revStopState revStopMode a) scan =
      (core.phase, restore1 a, rw0 a, Move.right)
  restore_p1 : ∀ a scan,
    core.program.transition core.phase (restore1 a) scan =
      (core.phase, restore2 a, rw1 a, Move.right)
  restore_p2 : ∀ a scan,
    core.program.transition core.phase (restore2 a) scan =
      (core.phase, restore3 a, rw2 a, Move.right)
  restore_p3 : ∀ a scan,
    core.program.transition core.phase (restore3 a) scan =
      (core.phase, exitState a, rw3 a, Move.right)

namespace FrameShuttle

variable {S : Type v} [Fintype S] [DecidableEq S]
variable {F Mode Aux : Type v} [Fintype Mode] [Fintype Aux]

abbrev machine (K : FrameShuttle S F Mode Aux) : TM.{v} := K.core.machine

abbrev cfg (K : FrameShuttle S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (q : S) :
    Configuration (M := K.machine) n :=
  K.core.alignedConfigQ n h hh tape q

/-- Reverse scanner derived from the one shared program/phase/codec. -/
def reverseScanner (K : FrameShuttle S F Mode Aux) :
    ReverseFrameScanner S F Mode Aux where
  program := K.core.program
  phase := K.core.phase
  codec := K.core.codec
  Stop := K.revStop
  revAdvance := K.revAdvance
  revComplete := K.revComplete
  Reverse := K.revReverse
  rst3 := K.rst3
  rst2 := K.rst2
  rst1 := K.rst1
  rst0 := K.rst0
  stopState := K.revStopState
  revComplete_decode := K.revComplete_decode
  rstep_p3 := K.rev_p3
  rstep_p2 := K.rev_p2
  rstep_p1 := K.rev_p1
  rstep_p0 := K.rev_p0
  rstep_p0_stop := K.rev_p0_stop

/-- Marker writer; its target and forward-seek exit are executable data. -/
def markWriter (K : FrameShuttle S F Mode Aux) : FrameWriter S F Aux where
  program := K.core.program
  phase := K.core.phase
  codec := K.core.codec
  target := K.marker
  w0 := K.mw0
  w1 := K.mw1
  w2 := K.mw2
  w3 := K.mw3
  wst0 := K.mark0
  wst1 := K.mark1
  wst2 := K.mark2
  wst3 := K.mark3
  exitState := fun a => K.core.st0 K.seekMode a
  target_bits := K.marker_bits
  wstep_p0 := K.mark_p0
  wstep_p1 := K.mark_p1
  wstep_p2 := K.mark_p2
  wstep_p3 := K.mark_p3

/-- Leftward destination writer; target = `image (carry a)` and its exit is
definitionally the reverse scanner's entry state. -/
def destinationWriter (K : FrameShuttle S F Mode Aux) :
    ReverseFrameWriter S F Aux where
  program := K.core.program
  phase := K.core.phase
  codec := K.core.codec
  target := fun a => K.image (K.carry a)
  w0 := K.dw0
  w1 := K.dw1
  w2 := K.dw2
  w3 := K.dw3
  lst3 := K.dest3
  lst2 := K.dest2
  lst1 := K.dest1
  lst0 := K.dest0
  exitState := fun a => K.rst3 K.revMode a
  target_bits := K.dest_bits
  lstep_p3 := K.dest_p3
  lstep_p2 := K.dest_p2
  lstep_p1 := K.dest_p1
  lstep_p0 := K.dest_p0

/-- Context-dependent source restorer; target = `carry a`, entry is the
reverse stop state, and exit is the shuttle endpoint. -/
def restoreWriter (K : FrameShuttle S F Mode Aux) : FrameWriterCtx S F Aux where
  program := K.core.program
  phase := K.core.phase
  codec := K.core.codec
  target := K.carry
  w0 := K.rw0
  w1 := K.rw1
  w2 := K.rw2
  w3 := K.rw3
  wst0 := fun a => K.revStopState K.revStopMode a
  wst1 := K.restore1
  wst2 := K.restore2
  wst3 := K.restore3
  exitState := K.exitState
  target_bits := K.restore_bits
  wstep_p0 := K.restore_p0
  wstep_p1 := K.restore_p1
  wstep_p2 := K.restore_p2
  wstep_p3 := K.restore_p3

/- Explicit coherence pins: all components compile the same shared program. -/
@[simp] private theorem reverseScanner_machine (K : FrameShuttle S F Mode Aux) :
    K.reverseScanner.machine = K.machine := rfl
@[simp] private theorem markWriter_machine (K : FrameShuttle S F Mode Aux) :
    K.markWriter.machine = K.machine := rfl
@[simp] private theorem destinationWriter_machine (K : FrameShuttle S F Mode Aux) :
    K.destinationWriter.machine = K.machine := rfl
@[simp] private theorem restoreWriter_machine (K : FrameShuttle S F Mode Aux) :
    K.restoreWriter.machine = K.machine := rfl

/-- Explicit program/phase/codec coherence for every derived component. -/
private theorem reverseScanner_shared (K : FrameShuttle S F Mode Aux) :
    K.reverseScanner.program = K.core.program ∧
    K.reverseScanner.phase = K.core.phase ∧
    K.reverseScanner.codec = K.core.codec := ⟨rfl, rfl, rfl⟩

private theorem markWriter_shared (K : FrameShuttle S F Mode Aux) :
    K.markWriter.program = K.core.program ∧ K.markWriter.phase = K.core.phase ∧
    K.markWriter.codec = K.core.codec := ⟨rfl, rfl, rfl⟩

private theorem destinationWriter_shared (K : FrameShuttle S F Mode Aux) :
    K.destinationWriter.program = K.core.program ∧
    K.destinationWriter.phase = K.core.phase ∧
    K.destinationWriter.codec = K.core.codec := ⟨rfl, rfl, rfl⟩

private theorem restoreWriter_shared (K : FrameShuttle S F Mode Aux) :
    K.restoreWriter.program = K.core.program ∧
    K.restoreWriter.phase = K.core.phase ∧
    K.restoreWriter.codec = K.core.codec := ⟨rfl, rfl, rfl⟩

/-- Executable target/exit glue, rather than unrelated component records. -/
private theorem markWriter_glue (K : FrameShuttle S F Mode Aux) (a : Aux) :
    K.markWriter.target = K.marker ∧
    K.markWriter.exitState a = K.core.st0 K.seekMode a := ⟨rfl, rfl⟩

private theorem destinationWriter_glue (K : FrameShuttle S F Mode Aux) (a : Aux) :
    K.destinationWriter.target a = K.image (K.carry a) ∧
    K.destinationWriter.exitState a = K.reverseScanner.rst3 K.revMode a :=
  ⟨rfl, rfl⟩

private theorem restoreWriter_glue (K : FrameShuttle S F Mode Aux) (a : Aux) :
    K.restoreWriter.target a = K.carry a ∧
    K.restoreWriter.wst0 a = K.reverseScanner.stopState K.revStopMode a ∧
    K.restoreWriter.exitState a = K.exitState a := ⟨rfl, rfl, rfl⟩

/-- Four genuine source-probe steps decode and latch one valid frame. -/
private theorem probe4 (K : FrameShuttle S F Mode Aux) (n base : Nat)
    (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (a : Aux) (f : F)
    (hf : K.admissible f)
    (hbits : physicalBitsAt hsafe tape = K.core.codec.bits f) :
    TM.runConfig (M := K.machine) (K.cfg n base (by omega) tape (K.pst0 a)) 4 =
      K.cfg n (base + 4) hsafe tape (K.turnBack3 (K.latch a f)) := by
  have h0 : base < K.machine.tapeLength n := by omega
  have h1 : base + 1 < K.machine.tapeLength n := by omega
  have h2 : base + 2 < K.machine.tapeLength n := by omega
  have h3 : base + 3 < K.machine.tapeLength n := by omega
  have hd : K.core.codec.decode?
      [tape ⟨base, h0⟩, tape ⟨base + 1, h1⟩,
       tape ⟨base + 2, h2⟩, tape ⟨base + 3, h3⟩] = some f := by
    rw [show [tape ⟨base, h0⟩, tape ⟨base + 1, h1⟩,
      tape ⟨base + 2, h2⟩, tape ⟨base + 3, h3⟩] = K.core.codec.bits f by
        simpa [physicalBitsAt] using hbits]
    exact K.core.codec.decode_bits f
  show TM.runConfig (M := K.machine)
      (K.cfg n base h0 tape (K.pst0 a)) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have s0 := Phased.stepRight K.core.program K.core.phase n base h0 h1 tape
    (K.pst0 a) (K.pst1 a (tape ⟨base, h0⟩)) (tape ⟨base, h0⟩)
    (K.probe_p0 a _)
  rw [writeCell_self] at s0
  have s0' : TM.stepConfig (M := K.machine) (K.cfg n base h0 tape (K.pst0 a)) =
      K.cfg n (base + 1) h1 tape (K.pst1 a (tape ⟨base, h0⟩)) := by
    simpa using s0
  rw [s0']
  have s1 := Phased.stepRight K.core.program K.core.phase n (base + 1) h1 h2 tape
    (K.pst1 a (tape ⟨base, h0⟩))
    (K.pst2 a (tape ⟨base, h0⟩) (tape ⟨base + 1, h1⟩))
    (tape ⟨base + 1, h1⟩) (K.probe_p1 a _ _)
  rw [writeCell_self] at s1
  have s1' : TM.stepConfig (M := K.machine)
      (K.cfg n (base + 1) h1 tape (K.pst1 a (tape ⟨base, h0⟩))) =
      K.cfg n (base + 2) h2 tape
        (K.pst2 a (tape ⟨base, h0⟩) (tape ⟨base + 1, h1⟩)) := by
    simpa using s1
  rw [s1']
  have s2 := Phased.stepRight K.core.program K.core.phase n (base + 2) h2 h3 tape
    (K.pst2 a (tape ⟨base, h0⟩) (tape ⟨base + 1, h1⟩))
    (K.pst3 a (tape ⟨base, h0⟩) (tape ⟨base + 1, h1⟩)
      (tape ⟨base + 2, h2⟩)) (tape ⟨base + 2, h2⟩) (K.probe_p2 a _ _ _)
  rw [writeCell_self] at s2
  have s2' : TM.stepConfig (M := K.machine)
      (K.cfg n (base + 2) h2 tape
        (K.pst2 a (tape ⟨base, h0⟩) (tape ⟨base + 1, h1⟩))) =
      K.cfg n (base + 3) h3 tape
        (K.pst3 a (tape ⟨base, h0⟩) (tape ⟨base + 1, h1⟩)
          (tape ⟨base + 2, h2⟩)) := by
    simpa using s2
  rw [s2']
  have s3 := Phased.stepRight K.core.program K.core.phase n (base + 3) h3 hsafe tape
    (K.pst3 a (tape ⟨base, h0⟩) (tape ⟨base + 1, h1⟩)
      (tape ⟨base + 2, h2⟩)) (K.turnBack3 (K.latch a f))
    (tape ⟨base + 3, h3⟩) (K.probe_p3 a _ _ _ _ f hf hd)
  rw [writeCell_self] at s3
  simpa using s3

/-- Four exact hold-left rows return to source p0 and enter marker write. -/
private theorem turnBack4 (K : FrameShuttle S F Mode Aux) (n base : Nat)
    (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (a : Aux) :
    TM.runConfig (M := K.machine)
        (K.cfg n (base + 4) hsafe tape (K.turnBack3 a)) 4 =
      K.cfg n base (by omega) tape (K.mark0 a) :=
  Phased.holdWalk4 K.core.program K.core.phase n base hsafe tape
    (K.turnBack3 a) (K.turnBack2 a) (K.turnBack1 a) (K.turnBack0 a)
    (K.mark0 a) (K.turnBack_p3 a) (K.turnBack_p2 a)
    (K.turnBack_p1 a) (K.turnBack_p0 a)

/-- One exact hold-left row enters the destination writer at blank p3. -/
private theorem turnDestination1 (K : FrameShuttle S F Mode Aux) (n base : Nat)
    (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (a : Aux) :
    TM.runConfig (M := K.machine)
        (K.cfg n (base + 4) hsafe tape (K.core.st0 K.destMode a)) 1 =
      K.cfg n (base + 3) (by omega) tape (K.dest3 a) := by
  rw [runConfig_one]
  simpa using Phased.holdLeft K.core.program K.core.phase n (base + 4)
    hsafe (by omega) tape (K.core.st0 K.destMode a) (K.dest3 a)
    (K.turn_destination a)

/-- Forward validity for exactly the marker-free/nonblank middle followed by
the first blank frontier. -/
private theorem forwardPath (K : FrameShuttle S F Mode Aux) (middle : List F)
    (hmid : ∀ g ∈ middle, g ≠ K.blank ∧ g ≠ K.marker) :
    K.core.ValidPath K.seekMode (middle ++ [K.blank]) ∧
      K.core.advanceList K.seekMode (middle ++ [K.blank]) = K.destMode := by
  induction middle with
  | nil =>
      constructor
      · exact ⟨K.seek_forward, by rw [K.seek_blank]; exact K.dest_not_reject,
          trivial⟩
      · exact K.seek_blank
  | cons g rest ih =>
      have hg := hmid g (by simp)
      have hrest : ∀ x ∈ rest, x ≠ K.blank ∧ x ≠ K.marker := by
        intro x hx; exact hmid x (by simp [hx])
      obtain ⟨hp, ha⟩ := ih hrest
      have hs := K.seek_other g hg.1 hg.2
      constructor
      · simp only [List.cons_append, FrameScanner.ValidPath]
        exact ⟨K.seek_forward, by rw [hs]; exact K.seek_not_reject,
          by simpa [hs] using hp⟩
      · simpa [FrameScanner.advanceList, hs] using ha

/-- The singleton middle path `[marker]` is rejected: its exact table row
contradicts `ValidPath`'s nonreject edge.  This is an executable necessity probe,
not an arbitrary-position theorem for every longer middle list. -/
theorem marker_breaks_forwardPath (K : FrameShuttle S F Mode Aux) :
    ¬ K.core.ValidPath K.seekMode [K.marker] := by
  intro h
  exact h.2.1 K.seek_marker

/-- The eight exact schedule segments. -/
def shuttleSegments (d : Nat) : List Nat :=
  [4, 4, 4, 4 * (d + 1), 1, 4, 4 * d + 4, 4]

def shuttleSteps (d : Nat) : Nat := (shuttleSegments d).sum

/-- Exact provenance: probe, turn-back, mark, forward scan, destination turn,
destination write, reverse seek, restore. -/
theorem shuttleSteps_provenance (d : Nat) :
    shuttleSteps d =
      4 + (4 + (4 + (4 * (d + 1) + (1 + (4 + ((4 * d + 4) + 4)))))) ∧
      shuttleSteps d = 8 * d + 29 := by
  simp [shuttleSteps, shuttleSegments]
  omega

/-- Documentary arithmetic span of `d+2` frames from source p0 through the
cell after the destination frontier.  The capstone discharges each concrete
segment-room premise directly. -/
def shuttleFootprint (d : Nat) : Nat := 4 * (d + 2)

/-- **Capstone.**  On an arbitrary list
`pre ++ f :: middle ++ blank :: rest`, start at source p0.  Exactly
`8*middle.length+29` genuine steps restore `f`, replace only the first blank by
`image f`, preserve all surrounding lists, and finish immediately after the
source in the exact exit state.  The explicit blank remains compatible with
implicit `frameListTape` padding by `frameListTape_append_blank`. -/
theorem shuttleOnList (K : FrameShuttle S F Mode Aux) (n : Nat)
    (pre : List F) (f : F) (middle rest : List F) (a : Aux)
    (hf : K.admissible f)
    (hmid : ∀ g ∈ middle, g ≠ K.blank ∧ g ≠ K.marker)
    (hsafe : 4 * (pre.length + middle.length + 2) < K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.cfg n (4 * pre.length) (by omega)
          (frameListTape
            ((pre ++ f :: middle ++ K.blank :: rest).flatMap K.core.codec.bits))
          (K.pst0 a))
        (shuttleSteps middle.length) =
      K.cfg n (4 * pre.length + 4) (by omega)
        (frameListTape
          ((pre ++ f :: middle ++ K.image f :: rest).flatMap K.core.codec.bits))
        (K.exitState (K.latch a f)) := by
  let a' := K.latch a f
  let tape0 : Fin (K.machine.tapeLength n) → Bool :=
    frameListTape ((pre ++ f :: middle ++ K.blank :: rest).flatMap
      K.core.codec.bits)
  let tapeM : Fin (K.machine.tapeLength n) → Bool :=
    frameListTape ((pre ++ K.marker :: middle ++ K.blank :: rest).flatMap
      K.core.codec.bits)
  let tapeD : Fin (K.machine.tapeLength n) → Bool :=
    frameListTape ((pre ++ K.marker :: middle ++ K.image f :: rest).flatMap
      K.core.codec.bits)
  let tapeF : Fin (K.machine.tapeLength n) → Bool :=
    frameListTape ((pre ++ f :: middle ++ K.image f :: rest).flatMap
      K.core.codec.bits)
  have hsource : physicalBitsAt (h := 4 * pre.length) (by omega) tape0 =
      K.core.codec.bits f := by
    simpa [tape0, List.append_assoc] using
      physicalBitsAt_flatMap (L := K.machine.tapeLength n) K.core.codec pre
        (middle ++ K.blank :: rest) f (by omega)
  have hA := K.probe4 n (4 * pre.length) (by omega) tape0 a f hf hsource
  have hB := K.turnBack4 n (4 * pre.length) (by omega) tape0 a'
  have hC := K.markWriter.writeFrameOnList n pre (middle ++ K.blank :: rest)
    f a' (by change 4 * pre.length + 4 < K.machine.tapeLength n; omega)
  have hpath := (K.forwardPath middle hmid).1
  have hadv := (K.forwardPath middle hmid).2
  have hD := K.core.scanFrames n (pre ++ [K.marker]) (middle ++ [K.blank]) rest
    K.seekMode a' hpath (by
      change 4 * ((pre ++ [K.marker]).length +
        (middle ++ [K.blank]).length) < K.machine.tapeLength n
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  have hE := K.turnDestination1 n (4 * (pre.length + middle.length + 1))
    (by omega) tapeM a'
  have hF := K.destinationWriter.writeFrameOnListLeft n
    (pre ++ K.marker :: middle) rest K.blank a' (by
      simp only [List.length_append, List.length_cons]
      omega)
    (by
      change 4 * (pre ++ K.marker :: middle).length + 4 <
        K.machine.tapeLength n
      simp only [List.length_append, List.length_cons]
      omega)
  have hskip : ∀ g ∈ middle,
      K.reverseScanner.revAdvance K.revMode g = K.revMode := by
    intro g hg
    exact K.rev_other g (hmid g hg).1 (hmid g hg).2
  have hG := K.reverseScanner.revSeekToMarker n pre K.marker middle
    (K.image f :: rest) K.revMode a' K.rev_mode K.rev_nostop hskip
    (by simpa [reverseScanner, K.rev_marker] using K.rev_marker_stops)
    (by
      change 4 * (pre.length + middle.length) + 4 < K.machine.tapeLength n
      omega)
  have hH := K.restoreWriter.writeFrameOnList n pre
    (middle ++ K.image f :: rest) K.marker a'
    (by change 4 * pre.length + 4 < K.machine.tapeLength n; omega)
  have hcarry : K.carry a' = f := K.carry_latch a f
  have hsegments := shuttleSteps_provenance middle.length
  rw [hsegments.1, runConfig_add, runConfig_add, runConfig_add, runConfig_add,
    runConfig_add, runConfig_add, runConfig_add]
  rw [show K.cfg n (4 * pre.length) (by omega)
      (frameListTape
        ((pre ++ f :: middle ++ K.blank :: rest).flatMap K.core.codec.bits))
      (K.pst0 a) = K.cfg n (4 * pre.length) (by omega) tape0 (K.pst0 a) by
        rfl,
    hA, hB]
  have hC' : TM.runConfig (M := K.machine)
      (K.cfg n (4 * pre.length) (by omega) tape0 (K.mark0 a')) 4 =
      K.cfg n (4 * pre.length + 4) (by omega) tapeM
        (K.core.st0 K.seekMode a') := by
    simpa [markWriter, tape0, tapeM, List.append_assoc] using hC
  rw [hC']
  have hD' : TM.runConfig (M := K.machine)
      (K.cfg n (4 * pre.length + 4) (by omega) tapeM
        (K.core.st0 K.seekMode a')) (4 * (middle.length + 1)) =
      K.cfg n (4 * (pre.length + middle.length + 2)) (by omega) tapeM
        (K.core.st0 K.destMode a') := by
    simpa [tapeM, List.length_append, hadv, List.append_assoc,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hD
  rw [hD']
  have hE' : TM.runConfig (M := K.machine)
      (K.cfg n (4 * (pre.length + middle.length + 2)) (by omega) tapeM
        (K.core.st0 K.destMode a')) 1 =
      K.cfg n (4 * (pre.length + middle.length + 1) + 3) (by omega) tapeM
        (K.dest3 a') := by simpa [Nat.mul_add] using hE
  rw [hE']
  have hF' : TM.runConfig (M := K.machine)
      (K.cfg n (4 * (pre.length + middle.length + 1) + 3) (by omega) tapeM
        (K.dest3 a')) 4 =
      K.cfg n (4 * (pre.length + middle.length) + 3) (by omega) tapeD
        (K.rst3 K.revMode a') := by
    simpa [destinationWriter, tapeM, tapeD, hcarry, List.length_append,
      List.append_assoc,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hF
  rw [hF']
  have hG' : TM.runConfig (M := K.machine)
      (K.cfg n (4 * (pre.length + middle.length) + 3) (by omega) tapeD
        (K.rst3 K.revMode a')) (4 * middle.length + 4) =
      K.cfg n (4 * pre.length) (by omega) tapeD
        (K.revStopState K.revStopMode a') := by
    simpa [reverseScanner, tapeD, K.rev_marker, List.append_assoc] using hG
  rw [hG']
  have hH' : TM.runConfig (M := K.machine)
      (K.cfg n (4 * pre.length) (by omega) tapeD
        (K.revStopState K.revStopMode a')) 4 =
      K.cfg n (4 * pre.length + 4) (by omega) tapeF (K.exitState a') := by
    simpa [restoreWriter, tapeD, tapeF, hcarry, List.append_assoc] using hH
  rw [hH']

/-- Capstone form with the next frontier explicit: two consecutive input
blanks become `image f :: blank`, so the blank immediately after the installed
image is pinned in the complete endpoint tape. -/
theorem shuttleOnList_nextBlank (K : FrameShuttle S F Mode Aux) (n : Nat)
    (pre : List F) (f : F) (middle rest : List F) (a : Aux)
    (hf : K.admissible f)
    (hmid : ∀ g ∈ middle, g ≠ K.blank ∧ g ≠ K.marker)
    (hsafe : 4 * (pre.length + middle.length + 2) < K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.cfg n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ f :: middle ++ K.blank :: K.blank :: rest).flatMap
            K.core.codec.bits)) (K.pst0 a))
        (shuttleSteps middle.length) =
      K.cfg n (4 * pre.length + 4) (by omega)
        (frameListTape ((pre ++ f :: middle ++ K.image f :: K.blank :: rest).flatMap
          K.core.codec.bits)) (K.exitState (K.latch a f)) := by
  simpa [List.append_assoc] using
    K.shuttleOnList n pre f middle (K.blank :: rest) a hf hmid hsafe

end FrameShuttle

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
