import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridge
import Complexity.TMVerifier.TuringToolkit.FrameScannerCodec

/-!
# The generic fixed-width frame-scanner kernel

This module proves the two *genuine Turing-machine* trace theorems that every
frame-based control table in `TuringToolkit` needs, **once**, generically:

* `FrameScanner.frameMacrostep` — a grammar-valid frame on an arbitrary
  surrounding tape is decoded in exactly four physical `TM.stepConfig`s, the
  head advancing by exactly four, no tape cell changing, and the carried
  context surviving;
* `FrameScanner.scanFrames` — the exact `List`-indexed induction that scans a
  whole list of frames left to right in `4 * frames.length` steps, over an
  *arbitrary* `pre`/`suffix` context, ending in the mode obtained by folding
  the transition table over the scanned frames.

Both are stated for an arbitrary `ConstStatePhasedProgram S`, an arbitrary
frame alphabet `F` with a fixed-width `FrameCodec F`, an arbitrary mode type
and an arbitrary carried context type `Aux` (for example one Boolean or a
multi-Boolean product).  Nothing here mentions `T1Frame`, `t1CS`, or any
concrete control table, and no hypothesis is left dangling: a `FrameScanner`
is a *complete* obligation set, discharged by `rfl`-sized table lemmas at each
instance (`FrameScannerT1`, `FrameScannerProbe`).

## What a `FrameScanner` packages

The four `step_p0 … step_p3` fields are exactly the "small transition facts"
of the four frame positions.  They are stated as opaque equations on
`program.transition` at one fixed phase, so this kernel — like
`ConstStatePhasedStepBridge`, which it consumes — never unfolds a concrete
control table.  Every `TM.stepConfig` fact below is obtained by applying a
bridge corollary to one of those four fields.

The scanner is *single-phase-preserving*: all four facts return the scanner's
own `phase`.  That is the regime every `TuringToolkit` frame table lives in
(`numPhases = 1`), and it is what makes the aligned-configuration constructor
`alignedConfigQ` well defined without phase bookkeeping.

## Non-goals

This is infrastructure only.  The kernel proves no validation, acceptance,
addressing, or rejection claim, and it says nothing about non-canonical or
physically padded tapes; those remain per-instance obligations.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

namespace FrameScan

universe v

open Pnp3.Internal.PsubsetPpoly.TM

/-- **A fixed-width frame scanner.**

`program` is an arbitrary `ConstStatePhasedProgram S`; `phase` is the phase its
frame-scanning modes stay in; `codec` fixes the 4-bit alphabet; `advance` is
the frame-level transition table and `complete` its bit-level form, which the
control table actually computes.

`st0 … st3` are the four aligned control states of a frame: `st0 m a` is
"about to read a frame in mode `m` with context `a`", and `stk m a b₀ … b_{k-1}`
holds the first `k` cells already buffered.  Keeping them as *functions*
rather than a concrete record is what lets an instance carry any extra state
it likes without touching this file.

The five proof fields are the complete obligation set. -/
structure FrameScanner (S : Type v) [Fintype S] [DecidableEq S]
    (F Mode Aux : Type v) where
  /-- The underlying zero-parameter phased program. -/
  program : ConstStatePhasedProgram S
  /-- The phase the frame-scanning modes live in and preserve. -/
  phase : Fin program.numPhases
  /-- The fixed-width frame alphabet. -/
  codec : FrameCodec F
  /-- The mode that means "grammar violation"; scans must avoid it. -/
  rejectMode : Mode
  /-- Frame-level forward transition table. -/
  advance : Mode → F → Mode
  /-- Bit-level form of `advance`, as the control table computes it. -/
  complete : Mode → Bool → Bool → Bool → Bool → Mode
  /-- The modes that read frames left to right through `advance`. -/
  Forward : Mode → Prop
  /-- Aligned state: about to read a frame. -/
  st0 : Mode → Aux → S
  /-- One cell buffered. -/
  st1 : Mode → Aux → Bool → S
  /-- Two cells buffered. -/
  st2 : Mode → Aux → Bool → Bool → S
  /-- Three cells buffered. -/
  st3 : Mode → Aux → Bool → Bool → Bool → S
  /-- `complete` is `advance` composed with the decoder. -/
  complete_decode : ∀ (m : Mode) (b0 b1 b2 b3 : Bool),
    complete m b0 b1 b2 b3 =
      match codec.decode? [b0, b1, b2, b3] with
      | some f => advance m f
      | none => rejectMode
  /-- Transition fact at frame position 0: buffer the cell, step right. -/
  step_p0 : ∀ {m : Mode}, Forward m → ∀ (a : Aux) (scan : Bool),
    program.transition phase (st0 m a) scan =
      (phase, st1 m a scan, scan, Move.right)
  /-- Transition fact at frame position 1. -/
  step_p1 : ∀ {m : Mode}, Forward m → ∀ (a : Aux) (b0 scan : Bool),
    program.transition phase (st1 m a b0) scan =
      (phase, st2 m a b0 scan, scan, Move.right)
  /-- Transition fact at frame position 2. -/
  step_p2 : ∀ {m : Mode}, Forward m → ∀ (a : Aux) (b0 b1 scan : Bool),
    program.transition phase (st2 m a b0 b1) scan =
      (phase, st3 m a b0 b1 scan, scan, Move.right)
  /-- Transition fact at frame position 3: complete the frame and re-align,
  provided the completed mode is not the reject mode. -/
  step_p3 : ∀ {m : Mode}, Forward m → ∀ (a : Aux) (b0 b1 b2 scan : Bool),
    complete m b0 b1 b2 scan ≠ rejectMode →
    program.transition phase (st3 m a b0 b1 b2) scan =
      (phase, st0 (complete m b0 b1 b2 scan) a, scan, Move.right)

namespace FrameScanner

variable {S : Type v} [Fintype S] [DecidableEq S] {F Mode Aux : Type v}

/-- The compiled machine of a scanner. -/
abbrev machine (K : FrameScanner S F Mode Aux) : TM.{v} :=
  K.program.toPhased.toTM

/-! ## The aligned configuration constructor

`alignedConfigQ` only packages `Fin` bookkeeping: the scanner's phase, an
explicit physical head position, and an arbitrary tape.  `alignedFrame` is the
frame-aligned specialisation used by both trace theorems. -/

/-- A configuration in the scanner's phase, at an explicit head position, with
an arbitrary tape and an arbitrary local state. -/
def alignedConfigQ (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (q : S) :
    Configuration (M := K.machine) n where
  state := ⟨K.phase, q⟩
  head := ⟨h, hh⟩
  tape := tape

@[simp] theorem alignedConfigQ_state (K : FrameScanner S F Mode Aux)
    (n h hh tape q) : (K.alignedConfigQ n h hh tape q).state = ⟨K.phase, q⟩ :=
  rfl

@[simp] theorem alignedConfigQ_head_val (K : FrameScanner S F Mode Aux)
    (n h hh tape q) : ((K.alignedConfigQ n h hh tape q).head : Nat) = h := rfl

@[simp] theorem alignedConfigQ_tape (K : FrameScanner S F Mode Aux)
    (n h hh tape q) : (K.alignedConfigQ n h hh tape q).tape = tape := rfl

/-- Frame-aligned configuration: mode `m`, context `a`, empty frame buffer. -/
def alignedFrame (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (a : Aux) :
    Configuration (M := K.machine) n :=
  K.alignedConfigQ n h hh tape (K.st0 m a)

/-! ## The three aligned step adapters

Each turns one transition-table equation into one exact `TM.stepConfig`
equation, by applying the matching generic bridge corollary.  They are public:
an instance can reuse them for its non-frame modes too. -/

theorem alignedStepRight (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hb : h + 1 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (q q' : S) (w : Bool)
    (htr : K.program.transition K.phase q (tape ⟨h, hh⟩) =
      (K.phase, q', w, Move.right)) :
    TM.stepConfig (M := K.machine) (K.alignedConfigQ n h hh tape q) =
      K.alignedConfigQ n (h + 1) hb (writeCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_right K.program
    (K.alignedConfigQ n h hh tape q) htr hb _ rfl rfl (fun _ => rfl)

theorem alignedStepLeft (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hpos : 0 < h)
    (tape : Fin (K.machine.tapeLength n) → Bool) (q q' : S) (w : Bool)
    (htr : K.program.transition K.phase q (tape ⟨h, hh⟩) =
      (K.phase, q', w, Move.left)) :
    TM.stepConfig (M := K.machine) (K.alignedConfigQ n h hh tape q) =
      K.alignedConfigQ n (h - 1) (by omega) (writeCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_left K.program
    (K.alignedConfigQ n h hh tape q) htr hpos _ rfl rfl (fun _ => rfl)

theorem alignedStepStay (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (q q' : S) (w : Bool)
    (htr : K.program.transition K.phase q (tape ⟨h, hh⟩) =
      (K.phase, q', w, Move.stay)) :
    TM.stepConfig (M := K.machine) (K.alignedConfigQ n h hh tape q) =
      K.alignedConfigQ n h hh (writeCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_stay K.program
    (K.alignedConfigQ n h hh tape q) htr _ rfl rfl (fun _ => rfl)

/-! ## The four cell steps of one frame -/

private theorem stepFrame_p0 (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hb : h + 1 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Forward m)
    (a : Aux) :
    TM.stepConfig (M := K.machine) (K.alignedConfigQ n h hh tape (K.st0 m a)) =
      K.alignedConfigQ n (h + 1) hb tape (K.st1 m a (tape ⟨h, hh⟩)) := by
  have hstep := K.alignedStepRight n h hh hb tape (K.st0 m a)
    (K.st1 m a (tape ⟨h, hh⟩)) (tape ⟨h, hh⟩) (K.step_p0 hm a _)
  rwa [writeCell_self] at hstep

private theorem stepFrame_p1 (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hb : h + 1 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Forward m)
    (a : Aux) (b0 : Bool) :
    TM.stepConfig (M := K.machine)
        (K.alignedConfigQ n h hh tape (K.st1 m a b0)) =
      K.alignedConfigQ n (h + 1) hb tape (K.st2 m a b0 (tape ⟨h, hh⟩)) := by
  have hstep := K.alignedStepRight n h hh hb tape (K.st1 m a b0)
    (K.st2 m a b0 (tape ⟨h, hh⟩)) (tape ⟨h, hh⟩) (K.step_p1 hm a b0 _)
  rwa [writeCell_self] at hstep

private theorem stepFrame_p2 (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hb : h + 1 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Forward m)
    (a : Aux) (b0 b1 : Bool) :
    TM.stepConfig (M := K.machine)
        (K.alignedConfigQ n h hh tape (K.st2 m a b0 b1)) =
      K.alignedConfigQ n (h + 1) hb tape (K.st3 m a b0 b1 (tape ⟨h, hh⟩)) := by
  have hstep := K.alignedStepRight n h hh hb tape (K.st2 m a b0 b1)
    (K.st3 m a b0 b1 (tape ⟨h, hh⟩)) (tape ⟨h, hh⟩) (K.step_p2 hm a b0 b1 _)
  rwa [writeCell_self] at hstep

private theorem stepFrame_p3 (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hb : h + 1 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Forward m)
    (a : Aux) (b0 b1 b2 : Bool)
    (hnext : K.complete m b0 b1 b2 (tape ⟨h, hh⟩) ≠ K.rejectMode) :
    TM.stepConfig (M := K.machine)
        (K.alignedConfigQ n h hh tape (K.st3 m a b0 b1 b2)) =
      K.alignedConfigQ n (h + 1) hb tape
        (K.st0 (K.complete m b0 b1 b2 (tape ⟨h, hh⟩)) a) := by
  have hstep := K.alignedStepRight n h hh hb tape (K.st3 m a b0 b1 b2)
    (K.st0 (K.complete m b0 b1 b2 (tape ⟨h, hh⟩)) a) (tape ⟨h, hh⟩)
    (K.step_p3 hm a b0 b1 b2 _ hnext)
  rwa [writeCell_self] at hstep

/-! ## The four-step frame macrostep -/

/-- The bit-level table agrees with the frame-level table on a codeword.
This is the only place the codec's round-trip law enters the kernel. -/
theorem complete_of_bits (K : FrameScanner S F Mode Aux) (m : Mode) (frame : F)
    {b0 b1 b2 b3 : Bool} (hbits : [b0, b1, b2, b3] = K.codec.bits frame) :
    K.complete m b0 b1 b2 b3 = K.advance m frame := by
  rw [K.complete_decode, hbits, K.codec.decode_bits]

/-- **Four-bit decoding macrostep, generically.**  In any forward mode, a
grammar-valid frame sitting on an arbitrary surrounding tape is decoded in
exactly four physical TM steps: the head advances by exactly four, *no tape
cell changes*, the carried context `a` is threaded through unchanged, and the
mode becomes `K.advance m frame`. -/
theorem frameMacrostep (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hsafe : h + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (frame : F)
    (a : Aux) (hm : K.Forward m)
    (hnext : K.advance m frame ≠ K.rejectMode)
    (hbits : physicalBitsAt hsafe tape = K.codec.bits frame) :
    TM.runConfig (M := K.machine)
        (K.alignedFrame n h (by omega) tape m a) 4 =
      K.alignedFrame n (h + 4) hsafe tape (K.advance m frame) a := by
  have hcomplete : K.complete m (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩)
      (tape ⟨h + 2, by omega⟩) (tape ⟨h + 3, by omega⟩) =
        K.advance m frame :=
    K.complete_of_bits m frame (by simpa [physicalBitsAt] using hbits)
  show TM.runConfig (M := K.machine)
      (K.alignedConfigQ n h (by omega) tape (K.st0 m a)) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [K.stepFrame_p0 n h (by omega) (by omega) tape hm a]
  rw [K.stepFrame_p1 n (h + 1) (by omega) (by omega) tape hm a _]
  rw [K.stepFrame_p2 n (h + 2) (by omega) (by omega) tape hm a _ _]
  rw [K.stepFrame_p3 n (h + 3) (by omega) (by omega) tape hm a _ _ _
    (by rw [hcomplete]; exact hnext)]
  rw [hcomplete]
  rfl

/-! ## Exact list-scan induction -/

/-- A list of frames is a *valid path* from `mode` when every frame is read in
a forward mode and never completes into the reject mode. -/
def ValidPath (K : FrameScanner S F Mode Aux) : Mode → List F → Prop
  | _, [] => True
  | m, frame :: rest =>
      K.Forward m ∧ K.advance m frame ≠ K.rejectMode ∧
        K.ValidPath (K.advance m frame) rest

/-- The state update of a whole scan: fold `advance` over the frames. -/
def advanceList (K : FrameScanner S F Mode Aux) : Mode → List F → Mode
  | m, [] => m
  | m, frame :: rest => K.advanceList (K.advance m frame) rest

@[simp] theorem advanceList_nil (K : FrameScanner S F Mode Aux) (m : Mode) :
    K.advanceList m [] = m := rfl

@[simp] theorem advanceList_cons (K : FrameScanner S F Mode Aux) (m : Mode)
    (frame : F) (rest : List F) :
    K.advanceList m (frame :: rest) = K.advanceList (K.advance m frame) rest :=
  rfl

/-- The mode update is literally a left fold of the frame table. -/
theorem advanceList_eq_foldl (K : FrameScanner S F Mode Aux) (m : Mode)
    (frames : List F) : K.advanceList m frames = frames.foldl K.advance m := by
  induction frames generalizing m with
  | nil => rfl
  | cons frame rest ih => simpa using ih (K.advance m frame)

/-- The fold composes over concatenation. -/
theorem advanceList_append (K : FrameScanner S F Mode Aux) (m : Mode)
    (fs gs : List F) :
    K.advanceList m (fs ++ gs) = K.advanceList (K.advanceList m fs) gs := by
  induction fs generalizing m with
  | nil => rfl
  | cons frame rest ih => simpa using ih (K.advance m frame)

/-- **Exact frame-scan induction, generically.**  Scanning a grammar-valid
list of frames left to right takes exactly four TM steps per frame, over an
*arbitrary* surrounding tape `pre`/`suffix`.  The complete list-backed tape is
preserved, the carried context is preserved, the head lands exactly at the
frame boundary `4 * (pre.length + frames.length)`, and the mode is the fold
`advanceList mode frames`. -/
theorem scanFrames (K : FrameScanner S F Mode Aux) (n : Nat)
    (pre frames suffix : List F) (mode : Mode) (a : Aux)
    (hpath : K.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.alignedFrame n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ frames ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * frames.length) =
      K.alignedFrame n (4 * (pre.length + frames.length)) hsafe
        (frameListTape ((pre ++ frames ++ suffix).flatMap K.codec.bits))
        (K.advanceList mode frames) a := by
  induction frames generalizing pre mode with
  | nil => simp [advanceList]
  | cons frame rest ih =>
      obtain ⟨hfwd, hnext, hrest⟩ := hpath
      have hframeSafe : 4 * pre.length + 4 < K.machine.tapeLength n := by
        simp only [List.length_cons] at hsafe
        omega
      have hmacro := K.frameMacrostep n (4 * pre.length) hframeSafe
        (frameListTape ((pre ++ frame :: rest ++ suffix).flatMap K.codec.bits))
        mode frame a hfwd hnext
        (by simpa [List.append_assoc] using
          physicalBitsAt_flatMap K.codec pre (rest ++ suffix) frame hframeSafe)
      rw [show 4 * (frame :: rest).length = 4 + 4 * rest.length by simp; omega,
        runConfig_add, hmacro]
      have hsafeTail :
          4 * ((pre ++ [frame]).length + rest.length) <
            K.machine.tapeLength n := by
        simp only [List.length_cons, List.length_append, List.length_nil]
          at hsafe ⊢
        omega
      have htail := ih (pre ++ [frame]) (K.advance mode frame) hrest hsafeTail
      simpa [List.length_append, List.length_nil, List.length_cons,
        List.singleton_append, List.append_assoc, advanceList, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-! ### The three components of a scan, separately

`scanFrames` pins the whole configuration; these read off its parts, which is
what composing callers actually rewrite with. -/

/-- **Tape preservation.**  A frame scan is read-only: the tape after the scan
is the tape before it, cell for cell. -/
theorem scanFrames_tape (K : FrameScanner S F Mode Aux) (n : Nat)
    (pre frames suffix : List F) (mode : Mode) (a : Aux)
    (hpath : K.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < K.machine.tapeLength n) :
    (TM.runConfig (M := K.machine)
        (K.alignedFrame n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ frames ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * frames.length)).tape =
      frameListTape ((pre ++ frames ++ suffix).flatMap K.codec.bits) := by
  rw [K.scanFrames n pre frames suffix mode a hpath hsafe]; rfl

/-- **State update.**  The control state after the scan is the aligned state
of the folded mode, with the carried context unchanged. -/
theorem scanFrames_state (K : FrameScanner S F Mode Aux) (n : Nat)
    (pre frames suffix : List F) (mode : Mode) (a : Aux)
    (hpath : K.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < K.machine.tapeLength n) :
    (TM.runConfig (M := K.machine)
        (K.alignedFrame n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ frames ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * frames.length)).state =
      ⟨K.phase, K.st0 (frames.foldl K.advance mode) a⟩ := by
  rw [K.scanFrames n pre frames suffix mode a hpath hsafe,
    ← K.advanceList_eq_foldl mode frames]
  rfl

/-- **Head placement.**  The scan ends exactly on the frame boundary after the
scanned block. -/
theorem scanFrames_head (K : FrameScanner S F Mode Aux) (n : Nat)
    (pre frames suffix : List F) (mode : Mode) (a : Aux)
    (hpath : K.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < K.machine.tapeLength n) :
    ((TM.runConfig (M := K.machine)
        (K.alignedFrame n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ frames ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * frames.length)).head : Nat) =
      4 * (pre.length + frames.length) := by
  rw [K.scanFrames n pre frames suffix mode a hpath hsafe]; rfl

end FrameScanner

end FrameScan

end TM
end PsubsetPpoly
end Internal
end Pnp3
