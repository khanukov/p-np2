import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridge
import Complexity.TMVerifier.TuringToolkit.FrameScannerCodec

/-!
# The generic reverse fixed-width frame-scanner kernel

`FrameScannerKernel` proves the *left-to-right* four-cell macrostep and its
list induction once, generically.  This module is its mirror image: the
*right-to-left* macrostep and the exact reverse `List` induction, again as
genuine `TM.stepConfig`/`TM.runConfig` theorems, over an arbitrary
`ConstStatePhasedProgram S`, mode type, carried context `Aux` and fixed-width
`FrameCodec F`.  It is what `T1`'s destructive operand reads and the planned
`G1` pass-B walk need and the forward kernel cannot supply: a control starting
on the *last* cell of a frame, buffering the four cells right to left, and
re-aligning on the last cell of the *preceding* frame.

`revFrameMacrostep` reads one reverse frame in exactly four physical steps
(head `base + 3 ↦ base - 1`, tape and carried context untouched, mode updated
by the reverse frame table `revAdvance`); `revAnchorStep` is the boundary
variant, where a stopping frame makes the fourth step *stay*, leaving the head
on the first cell of that frame in `stopState`.  `revScanFrames` is the exact
reverse induction over an arbitrary `pre`/`anchor`/`scanned`/`suffix` frame
list — exactly `4 * scanned.length` steps, right-to-left fold order, head
`4 * (pre.length + scanned.length) + 3 ↦ 4 * pre.length + 3` — with
`revScanFrames_tape`/`_state`/`_head` its three projections, and
`revScanToAnchor` composes the two into the generic "rewind to the anchor".

**Obligation hygiene.**  A `ReverseFrameScanner` carries no semantic-correctness
field and no "desired run" field: its obligations are exactly one codec law
(`revComplete_decode`) and five *concrete transition tuple equalities* on
`program.transition` at one fixed phase, and everything executable is derived
from those five tuples through `ConstStatePhasedStepBridge`.  No concrete
control table is unfolded here.  The `Phased` namespace holds the aligned
configuration constructor and the three step adapters shared with
`FrameScannerWrite`.

**Non-goals.**  No validation, addressing, acceptance or rejection claim, and
nothing about non-canonical or physically padded tapes.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

universe v

open Pnp3.Internal.PsubsetPpoly.TM

/-! ## The shared phase-aligned layer -/
namespace Phased

variable {S : Type v} [Fintype S] [DecidableEq S]

/-- The compiled machine of a zero-parameter phased program. -/
abbrev machine (U : ConstStatePhasedProgram S) : TM.{v} := U.toPhased.toTM

/-- A configuration in one fixed phase, at an explicit head position, with an
arbitrary tape and an arbitrary local state.  Only `Fin` bookkeeping. -/
def alignedAt (U : ConstStatePhasedProgram S) (ph : Fin U.numPhases) (n h : Nat)
    (hh : h < (machine U).tapeLength n)
    (tape : Fin ((machine U).tapeLength n) → Bool) (q : S) :
    Configuration (M := machine U) n where
  state := ⟨ph, q⟩
  head := ⟨h, hh⟩
  tape := tape

/-- One `Move.right` transition tuple, as one exact `TM.stepConfig`. -/
theorem stepRight (U : ConstStatePhasedProgram S) (ph : Fin U.numPhases)
    (n h : Nat) (hh : h < (machine U).tapeLength n)
    (hb : h + 1 < (machine U).tapeLength n)
    (tape : Fin ((machine U).tapeLength n) → Bool) (q q' : S) (w : Bool)
    (htr : U.transition ph q (tape ⟨h, hh⟩) = (ph, q', w, Move.right)) :
    TM.stepConfig (M := machine U) (alignedAt U ph n h hh tape q) =
      alignedAt U ph n (h + 1) hb (writeCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_right U
    (alignedAt U ph n h hh tape q) htr hb _ rfl rfl (fun _ => rfl)

/-- One `Move.left` transition tuple at a positive head, as one exact
`TM.stepConfig`. -/
theorem stepLeft (U : ConstStatePhasedProgram S) (ph : Fin U.numPhases)
    (n h : Nat) (hh : h < (machine U).tapeLength n) (hpos : 0 < h)
    (tape : Fin ((machine U).tapeLength n) → Bool) (q q' : S) (w : Bool)
    (htr : U.transition ph q (tape ⟨h, hh⟩) = (ph, q', w, Move.left)) :
    TM.stepConfig (M := machine U) (alignedAt U ph n h hh tape q) =
      alignedAt U ph n (h - 1) (by omega) (writeCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_left U
    (alignedAt U ph n h hh tape q) htr hpos _ rfl rfl (fun _ => rfl)

/-- One `Move.stay` transition tuple, as one exact `TM.stepConfig`. -/
theorem stepStay (U : ConstStatePhasedProgram S) (ph : Fin U.numPhases)
    (n h : Nat) (hh : h < (machine U).tapeLength n)
    (tape : Fin ((machine U).tapeLength n) → Bool) (q q' : S) (w : Bool)
    (htr : U.transition ph q (tape ⟨h, hh⟩) = (ph, q', w, Move.stay)) :
    TM.stepConfig (M := machine U) (alignedAt U ph n h hh tape q) =
      alignedAt U ph n h hh (writeCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_stay U
    (alignedAt U ph n h hh tape q) htr _ rfl rfl (fun _ => rfl)

end Phased

/-! ## The reverse scanner -/
/-- **A fixed-width reverse frame scanner.**

`rst3 m a` is the reverse-aligned state — "on the last cell of a frame, about
to read it right to left in mode `m` with context `a`" — and `rst2`, `rst1`,
`rst0` hold the trailing cells already buffered, in frame order (`rst1 m a b2
b3` means cells `base+2` and `base+3` are known).  `revAdvance` is the reverse
frame table, `revComplete` its bit-level form, `Reverse` the modes that read
right to left, and `Stop` the modes at which the pass ends: on such a frame the
control does not step left again but *stays*, leaving the head on the first
cell of the stopping frame in `stopState`.

The six proof fields are the complete obligation set: one codec law
(`revComplete_decode`) and the five concrete transition tuple equalities of the
four frame positions, `rstep_p0` splitting on whether the completed mode
stops. -/
structure ReverseFrameScanner (S : Type v) [Fintype S] [DecidableEq S]
    (F Mode Aux : Type v) where
  program : ConstStatePhasedProgram S
  phase : Fin program.numPhases
  codec : FrameCodec F
  Stop : Mode → Prop
  revAdvance : Mode → F → Mode
  revComplete : Mode → Bool → Bool → Bool → Bool → Mode
  Reverse : Mode → Prop
  rst3 : Mode → Aux → S
  rst2 : Mode → Aux → Bool → S
  rst1 : Mode → Aux → Bool → Bool → S
  rst0 : Mode → Aux → Bool → Bool → Bool → S
  stopState : Mode → Aux → S
  revComplete_decode : ∀ (m : Mode) (f : F) (b0 b1 b2 b3 : Bool),
    codec.decode? [b0, b1, b2, b3] = some f →
      revComplete m b0 b1 b2 b3 = revAdvance m f
  rstep_p3 : ∀ {m : Mode}, Reverse m → ∀ (a : Aux) (scan : Bool),
    program.transition phase (rst3 m a) scan =
      (phase, rst2 m a scan, scan, Move.left)
  rstep_p2 : ∀ {m : Mode}, Reverse m → ∀ (a : Aux) (b3 scan : Bool),
    program.transition phase (rst2 m a b3) scan =
      (phase, rst1 m a scan b3, scan, Move.left)
  rstep_p1 : ∀ {m : Mode}, Reverse m → ∀ (a : Aux) (b2 b3 scan : Bool),
    program.transition phase (rst1 m a b2 b3) scan =
      (phase, rst0 m a scan b2 b3, scan, Move.left)
  rstep_p0 : ∀ {m : Mode}, Reverse m → ∀ (a : Aux) (b1 b2 b3 scan : Bool),
    ¬ Stop (revComplete m scan b1 b2 b3) →
    program.transition phase (rst0 m a b1 b2 b3) scan =
      (phase, rst3 (revComplete m scan b1 b2 b3) a, scan, Move.left)
  rstep_p0_stop : ∀ {m : Mode}, Reverse m → ∀ (a : Aux) (b1 b2 b3 scan : Bool),
    Stop (revComplete m scan b1 b2 b3) →
    program.transition phase (rst0 m a b1 b2 b3) scan =
      (phase, stopState (revComplete m scan b1 b2 b3) a, scan, Move.stay)

namespace ReverseFrameScanner

variable {S : Type v} [Fintype S] [DecidableEq S] {F Mode Aux : Type v}

/-- The compiled machine of a reverse scanner. -/
abbrev machine (K : ReverseFrameScanner S F Mode Aux) : TM.{v} :=
  Phased.machine K.program

/-- A configuration in the scanner's phase with an explicit head and state. -/
abbrev alignedConfigQ (K : ReverseFrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (q : S) :
    Configuration (M := K.machine) n :=
  Phased.alignedAt K.program K.phase n h hh tape q

/-- Reverse-aligned configuration: head on the last cell of the frame about to
be read, empty frame buffer. -/
def revAligned (K : ReverseFrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (a : Aux) :
    Configuration (M := K.machine) n :=
  K.alignedConfigQ n h hh tape (K.rst3 m a)

/-! ### The four cell steps of one reverse frame -/
private theorem revStep_p3 (K : ReverseFrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hpos : 0 < h)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Reverse m)
    (a : Aux) :
    TM.stepConfig (M := K.machine) (K.alignedConfigQ n h hh tape (K.rst3 m a)) =
      K.alignedConfigQ n (h - 1) (by omega) tape (K.rst2 m a (tape ⟨h, hh⟩)) := by
  have hstep := Phased.stepLeft K.program K.phase n h hh hpos tape
    (K.rst3 m a) (K.rst2 m a (tape ⟨h, hh⟩)) (tape ⟨h, hh⟩) (K.rstep_p3 hm a _)
  rwa [writeCell_self] at hstep

private theorem revStep_p2 (K : ReverseFrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hpos : 0 < h)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Reverse m)
    (a : Aux) (b3 : Bool) :
    TM.stepConfig (M := K.machine)
        (K.alignedConfigQ n h hh tape (K.rst2 m a b3)) =
      K.alignedConfigQ n (h - 1) (by omega) tape
        (K.rst1 m a (tape ⟨h, hh⟩) b3) := by
  have hstep := Phased.stepLeft K.program K.phase n h hh hpos tape
    (K.rst2 m a b3) (K.rst1 m a (tape ⟨h, hh⟩) b3) (tape ⟨h, hh⟩)
    (K.rstep_p2 hm a b3 _)
  rwa [writeCell_self] at hstep

private theorem revStep_p1 (K : ReverseFrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hpos : 0 < h)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Reverse m)
    (a : Aux) (b2 b3 : Bool) :
    TM.stepConfig (M := K.machine)
        (K.alignedConfigQ n h hh tape (K.rst1 m a b2 b3)) =
      K.alignedConfigQ n (h - 1) (by omega) tape
        (K.rst0 m a (tape ⟨h, hh⟩) b2 b3) := by
  have hstep := Phased.stepLeft K.program K.phase n h hh hpos tape
    (K.rst1 m a b2 b3) (K.rst0 m a (tape ⟨h, hh⟩) b2 b3) (tape ⟨h, hh⟩)
    (K.rstep_p1 hm a b2 b3 _)
  rwa [writeCell_self] at hstep

private theorem revStep_p0 (K : ReverseFrameScanner S F Mode Aux) (n h : Nat)
    (hh : h < K.machine.tapeLength n) (hpos : 0 < h)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Reverse m)
    (a : Aux) (b1 b2 b3 : Bool)
    (hnext : ¬ K.Stop (K.revComplete m (tape ⟨h, hh⟩) b1 b2 b3)) :
    TM.stepConfig (M := K.machine)
        (K.alignedConfigQ n h hh tape (K.rst0 m a b1 b2 b3)) =
      K.alignedConfigQ n (h - 1) (by omega) tape
        (K.rst3 (K.revComplete m (tape ⟨h, hh⟩) b1 b2 b3) a) := by
  have hstep := Phased.stepLeft K.program K.phase n h hh hpos tape
    (K.rst0 m a b1 b2 b3) (K.rst3 (K.revComplete m (tape ⟨h, hh⟩) b1 b2 b3) a)
    (tape ⟨h, hh⟩) (K.rstep_p0 hm a b1 b2 b3 _ hnext)
  rwa [writeCell_self] at hstep

private theorem revStep_p0_stop (K : ReverseFrameScanner S F Mode Aux)
    (n h : Nat) (hh : h < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Reverse m)
    (a : Aux) (b1 b2 b3 : Bool)
    (hstop : K.Stop (K.revComplete m (tape ⟨h, hh⟩) b1 b2 b3)) :
    TM.stepConfig (M := K.machine)
        (K.alignedConfigQ n h hh tape (K.rst0 m a b1 b2 b3)) =
      K.alignedConfigQ n h hh tape
        (K.stopState (K.revComplete m (tape ⟨h, hh⟩) b1 b2 b3) a) := by
  have hstep := Phased.stepStay K.program K.phase n h hh tape
    (K.rst0 m a b1 b2 b3)
    (K.stopState (K.revComplete m (tape ⟨h, hh⟩) b1 b2 b3) a) (tape ⟨h, hh⟩)
    (K.rstep_p0_stop hm a b1 b2 b3 _ hstop)
  rwa [writeCell_self] at hstep

/-! ### The reverse macrostep -/
/-- The bit-level reverse table agrees with the frame-level one on a codeword.
This is the only place the codec's round-trip law enters the kernel. -/
theorem revComplete_of_bits (K : ReverseFrameScanner S F Mode Aux) (m : Mode)
    (frame : F) {b0 b1 b2 b3 : Bool} (hbits : [b0, b1, b2, b3] = K.codec.bits frame) :
    K.revComplete m b0 b1 b2 b3 = K.revAdvance m frame :=
  K.revComplete_decode m frame b0 b1 b2 b3 (by rw [hbits]; exact K.codec.decode_bits frame)

/-- The three leftward buffering steps shared by the two frame-position-0
outcomes: from `base + 3` they reach `base` with the trailing cells buffered. -/
private theorem revBuffer (K : ReverseFrameScanner S F Mode Aux) (n base : Nat)
    (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) {m : Mode} (hm : K.Reverse m)
    (a : Aux) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (base + 3) (by omega) tape m a) 3 =
      K.alignedConfigQ n base (by omega) tape
        (K.rst0 m a (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
          (tape ⟨base + 3, by omega⟩)) := by
  show TM.runConfig (M := K.machine)
      (K.alignedConfigQ n (base + 3) (by omega) tape (K.rst3 m a)) (1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have hs1 : TM.stepConfig (M := K.machine)
      (K.alignedConfigQ n (base + 3) (by omega) tape (K.rst3 m a)) =
      K.alignedConfigQ n (base + 2) (by omega) tape
        (K.rst2 m a (tape ⟨base + 3, by omega⟩)) := by
    simpa using K.revStep_p3 n (base + 3) (by omega) (by omega) tape hm a
  have hs2 : TM.stepConfig (M := K.machine)
      (K.alignedConfigQ n (base + 2) (by omega) tape
        (K.rst2 m a (tape ⟨base + 3, by omega⟩))) =
      K.alignedConfigQ n (base + 1) (by omega) tape
        (K.rst1 m a (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩)) := by
    simpa using K.revStep_p2 n (base + 2) (by omega) (by omega) tape hm a
      (tape ⟨base + 3, by omega⟩)
  have hs3 : TM.stepConfig (M := K.machine)
      (K.alignedConfigQ n (base + 1) (by omega) tape
        (K.rst1 m a (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩))) =
      K.alignedConfigQ n base (by omega) tape
        (K.rst0 m a (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
          (tape ⟨base + 3, by omega⟩)) := by
    simpa using K.revStep_p1 n (base + 1) (by omega) (by omega) tape hm a
      (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩)
  rw [hs1, hs2, hs3]

/-- **Reverse four-bit decoding macrostep, generically.**  The frame occupying
cells `base … base+3` of an arbitrary surrounding tape is read right to left in
exactly four physical TM steps: the head goes from `base + 3` to `base - 1` —
the last cell of the *preceding* frame — *no tape cell changes*, the carried
context `a` survives, and the mode becomes `K.revAdvance m frame`. -/
theorem revFrameMacrostep (K : ReverseFrameScanner S F Mode Aux) (n base : Nat)
    (hpos : 0 < base) (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (frame : F)
    (a : Aux) (hm : K.Reverse m) (hnext : ¬ K.Stop (K.revAdvance m frame))
    (hbits : physicalBitsAt hsafe tape = K.codec.bits frame) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (base + 3) (by omega) tape m a) 4 =
      K.revAligned n (base - 1) (by omega) tape (K.revAdvance m frame) a := by
  have hcomplete : K.revComplete m (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩) = K.revAdvance m frame :=
    K.revComplete_of_bits m frame (by simpa [physicalBitsAt] using hbits)
  rw [show (4 : Nat) = 3 + 1 by rfl, runConfig_add,
    K.revBuffer n base hsafe tape hm a]
  simp only [runConfig_one]
  rw [K.revStep_p0 n base (by omega) hpos tape hm a _ _ _
    (by rw [hcomplete]; exact hnext), hcomplete]
  rfl

/-- `revFrameMacrostep` with the landing head supplied subtraction-free: a
convenience form, since `base - 1` does not rewrite through head-safety
proofs. -/
theorem revFrameMacrostepAt (K : ReverseFrameScanner S F Mode Aux)
    (n base hend : Nat) (hbase : base = hend + 1)
    (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (frame : F)
    (a : Aux) (hm : K.Reverse m) (hnext : ¬ K.Stop (K.revAdvance m frame))
    (hbits : physicalBitsAt hsafe tape = K.codec.bits frame) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (base + 3) (by omega) tape m a) 4 =
      K.revAligned n hend (by omega) tape (K.revAdvance m frame) a := by
  subst hbase
  simpa using K.revFrameMacrostep n (hend + 1) (by omega) hsafe tape m frame a
    hm hnext hbits

/-- **Reverse boundary macrostep, generically.**  On a stopping frame the fourth
step *stays*: the head finishes on `base`, the first cell of that frame, the
tape and context are untouched, and the control enters `stopState`.  No
positivity premise is needed. -/
theorem revAnchorStep (K : ReverseFrameScanner S F Mode Aux) (n base : Nat)
    (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (frame : F)
    (a : Aux) (hm : K.Reverse m) (hstop : K.Stop (K.revAdvance m frame))
    (hbits : physicalBitsAt hsafe tape = K.codec.bits frame) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (base + 3) (by omega) tape m a) 4 =
      K.alignedConfigQ n base (by omega) tape
        (K.stopState (K.revAdvance m frame) a) := by
  have hcomplete : K.revComplete m (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩) = K.revAdvance m frame :=
    K.revComplete_of_bits m frame (by simpa [physicalBitsAt] using hbits)
  rw [show (4 : Nat) = 3 + 1 by rfl, runConfig_add,
    K.revBuffer n base hsafe tape hm a]
  simp only [runConfig_one]
  rw [K.revStep_p0_stop n base (by omega) tape hm a _ _ _
    (by rw [hcomplete]; exact hstop), hcomplete]

/-! ### The reverse frame language and the right-to-left fold -/
/-- The reverse path condition in *reading* order: each frame of `fs` is read in
a reverse mode and none of them stops the pass. -/
def RevPathFrom (K : ReverseFrameScanner S F Mode Aux) : Mode → List F → Prop
  | _, [] => True
  | m, frame :: rest =>
      K.Reverse m ∧ ¬ K.Stop (K.revAdvance m frame) ∧
        K.RevPathFrom (K.revAdvance m frame) rest

/-- A left-to-right frame list is a valid reverse path when its reversal — the
order the head meets the frames — is a `RevPathFrom`. -/
def RevValidPath (K : ReverseFrameScanner S F Mode Aux) (m : Mode)
    (fs : List F) : Prop := K.RevPathFrom m fs.reverse

/-- The mode update of a reverse scan: fold `revAdvance` from the right. -/
def revAdvanceList (K : ReverseFrameScanner S F Mode Aux) (m : Mode)
    (fs : List F) : Mode := fs.reverse.foldl K.revAdvance m

@[simp] theorem revAdvanceList_nil (K : ReverseFrameScanner S F Mode Aux)
    (m : Mode) : K.revAdvanceList m [] = m := rfl

/-- Peeling the *rightmost* frame is peeling the first frame read. -/
@[simp] theorem revAdvanceList_append_singleton
    (K : ReverseFrameScanner S F Mode Aux) (m : Mode) (rest : List F)
    (frame : F) :
    K.revAdvanceList m (rest ++ [frame]) =
      K.revAdvanceList (K.revAdvance m frame) rest := by
  simp [revAdvanceList]

/-- The reverse mode update is literally a right fold of the reverse table. -/
theorem revAdvanceList_eq_foldr (K : ReverseFrameScanner S F Mode Aux)
    (m : Mode) (fs : List F) :
    K.revAdvanceList m fs = fs.foldr (fun f m' => K.revAdvance m' f) m := by
  simp [revAdvanceList, List.foldl_reverse]

@[simp] theorem revValidPath_nil (K : ReverseFrameScanner S F Mode Aux)
    (m : Mode) : K.RevValidPath m [] := trivial

/-- The reverse path condition, peeled at the rightmost frame. -/
@[simp] theorem revValidPath_append_singleton
    (K : ReverseFrameScanner S F Mode Aux) (m : Mode) (rest : List F)
    (frame : F) :
    K.RevValidPath m (rest ++ [frame]) ↔
      (K.Reverse m ∧ ¬ K.Stop (K.revAdvance m frame) ∧
        K.RevValidPath (K.revAdvance m frame) rest) := by
  simp [RevValidPath, RevPathFrom]

/-- **Homogeneous reverse runs.**  If a non-stopping reverse mode `m` is fixed by
every frame of `fs`, then `fs` is a valid reverse path from `m` and the fold
leaves the mode at `m`.  Every "skip to the anchor" pass has this shape. -/
theorem revValidPath_const (K : ReverseFrameScanner S F Mode Aux) {m : Mode}
    (hrev : K.Reverse m) (hstop : ¬ K.Stop m) (fs : List F)
    (hfix : ∀ f ∈ fs, K.revAdvance m f = m) :
    K.RevValidPath m fs ∧ K.revAdvanceList m fs = m := by
  have main : ∀ l : List F, (∀ f ∈ l, K.revAdvance m f = m) →
      K.RevPathFrom m l ∧ l.foldl K.revAdvance m = m := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨trivial, rfl⟩
    | cons f rest ih =>
        intro h
        have hf : K.revAdvance m f = m := h f (by simp)
        have hrest := ih fun g hg => h g (by simp [hg])
        exact ⟨⟨hrev, by rw [hf]; exact hstop, by rw [hf]; exact hrest.1⟩,
          by rw [List.foldl_cons, hf]; exact hrest.2⟩
  exact main fs.reverse fun f hf => hfix f (List.mem_reverse.mp hf)

/-! ### Exact reverse list-scan induction -/
/-- **Exact reverse frame-scan induction, generically.**  On a tape backed by an
arbitrary frame list `pre ++ anchor :: scanned ++ suffix`, starting on the last
cell of the last frame of `scanned`, the machine reads `scanned` right to left
in exactly four TM steps per frame and finishes on the last cell of `anchor`.
The list-backed tape and the carried context are preserved and the mode is the
right-to-left fold `revAdvanceList mode scanned`. -/
theorem revScanFrames (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (anchor : F) (scanned suffix : List F) (mode : Mode)
    (a : Aux) (hpath : K.RevValidPath mode scanned)
    (hsafe : 4 * (pre.length + scanned.length) + 4 < K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (4 * (pre.length + scanned.length) + 3) (by omega)
          (frameListTape
            ((pre ++ anchor :: scanned ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * scanned.length) =
      K.revAligned n (4 * pre.length + 3) (by omega)
        (frameListTape
          ((pre ++ anchor :: scanned ++ suffix).flatMap K.codec.bits))
        (K.revAdvanceList mode scanned) a := by
  induction scanned using List.reverseRecOn generalizing mode suffix with
  | nil => simp
  | append_singleton rest frame ih =>
      rw [K.revValidPath_append_singleton] at hpath
      obtain ⟨hrev, hnext, hrest⟩ := hpath
      simp only [List.length_append, List.length_cons, List.length_nil]
        at hsafe ⊢
      have hbaseEq : 4 * (pre ++ anchor :: rest).length =
          4 * (pre.length + rest.length) + 4 := by
        simp only [List.length_append, List.length_cons]; omega
      have hframeSafe :
          4 * (pre.length + rest.length) + 4 + 4 < K.machine.tapeLength n := by
        omega
      have hframeBits : physicalBitsAt hframeSafe
          (frameListTape (L := K.machine.tapeLength n)
            ((pre ++ anchor :: (rest ++ [frame]) ++ suffix).flatMap
              K.codec.bits)) = K.codec.bits frame := by
        have raw := physicalBitsAt_flatMap (L := K.machine.tapeLength n)
          K.codec (pre ++ anchor :: rest) suffix frame (by rw [hbaseEq]; omega)
        have hlist : pre ++ anchor :: (rest ++ [frame]) ++ suffix =
            (pre ++ anchor :: rest) ++ frame :: suffix := by
          simp [List.append_assoc]
        rw [hlist]
        simpa only [hbaseEq] using raw
      have hmacro := K.revFrameMacrostepAt n (4 * (pre.length + rest.length) + 4)
        (4 * (pre.length + rest.length) + 3) (by omega) hframeSafe
        (frameListTape
          ((pre ++ anchor :: (rest ++ [frame]) ++ suffix).flatMap K.codec.bits))
        mode frame a hrev hnext hframeBits
      rw [show 4 * (rest.length + 1) = 4 + 4 * rest.length by omega,
        runConfig_add]
      simp only [show 4 * (pre.length + (rest.length + 1)) + 3 =
        4 * (pre.length + rest.length) + 4 + 3 by omega]
      rw [hmacro, K.revAdvanceList_append_singleton]
      have htail := ih (mode := K.revAdvance mode frame)
        (suffix := frame :: suffix) hrest (by omega)
      simpa [List.append_assoc] using htail

/-! ### The three components of a reverse scan, separately -/
/-- **Tape preservation.**  A reverse frame scan is read-only. -/
theorem revScanFrames_tape (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (anchor : F) (scanned suffix : List F) (mode : Mode)
    (a : Aux) (hpath : K.RevValidPath mode scanned)
    (hsafe : 4 * (pre.length + scanned.length) + 4 < K.machine.tapeLength n) :
    (TM.runConfig (M := K.machine)
        (K.revAligned n (4 * (pre.length + scanned.length) + 3) (by omega)
          (frameListTape
            ((pre ++ anchor :: scanned ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * scanned.length)).tape =
      frameListTape
        ((pre ++ anchor :: scanned ++ suffix).flatMap K.codec.bits) := by
  rw [K.revScanFrames n pre anchor scanned suffix mode a hpath hsafe]; rfl

/-- **State update.**  The reverse-aligned state of the folded mode. -/
theorem revScanFrames_state (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (anchor : F) (scanned suffix : List F) (mode : Mode)
    (a : Aux) (hpath : K.RevValidPath mode scanned)
    (hsafe : 4 * (pre.length + scanned.length) + 4 < K.machine.tapeLength n) :
    (TM.runConfig (M := K.machine)
        (K.revAligned n (4 * (pre.length + scanned.length) + 3) (by omega)
          (frameListTape
            ((pre ++ anchor :: scanned ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * scanned.length)).state =
      ⟨K.phase, K.rst3
        (scanned.foldr (fun f m' => K.revAdvance m' f) mode) a⟩ := by
  rw [K.revScanFrames n pre anchor scanned suffix mode a hpath hsafe,
    ← K.revAdvanceList_eq_foldr mode scanned]
  rfl

/-- **Head placement.**  Exactly the last cell of the anchor frame. -/
theorem revScanFrames_head (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (anchor : F) (scanned suffix : List F) (mode : Mode)
    (a : Aux) (hpath : K.RevValidPath mode scanned)
    (hsafe : 4 * (pre.length + scanned.length) + 4 < K.machine.tapeLength n) :
    ((TM.runConfig (M := K.machine)
        (K.revAligned n (4 * (pre.length + scanned.length) + 3) (by omega)
          (frameListTape
            ((pre ++ anchor :: scanned ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * scanned.length)).head : Nat) = 4 * pre.length + 3 := by
  rw [K.revScanFrames n pre anchor scanned suffix mode a hpath hsafe]; rfl

/-! ### Reverse scan all the way to the anchor -/
/-- **The generic rewind.**  From the last cell of the last scanned frame,
`4 * scanned.length + 4` genuine TM steps read `scanned` right to left and then
the leading `anchor`, which stops the pass: head `0`, tape untouched, context
preserved, control in `stopState`. -/
theorem revScanToAnchor (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (anchor : F) (scanned suffix : List F) (mode : Mode) (a : Aux)
    (hpath : K.RevValidPath mode scanned)
    (hrev : K.Reverse (K.revAdvanceList mode scanned))
    (hstop : K.Stop (K.revAdvance (K.revAdvanceList mode scanned) anchor))
    (hsafe : 4 * scanned.length + 4 < K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (4 * scanned.length + 3) (by omega)
          (frameListTape ((anchor :: scanned ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * scanned.length + 4) =
      K.alignedConfigQ n 0 (by omega)
        (frameListTape ((anchor :: scanned ++ suffix).flatMap K.codec.bits))
        (K.stopState (K.revAdvance (K.revAdvanceList mode scanned) anchor) a) := by
  have hscan := K.revScanFrames n [] anchor scanned suffix mode a hpath
    (by simpa using hsafe)
  have hanchorBits : physicalBitsAt (h := 0) (L := K.machine.tapeLength n)
      (by omega)
      (frameListTape ((anchor :: scanned ++ suffix).flatMap K.codec.bits)) =
      K.codec.bits anchor := by
    have raw := physicalBitsAt_flatMap (L := K.machine.tapeLength n) K.codec []
      (scanned ++ suffix) anchor (by simp only [List.length_nil]; omega)
    simpa using raw
  have hanchor := K.revAnchorStep n 0 (by omega)
    (frameListTape (L := K.machine.tapeLength n)
      ((anchor :: scanned ++ suffix).flatMap K.codec.bits))
    (K.revAdvanceList mode scanned) anchor a hrev hstop hanchorBits
  rw [runConfig_add]
  simp only [List.length_nil, List.nil_append, Nat.mul_zero, Nat.zero_add]
    at hscan hanchor
  rw [hscan, hanchor]

end ReverseFrameScanner

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
