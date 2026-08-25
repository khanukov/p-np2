import Complexity.TMVerifier.TuringToolkit.FrameScannerSeek
import Complexity.TMVerifier.TuringToolkit.FrameScannerWriteLeft

/-!
# The generic thirteen-step frame rewrite cycle

This is the composition the reverse scanner and the frame writer were factored
out for: **one destructive rewrite of a single frame inside an arbitrary frame
list, in exactly thirteen genuine TM steps**, returning the control to the
reverse scan's entry shape one frame further left.  It is the machine shape of
`T1`'s `spent ↦ index` repair cycle and of any future runtime index walk, so it
is proved once, generically.

The thirteen steps are `4 + 4 + 4 + 1`:

* **read (4)** — the reverse scanner reads the marker frame right to left and
  *stops* on its first cell (`ReverseFrameScanner.revAnchorStep`), leaving the
  head on `base` in `stopState`;
* **write (4)** — the frame writer overwrites those four cells with the
  codeword of the replacement frame while walking right
  (`FrameWriter.writeMacrostep`), leaving the head on `base + 4`;
* **walk back (4)** — four hold-and-move-left steps return the head to `base`;
* **hop (1)** — one further left step re-enters the reverse scan's aligned
  state on `base - 1`.

`rewriteCycle` is that theorem on an arbitrary tape, `rewriteCycleOnList` its
frame-list form (`pre ++ marker :: suffix ↦ pre ++ target :: suffix`, head
`4 * pre.length + 3 ↦ 4 * pre.length - 1`), and `seekAndRewrite` composes the
seek driver in front of it: skip an arbitrary run of skippable frames, then
rewrite, in `4 * skipped.length + 13` steps.

**Obligation hygiene.**  A `FrameRewriteCycle` is a `ReverseFrameScanner` plus
one codec law, four *table facts* about the seek/stop modes, and nine *concrete
transition tuple equalities* (four write, four walk-back, one hop, quantified
over the scanned cell and the carried context).  No semantic-correctness field,
no desired-run field, no step-count field: the thirteen is *derived* from the
scanner's boundary macrostep, the writer's macrostep and the explicit hop
transition.  The write control is entered at the scanner's own `stopState`, so
the two halves are genuinely glued rather than stated to agree.

**Non-goals.**  This slice rewrites *one* frame per cycle.  Iterating the cycle
along a run, addressing a runtime index, validation, acceptance and rejection
are all outside it, and nothing here claims them.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

universe v

open Pnp3.Internal.PsubsetPpoly.TM

/-- **A fixed-width frame rewrite cycle.**

`seekMode` is the reverse mode the scan runs in and `marker` the frame that
stops it; `stopMode` is the mode the reverse table produces there, so the
control enters the write in `scanner.stopState stopMode`.  `wst1 … wst3` are
the remaining three write states, `bst0 … bst3` the four states of the walk
back (`bst0` is where the write exits) and `hopState` the state of the single
hop that re-enters the scan.  `target` is the frame installed in the marker's
place and `w0 … w3` the literal cells written for it. -/
structure FrameRewriteCycle (S : Type v) [Fintype S] [DecidableEq S]
    (F Mode Aux : Type v) where
  scanner : ReverseFrameScanner S F Mode Aux
  seekMode : Mode
  stopMode : Mode
  /-- The frame whose reading stops the scan and which the cycle overwrites. -/
  marker : F
  /-- The frame installed in the marker's place. -/
  target : F
  w0 : Bool
  w1 : Bool
  w2 : Bool
  w3 : Bool
  wst1 : Aux → S
  wst2 : Aux → S
  wst3 : Aux → S
  bst0 : Aux → S
  bst1 : Aux → S
  bst2 : Aux → S
  bst3 : Aux → S
  hopState : Aux → S
  seek_reverse : scanner.Reverse seekMode
  seek_nostop : ¬ scanner.Stop seekMode
  marker_stop : scanner.revAdvance seekMode marker = stopMode
  stop_stops : scanner.Stop stopMode
  target_bits : scanner.codec.bits target = [w0, w1, w2, w3]
  wstep_p0 : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (scanner.stopState stopMode a)
      scan = (scanner.phase, wst1 a, w0, Move.right)
  wstep_p1 : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (wst1 a) scan =
      (scanner.phase, wst2 a, w1, Move.right)
  wstep_p2 : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (wst2 a) scan =
      (scanner.phase, wst3 a, w2, Move.right)
  wstep_p3 : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (wst3 a) scan =
      (scanner.phase, bst0 a, w3, Move.right)
  bstep_p0 : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (bst0 a) scan =
      (scanner.phase, bst1 a, scan, Move.left)
  bstep_p1 : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (bst1 a) scan =
      (scanner.phase, bst2 a, scan, Move.left)
  bstep_p2 : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (bst2 a) scan =
      (scanner.phase, bst3 a, scan, Move.left)
  bstep_p3 : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (bst3 a) scan =
      (scanner.phase, hopState a, scan, Move.left)
  hop_step : ∀ (a : Aux) (scan : Bool),
    scanner.program.transition scanner.phase (hopState a) scan =
      (scanner.phase, scanner.rst3 seekMode a, scan, Move.left)

namespace FrameRewriteCycle

variable {S : Type v} [Fintype S] [DecidableEq S] {F Mode Aux : Type v}

/-- A configuration in the cycle's phase with an explicit head and state.  The
machine is spelled `C.scanner.machine` throughout, so that every head-safety
side goal of this module talks about one atom. -/
abbrev cfg (C : FrameRewriteCycle S F Mode Aux) (n h : Nat)
    (hh : h < C.scanner.machine.tapeLength n)
    (tape : Fin (C.scanner.machine.tapeLength n) → Bool) (q : S) :
    Configuration (M := C.scanner.machine) n :=
  C.scanner.alignedConfigQ n h hh tape q

/-- **The write half of a cycle is a genuine `FrameWriter`.**  Its entry state
is the *scanner's* stop state, which is what glues the two halves. -/
def toWriter (C : FrameRewriteCycle S F Mode Aux) : FrameWriter S F Aux where
  program := C.scanner.program
  phase := C.scanner.phase
  codec := C.scanner.codec
  target := C.target
  w0 := C.w0
  w1 := C.w1
  w2 := C.w2
  w3 := C.w3
  wst0 := fun a => C.scanner.stopState C.stopMode a
  wst1 := C.wst1
  wst2 := C.wst2
  wst3 := C.wst3
  exitState := C.bst0
  target_bits := C.target_bits
  wstep_p0 := C.wstep_p0
  wstep_p1 := C.wstep_p1
  wstep_p2 := C.wstep_p2
  wstep_p3 := C.wstep_p3

/-! ### The two derived halves -/
/-- **The walk back.**  Four hold-and-move-left steps return the head from the
cell after the rewritten frame to its first cell, with the tape and the carried
context untouched. -/
theorem backWalk (C : FrameRewriteCycle S F Mode Aux) (n base : Nat)
    (hsafe : base + 4 < C.scanner.machine.tapeLength n)
    (tape : Fin (C.scanner.machine.tapeLength n) → Bool) (a : Aux) :
    TM.runConfig (M := C.scanner.machine)
        (C.cfg n (base + 4) hsafe tape (C.bst0 a)) 4 =
      C.cfg n base (by omega) tape (C.hopState a) := by
  have hb0 : base < C.scanner.machine.tapeLength n := by omega
  have hb1 : base + 1 < C.scanner.machine.tapeLength n := by omega
  have hb2 : base + 2 < C.scanner.machine.tapeLength n := by omega
  have hb3 : base + 3 < C.scanner.machine.tapeLength n := by omega
  have hs0 : TM.stepConfig (M := C.scanner.machine)
      (C.cfg n (base + 4) hsafe tape (C.bst0 a)) =
      C.cfg n (base + 3) hb3 tape (C.bst1 a) := by
    have h := Phased.stepLeft C.scanner.program C.scanner.phase n (base + 4)
      hsafe (by omega) tape (C.bst0 a) (C.bst1 a) (tape ⟨base + 4, hsafe⟩)
      (C.bstep_p0 a _)
    rw [writeCell_self] at h
    simpa using h
  have hs1 : TM.stepConfig (M := C.scanner.machine)
      (C.cfg n (base + 3) hb3 tape (C.bst1 a)) =
      C.cfg n (base + 2) hb2 tape (C.bst2 a) := by
    have h := Phased.stepLeft C.scanner.program C.scanner.phase n (base + 3)
      hb3 (by omega) tape (C.bst1 a) (C.bst2 a) (tape ⟨base + 3, hb3⟩)
      (C.bstep_p1 a _)
    rw [writeCell_self] at h
    simpa using h
  have hs2 : TM.stepConfig (M := C.scanner.machine)
      (C.cfg n (base + 2) hb2 tape (C.bst2 a)) =
      C.cfg n (base + 1) hb1 tape (C.bst3 a) := by
    have h := Phased.stepLeft C.scanner.program C.scanner.phase n (base + 2)
      hb2 (by omega) tape (C.bst2 a) (C.bst3 a) (tape ⟨base + 2, hb2⟩)
      (C.bstep_p2 a _)
    rw [writeCell_self] at h
    simpa using h
  have hs3 : TM.stepConfig (M := C.scanner.machine)
      (C.cfg n (base + 1) hb1 tape (C.bst3 a)) =
      C.cfg n base hb0 tape (C.hopState a) := by
    have h := Phased.stepLeft C.scanner.program C.scanner.phase n (base + 1)
      hb1 (by omega) tape (C.bst3 a) (C.hopState a) (tape ⟨base + 1, hb1⟩)
      (C.bstep_p3 a _)
    rw [writeCell_self] at h
    simpa using h
  show TM.runConfig (M := C.scanner.machine)
      (C.cfg n (base + 4) hsafe tape (C.bst0 a)) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3]

/-- **The hop.**  One further left step re-enters the reverse scan's aligned
entry shape on the last cell of the preceding frame. -/
theorem hopStep (C : FrameRewriteCycle S F Mode Aux) (n base : Nat)
    (hpos : 0 < base) (hh : base < C.scanner.machine.tapeLength n)
    (tape : Fin (C.scanner.machine.tapeLength n) → Bool) (a : Aux) :
    TM.runConfig (M := C.scanner.machine) (C.cfg n base hh tape (C.hopState a)) 1 =
      C.scanner.revAligned n (base - 1) (by omega) tape C.seekMode a := by
  rw [runConfig_one]
  have h := Phased.stepLeft C.scanner.program C.scanner.phase n base hh hpos
    tape (C.hopState a) (C.scanner.rst3 C.seekMode a) (tape ⟨base, hh⟩)
    (C.hop_step a _)
  rw [writeCell_self] at h
  exact h

/-! ### The cycle -/
/-- **The exact thirteen-step frame rewrite cycle, generically.**  From the last
cell of a frame whose four cells spell `marker`, thirteen genuine TM steps
replace it by `target` and return the control to the reverse scan's entry shape
on the last cell of the preceding frame: head `base + 3 ↦ base - 1`, carried
context `a` preserved, mode back to `seekMode`, tape exactly `writeFrame4` of
the old tape.

The thirteen is `4 + 4 + 4 + 1` and every summand is a theorem: the reverse
scanner's boundary macrostep, the frame writer's macrostep, the walk back, and
one explicit transition tuple. -/
theorem rewriteCycle (C : FrameRewriteCycle S F Mode Aux) (n base : Nat)
    (hpos : 0 < base) (hsafe : base + 4 < C.scanner.machine.tapeLength n)
    (tape : Fin (C.scanner.machine.tapeLength n) → Bool) (a : Aux)
    (hbits : physicalBitsAt hsafe tape = C.scanner.codec.bits C.marker) :
    TM.runConfig (M := C.scanner.machine)
        (C.scanner.revAligned n (base + 3) (by omega) tape C.seekMode a) 13 =
      C.scanner.revAligned n (base - 1) (by omega)
        (writeFrame4 base C.w0 C.w1 C.w2 C.w3 tape) C.seekMode a := by
  have hA : TM.runConfig (M := C.scanner.machine)
      (C.cfg n (base + 3) (by omega) tape (C.scanner.rst3 C.seekMode a)) 4 =
      C.cfg n base (by omega) tape (C.scanner.stopState C.stopMode a) := by
    have h := C.scanner.revAnchorStep n base hsafe tape C.seekMode C.marker a
      C.seek_reverse (by rw [C.marker_stop]; exact C.stop_stops) hbits
    rw [C.marker_stop] at h
    exact h
  have hB : TM.runConfig (M := C.scanner.machine)
      (C.cfg n base (by omega) tape (C.scanner.stopState C.stopMode a)) 4 =
      C.cfg n (base + 4) hsafe
        (writeFrame4 base C.w0 C.w1 C.w2 C.w3 tape) (C.bst0 a) :=
    C.toWriter.writeMacrostep n base hsafe tape a
  have hC := C.backWalk n base hsafe
    (writeFrame4 base C.w0 C.w1 C.w2 C.w3 tape) a
  have hD := C.hopStep n base hpos (by omega)
    (writeFrame4 base C.w0 C.w1 C.w2 C.w3 tape) a
  show TM.runConfig (M := C.scanner.machine)
      (C.cfg n (base + 3) (by omega) tape (C.scanner.rst3 C.seekMode a))
      (4 + 4 + 4 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add, hA, hB, hC, hD]

/-- **The rewrite cycle on an arbitrary frame list.**  Thirteen genuine TM steps
turn the tape backed by `pre ++ marker :: suffix` into the tape backed by
`pre ++ target :: suffix`, with the head returning to the last cell of the frame
before the rewritten one and the mode and context restored.  Nothing outside
the rewritten frame changes. -/
theorem rewriteCycleOnList (C : FrameRewriteCycle S F Mode Aux) (n : Nat)
    (pre suffix : List F) (a : Aux) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < C.scanner.machine.tapeLength n) :
    TM.runConfig (M := C.scanner.machine)
        (C.scanner.revAligned n (4 * pre.length + 3) (by omega)
          (frameListTape
            ((pre ++ C.marker :: suffix).flatMap C.scanner.codec.bits))
          C.seekMode a) 13 =
      C.scanner.revAligned n (4 * pre.length - 1) (by omega)
        (frameListTape
          ((pre ++ C.target :: suffix).flatMap C.scanner.codec.bits))
        C.seekMode a := by
  have hbits := physicalBitsAt_flatMap (L := C.scanner.machine.tapeLength n)
    C.scanner.codec pre suffix C.marker hsafe
  rw [C.rewriteCycle n (4 * pre.length) (by omega) hsafe _ a hbits,
    writeFrame4_frameListTape C.scanner.codec pre suffix C.marker C.target
      C.target_bits]

/-- **Seek, then rewrite.**  From the last cell of the last frame of an
arbitrary skippable run, `4 * skipped.length + 13` genuine TM steps cross the
run right to left, rewrite the marker frame that ends it, and return to the
reverse scan's entry shape one frame further left.  The tape changes in exactly
the four cells of the marker frame. -/
theorem seekAndRewrite (C : FrameRewriteCycle S F Mode Aux) (n : Nat)
    (pre skipped suffix : List F) (a : Aux) (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, C.scanner.revAdvance C.seekMode f = C.seekMode)
    (hsafe : 4 * (pre.length + skipped.length) + 4 <
      C.scanner.machine.tapeLength n) :
    TM.runConfig (M := C.scanner.machine)
        (C.scanner.revAligned n (4 * (pre.length + skipped.length) + 3)
          (by omega)
          (frameListTape ((pre ++ C.marker :: skipped ++ suffix).flatMap
            C.scanner.codec.bits))
          C.seekMode a)
        (4 * skipped.length + 13) =
      C.scanner.revAligned n (4 * pre.length - 1) (by omega)
        (frameListTape ((pre ++ C.target :: skipped ++ suffix).flatMap
          C.scanner.codec.bits))
        C.seekMode a := by
  have hskipRun := C.scanner.revSkipRun n pre C.marker skipped suffix
    C.seekMode a C.seek_reverse C.seek_nostop hskip hsafe
  have hcycle := C.rewriteCycleOnList n pre (skipped ++ suffix) a hpre
    (by omega)
  simp only [List.append_assoc, List.cons_append] at hskipRun hcycle ⊢
  rw [runConfig_add, hskipRun, hcycle]

end FrameRewriteCycle

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
