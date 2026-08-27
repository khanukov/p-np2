import Complexity.TMVerifier.TuringToolkit.FrameScannerWrite

/-!
# The generic *leftward* four-cell frame writer

`FrameScannerWrite` supplies the left-to-right frame writer.  This module is
its mirror image — the shape `T1`'s output write (`outWriteOut`) already has,
and the shape any control that has just *read* a frame right to left needs:
from the **last** cell `base + 3`, four steps install the codeword in the order
`p3, p2, p1, p0` while the head *retreats* to `base - 1`, the last cell of the
preceding frame, so the reverse scan can resume immediately.

`writeFrame4_descending` is the tape-level fact that the descending write order
produces the *same* tape as the ascending one, so both writers share
`writeFrame4` and its replacement law `writeFrame4_frameListTape`.
`writeMacrostepLeft` is the exact four-step machine macro and
`writeFrameOnListLeft` the executable frame replacement on an **arbitrary**
surrounding frame list `pre ++ old :: suffix`.

**Obligation hygiene.**  A `ReverseFrameWriter` carries one codec law and four
*concrete transition tuple equalities*, quantified over the scanned cell and
the carried context.  Unlike the rightward `FrameWriter` the installed frame may
*depend on the context* (`target : Aux → F`), which is what `T1`'s
`output latch` does.  No semantic-correctness field, no desired-run field; every
execution theorem goes through `ConstStatePhasedStepBridge` via
`Phased.stepLeft`.

**Non-goals.**  Nothing here scans, decodes, addresses, accepts or rejects, and
nothing is claimed about non-canonical or physically padded tapes.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

universe v

open Pnp3.Internal.PsubsetPpoly.TM

/-! ## The tape-level mirror law -/
/-- **Descending writes agree with ascending ones.**  The four single-cell
writes a right-to-left writer performs, in the order it performs them, produce
exactly `writeFrame4`.  Hence the leftward writer inherits the generic
frame-replacement law `writeFrame4_frameListTape` unchanged. -/
theorem writeFrame4_descending {L : Nat} (base : Nat) (b0 b1 b2 b3 : Bool)
    (tape : Fin L → Bool) :
    writeCell base b0
        (writeCell (base + 1) b1
          (writeCell (base + 2) b2 (writeCell (base + 3) b3 tape))) =
      writeFrame4 base b0 b1 b2 b3 tape := by
  funext i
  rw [writeFrame4_apply]
  by_cases h0 : (i : Nat) = base
  · simp [writeCell, h0]
  · by_cases h1 : (i : Nat) = base + 1
    · simp [writeCell, h1]
    · by_cases h2 : (i : Nat) = base + 2
      · simp [writeCell, h2]
      · by_cases h3 : (i : Nat) = base + 3
        · simp [writeCell, h3]
        · simp [writeCell, h0, h1, h2, h3]

/-! ## The leftward writer -/
/-- **A fixed-width right-to-left frame writer.**

`lst3 … lst0` are the four aligned control states of a destructive right-to-left
walk across one frame — `lst3` standing on the last cell — and `exitState` the
state the control lands in on `base - 1`.  `w3 a … w0 a` are the literal cells
the finite control writes, in the order it writes them, and `target_bits` is
the codec law identifying them with the codeword of the frame `target a` this
control installs while carrying `a`. -/
structure ReverseFrameWriter (S : Type v) [Fintype S] [DecidableEq S]
    (F Aux : Type v) where
  program : ConstStatePhasedProgram S
  phase : Fin program.numPhases
  codec : FrameCodec F
  /-- The frame this control installs while carrying `a`. -/
  target : Aux → F
  w0 : Aux → Bool
  w1 : Aux → Bool
  w2 : Aux → Bool
  w3 : Aux → Bool
  lst3 : Aux → S
  lst2 : Aux → S
  lst1 : Aux → S
  lst0 : Aux → S
  exitState : Aux → S
  target_bits : ∀ a : Aux, codec.bits (target a) = [w0 a, w1 a, w2 a, w3 a]
  lstep_p3 : ∀ (a : Aux) (scan : Bool),
    program.transition phase (lst3 a) scan = (phase, lst2 a, w3 a, Move.left)
  lstep_p2 : ∀ (a : Aux) (scan : Bool),
    program.transition phase (lst2 a) scan = (phase, lst1 a, w2 a, Move.left)
  lstep_p1 : ∀ (a : Aux) (scan : Bool),
    program.transition phase (lst1 a) scan = (phase, lst0 a, w1 a, Move.left)
  lstep_p0 : ∀ (a : Aux) (scan : Bool),
    program.transition phase (lst0 a) scan =
      (phase, exitState a, w0 a, Move.left)

namespace ReverseFrameWriter

variable {S : Type v} [Fintype S] [DecidableEq S] {F Aux : Type v}

/-- The compiled machine of a leftward writer. -/
abbrev machine (W : ReverseFrameWriter S F Aux) : TM.{v} :=
  Phased.machine W.program

/-- A configuration in the writer's phase with an explicit head and state. -/
abbrev alignedConfigQ (W : ReverseFrameWriter S F Aux) (n h : Nat)
    (hh : h < W.machine.tapeLength n)
    (tape : Fin (W.machine.tapeLength n) → Bool) (q : S) :
    Configuration (M := W.machine) n :=
  Phased.alignedAt W.program W.phase n h hh tape q

/-- **Exact four-step leftward frame write, generically.**  From the *last*
cell of a frame, four genuine TM steps install `w0 … w3` into its four cells:
the head retreats from `base + 3` to `base - 1`, the carried context `a`
survives, the control lands in `exitState a`, and the tape is exactly
`writeFrame4` of the old tape. -/
theorem writeMacrostepLeft (W : ReverseFrameWriter S F Aux) (n base : Nat)
    (hpos : 0 < base) (hsafe : base + 4 < W.machine.tapeLength n)
    (tape : Fin (W.machine.tapeLength n) → Bool) (a : Aux) :
    TM.runConfig (M := W.machine)
        (W.alignedConfigQ n (base + 3) (by omega) tape (W.lst3 a)) 4 =
      W.alignedConfigQ n (base - 1) (by omega)
        (writeFrame4 base (W.w0 a) (W.w1 a) (W.w2 a) (W.w3 a) tape)
        (W.exitState a) := by
  have hb0 : base < W.machine.tapeLength n := by omega
  have hb1 : base + 1 < W.machine.tapeLength n := by omega
  have hb2 : base + 2 < W.machine.tapeLength n := by omega
  have hb3 : base + 3 < W.machine.tapeLength n := by omega
  have hs3 : TM.stepConfig (M := W.machine)
      (W.alignedConfigQ n (base + 3) hb3 tape (W.lst3 a)) =
      W.alignedConfigQ n (base + 2) hb2
        (writeCell (base + 3) (W.w3 a) tape) (W.lst2 a) := by
    simpa using Phased.stepLeft W.program W.phase n (base + 3) hb3 (by omega)
      tape (W.lst3 a) (W.lst2 a) (W.w3 a) (W.lstep_p3 a _)
  have hs2 : TM.stepConfig (M := W.machine)
      (W.alignedConfigQ n (base + 2) hb2
        (writeCell (base + 3) (W.w3 a) tape) (W.lst2 a)) =
      W.alignedConfigQ n (base + 1) hb1
        (writeCell (base + 2) (W.w2 a)
          (writeCell (base + 3) (W.w3 a) tape)) (W.lst1 a) := by
    simpa using Phased.stepLeft W.program W.phase n (base + 2) hb2 (by omega)
      (writeCell (base + 3) (W.w3 a) tape) (W.lst2 a) (W.lst1 a) (W.w2 a)
      (W.lstep_p2 a _)
  have hs1 : TM.stepConfig (M := W.machine)
      (W.alignedConfigQ n (base + 1) hb1
        (writeCell (base + 2) (W.w2 a)
          (writeCell (base + 3) (W.w3 a) tape)) (W.lst1 a)) =
      W.alignedConfigQ n base hb0
        (writeCell (base + 1) (W.w1 a) (writeCell (base + 2) (W.w2 a)
          (writeCell (base + 3) (W.w3 a) tape))) (W.lst0 a) := by
    simpa using Phased.stepLeft W.program W.phase n (base + 1) hb1 (by omega)
      (writeCell (base + 2) (W.w2 a) (writeCell (base + 3) (W.w3 a) tape))
      (W.lst1 a) (W.lst0 a) (W.w1 a) (W.lstep_p1 a _)
  have hs0 : TM.stepConfig (M := W.machine)
      (W.alignedConfigQ n base hb0
        (writeCell (base + 1) (W.w1 a) (writeCell (base + 2) (W.w2 a)
          (writeCell (base + 3) (W.w3 a) tape))) (W.lst0 a)) =
      W.alignedConfigQ n (base - 1) (by omega)
        (writeCell base (W.w0 a) (writeCell (base + 1) (W.w1 a)
          (writeCell (base + 2) (W.w2 a)
            (writeCell (base + 3) (W.w3 a) tape)))) (W.exitState a) :=
    Phased.stepLeft W.program W.phase n base hb0 hpos
      (writeCell (base + 1) (W.w1 a) (writeCell (base + 2) (W.w2 a)
        (writeCell (base + 3) (W.w3 a) tape)))
      (W.lst0 a) (W.exitState a) (W.w0 a) (W.lstep_p0 a _)
  show TM.runConfig (M := W.machine)
      (W.alignedConfigQ n (base + 3) hb3 tape (W.lst3 a)) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs3, hs2, hs1, hs0, writeFrame4_descending]

/-- **Executable leftward frame replacement, generically.**  On a tape backed by
an arbitrary frame list `pre ++ old :: suffix`, four genuine TM steps replace
the frame at index `pre.length` by `W.target a`: the head goes from the last
cell of that frame, `4 * pre.length + 3`, to the last cell of its predecessor,
the control lands in `exitState a`, and the tape is exactly the one backed by
`pre ++ W.target a :: suffix`. -/
theorem writeFrameOnListLeft (W : ReverseFrameWriter S F Aux) (n : Nat)
    (pre suffix : List F) (old : F) (a : Aux) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < W.machine.tapeLength n) :
    TM.runConfig (M := W.machine)
        (W.alignedConfigQ n (4 * pre.length + 3) (by omega)
          (frameListTape ((pre ++ old :: suffix).flatMap W.codec.bits))
          (W.lst3 a)) 4 =
      W.alignedConfigQ n (4 * pre.length - 1) (by omega)
        (frameListTape ((pre ++ W.target a :: suffix).flatMap W.codec.bits))
        (W.exitState a) := by
  rw [W.writeMacrostepLeft n (4 * pre.length) (by omega) hsafe _ a,
    writeFrame4_frameListTape W.codec pre suffix old (W.target a)
      (W.target_bits a)]

end ReverseFrameWriter

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
