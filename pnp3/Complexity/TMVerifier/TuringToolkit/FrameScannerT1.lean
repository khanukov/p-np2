import Complexity.TMVerifier.TuringToolkit.FrameScannerKernel
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeek

/-!
# T1 as an instance of the generic frame-scanner kernel

`t1FrameCodec` presents `T1Frame` as a fixed-width `FrameCodec`, and
`t1FrameScanner` presents the T1 finite control as a `FrameScanner`: the T1
program `t1CS`, its single phase, the shared left-to-right table
`t1Advance`/`t1Complete`, the forward-mode predicate `T1ForwardMode`, and the
four aligned control states of `T1State` — whose carried context (`Aux`) is
T1's single Boolean latch.

Four transition obligations are discharged by the *existing* standalone
table lemmas of `TrueUniformSeek`; the fifth, `complete_decode`, follows by
definitional unfolding of `t1Complete`.  Nothing here unfolds `t1Transition`,
and no new hypothesis is introduced.  The named regression theorems below instantiate `FrameScanner.frameMacrostep`
and `FrameScanner.scanFrames` directly at T1.  Existing validation theorems
retain their public statements; the regressions pin that the generic kernel
reproduces the same execution shape without changing downstream APIs.

The compatibility facts below pin the program, machine, phase, frame codec,
advance table, and aligned start state used by the two regression theorems.
No equivalence with every legacy T1 helper (`T1ValidPath`, list tape, or all
intermediate state constructors) is claimed here.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- The T1 four-bit alphabet as a generic fixed-width codec. -/
def t1FrameCodec : FrameCodec T1Frame where
  bits := T1Frame.bits
  decode? := decodeT1Frame?
  bits_length := T1Frame.bits_length
  decode_bits := decodeT1Frame_bits

@[simp] theorem t1FrameCodec_bits : t1FrameCodec.bits = T1Frame.bits := rfl

@[simp] theorem t1FrameCodec_decode : t1FrameCodec.decode? = decodeT1Frame? :=
  rfl

/-- **T1 is an instance of the generic kernel.**  The context type is `Bool`,
carrying T1's cursor-value latch through every frame. -/
def t1FrameScanner : FrameScanner T1State T1Frame T1Mode Bool where
  program := t1CS
  phase := t1CS.startPhase
  codec := t1FrameCodec
  rejectMode := .reject
  advance := t1Advance
  complete := t1Complete
  Forward := T1ForwardMode
  st0 := fun mode latch => t1State mode .p0 false false false latch
  st1 := fun mode latch b0 => t1State mode .p1 b0 false false latch
  st2 := fun mode latch b0 b1 => t1State mode .p2 b0 b1 false latch
  st3 := fun mode latch b0 b1 b2 => t1State mode .p3 b0 b1 b2 latch
  complete_decode := fun m b0 b1 b2 b3 => by
    cases h : decodeT1Frame? [b0, b1, b2, b3] <;>
      simp [t1Complete, t1FrameCodec, h]
  step_p0 := fun hmode latch scan =>
    t1Transition_forward_p0 hmode t1CS.startPhase false false false latch scan
  step_p1 := fun hmode latch b0 scan =>
    t1Transition_forward_p1 hmode t1CS.startPhase b0 false false latch scan
  step_p2 := fun hmode latch b0 b1 scan =>
    t1Transition_forward_p2 hmode t1CS.startPhase b0 b1 false latch scan
  step_p3 := fun hmode latch b0 b1 b2 scan hne =>
    t1Transition_forward_p3_advance hmode t1CS.startPhase b0 b1 b2 latch scan hne

@[simp] theorem t1FrameScanner_program : t1FrameScanner.program = t1CS := rfl

@[simp] theorem t1FrameScanner_machine :
    t1FrameScanner.machine = t1CS.toPhased.toTM := rfl

@[simp] theorem t1FrameScanner_phase :
    t1FrameScanner.phase = t1CS.toPhased.startPhase := rfl

@[simp] theorem t1FrameScanner_advance : t1FrameScanner.advance = t1Advance :=
  rfl

@[simp] theorem t1FrameScanner_st0 (mode : T1Mode) (latch : Bool) :
    t1FrameScanner.st0 mode latch = t1State mode .p0 false false false latch :=
  rfl

/-- Concrete T1 instantiation of the generic four-step macro theorem. -/
theorem t1FrameScanner_frameMacrostep (n h : Nat)
    (hsafe : h + 4 < t1FrameScanner.machine.tapeLength n)
    (tape : Fin (t1FrameScanner.machine.tapeLength n) → Bool)
    (mode : T1Mode) (frame : T1Frame) (latch : Bool)
    (hmode : T1ForwardMode mode) (hnext : t1Advance mode frame ≠ .reject)
    (hbits : FrameScan.physicalBitsAt hsafe tape = T1Frame.bits frame) :
    TM.runConfig (M := t1FrameScanner.machine)
        (t1FrameScanner.alignedFrame n h (by omega) tape mode latch) 4 =
      t1FrameScanner.alignedFrame n (h + 4) hsafe tape
        (t1Advance mode frame) latch :=
  t1FrameScanner.frameMacrostep n h hsafe tape mode frame latch hmode hnext
    (by simpa using hbits)

/-- Concrete T1 instantiation of the generic exact list-scan induction. -/
theorem t1FrameScanner_scanFrames (n : Nat)
    (pre frames suffix : List T1Frame) (mode : T1Mode) (latch : Bool)
    (hpath : t1FrameScanner.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) <
      t1FrameScanner.machine.tapeLength n) :
    TM.runConfig (M := t1FrameScanner.machine)
        (t1FrameScanner.alignedFrame n (4 * pre.length) (by omega)
          (FrameScan.frameListTape
            ((pre ++ frames ++ suffix).flatMap T1Frame.bits)) mode latch)
        (4 * frames.length) =
      t1FrameScanner.alignedFrame n (4 * (pre.length + frames.length)) hsafe
        (FrameScan.frameListTape
          ((pre ++ frames ++ suffix).flatMap T1Frame.bits))
        (t1FrameScanner.advanceList mode frames) latch :=
  t1FrameScanner.scanFrames n pre frames suffix mode latch hpath hsafe

end TM
end PsubsetPpoly
end Internal
end Pnp3
