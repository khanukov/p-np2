import Complexity.TMVerifier.TuringToolkit.FrameScannerProbe
import Complexity.TMVerifier.TuringToolkit.FrameScannerT1

/-!
# Generic frame-scanner surface tests

Pins the codec, generic four-step and list-scan execution kernels, a genuinely
non-T1 instance, and the concrete T1 regression instantiation.
-/

namespace Pnp3.Tests.TMFrameScannerSurface

universe v

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

#check @FrameCodec
#check @FrameCodec.decode_bits
#check @FrameCodec.bits_injective
#check @FrameCodec.bits_eq_four
#check @FrameCodec.flatMap_bits_length
#check @FrameScan.writeCell_self
#check @FrameScan.frameListTape
#check @FrameScan.physicalBitsAt_flatMap
#check @FrameScanner
#check @FrameScanner.alignedStepRight
#check @FrameScanner.alignedStepLeft
#check @FrameScanner.alignedStepStay
#check @FrameScanner.complete_of_bits
#check @FrameScanner.frameMacrostep
#check @FrameScanner.ValidPath
#check @FrameScanner.advanceList
#check @FrameScanner.advanceList_eq_foldl
#check @FrameScanner.advanceList_append
#check @FrameScanner.scanFrames
#check @FrameScanner.scanFrames_tape
#check @FrameScanner.scanFrames_state
#check @FrameScanner.scanFrames_head

#check @probeFrameCodec
#check @probeFrameScanner
#check @probeCS_runTime
#check @probeCS_frame_macrostep
#check @probeCS_scan_frames
#check @probeCS_scan_probeWord
#check @probeCS_scan_probeWord_one

#check @t1FrameCodec
#check @t1FrameCodec_bits
#check @t1FrameCodec_decode
#check @t1FrameScanner
#check @t1FrameScanner_machine
#check @t1FrameScanner_frameMacrostep
#check @t1FrameScanner_scanFrames

/-! ## Exact theorem-contract pins -/

theorem check_frameMacrostep {S : Type v} [Fintype S] [DecidableEq S]
    {F Mode Aux : Type v} (K : FrameScanner S F Mode Aux) (n h : Nat)
    (hsafe : h + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (frame : F)
    (a : Aux) (hm : K.Forward m) (hnext : K.advance m frame ≠ K.rejectMode)
    (hbits : physicalBitsAt hsafe tape = K.codec.bits frame) :
    K.machine.runConfig
        (K.alignedFrame n h (by omega) tape m a) 4 =
      K.alignedFrame n (h + 4) hsafe tape (K.advance m frame) a :=
  K.frameMacrostep n h hsafe tape m frame a hm hnext hbits

theorem check_scanFrames {S : Type v} [Fintype S] [DecidableEq S]
    {F Mode Aux : Type v} (K : FrameScanner S F Mode Aux) (n : Nat)
    (pre frames suffix : List F) (mode : Mode) (a : Aux)
    (hpath : K.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < K.machine.tapeLength n) :
    K.machine.runConfig
        (K.alignedFrame n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ frames ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * frames.length) =
      K.alignedFrame n (4 * (pre.length + frames.length)) hsafe
        (frameListTape ((pre ++ frames ++ suffix).flatMap K.codec.bits))
        (K.advanceList mode frames) a :=
  K.scanFrames n pre frames suffix mode a hpath hsafe

theorem check_probeCS_scan_probeWord (n : Nat)
    (hsafe : 24 < probeFrameScanner.machine.tapeLength n) (a : Bool × Bool) :
    probeFrameScanner.machine.runConfig
        (probeFrameScanner.alignedFrame n 0 (by omega)
          (frameListTape (probeWord.flatMap ProbeFrame.bits)) .scanTag a) 24 =
      probeFrameScanner.alignedFrame n 24 hsafe
        (frameListTape (probeWord.flatMap ProbeFrame.bits)) .done a :=
  probeCS_scan_probeWord n hsafe a

theorem check_t1FrameScanner_frameMacrostep (n h : Nat)
    (hsafe : h + 4 < t1FrameScanner.machine.tapeLength n)
    (tape : Fin (t1FrameScanner.machine.tapeLength n) → Bool)
    (mode : T1Mode) (frame : T1Frame) (latch : Bool)
    (hmode : T1ForwardMode mode) (hnext : t1Advance mode frame ≠ .reject)
    (hbits : physicalBitsAt hsafe tape = T1Frame.bits frame) :
    t1FrameScanner.machine.runConfig
        (t1FrameScanner.alignedFrame n h (by omega) tape mode latch) 4 =
      t1FrameScanner.alignedFrame n (h + 4) hsafe tape
        (t1Advance mode frame) latch :=
  t1FrameScanner_frameMacrostep n h hsafe tape mode frame latch hmode hnext hbits

theorem check_t1FrameScanner_scanFrames (n : Nat)
    (pre frames suffix : List T1Frame) (mode : T1Mode) (latch : Bool)
    (hpath : t1FrameScanner.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) <
      t1FrameScanner.machine.tapeLength n) :
    t1FrameScanner.machine.runConfig
        (t1FrameScanner.alignedFrame n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ frames ++ suffix).flatMap T1Frame.bits))
          mode latch)
        (4 * frames.length) =
      t1FrameScanner.alignedFrame n (4 * (pre.length + frames.length)) hsafe
        (frameListTape ((pre ++ frames ++ suffix).flatMap T1Frame.bits))
        (t1FrameScanner.advanceList mode frames) latch :=
  t1FrameScanner_scanFrames n pre frames suffix mode latch hpath hsafe

end Pnp3.Tests.TMFrameScannerSurface
