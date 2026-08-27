import Complexity.TMVerifier.TuringToolkit.FrameScannerReverseProbe
import Complexity.TMVerifier.TuringToolkit.FrameScannerReverseInstances

/-!
# Reverse/write frame-kernel surface tests

Pins the shared phase-aligned layer, the generic reverse macrostep and list
induction with its projections, the four-cell write/replacement layer, the
non-T1 probe with its two concrete runs, and the T1/G1 reverse regressions.
-/

namespace Pnp3.Tests.TMFrameScannerReverseSurface

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

-- shared phase-aligned layer
#check @Phased.alignedAt
#check @Phased.stepRight
#check @Phased.stepLeft
#check @Phased.stepStay

-- generic reverse kernel
#check @ReverseFrameScanner
#check @ReverseFrameScanner.revAligned
#check @ReverseFrameScanner.revComplete_of_bits
#check @ReverseFrameScanner.revFrameMacrostepAt
#check @ReverseFrameScanner.RevValidPath
#check @ReverseFrameScanner.revAdvanceList
#check @ReverseFrameScanner.revAdvanceList_eq_foldr
#check @ReverseFrameScanner.revValidPath_append_singleton
#check @ReverseFrameScanner.revScanFrames_tape
#check @ReverseFrameScanner.revScanFrames_state
#check @ReverseFrameScanner.revScanFrames_head

-- generic write/replacement kernel
#check @writeFrame4
#check @FrameWriter

-- non-T1 genericity probe: instances and concrete executable runs
#check @revProbeCodec
#check @revProbeScanner
#check @revProbeWriter
#check @ReverseFrameScanner.revValidPath_const
#check @revProbeTail_advanceList


-- concrete T1/G1 reverse instances and regressions
#check @t1RevScanner
#check @g1RevScanner

/-! ## Exact theorem-contract pins -/

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]
variable {F Mode Aux : Type v}

theorem check_revFrameMacrostep
    (K : ReverseFrameScanner S F Mode Aux) (n base : Nat)
    (hpos : 0 < base) (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (frame : F)
    (a : Aux) (hm : K.Reverse m) (hnext : ¬ K.Stop (K.revAdvance m frame))
    (hbits : physicalBitsAt hsafe tape = K.codec.bits frame) :
    K.machine.runConfig
        (K.revAligned n (base + 3) (by omega) tape m a) 4 =
      K.revAligned n (base - 1) (by omega) tape (K.revAdvance m frame) a :=
  K.revFrameMacrostep n base hpos hsafe tape m frame a hm hnext hbits

theorem check_revAnchorStep
    (K : ReverseFrameScanner S F Mode Aux) (n base : Nat)
    (hsafe : base + 4 < K.machine.tapeLength n)
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (frame : F)
    (a : Aux) (hm : K.Reverse m) (hstop : K.Stop (K.revAdvance m frame))
    (hbits : physicalBitsAt hsafe tape = K.codec.bits frame) :
    K.machine.runConfig
        (K.revAligned n (base + 3) (by omega) tape m a) 4 =
      K.alignedConfigQ n base (by omega) tape
        (K.stopState (K.revAdvance m frame) a) :=
  K.revAnchorStep n base hsafe tape m frame a hm hstop hbits

theorem check_revScanFrames
    (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (anchor : F) (scanned suffix : List F) (mode : Mode)
    (a : Aux) (hpath : K.RevValidPath mode scanned)
    (hsafe : 4 * (pre.length + scanned.length) + 4 < K.machine.tapeLength n) :
    K.machine.runConfig
        (K.revAligned n (4 * (pre.length + scanned.length) + 3) (by omega)
          (frameListTape
            ((pre ++ anchor :: scanned ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * scanned.length) =
      K.revAligned n (4 * pre.length + 3) (by omega)
        (frameListTape
          ((pre ++ anchor :: scanned ++ suffix).flatMap K.codec.bits))
        (K.revAdvanceList mode scanned) a :=
  K.revScanFrames n pre anchor scanned suffix mode a hpath hsafe

theorem check_revScanToAnchor
    (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (anchor : F) (scanned suffix : List F) (mode : Mode) (a : Aux)
    (hpath : K.RevValidPath mode scanned)
    (hrev : K.Reverse (K.revAdvanceList mode scanned))
    (hstop : K.Stop (K.revAdvance (K.revAdvanceList mode scanned) anchor))
    (hsafe : 4 * scanned.length + 4 < K.machine.tapeLength n) :
    K.machine.runConfig
        (K.revAligned n (4 * scanned.length + 3) (by omega)
          (frameListTape ((anchor :: scanned ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * scanned.length + 4) =
      K.alignedConfigQ n 0 (by omega)
        (frameListTape ((anchor :: scanned ++ suffix).flatMap K.codec.bits))
        (K.stopState (K.revAdvance (K.revAdvanceList mode scanned) anchor) a) :=
  K.revScanToAnchor n anchor scanned suffix mode a hpath hrev hstop hsafe

theorem check_writeFrame4_apply {L : Nat} (base : Nat) (b0 b1 b2 b3 : Bool)
    (tape : Fin L → Bool) (i : Fin L) :
    writeFrame4 base b0 b1 b2 b3 tape i =
      if (i : Nat) = base then b0
      else if (i : Nat) = base + 1 then b1
      else if (i : Nat) = base + 2 then b2
      else if (i : Nat) = base + 3 then b3
      else tape i :=
  writeFrame4_apply base b0 b1 b2 b3 tape i

theorem check_writeFrame4_frameListTape
    (C : FrameCodec F) {L : Nat} (pre suffix : List F) (old new : F)
    {b0 b1 b2 b3 : Bool} (hbits : C.bits new = [b0, b1, b2, b3]) :
    writeFrame4 (L := L) (4 * pre.length) b0 b1 b2 b3
        (frameListTape ((pre ++ old :: suffix).flatMap C.bits)) =
      frameListTape ((pre ++ new :: suffix).flatMap C.bits) :=
  writeFrame4_frameListTape C pre suffix old new hbits

theorem check_writeMacrostep
    (W : FrameWriter S F Aux) (n base : Nat)
    (hsafe : base + 4 < W.machine.tapeLength n)
    (tape : Fin (W.machine.tapeLength n) → Bool) (a : Aux) :
    W.machine.runConfig
        (W.alignedConfigQ n base (by omega) tape (W.wst0 a)) 4 =
      W.alignedConfigQ n (base + 4) hsafe
        (writeFrame4 base W.w0 W.w1 W.w2 W.w3 tape) (W.exitState a) :=
  W.writeMacrostep n base hsafe tape a

theorem check_writeFrameOnList
    (W : FrameWriter S F Aux) (n : Nat)
    (pre suffix : List F) (old : F) (a : Aux)
    (hsafe : 4 * pre.length + 4 < W.machine.tapeLength n) :
    W.machine.runConfig
        (W.alignedConfigQ n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ old :: suffix).flatMap W.codec.bits))
          (W.wst0 a)) 4 =
      W.alignedConfigQ n (4 * pre.length + 4) hsafe
        (frameListTape ((pre ++ W.target :: suffix).flatMap W.codec.bits))
        (W.exitState a) :=
  W.writeFrameOnList n pre suffix old a hsafe

theorem check_revProbeCS_scan_word (n : Nat) (a : Bool × Bool × Bool) :
    revProbeScanner.machine.runConfig
        (revProbeScanner.revAligned n 19
          (revProbeScanner_lt_tapeLength (by omega))
          (frameListTape (revProbeWord.flatMap RevFrame.bits)) .rScan a) 20 =
      revProbeScanner.alignedConfigQ n 0
        (revProbeScanner_lt_tapeLength (by omega))
        (frameListTape (revProbeWord.flatMap RevFrame.bits))
        (revState .rHalt .q0 false false false a) :=
  revProbeCS_scan_word n a

theorem check_revProbeCS_write_cell (n : Nat) (a : Bool × Bool × Bool) :
    revProbeWriter.machine.runConfig
        (revProbeWriter.alignedConfigQ n 12
          (revProbeWriter_lt_tapeLength (by omega))
          (frameListTape (revProbeWord.flatMap RevFrame.bits))
          (revState .wCell .q0 false false false a)) 4 =
      revProbeWriter.alignedConfigQ n 16
        (revProbeWriter_lt_tapeLength (by omega))
        (frameListTape
          ([RevFrame.rvAnchor, .rvCell true, .rvMark, .rvSpent,
            .rvSpent].flatMap RevFrame.bits))
        (revState .wDone .q0 false false false a) :=
  revProbeCS_write_cell n a

theorem check_t1RevScanner_rewind_tail (n : Nat) (tail suffix : List T1Frame)
    (latch : Bool) (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * (1 + tail.length) < T1M.tapeLength n) :
    T1M.runConfig
        (t1AlignedConfig n (4 * (1 + tail.length) - 1) (by omega)
          (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
          .rewind .p3 false false false latch) (4 * tail.length) =
      t1AlignedConfig n 3 (by omega)
        (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
        .rewind .p3 false false false latch :=
  t1RevScanner_rewind_tail n tail suffix latch hne hsafe

theorem check_g1RevScanner_rewind_tail (n : Nat) (tail suffix : List G1Frame)
    (ctx : G1Ctx) (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * (1 + tail.length) < G1M.tapeLength n) :
    G1M.runConfig
        (g1AlignedConfig n (4 * (1 + tail.length) - 1) (by omega)
          (g1ListTape ((.bof :: tail ++ suffix).flatMap G1Frame.bits))
          .rewind .p3 false false false ctx) (4 * tail.length) =
      g1AlignedConfig n 3 (by omega)
        (g1ListTape ((.bof :: tail ++ suffix).flatMap G1Frame.bits))
        .rewind .p3 false false false ctx :=
  g1RevScanner_rewind_tail n tail suffix ctx hne hsafe

end Pnp3.Tests.TMFrameScannerReverseSurface
