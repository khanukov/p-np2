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
#check @ReverseFrameScanner.revFrameMacrostep
#check @ReverseFrameScanner.revFrameMacrostepAt
#check @ReverseFrameScanner.revAnchorStep
#check @ReverseFrameScanner.RevValidPath
#check @ReverseFrameScanner.revAdvanceList
#check @ReverseFrameScanner.revAdvanceList_eq_foldr
#check @ReverseFrameScanner.revValidPath_append_singleton
#check @ReverseFrameScanner.revScanFrames
#check @ReverseFrameScanner.revScanFrames_tape
#check @ReverseFrameScanner.revScanFrames_state
#check @ReverseFrameScanner.revScanFrames_head
#check @ReverseFrameScanner.revScanToAnchor

-- generic write/replacement kernel
#check @writeFrame4
#check @writeFrame4_apply
#check @writeFrame4_frameListTape
#check @FrameWriter
#check @FrameWriter.writeMacrostep
#check @FrameWriter.writeFrameOnList

-- non-T1 genericity probe: instances and concrete executable runs
#check @revProbeCodec
#check @revProbeScanner
#check @revProbeWriter
#check @ReverseFrameScanner.revValidPath_const
#check @revProbeTail_advanceList
#check @revProbeCS_scan_word
#check @revProbeCS_write_cell

-- concrete T1/G1 reverse instances and regressions
#check @t1RevScanner
#check @t1RevScanner_rewind_tail
#check @g1RevScanner
#check @g1RevScanner_rewind_tail

end Pnp3.Tests.TMFrameScannerReverseSurface
