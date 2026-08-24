import Complexity.TMVerifier.TuringToolkit.FrameScannerProbe
import Complexity.TMVerifier.TuringToolkit.FrameScannerT1

/-!
# Generic frame-scanner surface tests

Pins the codec, generic four-step and list-scan execution kernels, a genuinely
non-T1 instance, and the concrete T1 regression instantiation.
-/

namespace Pnp3.Tests.TMFrameScannerSurface

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

#check @FrameCodec
#check @FrameCodec.decode_bits
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
#check @probeCS_frame_macrostep
#check @probeCS_scan_frames
#check @probeCS_scan_probeWord

#check @t1FrameCodec
#check @t1FrameScanner
#check @t1FrameScanner_frameMacrostep
#check @t1FrameScanner_scanFrames

end Pnp3.Tests.TMFrameScannerSurface
