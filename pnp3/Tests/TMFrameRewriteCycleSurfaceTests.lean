import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleProbe
import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleInstances

/-!
# Rewrite-cycle surface tests

Pins the generic leftward writer, the seek-until-marker driver, the exact
thirteen-step frame rewrite cycle with its frame-list and seek forms, the
non-T1 probe with its four concrete runs, the T1 regressions, the G1 seek
instantiation, G1's `index -> spent` round as a genuine instance, and the G1
cycle obligation together with its constructed inhabitant.
-/
namespace Pnp3.Tests.TMFrameRewriteCycleSurface

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

-- generic leftward four-cell writer
#check @writeFrame4_descending
#check @ReverseFrameWriter
#check @ReverseFrameWriter.writeMacrostepLeft
#check @ReverseFrameWriter.writeFrameOnListLeft
-- generic seek-until-marker driver
#check @ReverseFrameScanner.revSkipRun
#check @ReverseFrameScanner.revSeekToMarker
#check @ReverseFrameScanner.revSeekToMarker_head
-- generic thirteen-step rewrite cycle
#check @FrameRewriteCycle
#check @FrameRewriteCycle.toWriter
#check @FrameRewriteCycle.backWalk
#check @FrameRewriteCycle.hopStep
#check @FrameRewriteCycle.rewriteCycle
#check @FrameRewriteCycle.rewriteCycleOnList
#check @FrameRewriteCycle.seekAndRewrite
-- non-T1 genericity probe: instances and concrete executable runs
#check @cycProbeCS
#check @cycProbeScanner
#check @cycProbeCycle
#check @cycProbeWriterL
#check @cycProbeCS_rewrite_cycle
#check @cycProbeCS_seek_rewrite
#check @cycProbeCS_seek_marker
#check @cycProbeCS_write_left
-- concrete T1 instances and regressions
#check @t1RepairScanner
#check @t1RepairCycle
#check @t1RepairCycle_repair_cycle
#check @t1RepairCycle_repair_cycle_onList
#check @t1OutWriter
#check @t1OutWriter_outWriteOut_frame
-- G1: the seek at the rewind modes, the destructive index round as a genuine
-- instance, and the now-inhabited obligation
#check @g1RevScanner_seek_bof
#check @g1IndexRevAdvance
#check @g1IndexRevComplete
#check @G1IndexWalkMode
#check @G1IndexStop
#check @g1IndexScanner
#check @g1IndexCycle
#check @g1CS_index_round
#check @g1CS_index_round_onList
#check @G1RewriteCycleObligation
#check @G1RewriteCycleObligation.machine_eq
#check @g1RewriteCycleObligation
#check @G1RewriteCycleObligation.rewrite_cycle

end Pnp3.Tests.TMFrameRewriteCycleSurface
