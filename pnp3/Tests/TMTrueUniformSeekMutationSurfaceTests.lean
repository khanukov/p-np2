import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekExamples

/-!
# T1b-A true uniform-seek mutation surfaces

Named compile-time pins for the fixed finite control, mutation tape vocabulary,
atomic genuine-TM steps, canonical first-cursor installation, and empty-data OOB
execution.  T1b-A does not claim the `j → j+1` loop, restoration, output, or
acceptance.  Since T1c-1 the OOB boundary is active, so only the exact
finite-prefix form survives here.
-/

namespace Pnp3.Tests.TMTrueUniformSeekMutationSurface

open Pnp3.Internal.PsubsetPpoly.TM

-- Fixed-control and transition-table surface.
#check @t1SuccessState
#check @t1OobState
#check @t1SeekBackAdvance
#check @t1Transition_startMutation_active
#check @t1Transition_probeData_p3_data
#check @t1Transition_probeData_p3_oob
#check @t1Transition_turnInstall
#check @t1Transition_writeCursor
#check @t1Transition_seekIndexBack_p0_mark
#check @t1Transition_seekIndexBack_p0_skip
#check @t1Transition_seekIndexBack_p0_success
#check @t1Transition_markSpent
#check @t1Transition_backupCursor
#check @t1Transition_writeData

-- Mutation tape vocabulary.
#check @t1WriteCell
#check @t1WriteFrame
#check @t1WriteFrame_ascending
#check @t1WriteFrame_descending
#check @t1MutationFrames
#check @t1CursorFrameIndex
#check @t1CursorBase
#check @t1MutationFrames_zero
#check @encodeT1Frames_split
#check @t1MutationTape
#check @t1MutationTape_zero
#check @t1ListTape_write_frame

theorem check_t1PhysicalBitsAt_flatMap
    (n : Nat) (pre suffix : List T1Frame) (frame : T1Frame)
    (hsafe : 4 * pre.length + 4 < T1M.tapeLength n) :
    t1PhysicalBitsAt hsafe
        (t1ListTape ((pre ++ frame :: suffix).flatMap T1Frame.bits)) =
      frame.bits :=
  t1PhysicalBitsAt_flatMap n pre suffix frame hsafe

-- Generic aligned-step bridge adapters and the stable accept/reject sinks.
#check @t1CS_aligned_step_right
#check @t1CS_aligned_step_left
#check @t1CS_aligned_step_stay
#check @t1CS_runConfig_sink

-- Atomic mutation execution.
#check @t1CS_startMutation_walk
#check @t1CS_probeData_frame_data
#check @t1CS_probeData_frame_oob
#check @t1CS_turnInstall_step
#check @t1CS_writeCursor_frame
#check @t1CS_markSpent_frame
#check @t1CS_backupCursor_walk
#check @t1CS_writeData_frame
#check @t1CS_seekIndexBack_frame_skip
#check @t1CS_seekIndexBack_frame_mark
#check @t1CS_seekIndexBack_frame_success

-- Dependency-closed T1b-A capstones.
#check @t1CS_install_first_cursor_exact
#check @t1CS_runConfig_install_first_cursor_exact
#check @t1CS_oob_empty_data_exact

-- Concrete zero/nonzero/OOB probes.
#check @t1bIndexZero_install
#check @t1bNonzeroIndex_install
#check @t1bEmptyData_oob_exact

end Pnp3.Tests.TMTrueUniformSeekMutationSurface
