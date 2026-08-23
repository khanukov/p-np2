import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoopExamples

/-!
# T1b-B mutation-loop surface tests

Compile-time pins for the canonical loop configuration, frame/tape invariants,
exact one-iteration theorem, exact OOB theorem, and concrete non-vacuity probes.
The induction and terminal split remain deliberately absent.
-/

namespace Pnp3.Tests.TMTrueUniformSeekMutationLoopSurface

open Pnp3.Internal.PsubsetPpoly.TM

#check @t1CS_scan_back_skip
#check @t1LoopFrames
#check @t1LoopFramesMarked
#check @t1LoopFramesRestored
#check @t1MutationTape_eq_listTape
#check @t1CursorBase_safe
#check @t1MutationConfig
#check @t1MutationConfig_tape
#check @t1MutationConfig_head
#check @t1CS_mutationConfig_zero
#check @t1CS_loop_iteration_exact
#check @t1CS_loop_oob_exact
#check @t1bbIterationZero
#check @t1bbOobAtOne

end Pnp3.Tests.TMTrueUniformSeekMutationLoopSurface
