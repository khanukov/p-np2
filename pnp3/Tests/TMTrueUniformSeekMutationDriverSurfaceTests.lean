import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriverExamples

/-!
# T1b-C seek-driver surface tests

Pins the exact closed-form loop clock, induction, success/OOB terminal cases,
public-clock padding and concrete non-vacuity probes.  These are boundary
execution theorems, not acceptance or output theorems.
-/

namespace Pnp3.Tests.TMTrueUniformSeekMutationDriverSurface

open Pnp3.Internal.PsubsetPpoly.TM

#check @t1LoopSteps
#check @t1LoopSteps_zero
#check @t1LoopSteps_one
#check @t1LoopSteps_mul
#check @t1LoopSteps_succ
#check @t1CS_loop_iterate_exact
#check @t1CS_loop_reach_exact
#check @t1CS_loop_success_tail_exact
#check @t1CS_loop_success_from_zero_exact
#check @t1CS_loop_oob_from_zero_exact
#check @t1SuccessSteps
#check @t1OobSteps
#check @t1DecideSteps
#check @t1DecideTotal
#check @t1DecideSteps_some
#check @t1DecideSteps_none
#check @t1Selected_none_iff
#check @t1CS_runConfig_decide_success_exact
#check @t1CS_runConfig_decide_oob_exact
#check @t1CS_runConfig_decide_oob_empty_exact
#check @t1CS_decideTotal_le_clock
#check @t1CS_run_encoded_decide_success
#check @t1CS_run_encoded_decide_oob_nonempty
#check @t1CS_run_encoded_decide_oob_empty
#check @t1CS_run_encoded_decide_oob

#check @t1bcDriveToSlotTwo
#check @t1bcSuccessTail
#check @t1bcSuccessFromInitial
#check @t1bcSuccessPublicClock
#check @t1bcOobFromInitial
#check @t1bcOobPublicClock
#check @t1bcEmptyOobFromInitial
#check @t1bcEmptyOobPublicClock
#check @t1bcSuccessFitsClock
#check @t1bcOobFitsClock
#check @t1bcEmptyFitsClock

end Pnp3.Tests.TMTrueUniformSeekMutationDriverSurface
