import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriverExamples

/-!
# T1b-C seek-driver surface tests

Pins the exact closed-form loop clock, induction, success/OOB terminal cases,
the clock estimate and concrete non-vacuity probes.  These are finite-prefix
boundary execution theorems, not acceptance or output theorems.  The
public-clock `TM.run` pins are gone: T1c-1 activated both boundaries.
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
#check @t1OobSteps_nil
#check @t1OobSteps_cons
#check @t1DecideSteps
#check @t1DecideTotal
#check @t1DecideSteps_some
#check @t1DecideSteps_none
#check @t1Selected_none_iff
#check @t1CS_runConfig_decide_success_exact
#check @t1CS_runConfig_decide_oob_exact
#check @t1CS_runConfig_decide_oob_empty_exact
#check @t1CS_decideTotal_le_clock

#check @t1bcDriveToSlotTwo
#check @t1bcSuccessTail
#check @t1bcSuccessFromInitial
#check @t1bcOobFromInitial
#check @t1bcEmptyOobFromInitial
#check @t1bcSuccessFitsClock
#check @t1bcOobFitsClock
#check @t1bcEmptyFitsClock

/-! ## Exact theorem-contract pins

Unlike the existence checks above, these wrappers restate the load-bearing
dependent configuration equalities.  A weakened head, tape, state, latch or
clock conclusion therefore fails this surface module. -/

theorem check_t1CS_loop_iterate_exact (r : T1Request) (b : Bool)
    (h0 : 0 < r.data.length) (hb : r.data[0]? = some b) :
    ∀ (m : Nat), m ≤ r.index → ∀ (hmd : m < r.data.length) (v : Bool),
      r.data[m]? = some v →
      T1M.runConfig (t1MutationConfig r 0 h0 b) (t1LoopSteps m) =
        t1MutationConfig r m hmd v :=
  t1CS_loop_iterate_exact r b h0 hb

theorem check_t1CS_loop_success_tail_exact (r : T1Request) (latch : Bool)
    (hk : r.index < r.data.length) :
    T1M.runConfig (t1MutationConfig r r.index hk latch)
        (8 * r.index + 8) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .successStart .p0 false false false latch :=
  t1CS_loop_success_tail_exact r latch hk

theorem check_t1CS_runConfig_decide_success_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    T1M.runConfig (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1DecideTotal r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .successStart .p0 false false false v :=
  t1CS_runConfig_decide_success_exact r v hv

theorem check_t1CS_runConfig_decide_oob_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = none) (hne : 0 < r.data.length)
    (hlast : r.data[r.data.length - 1]? = some v) :
    T1M.runConfig (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1DecideTotal r) =
      t1AlignedConfig (encodeT1 r).length
        (4 * (r.index + (r.data.length - 1) + 3) + 3) (t1dOobHead_safe r)
        (t1ListTape
          ((t1LoopFramesRestored r (r.data.length - 1)).flatMap T1Frame.bits))
        .oobStart .p0 false false false v :=
  t1CS_runConfig_decide_oob_exact r v hv hne hlast

theorem check_t1CS_runConfig_decide_oob_empty_exact (r : T1Request)
    (hdata : r.data = []) :
    T1M.runConfig (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1DecideTotal r) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3)
        (t1dEmptyOobHead_safe r)
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .oobStart .p0
        false false false false :=
  t1CS_runConfig_decide_oob_empty_exact r hdata

theorem check_t1CS_decideTotal_le_clock (r : T1Request) :
    t1DecideTotal r ≤ t1Clock (encodeT1 r).length :=
  t1CS_decideTotal_le_clock r

/-! The three former `check_t1CS_run_encoded_decide_*` wrappers are gone with
the theorems they restated: T1c-1 activated `successStart` and `oobStart`, so
there is no public-clock `TM.run` surface left to pin here. -/

#check @t1bcIndexZeroSuccessFromInitial
#check @t1bcOobBoundaryFromInitial

end Pnp3.Tests.TMTrueUniformSeekMutationDriverSurface
