import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemanticsExamples

/-!
# T1c-3 canonical-semantics surfaces

Pins the total honest clock, the three exact compositions from the genuine
`T1M.initialConfig`, the merged reject arm, the public-clock bound, the two
full `T1M.run` theorems, full `TM.accepts` correctness, output-cell/tape
conservation, and the five concrete probes.

Out of scope by design (and unchanged by this slice): malformed or
trailing-padded physical tapes.  `T1Physical` stays reserved vocabulary; no
surface below consumes or discharges it.
-/

namespace Pnp3.Tests.TMTrueUniformSeekSemanticsSurface

open Pnp3.Internal.PsubsetPpoly.TM

-- Total honest clock, selected by the request's own slot option.
#check @t1TotalSteps
#check @t1TotalSteps_some
#check @t1TotalSteps_none

-- Exact composition from the real initial configuration.
#check @t1CS_runConfig_total_success_exact
#check @t1CS_runConfig_total_oob_exact
#check @t1CS_runConfig_total_oob_empty_exact
#check @t1CS_runConfig_total_reject_exact

-- The unchanged public clock has room for the whole run.
#check @t1CS_totalSteps_le_clock

-- Full public `TM.run`, padded only inside the stable sinks.
#check @t1CS_run_success_exact
#check @t1CS_run_reject_exact
#check @t1CS_run_head_zero

-- Full acceptance correctness (whole dependent state vs `T1M.accept`).
#check @t1CS_accepts_eq_isSome
#check @t1CS_accepts_iff
#check @t1CS_accepts_eq_decide_lt
#check @t1CS_run_reject_not_accepts

-- Output/tape correctness on the full run.
#check @t1CS_run_success_tape_eq
#check @t1CS_run_output_at
#check @t1CS_run_tape_off
#check @t1CS_run_reject_tape_eq
#check @t1CS_canonical_semantics

-- Concrete probes: true bit, false bit, strict OOB, boundary OOB, empty OOB.
#check @t1c3TrueRun
#check @t1c3TrueOutput
#check @t1c3TrueAccepts
#check @t1c3FalseRun
#check @t1c3FalseOutput
#check @t1c3FalseAccepts
#check @t1c3OobRun
#check @t1c3OobTapePreserved
#check @t1c3OobRejects
#check @t1c3BoundaryRun
#check @t1c3BoundaryRejects
#check @t1c3EmptyRun
#check @t1c3EmptyTapePreserved
#check @t1c3EmptyRejects
#check @t1c3TrueClockFits
#check @t1c3OobClockFits
#check @t1c3EmptyClockFits

/-! ## Exact theorem-contract pins -/

theorem check_t1CS_runConfig_total_success_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    T1M.runConfig (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1TotalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r v).flatMap T1Frame.bits))
        .accept .p0 false false false false :=
  t1CS_runConfig_total_success_exact r v hv

theorem check_t1CS_runConfig_total_oob_exact (r : T1Request)
    (hv : r.data[r.index]? = none) (hne : 0 < r.data.length) :
    T1M.runConfig (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1TotalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r false).flatMap T1Frame.bits))
        .reject .p0 false false false false :=
  t1CS_runConfig_total_oob_exact r hv hne

theorem check_t1CS_runConfig_total_oob_empty_exact (r : T1Request)
    (hdata : r.data = []) :
    T1M.runConfig (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1TotalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .reject .p0 false false false false :=
  t1CS_runConfig_total_oob_empty_exact r hdata

theorem check_t1CS_runConfig_total_reject_exact (r : T1Request)
    (hv : r.data[r.index]? = none) :
    T1M.runConfig (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1TotalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .reject .p0 false false false false :=
  t1CS_runConfig_total_reject_exact r hv

theorem check_t1CS_totalSteps_le_clock (r : T1Request) :
    t1TotalSteps r ≤ t1Clock (encodeT1 r).length :=
  t1CS_totalSteps_le_clock r

theorem check_t1CS_run_success_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r v).flatMap T1Frame.bits))
        .accept .p0 false false false false :=
  t1CS_run_success_exact r v hv

theorem check_t1CS_run_reject_exact (r : T1Request)
    (hv : r.data[r.index]? = none) :
    T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .reject .p0 false false false false :=
  t1CS_run_reject_exact r hv

theorem check_t1CS_accepts_eq_isSome (r : T1Request) :
    T1M.accepts (encodeT1 r).length (t1Point (encodeT1 r)) =
      (r.data[r.index]?).isSome :=
  t1CS_accepts_eq_isSome r

theorem check_t1CS_accepts_iff (r : T1Request) :
    T1M.accepts (encodeT1 r).length
        (t1Point (encodeT1 r)) = true ↔
      (r.data[r.index]?).isSome = true :=
  t1CS_accepts_iff r

theorem check_t1CS_accepts_eq_decide_lt (r : T1Request) :
    T1M.accepts (encodeT1 r).length (t1Point (encodeT1 r)) =
      decide (r.index < r.data.length) :=
  t1CS_accepts_eq_decide_lt r

theorem check_t1CS_run_success_tape_eq (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape =
      t1WriteCell (t1OutputPosition r) v
        (T1M.initialConfig (t1Point (encodeT1 r))).tape :=
  t1CS_run_success_tape_eq r v hv

theorem check_t1CS_run_reject_tape_eq (r : T1Request)
    (hv : r.data[r.index]? = none) :
    (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape :=
  t1CS_run_reject_tape_eq r hv

theorem check_t1CS_run_output_at (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v)
    (i : Fin (T1M.tapeLength (encodeT1 r).length))
    (hi : (i : Nat) = t1OutputPosition r) :
    (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape i = v :=
  t1CS_run_output_at r v hv i hi

theorem check_t1CS_run_tape_off (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v)
    (i : Fin (T1M.tapeLength (encodeT1 r).length))
    (hi : (i : Nat) ≠ t1OutputPosition r) :
    (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape i =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape i :=
  t1CS_run_tape_off r v hv i hi

theorem check_t1CS_run_head_zero (r : T1Request) :
    ((T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).head : Nat) =
      0 :=
  t1CS_run_head_zero r

theorem check_t1CS_canonical_semantics (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    T1M.accepts (encodeT1 r).length (t1Point (encodeT1 r)) = true ∧
      (∀ i : Fin (T1M.tapeLength (encodeT1 r).length),
        (i : Nat) = t1OutputPosition r →
          (T1M.run (n := (encodeT1 r).length)
            (t1Point (encodeT1 r))).tape i = v) ∧
      (∀ i : Fin (T1M.tapeLength (encodeT1 r).length),
        (i : Nat) ≠ t1OutputPosition r →
          (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape i =
            (T1M.initialConfig (t1Point (encodeT1 r))).tape i) :=
  t1CS_canonical_semantics r v hv

end Pnp3.Tests.TMTrueUniformSeekSemanticsSurface
