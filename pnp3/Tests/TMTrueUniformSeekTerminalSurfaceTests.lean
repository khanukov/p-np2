import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalExamples

/-!
# T1c-2 terminal execution surfaces

Pins exact restored tape vocabulary, shared repair execution, terminal clocks,
three sink-reaching cases and concrete probes.  Public-clock composition and
`TM.accepts` semantics remain T1c-3.
-/

namespace Pnp3.Tests.TMTrueUniformSeekTerminalSurface

open Pnp3.Internal.PsubsetPpoly.TM

#check @t1OutputFrames
#check @t1SpentFrames
#check @t1OutputBase
#check @t1OutputPosition_eq
#check @t1OutputPosition_safe
#check @t1OutputFrames_false
#check @t1OutputFrames_length
#check @t1tOutputBase_safe
#check @t1tOutputEntry_safe
#check @t1OutputFrames_count_spent
#check @t1OutputFrames_count_index
#check @t1CS_success_final_tape_eq
#check @t1CS_success_final_tape_off
#check @t1CS_success_final_tape_at
#check @t1CS_oob_final_tape_eq
#check @t1CS_repair_scan_skip
#check @t1CS_repair_cycle
#check @t1CS_repair_spent_run
#check @t1RepairSteps
#check @t1CS_repair_pass_exact
#check @t1OutputSteps
#check @t1CS_output_write_exact
#check @t1SuccessTerminalSteps
#check @t1OobTerminalSteps
#check @t1TerminalSteps
#check @t1TerminalSteps_some
#check @t1TerminalSteps_none
#check @t1CS_terminal_success_exact
#check @t1CS_terminal_oob_exact
#check @t1CS_terminal_oob_empty_exact

#check @t1c2SuccessTerminal
#check @t1c2SuccessOutputAt
#check @t1c2OobTerminal
#check @t1c2EmptyTerminal

/-! ## Exact theorem-contract pins -/

theorem check_t1CS_success_final_tape_eq (r : T1Request) (v : Bool) :
    t1ListTape (n := (encodeT1 r).length)
        ((t1OutputFrames r v).flatMap T1Frame.bits) =
      t1WriteCell (t1OutputPosition r) v
        (T1M.initialConfig (t1Point (encodeT1 r))).tape :=
  t1CS_success_final_tape_eq r v

theorem check_t1CS_terminal_success_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    T1M.runConfig
        (t1AlignedConfig (encodeT1 r).length 0
          (t1_lt_tapeLength _ _ (Nat.zero_le _))
          (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
          .successStart .p0 false false false v)
        (t1SuccessTerminalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r v).flatMap T1Frame.bits))
        .accept .p0 false false false false :=
  t1CS_terminal_success_exact r v hv

theorem check_t1CS_terminal_oob_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = none) (hne : 0 < r.data.length) :
    T1M.runConfig
        (t1AlignedConfig (encodeT1 r).length
          (4 * (r.index + (r.data.length - 1) + 3) + 3) (t1dOobHead_safe r)
          (t1ListTape
            ((t1LoopFramesRestored r (r.data.length - 1)).flatMap
              T1Frame.bits))
          .oobStart .p0 false false false v)
        (t1OobTerminalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r false).flatMap T1Frame.bits))
        .reject .p0 false false false false :=
  t1CS_terminal_oob_exact r v hv hne

theorem check_t1CS_terminal_oob_empty_exact (r : T1Request)
    (hdata : r.data = []) :
    T1M.runConfig
        (t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3)
          (t1dEmptyOobHead_safe r)
          (T1M.initialConfig (t1Point (encodeT1 r))).tape .oobStart .p0
          false false false false)
        (t1OobTerminalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .reject .p0 false false false false :=
  t1CS_terminal_oob_empty_exact r hdata

end Pnp3.Tests.TMTrueUniformSeekTerminalSurface
