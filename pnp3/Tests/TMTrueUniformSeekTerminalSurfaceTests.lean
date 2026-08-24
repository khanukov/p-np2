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
#check @t1OutputFrames_false
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

end Pnp3.Tests.TMTrueUniformSeekTerminalSurface
