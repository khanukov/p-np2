import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemanticsExamples

/-!
# T1c-3 canonical-semantics surfaces

Pins the total honest clock, the three exact compositions from the genuine
`T1M.initialConfig`, the merged reject arm, the public-clock bound, the two
full `T1M.run` theorems, full `TM.accepts` correctness, output-cell/tape
conservation, and the four concrete probes.

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

-- Concrete probes: true bit, false bit (still accepts), OOB, empty OOB.
#check @t1c3TrueRun
#check @t1c3TrueOutput
#check @t1c3TrueAccepts
#check @t1c3FalseRun
#check @t1c3FalseOutput
#check @t1c3FalseAccepts
#check @t1c3OobRun
#check @t1c3OobTapePreserved
#check @t1c3OobRejects
#check @t1c3EmptyRun
#check @t1c3EmptyTapePreserved
#check @t1c3EmptyRejects
#check @t1c3TrueClockFits
#check @t1c3OobClockFits
#check @t1c3EmptyClockFits

end Pnp3.Tests.TMTrueUniformSeekSemanticsSurface
