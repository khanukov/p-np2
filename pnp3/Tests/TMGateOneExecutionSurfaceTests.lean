import Complexity.TMVerifier.TuringToolkit.GateOneExamples

/-!
# G1 one-gate interpreter, execution layer: surface tests

Import-side type probes for the T2a execution surface: exact
`TM.runConfig` validation of the canonical grammar from the real initial
configuration, the exact reverse scan, the `readBStart` handoff capstone, the
matching exact rejection of a noncanonical encoded request, and the named
per-tag examples.

Every theorem pinned here is scoped to `encodeG1 r`; no execution claim is made
for arbitrary padded physical tapes.

This is an audit surface: it pins public signatures, it does not prove
anything new.
-/

namespace Pnp3.Tests.TMGateOneExecutionSurface

open Pnp3.Internal.PsubsetPpoly.TM

-- Exact execution: validation, rewind, and the capstone.
#check @g1M_tapeLength
#check @g1_lt_tapeLength
#check @g1AlignedConfig
#check @g1AlignedConfigQ
#check @g1CS_aligned_step_left
#check @g1CS_aligned_step_right
#check @g1CS_aligned_step_stay
#check @g1ValidationFrames
#check @g1ValidationPath
#check @g1ValidationAdvance
#check @g1ValidationAdvance_reject_of_not_canonical
#check @g1CanonicalEncoderAutomatonTrace
#check @g1FrameScanner_encode_iff_canonical
#check @g1ListTape_validation_eq_initial
#check @g1CS_validate_encoded_exact
#check @g1CS_rewind_tail
#check @g1ReadBHandoffSteps
#check @g1ReadBHandoffSteps_le_clock
#check @g1CS_validate_rewind_readB_exact
#check @g1CS_readB_head
#check @g1CS_readB_state
#check @g1CS_readB_tape

-- Exact rejection of a noncanonical encoded request.
#check @g1CS_runConfig_reject_sink
#check @g1CS_scan_reject
#check @g1CS_validate_noncanonical_reject_exact
#check @g1CS_noncanonical_ne_readB

-- Named examples.
#check @G1Examples.capstone_input
#check @G1Examples.capstone_const
#check @G1Examples.capstone_not
#check @G1Examples.capstone_and
#check @G1Examples.capstone_or
#check @G1Examples.capstone_and_steps
#check @G1Examples.capstone_and_clock
#check @G1Examples.reject_zero_tags
#check @G1Examples.reject_six_tags
#check @G1Examples.reject_unused_field
#check @G1Examples.reject_const_convention
#check @G1Examples.automaton_reject_zero_tags
#check @G1Examples.automaton_reject_six_tags
#check @G1Examples.machine_reject_constBig
#check @G1Examples.machine_reject_notUnused
#check @G1Examples.machine_reject_inputUnused
#check @G1Examples.machine_reject_constUnused
#check @G1Examples.machine_no_handoff_constBig
#check @G1Examples.machine_no_handoff_notUnused
#check @G1Examples.machine_no_handoff_inputUnused
#check @G1Examples.machine_no_handoff_constUnused
#check @G1Examples.automaton_accepts_reqAnd
#check @G1Examples.automaton_rejects_reqNotUnused
#check @G1Examples.parser_rejects_reqNotUnused

end Pnp3.Tests.TMGateOneExecutionSurface
