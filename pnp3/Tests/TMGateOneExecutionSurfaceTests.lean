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
#check @g1AlignedFrame_eq
#check @g1CS_aligned_step_left
#check @g1CS_aligned_step_right
#check @g1CS_aligned_step_stay
#check @g1ValidationFrames
#check @g1ValidationFrames_length
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
#check @g1CS_readB_phase
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
#check @G1Examples.reject_reserved_code
#check @G1Examples.reject_ragged_word
#check @G1Examples.reject_missing_argSep
#check @G1Examples.reject_missing_finish
#check @G1Examples.reject_trailing_frame
#check @G1Examples.reject_internal_marker
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

/-! ## Exact theorem-contract pins -/

theorem check_g1CS_validate_encoded_exact (r : G1Request) (hc : r.Canonical) :
    let n := (encodeG1 r).length
    G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r))) (n + 4) =
      g1AlignedConfig n (n + 4) (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape .rewindStart :=
  g1CS_validate_encoded_exact r hc

theorem check_g1ReadBHandoffSteps_le_clock (r : G1Request) :
    g1ReadBHandoffSteps r ≤ g1Clock (encodeG1 r).length :=
  g1ReadBHandoffSteps_le_clock r

theorem check_g1CS_validate_rewind_readB_exact (r : G1Request)
    (hc : r.Canonical) :
    let n := (encodeG1 r).length
    G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r) =
      g1AlignedConfig n 0 (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readBStart .p0 false false false g1Ctx0 :=
  g1CS_validate_rewind_readB_exact r hc

theorem check_g1CS_readB_head (r : G1Request) (hc : r.Canonical) :
    ((G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)).head : Nat) = 0 :=
  g1CS_readB_head r hc

theorem check_g1CS_readB_phase (r : G1Request) (hc : r.Canonical) :
    (G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)).state.fst = g1CS.toPhased.startPhase :=
  g1CS_readB_phase r hc

theorem check_g1CS_readB_state (r : G1Request) (hc : r.Canonical) :
    (G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)).state.snd =
      g1State .readBStart .p0 false false false g1Ctx0 :=
  g1CS_readB_state r hc

theorem check_g1CS_readB_tape (r : G1Request) (hc : r.Canonical) :
    (G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1CS_readB_tape r hc

theorem check_g1CS_validate_noncanonical_reject_exact (r : G1Request)
    (hc : ¬ r.Canonical) :
    (G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).state.snd = g1RejectState ∧
      (G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).tape =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1CS_validate_noncanonical_reject_exact r hc

theorem check_g1CS_noncanonical_ne_readB (r : G1Request)
    (hc : ¬ r.Canonical) (ctx : G1Ctx) :
    (G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).state.snd ≠ g1ReadBState ctx :=
  g1CS_noncanonical_ne_readB r hc ctx

theorem check_capstone_input :
    G1M.runConfig
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqInput)))
        (g1ReadBHandoffSteps G1Examples.reqInput) =
      g1AlignedConfig (encodeG1 G1Examples.reqInput).length 0
        (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqInput))).tape
        .readBStart .p0 false false false g1Ctx0 :=
  G1Examples.capstone_input

theorem check_capstone_const :
    G1M.runConfig
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqConst)))
        (g1ReadBHandoffSteps G1Examples.reqConst) =
      g1AlignedConfig (encodeG1 G1Examples.reqConst).length 0
        (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqConst))).tape
        .readBStart .p0 false false false g1Ctx0 :=
  G1Examples.capstone_const

theorem check_capstone_not :
    G1M.runConfig
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqNot)))
        (g1ReadBHandoffSteps G1Examples.reqNot) =
      g1AlignedConfig (encodeG1 G1Examples.reqNot).length 0
        (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqNot))).tape
        .readBStart .p0 false false false g1Ctx0 :=
  G1Examples.capstone_not

theorem check_capstone_and :
    G1M.runConfig
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqAnd)))
        (g1ReadBHandoffSteps G1Examples.reqAnd) =
      g1AlignedConfig (encodeG1 G1Examples.reqAnd).length 0
        (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqAnd))).tape
        .readBStart .p0 false false false g1Ctx0 :=
  G1Examples.capstone_and

theorem check_capstone_or :
    G1M.runConfig
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqOr)))
        (g1ReadBHandoffSteps G1Examples.reqOr) =
      g1AlignedConfig (encodeG1 G1Examples.reqOr).length 0
        (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 G1Examples.reqOr))).tape
        .readBStart .p0 false false false g1Ctx0 :=
  G1Examples.capstone_or

end Pnp3.Tests.TMGateOneExecutionSurface
