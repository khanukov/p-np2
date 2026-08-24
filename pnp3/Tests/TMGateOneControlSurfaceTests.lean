import Complexity.TMVerifier.TuringToolkit.GateOneScanner

/-!
# G1 one-gate interpreter, fixed control layer: surface tests

Import-side type probes for the T2a control surface: the one fixed
zero-parameter program, the frame-level language its forward table decides,
the proved correspondence between that language and the pure parser, the named
noncanonical-rejection witnesses, and the program as a genuine instance of the
generic frame-scanner kernel.

Everything here is at frame-word level or at the level of the transition
tuple lemmas.  The exact `TM.runConfig` validation/rewind execution capstone is
a separate layer with its own surface file.

This is an audit surface: it pins public signatures, it does not prove
anything new.
-/

namespace Pnp3.Tests.TMGateOneControlSurface

open Pnp3.Internal.PsubsetPpoly.TM

-- The one fixed zero-parameter machine.
#check @G1State
#check @G1Mode
#check @G1FramePosition
#check @G1Ctx
#check @g1Ctx0
#check @g1State
#check @g1AcceptState
#check @g1RejectState
#check @g1ReadBState
#check @g1Clock
#check @g1CS
#check @g1CS_runTime
#check @g1Transition
#check @g1Transition_forward_p0
#check @g1Transition_forward_p1
#check @g1Transition_forward_p2
#check @g1Transition_forward_p3_advance
#check @g1Transition_forward_p3_reject
#check @g1Transition_rewindStart
#check @g1Transition_rewind_p3
#check @g1Transition_rewind_p2
#check @g1Transition_rewind_p1
#check @g1Transition_rewind_p0_bof
#check @g1Transition_rewind_p0_other
#check @g1Transition_readBStart_idle
#check @g1RejectState_ne_readB

-- The frame-level language of the fixed forward control.
#check @g1Advance
#check @g1Complete
#check @G1ForwardMode
#check @g1AdvanceList
#check @g1AdvanceList_append
#check @G1ValidPath
#check @G1RejectPath
#check @g1ValidPath_of_accepts
#check @g1AdvanceList_encode
#check @g1AdvanceList_encode_reject
#check @g1RejectPath_encode
#check @encodeG1Frames_blank_shape
#check @g1_structure_of_accepts
#check @g1Automaton_accepts_iff_decode
#check @g1CanonicalEncoderAutomatonTrace_iff

-- Named rejection witnesses: wrong tag counts, the `const` operand
-- convention, and the unused operand-2 field of every arity-1 tag.
#check @g1_reject_tagRun_zero
#check @g1_reject_tagRun_six
#check @g1_reject_const_arg1_ge_two
#check @g1_reject_unusedField_input
#check @g1_reject_unusedField_not
#check @g1_reject_unusedField_const
#check @g1_rejectPath_vArg2Zero
#check @g1_rejectPath_vArg1Unary
#check @g1_rejectPath_vConst0_arg1
#check @g1_rejectPath_vConst0_arg2

-- The generic frame-scanner kernel, instantiated at G1.
#check @G1M
#check @g1FrameCodec
#check @g1FrameScanner
#check @g1FrameScanner_frameMacrostep
#check @g1FrameScanner_scanFrames
#check @g1FrameScanner_advanceList
#check @g1FrameScanner_validPath
#check @g1FrameScanner_accepts_iff_decode

end Pnp3.Tests.TMGateOneControlSurface
