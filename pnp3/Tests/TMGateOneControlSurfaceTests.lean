import Complexity.TMVerifier.TuringToolkit.GateOneScanner

/-!
# G1 one-gate interpreter, fixed control layer: surface tests

Import-side type probes for the T2a control surface: the one fixed
zero-parameter program, the frame-level language its forward table decides,
the proved correspondence between that language and the pure parser, the named
noncanonical-rejection witnesses, and the program as a genuine instance of the
generic frame-scanner kernel.

This layer exposes frame-word/table correspondence and the generic kernel's
exact four-step and multi-frame `TM.runConfig` primitives.  End-to-end physical
validation, rejection, rewind, and `readBStart` composition are deferred.

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
#check @G1ForwardMode.not_reject
#check @G1ForwardMode.not_rewindStart
#check @g1AdvanceList
#check @g1AdvanceList_append
#check @G1ValidPath
#check @G1RejectPath
#check @G1RejectPath.forward
#check @g1ValidPath_of_accepts
#check @g1AdvanceList_encode
#check @g1AdvanceList_encode_reject
#check @g1RejectPath_encode
#check @encodeG1Frames_blank_shape
#check @g1_structure_of_accepts
#check @g1Automaton_accepts_iff_decode
#check @g1CanonicalEncoderAutomatonTrace_iff
#check @g1_example_control_and_accepts
#check @g1_example_control_const_rejects

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
#check @g1FrameScanner_codec
#check @g1FrameScanner_frameMacrostep
#check @g1FrameScanner_scanFrames
#check @g1FrameScanner_advanceList
#check @g1FrameScanner_validPath
#check @g1FrameScanner_frameLanguage_iff_decode

/-! ## Exact theorem-contract pins -/

theorem check_g1CS_runTime (N : Nat) :
    g1CS.toPhased.toTM.runTime N = 512 * (N + 1) ^ 2 + 512 :=
  g1CS_runTime N

theorem check_g1AdvanceList_encode_reject (r : G1Request)
    (hc : ¬ r.Canonical) :
    g1AdvanceList .vBof (encodeG1Frames r ++ [.blank]) = .reject :=
  g1AdvanceList_encode_reject r hc

theorem check_g1_reject_tagRun_zero (rest : List G1Frame) :
    g1AdvanceList .vBof (.bof :: .argSep :: rest) = .reject :=
  g1_reject_tagRun_zero rest

theorem check_g1_reject_tagRun_six (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .tag :: .tag :: .tag :: .tag :: rest) =
      .reject :=
  g1_reject_tagRun_six rest

theorem check_g1_reject_const_arg1_ge_two (a1 : Nat) (h : 2 ≤ a1)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .argSep ::
          (List.replicate a1 .index ++ rest)) = .reject :=
  g1_reject_const_arg1_ge_two a1 h rest

theorem check_g1_reject_unusedField_input (a1 a2 : Nat) (h : a2 ≠ 0)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1_reject_unusedField_input a1 a2 h rest

theorem check_g1_reject_unusedField_not (a1 a2 : Nat) (h : a2 ≠ 0)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1_reject_unusedField_not a1 a2 h rest

theorem check_g1_reject_unusedField_const (a1 a2 : Nat) (h1 : a1 ≤ 1)
    (h2 : a2 ≠ 0) (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1_reject_unusedField_const a1 a2 h1 h2 rest

theorem check_g1Automaton_accepts_iff_decode (fs : List G1Frame) :
    g1AdvanceList .vBof (fs ++ [.blank]) = .rewindStart ↔
      ∃ r : G1Request, decodeG1FrameList? fs = some r :=
  g1Automaton_accepts_iff_decode fs

theorem check_g1CanonicalEncoderAutomatonTrace_iff (r : G1Request) :
    g1AdvanceList .vBof (encodeG1Frames r ++ [.blank]) = .rewindStart ↔
      r.Canonical :=
  g1CanonicalEncoderAutomatonTrace_iff r

theorem check_g1FrameScanner_frameLanguage_iff_decode (fs : List G1Frame) :
    g1FrameScanner.advanceList .vBof (fs ++ [.blank]) = .rewindStart ↔
      ∃ r : G1Request, decodeG1FrameList? fs = some r :=
  g1FrameScanner_frameLanguage_iff_decode fs

theorem check_g1FrameScanner_frameMacrostep (n h : Nat)
    (hsafe : h + 4 < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (mode : G1Mode) (frame : G1Frame) (ctx : G1Ctx)
    (hmode : G1ForwardMode mode) (hnext : g1Advance mode frame ≠ .reject)
    (hbits : FrameScan.physicalBitsAt hsafe tape = frame.bits) :
    G1M.runConfig
        (g1FrameScanner.alignedFrame n h
          (by rw [g1FrameScanner_machine]; omega) tape mode ctx) 4 =
      g1FrameScanner.alignedFrame n (h + 4) hsafe tape
        (g1Advance mode frame) ctx :=
  g1FrameScanner_frameMacrostep n h hsafe tape mode frame ctx hmode hnext hbits

theorem check_g1FrameScanner_scanFrames (n : Nat)
    (pre frames suffix : List G1Frame) (mode : G1Mode) (ctx : G1Ctx)
    (hpath : g1FrameScanner.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < G1M.tapeLength n) :
    G1M.runConfig
        (g1FrameScanner.alignedFrame n (4 * pre.length)
          (by rw [g1FrameScanner_machine]; omega)
          (FrameScan.frameListTape
            ((pre ++ frames ++ suffix).flatMap G1Frame.bits)) mode ctx)
        (4 * frames.length) =
      g1FrameScanner.alignedFrame n (4 * (pre.length + frames.length)) hsafe
        (FrameScan.frameListTape
          ((pre ++ frames ++ suffix).flatMap G1Frame.bits))
        (g1FrameScanner.advanceList mode frames) ctx :=
  g1FrameScanner_scanFrames n pre frames suffix mode ctx hpath hsafe

end Pnp3.Tests.TMGateOneControlSurface
