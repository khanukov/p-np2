import Magnification.FinalResult
import Magnification.AC0AtlasBridge
import Magnification.AC0ApproxFamilyBridge
import LowerBounds.ApproxClassContradiction
import LowerBounds.ApproxClassNoGo
import LowerBounds.SingletonProvenanceEndpoint
import LowerBounds.SingletonDensityEndpoint
import LowerBounds.SingletonDensityContradiction
import LowerBounds.DAGStableRestrictionProducer
import LowerBounds.AC0_GapMCSP
import Tests.BridgeLocalityRegression
import Tests.PromiseRouteConclusionProbe
import ThirdPartyFacts.Facts_Switching
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRunExamples
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridgeExamples
import Complexity.TMVerifier.TuringToolkit.FrameScannerProbe
import Complexity.TMVerifier.TuringToolkit.FrameScannerT1
import Complexity.TMVerifier.TuringToolkit.FrameScannerReverseProbe
import Complexity.TMVerifier.TuringToolkit.FrameScannerReverseInstances
import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleProbe
import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleInstances
import Complexity.TMVerifier.TuringToolkit.GateOneExamples
import Complexity.TMVerifier.TuringToolkit.GateOneRouting
import Complexity.TMVerifier.TuringToolkit.GateOneReadBExamples
import Complexity.TMVerifier.TuringToolkit.GateOneInstallScanExamples
import Complexity.TMVerifier.TuringToolkit.GateOneProbeInstallExamples
import Complexity.TMVerifier.TuringToolkit.GateOneWalkExamples
import Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariantExamples
import Complexity.TMVerifier.TuringToolkit.GateOneWalkDriverExamples
import Complexity.TMVerifier.TuringToolkit.GateOneIndexRound
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqListRunExamples
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAccept
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAcceptExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoopExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriverExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemanticsExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalControl

/-!
  pnp3/Tests/AxiomsAudit.lean

  Тест-аудит: выводим список аксиом, от которых зависят ключевые теоремы.
  Этот файл компилируется вместе с проектом, чтобы случайные зависимости
  (например, от неожиданных внешних аксиом) были заметны сразу.
-/

open Pnp3
open Pnp3.ComplexityInterfaces
open Pnp3.Magnification

-- Reusable sequential-TM infrastructure (W-A).
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_boundary_step_eq_embedSeqP2Config_lift
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_run_full
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.RunSpec.seq
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.RunSpec.final_state_eq_accept_iff
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.RunSpec.accepts_eq_decide_local
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_numPhases
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_timeBound
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_startPhase_val
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_startState
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_acceptPhase_val
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_acceptState
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_terminal_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.castAcceptIfCellConfig_state
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.castAcceptIfCellConfig_head
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.castAcceptIfCellConfig_tape
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.castAcceptIfCellConfig_stepConfig
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.castAcceptIfCellConfig_runConfig
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_run_full
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_runConfig_stabilizes
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_run_state_eq_accept_iff
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_runSpec
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_initial_flag_eq
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.acceptIfCellCS_accepts_iff_input_or_blank_flag
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.RunSpec.seqList_singleton
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_seqList_singleton_runSpec
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_seq_run_full
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.RunSpec.imp
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.liftP1ToSeq_eq_embedSeqConfig_lift
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.RunSpec.seqList_singleton_exact
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.RunSpec.seqList_cons
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.ReadyStep
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.RunSpec.seqList_of_forall
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_tapeLength_mono
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_seqList_two_runSpec
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_seqList_two_run_full
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_seqList_three_recursion_probe
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCSReady
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_seqList_replicate_runSpec
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.initialConfig_seq_eq_embedSeqConfig_initialConfig
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_timeBound_eq_acceptIfCellCS_timeBound
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstThenAcceptIfCS_timeBound
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstThenAcceptIfCS_runSpec
#print axioms Internal.PsubsetPpoly.TM.GateEvalCS.gateConstThenAcceptIfCS_accepts

-- Generic `ConstStatePhasedProgram` transition → `stepConfig` step bridge
-- (`TuringToolkit/ConstStatePhasedStepBridge.lean`), its five move
-- corollaries, the generic `Foundation` lemmas they use that are new in this
-- increment (componentwise `Configuration` extensionality, plus the
-- `Move.left` clamp lemma that only `stepConfig_eq_of_transition_left_clamped`
-- rests on), and the one-phase concrete probes.  Machine-independent
-- infrastructure: no acceptance, runtime, or verifier claim.
#print axioms Internal.PsubsetPpoly.TM.Configuration.ext_of_components
#print axioms Internal.PsubsetPpoly.TM.Configuration.moveHead_left_clamp
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.toTM_step_of_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.toTM_step_config_of_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_state_of_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_head_of_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_tape_of_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_tape_apply_of_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_of_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_eq_of_transition_right
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_eq_of_transition_right_clamped
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_eq_of_transition_left
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_eq_of_transition_left_clamped
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepConfig_eq_of_transition_stay
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeCS_transition_true
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeCS_transition_false
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeCS_step_right
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeCS_step_right_clamped
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeCS_step_left
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeCS_step_left_clamped
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeCS_stepConfig_true
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeStayCS_transition
#print axioms Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.stepBridgeProbeStayCS_step_stay

-- Generic four-bit frame-scanner execution kernel, a non-T1 probe and the T1
-- regression instantiation.  This is execution infrastructure, not a scanner
-- correctness provider or a verifier claim.
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameCodec.bits_injective
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameCodec.bits_eq_four
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameCodec.flatMap_bits_length
#print axioms Internal.PsubsetPpoly.TM.FrameScan.writeCell_self
#print axioms Internal.PsubsetPpoly.TM.FrameScan.physicalBitsAt_flatMap
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.alignedStepRight
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.alignedStepLeft
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.alignedStepStay
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.complete_of_bits
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.frameMacrostep
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.advanceList_eq_foldl
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.advanceList_append
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.scanFrames
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.scanFrames_tape
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.scanFrames_state
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameScanner.scanFrames_head
#print axioms Internal.PsubsetPpoly.TM.FrameScan.probeCS_frame_macrostep
#print axioms Internal.PsubsetPpoly.TM.FrameScan.probeCS_scan_frames
#print axioms Internal.PsubsetPpoly.TM.FrameScan.probeWord_validPath
#print axioms Internal.PsubsetPpoly.TM.FrameScan.probeCS_runTime
#print axioms Internal.PsubsetPpoly.TM.FrameScan.probeCS_scan_probeWord
#print axioms Internal.PsubsetPpoly.TM.FrameScan.probeCS_scan_probeWord_one
#print axioms Internal.PsubsetPpoly.TM.t1FrameCodec_bits
#print axioms Internal.PsubsetPpoly.TM.t1FrameCodec_decode
#print axioms Internal.PsubsetPpoly.TM.t1FrameScanner_program
#print axioms Internal.PsubsetPpoly.TM.t1FrameScanner_machine
#print axioms Internal.PsubsetPpoly.TM.t1FrameScanner_phase
#print axioms Internal.PsubsetPpoly.TM.t1FrameScanner_advance
#print axioms Internal.PsubsetPpoly.TM.t1FrameScanner_st0
#print axioms Internal.PsubsetPpoly.TM.t1FrameScanner_frameMacrostep
#print axioms Internal.PsubsetPpoly.TM.t1FrameScanner_scanFrames

-- Generic *reverse* four-bit frame-scanner kernel and the generic four-cell
-- frame write/replacement layer, a genuinely non-T1 probe of both, and the T1
-- and G1 reverse-scan regressions.  Execution infrastructure only: no
-- addressing, acceptance, gate-evaluation or verifier claim.
#print axioms Internal.PsubsetPpoly.TM.FrameScan.Phased.stepLeft
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revFrameMacrostep
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revFrameMacrostepAt
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revAnchorStep
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revValidPath_const
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revScanFrames
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revScanFrames_tape
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revScanFrames_state
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revScanFrames_head
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revScanToAnchor
#print axioms Internal.PsubsetPpoly.TM.FrameScan.writeFrame4_apply
#print axioms Internal.PsubsetPpoly.TM.FrameScan.writeFrame4_frameListTape
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameWriter.writeMacrostep
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameWriter.writeFrameOnList
#print axioms Internal.PsubsetPpoly.TM.FrameScan.revProbeCS_scan_word
#print axioms Internal.PsubsetPpoly.TM.FrameScan.revProbeCS_write_cell
#print axioms Internal.PsubsetPpoly.TM.t1RevScanner_rewind_tail
#print axioms Internal.PsubsetPpoly.TM.g1RevScanner_rewind_tail

-- Mutation half of the same kernel: the leftward writer, the seek-until-marker
-- driver, the exact thirteen-step rewrite cycle composed from them, the non-T1
-- executable probe, and the T1 regressions.  Execution infrastructure only: one
-- frame per cycle, no addressing/runtime-index/acceptance/verifier claim.
-- `G1RewriteCycleObligation` is now inhabited by `g1RewriteCycleObligation`,
-- whose cycle is G1's own `index -> spent` round; still one round only.
#print axioms Internal.PsubsetPpoly.TM.FrameScan.writeFrame4_descending
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameWriter.writeMacrostepLeft
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameWriter.writeFrameOnListLeft
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revSkipRun
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revSeekToMarker
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revSeekToMarker_head
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameRewriteCycle.backWalk
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameRewriteCycle.hopStep
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameRewriteCycle.rewriteCycle
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameRewriteCycle.rewriteCycleOnList
#print axioms Internal.PsubsetPpoly.TM.g1CS_index_round
#print axioms Internal.PsubsetPpoly.TM.g1CS_index_round_onList
#print axioms Internal.PsubsetPpoly.TM.g1RewriteCycleObligation
#print axioms Internal.PsubsetPpoly.TM.G1RewriteCycleObligation.rewrite_cycle
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameRewriteCycle.seekAndRewrite
#print axioms Internal.PsubsetPpoly.TM.FrameScan.cycProbeCS_rewrite_cycle
#print axioms Internal.PsubsetPpoly.TM.FrameScan.cycProbeCS_seek_rewrite
#print axioms Internal.PsubsetPpoly.TM.FrameScan.cycProbeCS_seek_marker
#print axioms Internal.PsubsetPpoly.TM.FrameScan.cycProbeCS_write_left
#print axioms Internal.PsubsetPpoly.TM.t1RepairCycle_repair_cycle
#print axioms Internal.PsubsetPpoly.TM.t1RepairCycle_repair_cycle_onList
#print axioms Internal.PsubsetPpoly.TM.t1OutWriter_outWriteOut_frame
#print axioms Internal.PsubsetPpoly.TM.g1RevScanner_seek_bof
#print axioms Internal.PsubsetPpoly.TM.G1RewriteCycleObligation.machine_eq

-- T2a, pure layer: the fresh unary one-gate ABI, its exact parser
-- characterisation, and the pure gate semantics.  These are parser/spec
-- surfaces only: no machine, no execution, no acceptance, no
-- gate-evaluation or verifier claim.
#print axioms Internal.PsubsetPpoly.TM.decodeG1Frame_bits
#print axioms Internal.PsubsetPpoly.TM.decodeG1Frame_reserved
#print axioms Internal.PsubsetPpoly.TM.g1FrameCodec_bits
#print axioms Internal.PsubsetPpoly.TM.g1FrameCodec_decode
#print axioms Internal.PsubsetPpoly.TM.G1Frame.bits_argSep
#print axioms Internal.PsubsetPpoly.TM.encodeG1_length
#print axioms Internal.PsubsetPpoly.TM.encodeG1Frames_injective
#print axioms Internal.PsubsetPpoly.TM.encodeG1_injective
#print axioms Internal.PsubsetPpoly.TM.decodeG1Tape_encode
#print axioms Internal.PsubsetPpoly.TM.decodeG1Tape?_eq_some
#print axioms Internal.PsubsetPpoly.TM.decodeG1Tape?_iff
#print axioms Internal.PsubsetPpoly.TM.decodeG1Tape?_encode_not_canonical
#print axioms Internal.PsubsetPpoly.TM.g1_example_tape_roundtrip
#print axioms Internal.PsubsetPpoly.TM.decodeG1FrameList?_reject_tagRun
#print axioms Internal.PsubsetPpoly.TM.encodeG1_getElem?_outputPosition
#print axioms Internal.PsubsetPpoly.TM.G1Request.spec_and_of
#print axioms Internal.PsubsetPpoly.TM.G1Request.spec_or_of
#print axioms Internal.PsubsetPpoly.TM.G1Request.spec_and_oob
#print axioms Internal.PsubsetPpoly.TM.G1Request.spec_or_oob
#print axioms Internal.PsubsetPpoly.TM.G1Request.spec_eq_none_of_not_canonical
#print axioms Internal.PsubsetPpoly.TM.G1Request.getElem?_isSome_iff
#print axioms Internal.PsubsetPpoly.TM.G1Request.spec_isSome_iff
#print axioms Internal.PsubsetPpoly.TM.G1Request.g1_example_canonical_oob_not_wellFormed

-- T2a, control layer: the frame-level correspondence between the fixed
-- forward control and the pure parser -- the machine language *is* the
-- canonical grammar -- and the same control as an instance of the generic
-- frame-scanner kernel.  Generic frame execution primitives are present; the
-- end-to-end validation/rewind roots are audited in the next block.
#print axioms Internal.PsubsetPpoly.TM.g1CS_runTime
#print axioms Internal.PsubsetPpoly.TM.g1CS_numPhases
#print axioms Internal.PsubsetPpoly.TM.g1Transition_forward_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_forward_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_forward_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_forward_p3_advance
#print axioms Internal.PsubsetPpoly.TM.g1Transition_forward_p3_reject
#print axioms Internal.PsubsetPpoly.TM.g1Transition_rewindStart
#print axioms Internal.PsubsetPpoly.TM.g1Transition_rewind_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_rewind_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_rewind_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_rewind_p0_bof
#print axioms Internal.PsubsetPpoly.TM.g1Transition_rewind_p0_other
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAStart_idle
#print axioms Internal.PsubsetPpoly.TM.g1Transition_combineStart_idle
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAResetStart_idle
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRoundStart_bridge
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bLatch
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bIns_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bIns_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bIns_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bIns_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bWalk_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bWalk_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bWalk_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bWalk_p0_index
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bWalk_p0_other
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bMark_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bMark_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bMark_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bMark_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bBack_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bBack_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bBack_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bBack_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bHop
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bOOB_stable
#print axioms Internal.PsubsetPpoly.TM.g1Transition_constLit
#print axioms Internal.PsubsetPpoly.TM.g1Transition_store
#print axioms Internal.PsubsetPpoly.TM.g1RejectState_ne_readB
#print axioms Internal.PsubsetPpoly.TM.g1AdvanceList_append
#print axioms Internal.PsubsetPpoly.TM.G1ForwardMode.not_reject
#print axioms Internal.PsubsetPpoly.TM.G1ForwardMode.not_rewindStart
#print axioms Internal.PsubsetPpoly.TM.G1RejectPath.forward
#print axioms Internal.PsubsetPpoly.TM.g1AdvanceList_encode
#print axioms Internal.PsubsetPpoly.TM.g1AdvanceList_encode_reject
#print axioms Internal.PsubsetPpoly.TM.g1RejectPath_encode
#print axioms Internal.PsubsetPpoly.TM.g1_structure_of_accepts
#print axioms Internal.PsubsetPpoly.TM.g1ValidPath_of_accepts
#print axioms Internal.PsubsetPpoly.TM.g1Automaton_accepts_iff_decode
#print axioms Internal.PsubsetPpoly.TM.g1CanonicalEncoderAutomatonTrace_iff
#print axioms Internal.PsubsetPpoly.TM.g1_example_control_and_accepts
#print axioms Internal.PsubsetPpoly.TM.g1_example_control_const_rejects
#print axioms Internal.PsubsetPpoly.TM.g1_reject_tagRun_zero
#print axioms Internal.PsubsetPpoly.TM.g1_reject_tagRun_six
#print axioms Internal.PsubsetPpoly.TM.g1_reject_const_arg1_ge_two
#print axioms Internal.PsubsetPpoly.TM.g1_reject_unusedField_input
#print axioms Internal.PsubsetPpoly.TM.g1_reject_unusedField_not
#print axioms Internal.PsubsetPpoly.TM.g1_reject_unusedField_const
#print axioms Internal.PsubsetPpoly.TM.g1FrameScanner_codec
#print axioms Internal.PsubsetPpoly.TM.g1FrameScanner_frameMacrostep
#print axioms Internal.PsubsetPpoly.TM.g1FrameScanner_scanFrames
#print axioms Internal.PsubsetPpoly.TM.g1FrameScanner_frameLanguage_iff_decode

-- T2a, execution layer: the exact validation/rewind capstone from the real
-- initial configuration, and the matching exact rejection of a noncanonical
-- encoded request over the same fixed validation prefix.  Still no operand
-- read, no acceptance, no gate-evaluation or verifier claim.
#print axioms Internal.PsubsetPpoly.TM.g1CanonicalEncoderAutomatonTrace
#print axioms Internal.PsubsetPpoly.TM.g1AlignedFrame_eq
#print axioms Internal.PsubsetPpoly.TM.g1ValidationFrames_length
#print axioms Internal.PsubsetPpoly.TM.g1ValidationAdvance_reject_of_not_canonical
#print axioms Internal.PsubsetPpoly.TM.g1FrameScanner_encode_iff_canonical
#print axioms Internal.PsubsetPpoly.TM.g1CS_validate_encoded_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_rewind_tail
#print axioms Internal.PsubsetPpoly.TM.g1ReadBHandoffSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_validate_rewind_readB_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_phase
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_runConfig_reject_sink
#print axioms Internal.PsubsetPpoly.TM.g1CS_scan_reject
#print axioms Internal.PsubsetPpoly.TM.g1CS_validate_noncanonical_reject_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_noncanonical_ne_readB
#print axioms Internal.PsubsetPpoly.TM.G1Examples.capstone_input
#print axioms Internal.PsubsetPpoly.TM.G1Examples.capstone_const
#print axioms Internal.PsubsetPpoly.TM.G1Examples.capstone_not
#print axioms Internal.PsubsetPpoly.TM.G1Examples.capstone_and
#print axioms Internal.PsubsetPpoly.TM.G1Examples.capstone_or
#print axioms Internal.PsubsetPpoly.TM.G1Examples.reject_reserved_code
#print axioms Internal.PsubsetPpoly.TM.G1Examples.reject_ragged_word
#print axioms Internal.PsubsetPpoly.TM.G1Examples.reject_missing_argSep
#print axioms Internal.PsubsetPpoly.TM.G1Examples.reject_missing_finish
#print axioms Internal.PsubsetPpoly.TM.G1Examples.reject_trailing_frame
#print axioms Internal.PsubsetPpoly.TM.G1Examples.reject_internal_marker
#print axioms Internal.PsubsetPpoly.TM.G1Examples.reject_unused_field
#print axioms Internal.PsubsetPpoly.TM.G1Examples.reject_const_convention
#print axioms Internal.PsubsetPpoly.TM.G1Examples.automaton_reject_zero_tags
#print axioms Internal.PsubsetPpoly.TM.G1Examples.automaton_reject_six_tags
#print axioms Internal.PsubsetPpoly.TM.G1Examples.machine_reject_constBig
#print axioms Internal.PsubsetPpoly.TM.G1Examples.machine_reject_notUnused
#print axioms Internal.PsubsetPpoly.TM.G1Examples.machine_reject_inputUnused
#print axioms Internal.PsubsetPpoly.TM.G1Examples.machine_reject_constUnused
#print axioms Internal.PsubsetPpoly.TM.G1Examples.machine_no_handoff_notUnused
#print axioms Internal.PsubsetPpoly.TM.G1Examples.machine_no_handoff_inputUnused
#print axioms Internal.PsubsetPpoly.TM.G1Examples.machine_no_handoff_constUnused
#print axioms Internal.PsubsetPpoly.TM.G1Examples.machine_no_handoff_constBig

-- T2b, pass-B layer: the physical tag rescan and finite-control routing,
-- exact initial-configuration prefixes, the zero-index operand-2 read and its
-- stable out-of-range boundary, and the positive-index **installation route**
-- that the re-pointed `bScan + index` row opens.  Local adapters retain
-- their arbitrary-aligned-tape scope and stability padding has no clock bound.
-- Still no `TM.accepts`, output write, combine step, pass-A read or
-- `spec`-correctness claim, and for `arg2 > 0` no latch, cursor install, round,
-- iteration, addressing or operand-value claim is audited here.
#print axioms Internal.PsubsetPpoly.TM.G1Ctx.withVB_vB
#print axioms Internal.PsubsetPpoly.TM.G1Ctx.withVB_pass
#print axioms Internal.PsubsetPpoly.TM.G1Ctx.withVB_crossed
#print axioms Internal.PsubsetPpoly.TM.G1ForwardMode.readBStart
#print axioms Internal.PsubsetPpoly.TM.g1OOBState_ne_readAReset
#print axioms Internal.PsubsetPpoly.TM.g1Advance_ne_sink
#print axioms Internal.PsubsetPpoly.TM.g1_tagRescan_advance
#print axioms Internal.PsubsetPpoly.TM.g1_tagRescan_validPath
#print axioms Internal.PsubsetPpoly.TM.g1TagRoute_split
#print axioms Internal.PsubsetPpoly.TM.g1FieldRoute_split
#print axioms Internal.PsubsetPpoly.TM.g1ReadBRoute_split
#print axioms Internal.PsubsetPpoly.TM.g1ReadBOOB_split
#print axioms Internal.PsubsetPpoly.TM.g1TagRoute_advance
#print axioms Internal.PsubsetPpoly.TM.g1TagRoute_validPath
#print axioms Internal.PsubsetPpoly.TM.g1TagRoute_advance_unary
#print axioms Internal.PsubsetPpoly.TM.g1FieldRoute_advance_const
#print axioms Internal.PsubsetPpoly.TM.g1FieldRoute_validPath_const
#print axioms Internal.PsubsetPpoly.TM.g1FieldRoute_advance_binary
#print axioms Internal.PsubsetPpoly.TM.g1FieldRoute_validPath_binary
#print axioms Internal.PsubsetPpoly.TM.g1ReadBRoute_advance
#print axioms Internal.PsubsetPpoly.TM.g1ReadBRoute_validPath
#print axioms Internal.PsubsetPpoly.TM.g1ReadBOOB_advance
#print axioms Internal.PsubsetPpoly.TM.g1ReadBOOB_validPath
#print axioms Internal.PsubsetPpoly.TM.g1_bScan_index_install
#print axioms Internal.PsubsetPpoly.TM.g1_insSeek_advance
#print axioms Internal.PsubsetPpoly.TM.g1_insSeek_validPath
#print axioms Internal.PsubsetPpoly.TM.g1_bProbe2_rows
#print axioms Internal.PsubsetPpoly.TM.g1_bFwd_rows
#print axioms Internal.PsubsetPpoly.TM.g1_bRet_rows
#print axioms Internal.PsubsetPpoly.TM.g1_bRoundStart_stuck
#print axioms Internal.PsubsetPpoly.TM.g1_bRoundStart_unreachable
#print axioms Internal.PsubsetPpoly.TM.g1InstallRouteFrames_length
#print axioms Internal.PsubsetPpoly.TM.g1InstallRoute_split
#print axioms Internal.PsubsetPpoly.TM.g1InstallRoute_advance
#print axioms Internal.PsubsetPpoly.TM.g1InstallRoute_validPath

-- T2b, pass-B execution layer: exact `TM.runConfig` statements from the real
-- `G1M.initialConfig (g1Point (encodeG1 r))` for the physical tag rescan and
-- its per-tag dispatch, the `const` literal decode/store, the `arg2 = 0`
-- operand-2 read and its empty-data `bOOB` boundary.  The five initial-config
-- arrival endpoints pin head,
-- state and tape, and their named prefix counts fit `g1Clock`.  Local adapters
-- use arbitrary aligned tapes; `bOOB + k` stability carries no clock bound.
-- Still no `TM.run` or `TM.accepts`, no output write, combine step, pass-A read
-- or `spec`-correctness claim, and no full-clock theorem.  The `arg2 > 0`
-- endpoint is the read-only installation scan audited below.
#print axioms Internal.PsubsetPpoly.TM.g1_route_le
#print axioms Internal.PsubsetPpoly.TM.g1_route_lt_tapeLength
#print axioms Internal.PsubsetPpoly.TM.g1_readB_steps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_scan
#print axioms Internal.PsubsetPpoly.TM.g1CS_runConfig_stable
#print axioms Internal.PsubsetPpoly.TM.g1CS_runConfig_readA_idle
#print axioms Internal.PsubsetPpoly.TM.g1CS_runConfig_combine_idle
#print axioms Internal.PsubsetPpoly.TM.g1CS_runConfig_readAReset_idle
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_round_bridge
#print axioms Internal.PsubsetPpoly.TM.g1CS_runConfig_oob_sink
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_constLit
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_store
#print axioms Internal.PsubsetPpoly.TM.g1ReadARouteSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1FieldRouteSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ConstRouteSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ReadBSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ReadBOOBSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_unary_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_unary_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_unary_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_unary_tape
#print axioms Internal.PsubsetPpoly.TM.g1_const_fields_of_spec
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_const_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_const_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_const_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_binary_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_route_binary_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_phase
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_oob_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_oob_stable
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_oob_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_oob_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_oob_ne_success
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_oob_ne_reject
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_route_input
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_route_not
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_const_false
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_const_true
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_field_route_and
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_field_route_or

-- The installation scan of the positive-index branch.  `g1CS_walk_install_scan` is the
-- forward-scan macro on a caller-supplied frame list;
-- `g1CS_readB_install_scan_exact` is the one statement here that starts from the
-- real initial configuration, and it is a **reachability** endpoint: it latches
-- nothing, installs no cursor, writes no cell and reads no operand-2 value.
-- Its endpoint `bProbe2` is where every real-initial-configuration statement of
-- this development stops; the probe, latch and cursor install behind it are
-- audited below and take the caller's configuration.
#print axioms Internal.PsubsetPpoly.TM.g1Advance_bInsSeek_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1ValidPath_fix
#print axioms Internal.PsubsetPpoly.TM.g1AdvanceList_fix
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_scan
#print axioms Internal.PsubsetPpoly.TM.g1InstallScanSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1InstallScanSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_install_scan_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_install_scan_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_install_scan_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_install_scan_state
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.g1WalkExample_canonical
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.g1WalkExample_length
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.g1WalkExample_initial_tape
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.walk_install_scan_steps
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.walk_install_scan
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.walk_install_scan_head
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.walk_install_scan_state
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.walk_install_scan_tape
#print axioms Internal.PsubsetPpoly.TM.G1InstallScanExamples.walk_install_scan_clock

-- The successor of the installation-scan endpoint: the probe's table fact, the
-- leftward cursor-writer instance, the three exact atomic macros on an
-- **arbitrary** frame list, and their four literal encoded-frame probes.
-- **Every one takes the caller's configuration**: none starts from
-- `G1M.initialConfig`, so no installation driver is audited here.
#print axioms Internal.PsubsetPpoly.TM.g1Advance_bProbe2_data
#print axioms Internal.PsubsetPpoly.TM.g1CursorWriter_machine
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_probe_latch
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_probe_oob
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_cursor
#print axioms Internal.PsubsetPpoly.TM.G1ProbeInstallExamples.probe_latch_false
#print axioms Internal.PsubsetPpoly.TM.G1ProbeInstallExamples.probe_latch_true
#print axioms Internal.PsubsetPpoly.TM.G1ProbeInstallExamples.probe_oob
#print axioms Internal.PsubsetPpoly.TM.G1ProbeInstallExamples.install_cursor

-- PR2b1, one **normal round** of the cursor walk behind `bSeek`: the six new
-- modes, the reverse seek and the merged latch/writer rows, the two generic
-- tape-preserving leftward primitives, the three new frame-kernel instances,
-- the seven exact atomic macros on an **arbitrary** frame list, and their five
-- literal encoded-frame probes.  **Every run takes the caller's
-- configuration**: none starts from `G1M.initialConfig`, so no installation
-- driver is audited, and nothing composes two macros into a round.  The
-- exhaustion outcome stops at `.bExh .p0` — head on the first cell of the
-- opening `argSep`; the terminal path continuing from that shape is audited in
-- the PR2b2 block below, on caller-supplied configurations only.  No walk
-- invariant, iteration, loop clock, out-of-range aggregation, repair,
-- arbitrary-index
-- read, `TM.accepts`, gate-semantics, full-clock or padded-tape statement is
-- audited here, because none exists.
#print axioms Internal.PsubsetPpoly.TM.g1ExhState_ne_dec
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bSeek_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bSeek_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bSeek_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bSeek_p0_index
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bSeek_p0_argSep
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bSeek_p0_other
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bDec_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bDec_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bDec_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bDec_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bTurn_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bTurn_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bTurn_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bTurn_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRestore_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRestore_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRestore_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRestore_p3
#print axioms Internal.PsubsetPpoly.TM.FrameScan.Phased.holdLeft
#print axioms Internal.PsubsetPpoly.TM.FrameScan.Phased.holdWalk4
#print axioms Internal.PsubsetPpoly.TM.g1Advance_bFwd_of_skip
#print axioms Internal.PsubsetPpoly.TM.G1WalkMode.eq
#print axioms Internal.PsubsetPpoly.TM.g1WalkRevAdvance_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1WalkScanner_machine
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_seek_to_index
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_seek_exhaust
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_mark
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_seek_mark
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_fwd_to_cursor
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_turn
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_restore
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.g1WalkFrames_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.walk_seek_mark
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.walk_seek_exhaust
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.walk_fwd_to_cursor
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.walk_turn
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.walk_restore

-- PR2b2, the **terminal exhaustion path** behind the merged `bExh` handoff: the
-- four new modes (`bRet`, `bTurnFin`, `bFinFalse`, `bFinTrue`), the five new
-- `g1Advance` rows pinned by `g1_bRet_rows`, the eight new transition tuples
-- (`g1Transition_bTurnFin_p0…p3`, `g1Transition_bFin_p0…p3`), the terminal
-- writer instance `g1FinWriter`, the three exact atomic macros on an
-- **arbitrary** frame list and their three literal encoded-frame probes.
-- `g1Transition_bFin_p3` is the row that hands off to `readAResetStart`, and
-- `G1WalkExamples.g1WalkFramesFinal_no_cursor` is the literal witness that the
-- resulting tape has no `cursor` frame left.  **Every run takes the caller's
-- configuration**: none starts from `G1M.initialConfig`, nothing composes a
-- round with the terminal path, and no theorem says a real run reaches `bExh`
-- after the right number of rounds.  No walk invariant, iteration, loop clock,
-- addressing, positive-index operand-value read, out-of-range aggregation,
-- repair, pass A, output write, `TM.accepts`, gate-semantics, full-clock or
-- padded-tape statement is audited here, because none exists.
#print axioms Internal.PsubsetPpoly.TM.g1FinMode_ne_restore
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bTurnFin_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bTurnFin_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bTurnFin_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bTurnFin_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bFin_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bFin_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bFin_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bFin_p3
#print axioms Internal.PsubsetPpoly.TM.g1Advance_bRet_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_exh_to_cursor
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_turn_fin
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_fin_restore
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.g1WalkFramesTerminal_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.g1WalkFramesFinal_no_cursor
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.walk_exh_to_cursor
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.walk_turn_fin
#print axioms Internal.PsubsetPpoly.TM.G1WalkExamples.walk_fin_restore

-- PR3a, the cursor-walk tape invariant `Σ(j)`: the exact layout with its
-- length, its `index`/`spent`/`cursor` counts and the two structural facts its
-- scans depend on, the head-safety bound, `Σ(j)`'s four projections, and the
-- **two executed capstones from `G1M.initialConfig`** — the installation into
-- `Σ(0)` and the empty-data out-of-range branch — with their projections, their
-- clock bounds and their all-literal probes.  Both capstones **stop** at their
-- endpoint; the one round that moves off `Σ(j)` is the PR3b block below.
-- **Deliberately absent from this block**: any induction over `j`, any loop,
-- driver or cumulative clock, any successful terminal, any aggregation of the
-- two out-of-range branches, and any addressing or positive-index
-- operand-value claim.
#print axioms Internal.PsubsetPpoly.TM.g1WalkSkipRun_mem
#print axioms Internal.PsubsetPpoly.TM.g1WalkSkipRun_no_index
#print axioms Internal.PsubsetPpoly.TM.g1WalkOperand2_spent_suffix
#print axioms Internal.PsubsetPpoly.TM.g1WalkFrames_length
#print axioms Internal.PsubsetPpoly.TM.g1WalkFrames_length_eq_validation
#print axioms Internal.PsubsetPpoly.TM.g1WalkFrames_count_index
#print axioms Internal.PsubsetPpoly.TM.g1WalkFrames_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1WalkFrames_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1WalkFramesMarked_length
#print axioms Internal.PsubsetPpoly.TM.g1WalkFramesMarked_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1WalkFramesMarked_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1WalkFramesMarked_count_index
#print axioms Internal.PsubsetPpoly.TM.g1WalkFramesRestored_length
#print axioms Internal.PsubsetPpoly.TM.g1WalkFramesRestored_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1WalkFramesRestored_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1WalkFramesRestored_count_index
#print axioms Internal.PsubsetPpoly.TM.g1WalkCursor_safe
#print axioms Internal.PsubsetPpoly.TM.g1WalkConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1WalkConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1WalkConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1WalkConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1WalkConfig_hidden
#print axioms Internal.PsubsetPpoly.TM.g1WalkInstallSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1WalkEmptyOOBSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1WalkInstallSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1WalkEmptyOOBSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_oob_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_oob_stable
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_oob_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_oob_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_oob_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_oob_ne_invariant
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_zero
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkCursor_zero
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_zero_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_zero_count_cursor
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_zero_count_index
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_zero_count_spent
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_install_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_install
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_install_head
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_install_clock
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.g1EmptyExample_canonical
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.g1EmptyExample_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_empty_oob_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_empty_oob
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_empty_oob_tape
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_empty_oob_clock

-- PR3b, **exactly one round** of the cursor walk on the PR3a invariant, in both
-- of its outcomes.  `g1CS_walk_iteration_exact` takes a **caller-supplied**
-- `Σ(r, j, v)` to `Σ(r, j+1, v')` in `16 * j + 37` genuine steps.  The
-- hidden-bit relations `vals[j]? = some v` and `vals[j+1]? = some v'` are
-- explicit arguments of the start and endpoint configurations respectively;
-- `g1CS_walk_oob_exact` and `_stable` take the same `Σ(j)` to
-- the stable `bOOB` boundary in `16 * j + 32` steps on
-- `g1WalkFramesRestored r j` — data region exactly `vals` and cursor-free,
-- operand 2 **partially spent and unrepaired**.  Reaching `bOOB` is **not** a
-- rejection: no output write, verdict or `TM.accepts` result is claimed.
-- **Absent from this block**: the induction over `j`, any driver reaching
-- `Σ(j)` for `j > 0` from `G1M.initialConfig`, the cumulative loop clock, the
-- successful terminal at `j = arg2`, the aggregation of the two out-of-range
-- branches and the positive-index operand-value theorem — all six are the PR3c
-- block below.  Absent everywhere: the `spent ↦ index` repair sweep, pass A,
-- combine, the output write, gate semantics, a full-clock theorem and padded
-- tapes.
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_iteration_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_oob_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_oob_stable
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_one
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_two
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFramesRestored_one
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkCursor_one
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkCursor_two
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_one_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_one_count_cursor
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_one_count_index
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walkFrames_one_count_spent
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_round_zero
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_round_one
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_round_zero_head
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_round_one_head
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_round_two_head
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.g1OOBExample_canonical
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.oobFrames_one
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.oobFrames_one_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.oobFrames_one_count_cursor
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.oobFramesRestored_one
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.oobFramesRestored_one_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.oobFramesRestored_one_count_cursor
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.oobFramesRestored_one_count_spent
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.oobFramesRestored_one_count_index
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_oob_round
#print axioms Internal.PsubsetPpoly.TM.G1WalkInvariantExamples.walk_oob_round_head

-- PR3c, the cursor-walk **driver**: the `8k² + 29k` loop clock, the induction
-- from the **real** initial configuration into `Σ(k)` — whose endpoint carries
-- the caller's own hidden-bit proof — the `g1BSpentFrames` repair-pending
-- layout family, the successful terminal at `j = arg2`, the **public arbitrary
-- positive-index operand-2 read** returning the actual `r.vals[r.arg2]`, and
-- the aggregated out-of-range branch, both inside the **unchanged** `g1Clock`.
-- Every endpoint tape is `g1BSpentFrames r s`: data region exactly `vals` and
-- cursor-free, operand 2 still consumed.  **Deliberately absent**: the
-- `spent ↦ index` repair sweep, pass A, combine, the output write, and any
-- `TM.accepts`, verdict, full-clock, gate-semantics, acceptance-gate, multi-gate
-- or specification-bridge claim.
#print axioms Internal.PsubsetPpoly.TM.g1BLoopSteps_succ
#print axioms Internal.PsubsetPpoly.TM.g1BLoopSteps_eq_sum
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_loop_exact
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_eq_restored
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_empty
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_length
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_length_eq_validation
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_count_index
#print axioms Internal.PsubsetPpoly.TM.g1ExhPre_length
#print axioms Internal.PsubsetPpoly.TM.g1ExhPre_argSep
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_terminal_exact
#print axioms Internal.PsubsetPpoly.TM.g1BReadSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1BReadSteps_eq_install
#print axioms Internal.PsubsetPpoly.TM.g1BReadSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1BOOBSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1BOOBSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_tape
#print axioms Internal.PsubsetPpoly.TM.g1BOOBCtx_nil
#print axioms Internal.PsubsetPpoly.TM.g1BOOBCtx_last
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_nil
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_cons
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_stable
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_ne_success
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.g1BReadExample_canonical
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.g1BReadExample_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readFramesFinal_eq
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readFramesFinal_count_cursor
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readFramesFinal_count_spent
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readExample_install_scan_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readExample_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_vB
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_head
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readExample_clock_value
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_clock
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.walkExample_framesFinal
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.walkExample_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_two
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_two_vB
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_two_clock
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.emptyExample_oob_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.emptyExample_frames
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_empty
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_empty_clock
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oobExample_oob_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oobExample_frames
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_nonempty
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_nonempty_head
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_nonempty_clock

-- The thirteen-step rewrite cycle at the G1 control, kept only as an
-- **arbitrary-configuration** regression: `g1_bRoundStart_unreachable` proves
-- the forward table never produces `bRoundStart`, so the caller supplies the
-- configuration, the frame list and the safety bound.  Nothing composes these
-- from `G1M.initialConfig`.
#print axioms Internal.PsubsetPpoly.TM.g1CS_round_from_bridge
#print axioms Internal.PsubsetPpoly.TM.g1CS_round_probe
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_and_true
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_and_false
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_or_true
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_and_oob
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_and_oob_stable
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_oob_ne_success
#print axioms Internal.PsubsetPpoly.TM.G1Examples.readB_oob_ne_reject

-- T1a fixed-control canonical validation and read-only rewind handoff.
#print axioms Internal.PsubsetPpoly.TM.decodeT1Tape_encode
#print axioms Internal.PsubsetPpoly.TM.decodeT1Tape?_eq_some
#print axioms Internal.PsubsetPpoly.TM.t1CS_frame_macrostep
#print axioms Internal.PsubsetPpoly.TM.t1CS_scan_frames
#print axioms Internal.PsubsetPpoly.TM.t1CS_validate_encoded_exact
#print axioms Internal.PsubsetPpoly.TM.t1CanonicalEncoderAutomatonTrace
#print axioms Internal.PsubsetPpoly.TM.t1CS_rewind_tail
#print axioms Internal.PsubsetPpoly.TM.t1CS_validate_rewind_encoded_exact

-- T1b-A fixed-control mutation and genuine execution surfaces.  This slice
-- stops before the j→j+1 loop, restoration, output, and acceptance.
#print axioms Internal.PsubsetPpoly.TM.t1Transition_startMutation_active
#print axioms Internal.PsubsetPpoly.TM.t1Transition_probeData_p3_data
#print axioms Internal.PsubsetPpoly.TM.t1Transition_probeData_p3_oob
#print axioms Internal.PsubsetPpoly.TM.t1Transition_turnInstall
#print axioms Internal.PsubsetPpoly.TM.t1Transition_writeCursor
#print axioms Internal.PsubsetPpoly.TM.t1Transition_seekIndexBack_p0_mark
#print axioms Internal.PsubsetPpoly.TM.t1Transition_seekIndexBack_p0_skip
#print axioms Internal.PsubsetPpoly.TM.t1Transition_seekIndexBack_p0_success
#print axioms Internal.PsubsetPpoly.TM.t1Transition_markSpent
#print axioms Internal.PsubsetPpoly.TM.t1Transition_backupCursor
#print axioms Internal.PsubsetPpoly.TM.t1Transition_writeData
#print axioms Internal.PsubsetPpoly.TM.t1WriteFrame_ascending
#print axioms Internal.PsubsetPpoly.TM.t1WriteFrame_descending
#print axioms Internal.PsubsetPpoly.TM.t1MutationFrames_length
#print axioms Internal.PsubsetPpoly.TM.t1MutationFrames_getElem?_cursor
#print axioms Internal.PsubsetPpoly.TM.t1MutationFrames_zero
#print axioms Internal.PsubsetPpoly.TM.encodeT1Frames_split
#print axioms Internal.PsubsetPpoly.TM.t1PhysicalBitsAt_flatMap
#print axioms Internal.PsubsetPpoly.TM.t1CS_aligned_step_right
#print axioms Internal.PsubsetPpoly.TM.t1CS_aligned_step_left
#print axioms Internal.PsubsetPpoly.TM.t1CS_aligned_step_stay
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_sink
#print axioms Internal.PsubsetPpoly.TM.t1CS_startMutation_walk
#print axioms Internal.PsubsetPpoly.TM.t1CS_probeData_frame_data
#print axioms Internal.PsubsetPpoly.TM.t1CS_probeData_frame_oob
#print axioms Internal.PsubsetPpoly.TM.t1CS_turnInstall_step
#print axioms Internal.PsubsetPpoly.TM.t1CS_writeCursor_frame
#print axioms Internal.PsubsetPpoly.TM.t1CS_markSpent_frame
#print axioms Internal.PsubsetPpoly.TM.t1CS_backupCursor_walk
#print axioms Internal.PsubsetPpoly.TM.t1CS_writeData_frame
#print axioms Internal.PsubsetPpoly.TM.t1CS_seekIndexBack_frame_skip
#print axioms Internal.PsubsetPpoly.TM.t1CS_seekIndexBack_frame_mark
#print axioms Internal.PsubsetPpoly.TM.t1CS_seekIndexBack_frame_success
#print axioms Internal.PsubsetPpoly.TM.t1ListTape_write_frame
#print axioms Internal.PsubsetPpoly.TM.t1MutationTape_zero
#print axioms Internal.PsubsetPpoly.TM.t1CS_install_first_cursor_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_install_first_cursor_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_oob_empty_data_exact
#print axioms Internal.PsubsetPpoly.TM.t1bIndexZero_install
#print axioms Internal.PsubsetPpoly.TM.t1bNonzeroIndex_install
#print axioms Internal.PsubsetPpoly.TM.t1bEmptyData_oob_exact

-- T1b-B genuine one-iteration mutation loop and exact OOB companion.  The
-- induction/terminal split is not part of this layer and is audited in T1b-C
-- below; the later T1c sections audit terminal control, restoration/output,
-- public-clock composition, and acceptance semantics.
#print axioms Internal.PsubsetPpoly.TM.t1CS_scan_back_skip
#print axioms Internal.PsubsetPpoly.TM.t1MutationTape_eq_listTape
#print axioms Internal.PsubsetPpoly.TM.t1CursorBase_safe
#print axioms Internal.PsubsetPpoly.TM.t1CS_mutationConfig_zero
#print axioms Internal.PsubsetPpoly.TM.t1LoopProbe_safe
#print axioms Internal.PsubsetPpoly.TM.t1CS_loop_iteration_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_loop_oob_exact
#print axioms Internal.PsubsetPpoly.TM.t1bbIterationZero
#print axioms Internal.PsubsetPpoly.TM.t1bbOobAtOne

-- T1b-C loop induction, exact terminal cases from the real initial
-- configuration, and the clock estimate.  These are finite-prefix `runConfig`
-- roots: T1c-1 activated both boundaries, so the former public-clock padding
-- theorems no longer exist and are not audited.
#print axioms Internal.PsubsetPpoly.TM.t1LoopSteps_succ
#print axioms Internal.PsubsetPpoly.TM.t1CS_loop_iterate_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_loop_reach_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_loop_success_tail_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_loop_success_from_zero_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_loop_oob_from_zero_exact
#print axioms Internal.PsubsetPpoly.TM.t1OobSteps_nil
#print axioms Internal.PsubsetPpoly.TM.t1OobSteps_cons
#print axioms Internal.PsubsetPpoly.TM.t1DecideSteps_some
#print axioms Internal.PsubsetPpoly.TM.t1DecideSteps_none
#print axioms Internal.PsubsetPpoly.TM.t1Selected_none_iff
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_decide_success_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_decide_oob_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_decide_oob_empty_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_decideTotal_le_clock
#print axioms Internal.PsubsetPpoly.TM.t1bcDriveToSlotTwo
#print axioms Internal.PsubsetPpoly.TM.t1bcSuccessTail
#print axioms Internal.PsubsetPpoly.TM.t1bcSuccessFromInitial
#print axioms Internal.PsubsetPpoly.TM.t1bcOobFromInitial
#print axioms Internal.PsubsetPpoly.TM.t1bcEmptyOobFromInitial
#print axioms Internal.PsubsetPpoly.TM.t1bcSuccessFitsClock
#print axioms Internal.PsubsetPpoly.TM.t1bcOobFitsClock
#print axioms Internal.PsubsetPpoly.TM.t1bcEmptyFitsClock
#print axioms Internal.PsubsetPpoly.TM.t1bcIndexZeroSuccessFromInitial
#print axioms Internal.PsubsetPpoly.TM.t1bcOobBoundaryFromInitial

-- T1c-1 active terminal control: the transition table for both terminal arms
-- and one genuine generic execution theorem per new mode.  T1c-2/T1c-3 below
-- audit restoration, terminal clocks, public runs, and acceptance semantics.
#print axioms Internal.PsubsetPpoly.TM.t1Transition_successStart_active
#print axioms Internal.PsubsetPpoly.TM.t1Transition_oobStart_active
#print axioms Internal.PsubsetPpoly.TM.t1Transition_outWalk
#print axioms Internal.PsubsetPpoly.TM.t1Transition_outBackup
#print axioms Internal.PsubsetPpoly.TM.t1Transition_outWriteData
#print axioms Internal.PsubsetPpoly.TM.t1Transition_outTurn
#print axioms Internal.PsubsetPpoly.TM.t1Transition_outWriteOut
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairWrite
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairBack
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairHop
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairSeek_p0_write
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairSeek_p0_skip
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairSeek_p0_done
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairSeek_p0_bad
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairDone_accept
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairDone_reject
#print axioms Internal.PsubsetPpoly.TM.t1Transition_repairDone_acceptState
#print axioms Internal.PsubsetPpoly.TM.t1CS_successStart_dispatch
#print axioms Internal.PsubsetPpoly.TM.t1CS_oobStart_dispatch
#print axioms Internal.PsubsetPpoly.TM.t1CS_outWalk_walk
#print axioms Internal.PsubsetPpoly.TM.t1CS_outSeekCursor_frame
#print axioms Internal.PsubsetPpoly.TM.t1CS_outBackup_walk
#print axioms Internal.PsubsetPpoly.TM.t1CS_outWriteData_frame
#print axioms Internal.PsubsetPpoly.TM.t1CS_outSeekOutput_frame
#print axioms Internal.PsubsetPpoly.TM.t1CS_outTurn_step
#print axioms Internal.PsubsetPpoly.TM.t1CS_outWriteOut_frame
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairSeek_frame_skip
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairSeek_frame_write
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairSeek_frame_done
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairWrite_frame
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairBack_walk
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairHop_step
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairDone_accept
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairDone_reject
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairDone_accept_stable
#print axioms Internal.PsubsetPpoly.TM.t1CS_repairDone_reject_stable

-- T1c-2 composite output/repair execution to literal accept/reject sinks.
#print axioms Internal.PsubsetPpoly.TM.t1OutputPosition_eq
#print axioms Internal.PsubsetPpoly.TM.t1OutputPosition_safe
#print axioms Internal.PsubsetPpoly.TM.t1OutputFrames_false
#print axioms Internal.PsubsetPpoly.TM.t1OutputFrames_length
#print axioms Internal.PsubsetPpoly.TM.t1tOutputBase_safe
#print axioms Internal.PsubsetPpoly.TM.t1tOutputEntry_safe
#print axioms Internal.PsubsetPpoly.TM.t1OutputFrames_count_spent
#print axioms Internal.PsubsetPpoly.TM.t1OutputFrames_count_index
#print axioms Internal.PsubsetPpoly.TM.t1CS_success_final_tape_eq
#print axioms Internal.PsubsetPpoly.TM.t1CS_success_final_tape_off
#print axioms Internal.PsubsetPpoly.TM.t1CS_success_final_tape_at
#print axioms Internal.PsubsetPpoly.TM.t1CS_oob_final_tape_eq
#print axioms Internal.PsubsetPpoly.TM.t1CS_repair_scan_skip
#print axioms Internal.PsubsetPpoly.TM.t1CS_repair_cycle
#print axioms Internal.PsubsetPpoly.TM.t1CS_repair_spent_run
#print axioms Internal.PsubsetPpoly.TM.t1CS_repair_pass_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_output_write_exact
#print axioms Internal.PsubsetPpoly.TM.t1TerminalSteps_some
#print axioms Internal.PsubsetPpoly.TM.t1TerminalSteps_none
#print axioms Internal.PsubsetPpoly.TM.t1CS_terminal_success_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_terminal_oob_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_terminal_oob_empty_exact
#print axioms Internal.PsubsetPpoly.TM.t1c2SuccessTerminal
#print axioms Internal.PsubsetPpoly.TM.t1c2SuccessOutputAt
#print axioms Internal.PsubsetPpoly.TM.t1c2OobTerminal
#print axioms Internal.PsubsetPpoly.TM.t1c2EmptyTerminal

-- T1c-3 full canonical semantics: initialConfig→sink, fixed public clock,
-- literal-state acceptance, output value and tape conservation.
#print axioms Internal.PsubsetPpoly.TM.t1TotalSteps_some
#print axioms Internal.PsubsetPpoly.TM.t1TotalSteps_none
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_total_success_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_total_oob_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_total_oob_empty_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_runConfig_total_reject_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_totalSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.t1CS_run_success_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_run_reject_exact
#print axioms Internal.PsubsetPpoly.TM.t1CS_run_head_zero
#print axioms Internal.PsubsetPpoly.TM.t1CS_accepts_eq_isSome
#print axioms Internal.PsubsetPpoly.TM.t1CS_accepts_iff
#print axioms Internal.PsubsetPpoly.TM.t1CS_accepts_eq_decide_lt
#print axioms Internal.PsubsetPpoly.TM.t1CS_run_reject_not_accepts
#print axioms Internal.PsubsetPpoly.TM.t1CS_run_success_tape_eq
#print axioms Internal.PsubsetPpoly.TM.t1CS_run_output_at
#print axioms Internal.PsubsetPpoly.TM.t1CS_run_tape_off
#print axioms Internal.PsubsetPpoly.TM.t1CS_run_reject_tape_eq
#print axioms Internal.PsubsetPpoly.TM.t1CS_canonical_semantics
#print axioms Internal.PsubsetPpoly.TM.t1c3TrueAccepts
#print axioms Internal.PsubsetPpoly.TM.t1c3TrueRun
#print axioms Internal.PsubsetPpoly.TM.t1c3TrueOutput
#print axioms Internal.PsubsetPpoly.TM.t1c3FalseAccepts
#print axioms Internal.PsubsetPpoly.TM.t1c3FalseRun
#print axioms Internal.PsubsetPpoly.TM.t1c3FalseOutput
#print axioms Internal.PsubsetPpoly.TM.t1c3OobRejects
#print axioms Internal.PsubsetPpoly.TM.t1c3OobRun
#print axioms Internal.PsubsetPpoly.TM.t1c3OobTapePreserved
#print axioms Internal.PsubsetPpoly.TM.t1c3BoundaryRun
#print axioms Internal.PsubsetPpoly.TM.t1c3BoundaryRejects
#print axioms Internal.PsubsetPpoly.TM.t1c3EmptyRejects
#print axioms Internal.PsubsetPpoly.TM.t1c3EmptyRun
#print axioms Internal.PsubsetPpoly.TM.t1c3EmptyTapePreserved
#print axioms Internal.PsubsetPpoly.TM.t1c3TrueClockFits
#print axioms Internal.PsubsetPpoly.TM.t1c3OobClockFits
#print axioms Internal.PsubsetPpoly.TM.t1c3EmptyClockFits

-- Итоговые утверждения (формульная сепарация).
#print axioms RefutedRoute_NP_not_subset_PpolyFormula_final
#print axioms NP_not_subset_PpolyFormula_final_with_provider
#print axioms RefutedRoute_NP_not_subset_PpolyFormula_final_with_supportBounds
#print axioms RefutedRoute_NP_not_subset_PpolyFormula_final_with_multiswitching
#print axioms asymptotic_formula_collapse
#print axioms RefutedRoute_NP_not_subset_PpolyReal_final
#print axioms NP_not_subset_PpolyReal_final_with_provider
#print axioms RefutedRoute_NP_not_subset_PpolyReal_final_with_supportBounds
#print axioms RefutedRoute_NP_not_subset_PpolyReal_final_with_multiswitching
#print axioms NP_not_subset_PpolyFormula_from_partial_formulas
#print axioms empty_witness_admissible_for_asymptotic_slice_of_nat_cmp

-- Мост от нижних оценок к `NP ⊄ PpolyFormula`.
#print axioms NP_not_subset_PpolyReal_from_partial_formulas
#print axioms OPS_trigger_formulas_partial_of_provider
#print axioms OPS_trigger_formulas_partial_of_provider_formula_separation_strict
#print axioms fixed_formula_collapse_of_provider
#print axioms asymptotic_formula_collapse_of_slice_bridge
#print axioms ppolyFormula_fixed_of_asymptotic_slice
#print axioms asymptotic_formula_collapse_of_slice_agreement
#print axioms NP_not_subset_PpolyFormula_of_fixed_formula_collapse
#print axioms NP_not_subset_PpolyFormula_of_asymptotic_formula_collapse
#print axioms P_ne_NP_final_with_provider
#print axioms AuditOnly_NP_not_subset_PpolyDAG_final_of_dag_stableRestrictionPayload_TM
#print axioms AuditOnly_NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM
#print axioms AuditOnly_NP_not_subset_PpolyDAG_final_of_certificateProvider_TM
#print axioms AuditOnly_NP_not_subset_PpolyDAG_final_of_invariantProvider_TM
#print axioms RefutedRoute_NP_not_subset_PpolyDAG_final_of_supportBounds_TM
#print axioms AuditOnly_P_ne_NP_final_of_dag_stableRestrictionPayload_TM
#print axioms AuditOnly_P_ne_NP_final_of_dag_stableRestriction_TM
#print axioms AuditOnly_P_ne_NP_final_of_certificateProvider_TM
#print axioms AuditOnly_P_ne_NP_final_of_invariantProvider_TM
#print axioms RefutedRoute_P_ne_NP_final_of_supportBounds_TM
#print axioms NP_not_subset_PpolyDAG_final
#print axioms RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData
#print axioms RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptoticPullback
#print axioms P_ne_NP_final
#print axioms RefutedRoute_P_ne_NP_final_of_multiswitchingData
#print axioms RefutedRoute_P_ne_NP_final_of_asymptoticPullback

-- Regression checks for I-1 / I-3 readiness.
#print axioms Tests.i1_trivial_realization_available
#print axioms Tests.i1_trivial_ppolyreal_route_no_manual_embed
#print axioms Tests.i3_certificate_auto_no_manual_hCardHalf
#print axioms Tests.i4_final_wiring_of_formulaCertificate
#print axioms Tests.i4_final_wiring_of_supportBounds
#print axioms Tests.i4_gap_targeted_payload_contradiction_of_formulaCertificate
#print axioms Tests.i4_gap_targeted_payload_contradiction_of_supportBounds
#print axioms Tests.i4_dagScenarioWitness_freePositions_card_eq_zero
#print axioms Tests.i4_dagCandidateRestriction_of_scenarioWitness_alive_card_eq_zero
#print axioms Tests.i4_dag_candidateRestriction_alive_small_of_freePositions_small
#print axioms Tests.i4_dag_candidateRestriction_of_scenarioWitness_forces_yes
#print axioms Tests.i4_np_not_subset_ppolyDAG_of_dag_stableRestrictionPayload
#print axioms Tests.i4_np_not_subset_ppolyDAG_of_dag_stableRestriction
#print axioms Tests.i4_np_not_subset_ppolyDAG_of_certificateProvider
#print axioms Tests.i4_np_not_subset_ppolyDAG_of_invariantProvider
#print axioms Tests.i4_np_not_subset_ppolyDAG_final_of_invariantProvider
#print axioms Tests.i4_np_not_subset_ppolyDAG_of_supportBounds
#print axioms Tests.i4_np_not_subset_ppolyDAG_final_of_multiswitching_data
#print axioms Tests.i4_p_ne_np_final_of_dag_stableRestrictionPayload
#print axioms Tests.i4_p_ne_np_final_of_dag_stableRestriction
#print axioms Tests.i4_p_ne_np_final_of_invariantProvider
#print axioms Tests.i4_p_ne_np_final_of_supportBounds
#print axioms Tests.i4_p_ne_np_final_of_multiswitching_data
#print axioms Tests.i4_final_wiring_of_multiswitching

-- Активный inclusion endpoint: no-arg, без внешнего `EvalAgreement`-контракта.
#print axioms Complexity.Simulation.proved_P_subset_PpolyDAG_internal
#print axioms Complexity.Simulation.proved_P_subset_PpolyDAG_internal_defeq_linear

-- Проверяем, что ключевые shrinkage-леммы не тянут лишних аксиом.
-- Это именно те утверждения, которые в TODO помечены для перепроверки.
#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0
#print axioms ThirdPartyFacts.shrinkage_for_localCircuit
#print axioms ThirdPartyFacts.canonicalCCDT_CNF_aux_leafPartition_free
#print axioms ThirdPartyFacts.shrinkage_negDnfFamily_to_dnf_canonicalCCDT

-- Проверяем новый constructive I-4 трек через явный multi-switching witness.
#print axioms LowerBounds.noSmallAC0Solver_partial_of_multiSwitching
#print axioms LowerBounds.noSmallAC0Solver_partial_of_multiSwitching_provider
#print axioms AC0LocalityBridge.semantic_provider_semantic_link
#print axioms AC0LocalityBridge.package_semantic_link
#print axioms AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal
#print axioms AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_singleton_family
#print axioms AC0LocalityBridge.semanticSwitchingCertificate_internal
#print axioms AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_cert_length_eq_one
#print axioms AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_not_nontrivial_family
#print axioms AC0LocalityBridge.semanticSwitchingCertificate_of_provider
#print axioms AC0LocalityBridge.semanticSwitchingCertificateProvider_of_provider
#print axioms AC0LocalityBridge.semanticSwitchingNontrivialFamilyPackage_of_certificate
#print axioms AC0LocalityBridge.semanticSwitchingNontrivialFamilyProvider_of_certificateProvider_and_length
#print axioms AC0LocalityBridge.semanticSingletonWitness
#print axioms AC0LocalityBridge.coveredB_semanticSingletonWitness
#print axioms AC0LocalityBridge.semanticSingletonWitness_err_zero
#print axioms AC0LocalityBridge.semanticSingletonWitness_nonempty_of_exists_true
#print axioms AC0LocalityBridge.semanticSingletonAtlas_exact_epsilon_with_witness
#print axioms AC0LocalityBridge.semanticSingletonAtlas_exact_epsilon_with_dict_eq_witness
#print axioms AC0AtlasBridge.boundedAtlasScenario_of_semanticSwitchingCertificate
#print axioms AC0AtlasBridge.scenarioBudget_of_semanticSwitchingCertificate
#print axioms AC0AtlasBridge.semanticSwitchingScenarioBudget_no_large_gap
#print axioms AC0AtlasBridge.linked_testset_of_semanticSwitchingScenarioBudget
#print axioms AC0AtlasBridge.semanticSwitchingSmallMismatchPackage_of_extraction
#print axioms AC0AtlasBridge.linked_small_testset_of_boundedAtlasScenario
#print axioms AC0AtlasBridge.linked_small_testset_of_semanticSwitchingSmallMismatchPackage
#print axioms AC0AtlasBridge.semanticSwitchingSmallMismatchProvider_of_boundedAtlasScenarioProvider_and_extraction
#print axioms AC0AtlasBridge.linked_small_testset_provider_of_semanticSwitchingSmallMismatchProvider
#print axioms contradiction_of_semanticSwitchingApproxFamilyPackage
#print axioms no_ppolyFormula_of_semanticSwitchingApproxFamilyProvider
#print axioms NP_strict_not_subset_PpolyFormula_of_semanticSwitchingApproxFamilyProvider
#print axioms NP_not_subset_PpolyFormula_of_semanticSwitchingApproxFamilyProvider
#print axioms Counting.exists_small_testset_for_fixed_approximant_iff
#print axioms Counting.exists_small_testset_iff_exists_small_mismatch_approximant
#print axioms Counting.distU_perm
#print axioms Counting.unionClass_perm_fixed
#print axioms Counting.unionClass_perm_fixed_of_perm
#print axioms Counting.unionClass_perm
#print axioms Counting.approxClass_perm_fixed
#print axioms Counting.approxClass_perm_fixed_of_perm
#print axioms Counting.approxClass_perm
#print axioms Counting.one_le_unionBound
#print axioms LowerBounds.linked_function_in_approxClass_of_semanticSwitchingScenarioBudget
#print axioms LowerBounds.current_source_route_gives_singleton_approxClass
#print axioms LowerBounds.current_source_route_no_two_point_family
#print axioms LowerBounds.singletonProvenancePackage_of_internal_provider
#print axioms LowerBounds.singletonProvenance_boundedWitness
#print axioms LowerBounds.linked_function_in_approxClass_of_singletonProvenancePackage
#print axioms LowerBounds.smallMismatchPackage_of_singletonProvenancePackage_of_mismatch_card_le
#print axioms LowerBounds.singletonDensityPackage_of_internal_provider
#print axioms LowerBounds.approxOnNaturalMismatchTestset_of_singletonDensityPackage
#print axioms LowerBounds.naturalMismatchTestset_density_le_of_singletonDensityPackage
#print axioms LowerBounds.naturalMismatchTestset_density_le_inv_of_singletonDensityPackage
#print axioms LowerBounds.naturalMismatchTestset_card_le_inv_mul_pow_of_singletonDensityPackage
#print axioms LowerBounds.linked_natural_testset_density_of_internal_provider
#print axioms LowerBounds.old_testset_endpoint_of_singletonDensityPackage_of_testsetCapacity_lt_one
#print axioms LowerBounds.one_le_testsetCapacity
#print axioms LowerBounds.not_testsetCapacity_lt_one
#print axioms LowerBounds.naturalMismatchTestset_not_testsetCapacity_lt_one_of_singletonDensityPackage
#print axioms LowerBounds.abstractSingletonDensityPayload_of_singletonDensityPackage
#print axioms LowerBounds.nonempty_abstractSingletonDensityPayload_false
#print axioms LowerBounds.abstractLinkedSingletonDensityPayload_of_abstract
#print axioms LowerBounds.nonempty_abstractLinkedSingletonDensityPayload_false
#print axioms LowerBounds.abstractLinkedSingletonDensityPayload_of_singletonDensityPackage
#print axioms LowerBounds.abstractTargetedSingletonDensityPayload_of_singletonDensityPackage
#print axioms LowerBounds.nonempty_abstractTargetedSingletonDensityPayload_false
#print axioms LowerBounds.abstractGapTargetedSingletonDensityPayload_of_singletonDensityPackage
#print axioms LowerBounds.approxOnNaturalMismatchTestset_of_abstractSingletonDensityPayload
#print axioms LowerBounds.naturalMismatchTestset_density_le_inv_of_abstractSingletonDensityPayload
#print axioms LowerBounds.old_testset_endpoint_of_abstractSingletonDensityPayload_of_testsetCapacity_lt_one
#print axioms LowerBounds.naturalMismatchTestset_not_testsetCapacity_lt_one_of_abstractSingletonDensityPayload
#print axioms LowerBounds.abstractSingletonDensityPayload_of_internal_provider
#print axioms LowerBounds.abstractLinkedSingletonDensityPayload_of_internal_provider
#print axioms LowerBounds.abstractTargetedSingletonDensityPayload_of_internal_provider
#print axioms LowerBounds.abstractGapTargetedSingletonDensityPayload_of_internal_provider
#print axioms LowerBounds.abstractGapTargetedSingletonDensityPayload_of_dag
#print axioms LowerBounds.gapPartialMCSP_exists_yes_input
#print axioms LowerBounds.abstractGapStableRestrictionPayload_of_exists_stableRestriction
#print axioms LowerBounds.abstractGapLocalityPayload_of_exists_locality
#print axioms LowerBounds.localityGoal_of_abstractGapTargetedPayload
#print axioms LowerBounds.stableRestrictionGoal_of_abstractGapTargetedPayload
#print axioms LowerBounds.stableRestrictionGoal_iff_exists_stableRestriction_package_with_base
#print axioms LowerBounds.localityGoal_of_abstractGapStableRestrictionPayload
#print axioms LowerBounds.localityGoal_iff_exists_locality_package_with_base
#print axioms LowerBounds.solvesPromise_of_abstractGapTargetedPayload
#print axioms LowerBounds.false_of_abstractGapLocalityPayload
#print axioms LowerBounds.false_of_abstractGapStableRestrictionPayload
#print axioms LowerBounds.false_of_abstractGapTargetedPayload_of_localityGoal
#print axioms LowerBounds.false_of_abstractGapTargetedPayload_of_stableRestrictionGoal
#print axioms LowerBounds.stableRestrictionGoal_of_abstractGapTargetedPayload_of_formulaCertificate
#print axioms LowerBounds.stableRestrictionGoal_of_abstractGapTargetedPayload_of_restrictionData
#print axioms LowerBounds.stableRestrictionGoal_of_abstractGapTargetedPayload_of_supportBounds
#print axioms LowerBounds.false_of_abstractGapTargetedPayload_of_formulaCertificate
#print axioms LowerBounds.false_of_abstractGapTargetedPayload_of_restrictionData
#print axioms LowerBounds.false_of_abstractGapTargetedPayload_of_supportBounds
#print axioms LowerBounds.abstractGapTargetedSingletonDensityPayload_of_dag_with_baseWitness_provenance
#print axioms LowerBounds.abstractGapTargetedSingletonDensityPayload_of_dag_with_k_eq_baseWitnessLen
#print axioms LowerBounds.dag_payload_nonemptyWitness_bridge_split
#print axioms LowerBounds.dagCanonicalPayload
#print axioms LowerBounds.dagCanonicalPayload_k_eq_baseWitnessLen
#print axioms LowerBounds.dagCanonicalPayload_baseWitness_eq_semanticSingletonWitness
#print axioms LowerBounds.dagCanonicalPayload_dict_eq_baseWitness
#print axioms LowerBounds.dagScenarioWitness
#print axioms LowerBounds.dagScenarioWitness_len
#print axioms LowerBounds.dagScenarioWitness_sub
#print axioms LowerBounds.dagScenarioWitness_err
#print axioms LowerBounds.dagScenarioWitness_sub_baseWitness
#print axioms LowerBounds.dagScenarioWitness_cubeYes
#print axioms LowerBounds.dagScenarioWitness_not_cubeNo
#print axioms LowerBounds.nonemptyWitnessGoal_iff_baseWitness_nonempty_of_dagCanonicalPayload
#print axioms LowerBounds.dag_payload_baseWitness_nonempty
#print axioms LowerBounds.dag_payload_baseWitness_nonempty_holds
#print axioms LowerBounds.dagScenarioWitness_eq_pointSubcube_of_mem
#print axioms LowerBounds.dagScenarioWitness_freePositions_card_eq_zero
#print axioms LowerBounds.dagCandidateRestrictionOfScenarioWitness_alive_card_eq_zero
#print axioms LowerBounds.dagCandidateRestrictionOfSubcube_alive_card
#print axioms LowerBounds.dagCandidateRestrictionOfSubcube_alive_small_of_freePositions_small
#print axioms LowerBounds.mem_of_apply_dagCandidateRestrictionOfSubcube
#print axioms LowerBounds.dagCandidateRestrictionOfScenarioWitness_forces_yes
#print axioms LowerBounds.not_ppolyDAG_of_abstractGapTargeted_consumer
#print axioms LowerBounds.not_ppolyDAG_of_dag_stableRestrictionPayload
#print axioms LowerBounds.not_ppolyDAG_of_dag_stableRestriction
#print axioms LowerBounds.stableRestrictionGoal_of_dagStableRestrictionCertificate
#print axioms LowerBounds.dagStableRestrictionCertificate_of_localInvariant
#print axioms LowerBounds.dagStableRestrictionCertificateProvider_of_invariantProvider
#print axioms LowerBounds.dag_stableRestriction_producer_of_certificateProvider
#print axioms LowerBounds.dag_stableRestriction_producer_of_invariantProvider
#print axioms LowerBounds.dag_stableRestriction_producer_iff
#print axioms LowerBounds.dag_stableRestrictionGoal_of_formulaCertificate
#print axioms LowerBounds.dag_stableRestriction_producer_of_formulaCertificate
#print axioms LowerBounds.dag_stableRestrictionGoal_of_supportBounds
#print axioms LowerBounds.dag_stableRestriction_producer_of_supportBounds
#print axioms Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_witness
#print axioms Magnification.AC0LocalityBridge.CurrentSingletonPreSingletonSelectorPackage
#print axioms Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_package
#print axioms Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_package_Rf_eq_semanticSingletonWitness
#print axioms Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_eq_pointSubcube_of_mem
#print axioms Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_freePositions_card_eq_zero
#print axioms LowerBounds.NP_not_subset_PpolyDAG_of_abstractGapTargeted_consumer
#print axioms LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestrictionPayload
#print axioms LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestriction
#print axioms LowerBounds.NP_not_subset_PpolyDAG_of_certificateProvider_TM
#print axioms LowerBounds.NP_not_subset_PpolyDAG_of_invariantProvider_TM
#print axioms LowerBounds.RefutedRoute_NP_not_subset_PpolyDAG_of_supportBounds
#print axioms LowerBounds.NP_not_subset_PpolyDAG_of_abstractGapTargeted_consumer_TM
#print axioms LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestrictionPayload_TM
#print axioms LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestriction_TM
#print axioms LowerBounds.RefutedRoute_NP_not_subset_PpolyDAG_of_supportBounds_TM
#print axioms Core.exists_mem_subcube
#print axioms LowerBounds.abstractGapWitnessedPayload_of_exists_nonemptyWitness
#print axioms LowerBounds.nonemptyWitnessGoal_of_abstractGapTargetedPayload
#print axioms LowerBounds.nonemptyWitnessGoal_iff_exists_witnessed_package_with_base
#print axioms LowerBounds.one_le_k_of_nonemptyWitnessGoal
#print axioms LowerBounds.k_ne_zero_of_nonemptyWitnessGoal
#print axioms LowerBounds.not_nonemptyWitnessGoal_of_k_eq_zero
#print axioms LowerBounds.nonemptyWitnessGoal_of_baseWitness_nonempty
#print axioms LowerBounds.not_nonemptyWitnessGoal_of_baseWitness_nil_of_k_eq_baseWitnessLen
#print axioms LowerBounds.exists_covered_point_of_abstractGapWitnessedPayload
#print axioms LowerBounds.exists_cubeSound_package_with_base_iff
#print axioms LowerBounds.cubeYesGoal_of_abstractGapWitnessedPayload
#print axioms LowerBounds.cubeYesGoal_iff_exists_cubeSound_package_with_base
#print axioms LowerBounds.false_of_abstractGapWitnessedPayload_of_cubeYes_and_cubeNo
#print axioms LowerBounds.cubeNoGoal_of_abstractGapWitnessedPayload
#print axioms LowerBounds.cubeSeparatedGoal_of_abstractGapWitnessedPayload
#print axioms LowerBounds.false_of_abstractGapWitnessedPayload_of_cubeSeparatedGoal
#print axioms LowerBounds.false_of_abstractGapTargetedPayload_of_exists_witnessed_cubeSeparatedGoal
#print axioms LowerBounds.false_of_abstractGapTargetedPayload_of_nonemptyWitnessGoal_and_cubeSeparated
#print axioms LowerBounds.dagNonemptyWitnessGoalProbe
#print axioms LowerBounds.dagNonemptyWitnessGoalProbe_iff_exists_witnessed_on_dag_payload
#print axioms LowerBounds.dagNonemptyWitnessGoalProbe_iff_baseWitness_nonempty
#print axioms LowerBounds.dagNonemptyWitnessGoalProbe_holds
#print axioms LowerBounds.dagWitnessedPayload
#print axioms LowerBounds.dagWitnessedPayload_base_eq
#print axioms LowerBounds.dagWitnessedPayload_Rf_eq_baseWitness
#print axioms LowerBounds.cubeYesGoal_of_dagWitnessedPayload
#print axioms LowerBounds.dagCubeSoundWitnessPayload
#print axioms LowerBounds.dagCubeSoundWitnessPayload_base_eq
#print axioms LowerBounds.dagSelectorProvenancePayload
#print axioms LowerBounds.dagSelectorProvenancePayload_base_eq
#print axioms LowerBounds.dagSelectorProvenancePayload_Rf_eq_semanticSingletonWitness
#print axioms LowerBounds.dagSelectorProvenancePayload_dict_eq_Rf
#print axioms LowerBounds.dagSelectorProvenancePayload_coveredB_eq_gapTarget
#print axioms LowerBounds.not_cubeNoGoal_of_dagWitnessedPayload
#print axioms LowerBounds.not_cubeSeparatedGoal_of_dagWitnessedPayload
#print axioms LowerBounds.not_cubeRefute_of_dagCubeSoundWitnessPayload
#print axioms LowerBounds.abstractGapCubeSoundWitnessPayload_of_cubeSound
#print axioms LowerBounds.gapTarget_true_of_covered_of_abstractGapCubeSoundWitnessPayload
#print axioms LowerBounds.exists_yes_point_of_abstractGapCubeSoundWitnessPayload
#print axioms LowerBounds.exists_yes_input_of_abstractGapCubeSoundWitnessPayload
#print axioms LowerBounds.contradiction_of_abstractGapCubeSoundWitnessPayload_of_cubeRefute
#print axioms LowerBounds.abstractGapSelectorProvenancePayload_of_equalities
#print axioms LowerBounds.dict_eq_Rf_of_abstractGapSelectorProvenancePayload
#print axioms LowerBounds.Rf_eq_semanticSingletonWitness_of_abstractGapSelectorProvenancePayload
#print axioms LowerBounds.coveredB_eq_f_of_abstractGapSelectorProvenancePayload
#print axioms LowerBounds.coveredB_eq_gapTarget_of_abstractGapSelectorProvenancePayload
#print axioms LowerBounds.cubeYesGoal_of_selectorProvenancePayload
#print axioms LowerBounds.not_cubeNoGoal_of_selectorProvenance
#print axioms LowerBounds.not_cubeSeparatedGoal_of_selectorProvenance
#print axioms LowerBounds.not_cubeRefute_of_selectorProvenanceCubeSound
#print axioms LowerBounds.false_of_abstractGapCubeSeparatedWitnessPayload
#print axioms LowerBounds.gapTarget_yesDensity_eq_yesInputSet_density
#print axioms LowerBounds.yesDensity_le_inv_of_abstractGapTargetedPayload_of_baseWitness_nil
#print axioms LowerBounds.yesDensity_le_inv_of_dagCanonicalPayload_of_baseWitness_nil
#print axioms LowerBounds.dag_payload_baseWitness_nonempty_of_yesDensity_gt_inv
#print axioms LowerBounds.gapTarget_yesDensity_le_circuitCountBound_mul_three_quarters_pow
#print axioms LowerBounds.empty_witness_admissible_of_gapTargetedSingletonDensityPayload_of_shannon_bound
#print axioms LowerBounds.mismatchSet_false_indicator_eq
#print axioms LowerBounds.approxClass_does_not_imply_small_mismatch
#print axioms AC0AtlasBridge.boundedAtlasScenarioProvider_of_semanticSwitchingCertificateProvider
#print axioms AC0AtlasBridge.scenarioBudgetProvider_of_semanticSwitchingCertificateProvider
#print axioms AC0AtlasBridge.boundedAtlasScenarioProvider_of_formulaSemanticMultiSwitchingProvider_internal
#print axioms AC0AtlasBridge.scenarioBudgetProvider_of_formulaSemanticMultiSwitchingProvider_internal
#print axioms Magnification.formulaSemanticLinkPartial_of_provider
#print axioms Magnification.formula_witness_yields_polylog_support_of_multiswitching_contract
#print axioms Magnification.small_local_core_shrinks_under_restrictions_of_multiswitching_contract
#print axioms Magnification.alive_card_quarter_bound_of_multiswitching_contract
#print axioms Magnification.formula_support_core_steps_of_multiswitching_contract
#print axioms Magnification.formula_support_bounds_internal_of_core_steps
#print axioms Magnification.formula_support_bounds_of_extracted_local_core_provider
#print axioms Magnification.formulaRestrictionCertificateData_of_generic_extracted_local_core_provider
#print axioms Magnification.multiswitching_contract_of_semantic_provider_and_support_bounds
#print axioms Magnification.multiswitching_contract_of_semantic_provider_and_core_steps
#print axioms Magnification.multiswitching_contract_internalized_of_support_bounds
#print axioms Magnification.formula_support_bounds_and_semantic_link_from_multiswitching
#print axioms Magnification.formula_support_bounds_and_semantic_link_of_semantic_provider_and_support_bounds
#print axioms Magnification.formula_support_bounds_and_semantic_link_of_support_bounds
#print axioms Magnification.extracted_local_core_provider_of_multiswitching_contract
#print axioms Magnification.generic_extracted_local_core_provider_of_multiswitching_contract
#print axioms Magnification.solverDecideFacts_stable_of_current_extracted_restriction
#print axioms Magnification.promisePreservingWeakGenericExtractedLocalCoreProvider_of_supportBounds
#print axioms Magnification.promisePreservingWeakGenericExtractedLocalCoreProvider_of_multiswitching_contract
#print axioms Magnification.weakGenericExtractedLocalCoreProvider_of_generic
#print axioms Magnification.weakGenericExtractedLocalCore_of_semantic_switching_certificate_and_extraction
#print axioms Magnification.weakGenericExtractedLocalCoreProvider_of_semantic_switching_certificate_provider_and_extraction
#print axioms Magnification.weakGenericExtractedLocalCoreProvider_of_semantic_provider_and_extraction
#print axioms Magnification.promisePreservingWeakGenericExtractedLocalCoreProvider_of_generic
#print axioms Magnification.promisePreservingWeakGenericExtractedLocalCoreProvider_of_weak_provider_and_preservation
#print axioms Magnification.genericRestrictedLocalBehaviorTransport_of_core
#print axioms Magnification.genericRestrictedLocalBehaviorTransport_of_weak_core
#print axioms Magnification.globalization_of_decision_preservation_on_promise
#print axioms Magnification.globalization_probe_of_decision_preservation
#print axioms Magnification.globalization_of_decision_preservation_on_promise_weak
#print axioms Magnification.globalization_probe_of_weak_decision_preservation
#print axioms Magnification.solvesPromise_of_promisePreservingWeakGenericExtractedLocalCore
#print axioms Magnification.restrictedBehaviorDecisionPreservationOnPromise_of_generic_extracted_local_core
#print axioms Magnification.globalization_of_generic_extracted_local_core
#print axioms Magnification.genericRestrictedBehaviorProvider_of_generic_extracted_local_core_provider_and_transport
#print axioms Magnification.weakGenericRestrictedBehaviorProvider_of_weak_generic_extracted_local_core_provider_and_transport
#print axioms Magnification.genericRestrictedLocalCertificateProvider_of_generic_extracted_local_core_provider_and_transport
#print axioms Magnification.structuredLocalityProviderPartial_of_generic_extracted_local_core_provider
#print axioms Magnification.structuredLocalityProviderPartial_of_generic_restricted_behavior_provider_and_globalize
#print axioms Magnification.structuredLocalityProviderPartial_of_weak_generic_restricted_behavior_provider_and_globalize
#print axioms Magnification.structuredLocalityProviderPartial_of_promisePreservingWeakGenericCoreProvider_and_behavior_transport
#print axioms Magnification.structuredLocalityProviderPartial_of_promisePreservingWeakGenericCoreProvider
#print axioms Magnification.structuredLocalityProviderPartial_of_supportBounds_via_promisePreservingWeakCore
#print axioms Magnification.structuredLocalityProviderPartial_of_generic_restricted_local_certificate_provider
#print axioms Magnification.structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_and_transport
#print axioms Magnification.structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_and_behavior_transport
#print axioms Magnification.structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_and_behavior_transport_and_globalize
#print axioms Magnification.structuredLocalityProviderPartial_of_weak_generic_extracted_local_core_provider_and_behavior_transport_and_globalize
#print axioms Magnification.structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_via_promisePreservingWeakCore
#print axioms Magnification.structuredLocalityProviderPartial_of_extracted_local_core_provider
#print axioms Magnification.structuredLocalityProviderPartial_of_multiswitching_contract_via_extracted_local_core
#print axioms Magnification.structuredLocalityProviderPartial_of_multiswitching_contract_via_generic_extracted_local_core
#print axioms Magnification.structuredLocalityProviderPartial_of_multiswitching_contract_via_promisePreservingWeakCore
#print axioms LowerBounds.LB_Formulas_core_partial_of_multiSwitching
#print axioms LowerBounds.LB_Formulas_core_partial_of_multiSwitching_provider
#print axioms LowerBounds.LB_Formulas_core_partial_closed
#print axioms LowerBounds.LB_Formulas_core_partial_fully_closed
#print axioms LowerBounds.LB_Formulas_core_partial_fully_closed_noExists
#print axioms LowerBounds.LB_Formulas_core_partial_fully_closed_of_syntacticLift
#print axioms LowerBounds.LB_Formulas_core_partial_fully_closed_noExists_of_syntacticLift
#print axioms LowerBounds.LB_Formulas_core_partial_fully_closed_iff_noExists
#print axioms LowerBounds.LB_Formulas_core_partial_closed_of_provider
#print axioms LowerBounds.LB_Formulas_core_partial_closed_internalized
#print axioms LowerBounds.LB_Formulas_core_partial_closed_of_syntacticLift_provider
#print axioms LowerBounds.LB_Formulas_core_partial_constructive_closed_of_provider
#print axioms LowerBounds.false_of_smallAC0Params_and_large_AC0Family
#print axioms LowerBounds.false_of_smallAC0Params_and_easyFamilyData
#print axioms LowerBounds.false_of_enrichedSmallAC0PackagePartial
#print axioms LowerBounds.not_exists_enrichedSmallAC0PackagePartial
#print axioms Magnification.ac0_statement_from_pipeline_partial_closed
#print axioms Magnification.ac0_statement_from_pipeline_partial_providerClosed
#print axioms Magnification.ac0_statement_from_pipeline_partial_internalized
#print axioms Magnification.ac0_statement_from_pipeline_partial_providerClosed_of_syntacticLift
#print axioms Magnification.ac0_statement_from_pipeline_partial_constructive_providerClosed
#print axioms Magnification.ac0_statement_from_pipeline_partial_fully_closed
#print axioms Magnification.ac0_statement_exists_false_from_pipeline_partial_fully_closed
#print axioms Magnification.ac0_statement_from_pipeline_partial_fully_closed_of_syntacticLift
#print axioms Magnification.ac0_statement_exists_false_from_pipeline_partial_fully_closed_of_syntacticLift
#print axioms Magnification.ac0_statement_fully_closed_iff_noExists

section DeprecatedAC0CompatibilityAxiomAudit

-- Keep the historical enriched-package aliases audited without emitting
-- deprecation warnings from these intentional compatibility checks.
set_option linter.deprecated false

#print axioms LowerBounds.gapPartialMCSP_no_semantic_AC0_solver
#print axioms LowerBounds.gapPartialMCSP_no_syntactic_AC0_solver
#print axioms LowerBounds.gapPartialMCSP_no_constructive_AC0_solver
#print axioms LowerBounds.gapPartialMCSP_not_in_AC0
#print axioms LowerBounds.gapPartialMCSP_notInSmallAC0_of_not_in_AC0
#print axioms LowerBounds.gapPartialMCSP_not_in_AC0_iff_notInSmallAC0

end DeprecatedAC0CompatibilityAxiomAudit

#print axioms LowerBounds.noSmallLocalCircuitSolver_partial_constructive
#print axioms LowerBounds.antiChecker_testset_incompatibility_local_partial_constructive

-- Companion promise-route conclusion negations at the canonical asymptotic
-- instantiation.  Together with the in-build general theorem
-- `isoStrong_conclusion_negative_general` (in `Tests/GeneralIsoStrongNoGoProbe.lean`,
-- which subsumes the archived canonical `isoStrong_conclusion_negative_for_canonical`),
-- these close the canonical-track conclusion side.
#print axioms Tests.PromiseRouteConclusionProbe.promiseYesCertificate_conclusion_negative_for_canonical
#print axioms Tests.PromiseRouteConclusionProbe.promiseYesWeak_conclusion_negative_for_canonical
