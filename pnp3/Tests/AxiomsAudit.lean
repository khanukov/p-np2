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
import Complexity.TMVerifier.TuringToolkit.FrameShuttleProbe
import Complexity.TMVerifier.TuringToolkit.GateOneExamples
import Complexity.TMVerifier.TuringToolkit.GateOneRouting
import Complexity.TMVerifier.TuringToolkit.GateOneReadBExamples
import Complexity.TMVerifier.TuringToolkit.GateOneInstallScanExamples
import Complexity.TMVerifier.TuringToolkit.GateOneProbeInstallExamples
import Complexity.TMVerifier.TuringToolkit.GateOneWalkExamples
import Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariantExamples
import Complexity.TMVerifier.TuringToolkit.GateOneWalkDriverExamples
import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernel
import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernelExamples
import Complexity.TMVerifier.TuringToolkit.GateOneRepairDriver
import Complexity.TMVerifier.TuringToolkit.GateOneRepairExamples
import Complexity.TMVerifier.TuringToolkit.GateOneIndexRound
import Complexity.TMVerifier.TuringToolkit.GateOnePassAControl
import Complexity.TMVerifier.TuringToolkit.GateOnePassAEntryExamples
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkInstallAtoms
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkKernel
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkInvariant
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkRound
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkDriver
import Complexity.TMVerifier.TuringToolkit.GateOneARepair
import Complexity.TMVerifier.TuringToolkit.GateOneAResult
import Complexity.TMVerifier.TuringToolkit.GateOneOutputKernel
import Complexity.TMVerifier.TuringToolkit.GateOneOutputAccept
import Complexity.TMVerifier.TuringToolkit.GateOneTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOnePassBTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOnePassBTerminalRepairTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOnePassBDriverTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOnePassATraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOnePassARoundTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOnePassADriverTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneARepairTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneOutputDoneTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneRouteRewindTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneUnaryARepairTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneFiveTagTraceSafety
import Complexity.TMVerifier.TuringToolkit.GateNLocateGrammar
import Complexity.TMVerifier.TuringToolkit.GateNFixedDelegateRelocation
import Complexity.TMVerifier.TuringToolkit.GateNFrameShuttle
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqListRunExamples
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAccept
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAcceptExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoopExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriverExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemanticsExamples
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalControl
import Complexity.TMVerifier.TuringToolkit.GateNEncodingExamples
import Complexity.TMVerifier.TuringToolkit.GateNTapeStateExamples
import Complexity.TMVerifier.TuringToolkit.GateNFirstInstallBridge
import Complexity.TMVerifier.TuringToolkit.GateNScratchBootstrap
import Complexity.TMVerifier.TuringToolkit.GateNBoundaryShuttle
import Complexity.TMVerifier.TuringToolkit.GateNBodyRound
import Complexity.TMVerifier.TuringToolkit.GateNRelocationExamples
import Complexity.Uniform.V1.Examples
import Complexity.DagGadgets
import Tests.UniformV1CircuitEncodingSurfaceTests

/-!
  pnp3/Tests/AxiomsAudit.lean

  Тест-аудит: выводим список аксиом, от которых зависят ключевые теоремы.
  Этот файл компилируется вместе с проектом, чтобы случайные зависимости
  (например, от неожиданных внешних аксиом) были заметны сразу.
-/

open Pnp3
open Pnp3.ComplexityInterfaces
open Pnp3.Magnification

section DagBundleComposeAxiomAudit

#print axioms Pnp3.ComplexityInterfaces.DagCircuit.substBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.substBundle_output_no_growth
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.asCircuit_substBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_substBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.identityBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.identityBundle_output
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_identityBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.DagBundle.evalFun_apply
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalFun_identityBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.iterateBundle_zero
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.iterateBundle_succ
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.iterateBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_iterateBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.iterateBundle_zero_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.iterateBundle_one_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.iterateBundle_two_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_iterateBundle_zero
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_iterateBundle_one
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_iterateBundle_two
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.projectionBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_projectionBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.constantBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_constantBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.notCircuit_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.size_notCircuit
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.eval_notCircuit
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.andCircuit_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.size_andCircuit
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.eval_andCircuit
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.orCircuit_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.size_orCircuit
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.eval_orCircuit
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.muxCircuit_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.size_muxCircuit
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.eval_muxCircuit
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.notBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_notBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.andBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_andBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.orBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_orBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.muxBundle_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_muxBundle
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.muxBundle_truthTable
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.doubleNot_iteration
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.doubleNot_false_literal

end DagBundleComposeAxiomAudit

section UniformV1CircuitEncodingAxiomAudit

#print axioms Pnp3.Complexity.Uniform.V1.Circuit.symbolRails_cases
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_symbolRails_cases
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.decodeSymbol_roundtrip
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_decodeSymbol_roundtrip
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.symbolRails_injective
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_symbolRails_injective
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.symbolRails_not_malformed
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_symbolRails_not_malformed
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.configIndex_layout
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_configIndex_layout
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.configIndex_ranges
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_configIndex_ranges
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.configIndex_injective
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_configIndex_injective
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.configIndex_disjoint
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_configIndex_disjoint
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.encodeConfig_state
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_encodeConfig_state
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.encodeConfig_head
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_encodeConfig_head
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.encodeConfig_tapePresent
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_encodeConfig_tapePresent
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.encodeConfig_tapeValue
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_encodeConfig_tapeValue
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.encodeConfig_tape_decode
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_encodeConfig_tape_decode
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.encodeConfig_state_unique
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_encodeConfig_state_unique
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.encodeConfig_head_unique
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_encodeConfig_head_unique
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.Spec_tape_decode
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_Spec_tape_decode
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.Spec_tape_not_malformed
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_Spec_tape_not_malformed
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.initialBundle_gates
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_initialBundle_gates
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.initialBundle_spec
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_initialBundle_spec
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.initialBundle_asCircuit_size
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_initialBundle_asCircuit_size
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.initialBundle_output_size
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_initialBundle_output_size
#print axioms Pnp3.Complexity.Uniform.V1.Circuit.initialBundle_blank_distinction
#print axioms Pnp3.Tests.UniformV1CircuitEncoding.check_initialBundle_blank_distinction

end UniformV1CircuitEncodingAxiomAudit

section UniformV1AxiomAudit

#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.step_accept
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.step_reject
#print axioms Pnp3.Complexity.Uniform.V1.moveHead_left_zero
#print axioms Pnp3.Complexity.Uniform.V1.moveHead_right_last
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig_accept
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig_reject
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.run_add
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.run_accept
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.run_reject
#print axioms Pnp3.Complexity.Uniform.V1.initialConfig_tape_input
#print axioms Pnp3.Complexity.Uniform.V1.initialConfig_tape_padding
#print axioms Pnp3.Complexity.Uniform.V1.acceptsAt_budget_iff_acceptsWithin
#print axioms Pnp3.Complexity.Uniform.V1.rejectsAt_budget_iff_rejectsWithin
#print axioms Pnp3.Complexity.Uniform.V1.not_acceptsAt_and_rejectsAt
#print axioms Pnp3.Complexity.Uniform.V1.not_acceptsWithin_and_rejectsWithin
#print axioms Pnp3.Complexity.Uniform.V1.decidesAt_budget_iff_decidesWithin
#print axioms Pnp3.Complexity.Uniform.V1.not_decidesAt_true_and_false
#print axioms Pnp3.Complexity.Uniform.V1.not_decidesWithin_true_and_false
#print axioms Pnp3.Complexity.Uniform.V1.polyClock_exponent_zero
#print axioms Pnp3.Complexity.Uniform.V1.polyClock_zero_zero
#print axioms Pnp3.Complexity.Uniform.V1.polyClock_input_zero
#print axioms Pnp3.Complexity.Uniform.V1.polyClock_exponent_one
#print axioms Pnp3.Complexity.Uniform.V1.polyClock_pos
#print axioms Pnp3.Complexity.Uniform.V1.uniformP_iff_exists_decidesAt
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.swap_step
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.swap_stepConfig
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.swap_run
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.swap_acceptsAt_iff_rejectsAt
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.swap_rejectsAt_iff_acceptsAt
#print axioms Pnp3.Complexity.Uniform.V1.UniformTM.swap_decidesWithin
#print axioms Pnp3.Complexity.Uniform.V1.uniformP_complement
#print axioms Pnp3.Complexity.Uniform.V1.allAccept_acceptsAt
#print axioms Pnp3.Complexity.Uniform.V1.allAccept_acceptsWithin
#print axioms Pnp3.Complexity.Uniform.V1.allReject_rejectsAt
#print axioms Pnp3.Complexity.Uniform.V1.allReject_rejectsWithin
#print axioms Pnp3.Complexity.Uniform.V1.firstBit_acceptsAt_iff
#print axioms Pnp3.Complexity.Uniform.V1.firstBit_rejectsAt_iff
#print axioms Pnp3.Complexity.Uniform.V1.firstBit_acceptsWithin_iff
#print axioms Pnp3.Complexity.Uniform.V1.firstBit_rejectsWithin_iff
#print axioms Pnp3.Complexity.Uniform.V1.firstBit_decidesAt
#print axioms Pnp3.Complexity.Uniform.V1.firstBit_decidesWithin
#print axioms Pnp3.Complexity.Uniform.V1.firstBit_true_verdict
#print axioms Pnp3.Complexity.Uniform.V1.firstBit_false_verdict
#print axioms Pnp3.Complexity.Uniform.V1.lengthParity_decidesAt
#print axioms Pnp3.Complexity.Uniform.V1.lengthParity_decidesWithin
#print axioms Pnp3.Complexity.Uniform.V1.lengthParity_empty_verdict
#print axioms Pnp3.Complexity.Uniform.V1.lengthParity_one_verdict
#print axioms Pnp3.Complexity.Uniform.V1.lengthParity_two_verdict
#print axioms Pnp3.Complexity.Uniform.V1.nonterminal_run_state
#print axioms Pnp3.Complexity.Uniform.V1.nonterminal_acceptFlag_false
#print axioms Pnp3.Complexity.Uniform.V1.nonterminal_not_rejectsWithin
#print axioms Pnp3.Complexity.Uniform.V1.nonterminal_not_acceptsWithin
#print axioms Pnp3.Complexity.Uniform.V1.nonterminal_not_decidesWithin_false
#print axioms Pnp3.Complexity.Uniform.V1.nonterminal_not_decidesWithin_true
#print axioms Pnp3.Complexity.Uniform.V1.nonterminal_timeout_counterexample
#print axioms Pnp3.Complexity.Uniform.V1.uniformP_constTrue
#print axioms Pnp3.Complexity.Uniform.V1.uniformP_constFalse
#print axioms Pnp3.Complexity.Uniform.V1.uniformP_firstBit
#print axioms Pnp3.Complexity.Uniform.V1.uniformP_lengthParity

end UniformV1AxiomAudit

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
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revSkipToBoundary
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revSeekAcrossBoundary
#print axioms Internal.PsubsetPpoly.TM.FrameScan.writeFrame4_apply
#print axioms Internal.PsubsetPpoly.TM.FrameScan.writeFrame4_frameListTape
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameWriter.writeMacrostep
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameWriter.writeFrameOnList
#print axioms Internal.PsubsetPpoly.TM.FrameScan.revProbeCS_scan_word
#print axioms Internal.PsubsetPpoly.TM.FrameScan.revProbeCS_seek_across_mark
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

-- GN-E2-1a generic source-restoring shuttle: context-dependent right writer,
-- one shared machine/phase/codec, exact list capstone/schedule, and unrelated
-- positive/negative probes.  Infrastructure only; no GNM instance.
#print axioms Internal.PsubsetPpoly.TM.FrameScan.frameListTape_append_blank
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameWriterCtx.writeMacrostep
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameWriterCtx.writeFrameOnList
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameShuttle.shuttleSteps_provenance
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameShuttle.marker_breaks_forwardPath
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameShuttle.shuttleOnList
#print axioms Internal.PsubsetPpoly.TM.FrameScan.FrameShuttle.shuttleOnList_nextBlank
#print axioms Internal.PsubsetPpoly.TM.FrameScan.shuttleProbe_run45
#print axioms Internal.PsubsetPpoly.TM.FrameScan.shuttleProbe_marker_middle_rejected

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

-- GN-1 (2026-08-30), pure infrastructure: the fixed 13-code-compatible
-- multi-gate record/program ABI, exact parsers, and current-value semantics.
-- Deliberately no machine, transition, execution, clock, or acceptance root.
#print axioms Internal.PsubsetPpoly.TM.gnGateFields_input
#print axioms Internal.PsubsetPpoly.TM.gnGateFields_const
#print axioms Internal.PsubsetPpoly.TM.gnGateFields_not
#print axioms Internal.PsubsetPpoly.TM.gnGateFields_and
#print axioms Internal.PsubsetPpoly.TM.gnGateFields_or
#print axioms Internal.PsubsetPpoly.TM.gnFieldEval_input
#print axioms Internal.PsubsetPpoly.TM.gnFieldEval_const
#print axioms Internal.PsubsetPpoly.TM.gnFieldEval_not
#print axioms Internal.PsubsetPpoly.TM.gnFieldEval_and
#print axioms Internal.PsubsetPpoly.TM.gnFieldEval_or
#print axioms Internal.PsubsetPpoly.TM.gnFieldEval_isSome_iff
#print axioms Internal.PsubsetPpoly.TM.g1RecordFrames_length
#print axioms Internal.PsubsetPpoly.TM.encodeGNRecord_length
#print axioms Internal.PsubsetPpoly.TM.decodeGNRecordFrames?_encoded
#print axioms Internal.PsubsetPpoly.TM.decodeGNRecord?_encoded
#print axioms Internal.PsubsetPpoly.TM.encodeGNRecord_injective
#print axioms Internal.PsubsetPpoly.TM.gnAssignFrames_length
#print axioms Internal.PsubsetPpoly.TM.gnSlotFrames_length
#print axioms Internal.PsubsetPpoly.TM.gnRecordsFrames_length
#print axioms Internal.PsubsetPpoly.TM.encodeGNFrames_length
#print axioms Internal.PsubsetPpoly.TM.encodeGN_length
#print axioms Internal.PsubsetPpoly.TM.gnOutputSlots_extent
#print axioms Internal.PsubsetPpoly.TM.gnRecords_extent
#print axioms Internal.PsubsetPpoly.TM.gnFinalOutputFrame_eq
#print axioms Internal.PsubsetPpoly.TM.gnRegions_within_frames
#print axioms Internal.PsubsetPpoly.TM.gnRegions_within_bits
#print axioms Internal.PsubsetPpoly.TM.gnGateOfFields?_gnGateFields
#print axioms Internal.PsubsetPpoly.TM.gnGateFields_canonical
#print axioms Internal.PsubsetPpoly.TM.gnGateOfFields?_eq_some
#print axioms Internal.PsubsetPpoly.TM.gnGateOfFields?_isSome_iff
#print axioms Internal.PsubsetPpoly.TM.decodeGNFrameList?_encodeGNFrames
#print axioms Internal.PsubsetPpoly.TM.decodeGNFrameList?_eq_some
#print axioms Internal.PsubsetPpoly.TM.decodeGNFrameList?_iff
#print axioms Internal.PsubsetPpoly.TM.decodeGN?_encodeGN
#print axioms Internal.PsubsetPpoly.TM.decodeGN?_eq_some
#print axioms Internal.PsubsetPpoly.TM.decodeGN?_iff
#print axioms Internal.PsubsetPpoly.TM.encodeGN_injective
#print axioms Internal.PsubsetPpoly.TM.decodeGN?_reserved_aligned
#print axioms Internal.PsubsetPpoly.TM.gnFieldEval_gnGateFields
#print axioms Internal.PsubsetPpoly.TM.evalGNFields_gates
#print axioms Internal.PsubsetPpoly.TM.evalGNProgramAll_eq_SLProgram_evalAll
#print axioms Internal.PsubsetPpoly.TM.evalGNProgram_eq_SLProgram_eval
#print axioms Internal.PsubsetPpoly.TM.evalGNFields_length
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.capstone_frames_literal
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.capstone_counts
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.capstone_records_decode
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.capstone_decode_and_eval
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.capstone_eval_all
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.empty_program_eval
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.empty_program_eval_all
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_wrong_marker
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_slot_record_mismatch_frames
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_slot_record_mismatch
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_bad_tag_run
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_invalid_input_index
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_prior_index_below_width
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_trailing_frame
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_trailing_frame_frames
#print axioms Internal.PsubsetPpoly.TM.GNEncodingExamples.reject_reserved_mid

-- GN-2 (2026-08-30), pure tape-state infrastructure.  Direct theorem roots;
-- no machine, transition, run, clock, acceptance, or relocation theorem.
#print axioms Internal.PsubsetPpoly.TM.gnIndex_lt_length
#print axioms Internal.PsubsetPpoly.TM.gnNat_le_sum
#print axioms Internal.PsubsetPpoly.TM.gnUniformRecordsFrames_nil
#print axioms Internal.PsubsetPpoly.TM.gnUniformRecordsFrames_length
#print axioms Internal.PsubsetPpoly.TM.gnRecordsFrames_bof
#print axioms Internal.PsubsetPpoly.TM.gnRecordsAtFrames_nil
#print axioms Internal.PsubsetPpoly.TM.gnRecordsAtFrames_zero
#print axioms Internal.PsubsetPpoly.TM.gnRecordsAtFrames_length
#print axioms Internal.PsubsetPpoly.TM.gnRecordsAtFrames_split
#print axioms Internal.PsubsetPpoly.TM.gnRecordsAtFrames_succ_split
#print axioms Internal.PsubsetPpoly.TM.gnRecordsAtFrames_all_spent
#print axioms Internal.PsubsetPpoly.TM.gnRecordsAtFrames_count_cursor
#print axioms Internal.PsubsetPpoly.TM.gnRecordsAtFrames_count_spent
#print axioms Internal.PsubsetPpoly.TM.encodeGNAtFrames_shape
#print axioms Internal.PsubsetPpoly.TM.encodeGNAtFrames_zero
#print axioms Internal.PsubsetPpoly.TM.encodeGNAt_zero
#print axioms Internal.PsubsetPpoly.TM.encodeGNAtFrames_length
#print axioms Internal.PsubsetPpoly.TM.encodeGNAt_length
#print axioms Internal.PsubsetPpoly.TM.encodeGNAt_regions
#print axioms Internal.PsubsetPpoly.TM.gnReadCurrentValues_exact
#print axioms Internal.PsubsetPpoly.TM.gnSelectedGate?_exact
#print axioms Internal.PsubsetPpoly.TM.gnSelectedRecord?_exact
#print axioms Internal.PsubsetPpoly.TM.gnSelectedRecord_decode
#print axioms Internal.PsubsetPpoly.TM.gnSelectedRecord_embedded
#print axioms Internal.PsubsetPpoly.TM.gnSelected_index_bound
#print axioms Internal.PsubsetPpoly.TM.gnCurrentValues_length
#print axioms Internal.PsubsetPpoly.TM.gnCurrentWork?_exact
#print axioms Internal.PsubsetPpoly.TM.gnWorkRequest_spec
#print axioms Internal.PsubsetPpoly.TM.gnCommit?_exact
#print axioms Internal.PsubsetPpoly.TM.gnCommit?_terminal
#print axioms Internal.PsubsetPpoly.TM.encodeGNAt_commit_shape
#print axioms Internal.PsubsetPpoly.TM.encodeGNAt_commit_length
#print axioms Internal.PsubsetPpoly.TM.encodeGNAt_commit_inputs
#print axioms Internal.PsubsetPpoly.TM.encodeGNAt_commit_records
#print axioms Internal.PsubsetPpoly.TM.gnFinalValue_before_terminal
#print axioms Internal.PsubsetPpoly.TM.gnFinalValue_terminal_commit
#print axioms Internal.PsubsetPpoly.TM.gnFinalValue_nonterminal_commit
#print axioms Internal.PsubsetPpoly.TM.GateNTapeState.initial
#print axioms Internal.PsubsetPpoly.TM.GateNTapeState.step
#print axioms Internal.PsubsetPpoly.TM.GateNTapeState.cursor_count
#print axioms Internal.PsubsetPpoly.TM.GateNTapeState.initial_parser
#print axioms Internal.PsubsetPpoly.TM.gnTapeFrames_scratch
#print axioms Internal.PsubsetPpoly.TM.gnTapeCell_scratch_blank
#print axioms Internal.PsubsetPpoly.TM.gnWorkWord_length
#print axioms Internal.PsubsetPpoly.TM.encodeGN_length_eq
#print axioms Internal.PsubsetPpoly.TM.gnRecordSize_le_recordsLength
#print axioms Internal.PsubsetPpoly.TM.gnWorkWord_add_sixteen_le_input
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_initial_literal
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_initial_state
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_first_literal
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_first_commit
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_first_state
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_first_values
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_second_selected
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_second_record_decode
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_second_work
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_final_literal
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_second_commit
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_final_state
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_final_values
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_final_output
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_final_terminal
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_lengths
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_eval_consistent
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.capstone_first_scratch_cell_blank
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.tight_work_length
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.tight_input_length
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.tight_bound_eq
#print axioms Internal.PsubsetPpoly.TM.GNTapeStateExamples.tight_bound_seventeen_false

-- GN-3A (2026-08-30), generic local-relocation infrastructure.  The copied
-- footprint is exactly `[0,W+5)`; delegation is transition-tuple equality;
-- there is no GN machine/controller/clock/copier/acceptance theorem.
#print axioms Internal.PsubsetPpoly.TM.gnLocalSpan_le_g1_tapeLength
#print axioms Internal.PsubsetPpoly.TM.gnLocalSpan_final_frame_fits
#print axioms Internal.PsubsetPpoly.TM.gnLocalSpan_four_insufficient
#print axioms Internal.PsubsetPpoly.TM.gnLocalSpan_room_iff
#print axioms Internal.PsubsetPpoly.TM.gnSourceIndex_val
#print axioms Internal.PsubsetPpoly.TM.gnTargetIndex_val
#print axioms Internal.PsubsetPpoly.TM.gnOverlayTape_inside
#print axioms Internal.PsubsetPpoly.TM.gnOverlayTape_outside
#print axioms Internal.PsubsetPpoly.TM.gnShiftConfig_state
#print axioms Internal.PsubsetPpoly.TM.gnShiftConfig_state_eq_iff
#print axioms Internal.PsubsetPpoly.TM.gnShiftConfig_head_val
#print axioms Internal.PsubsetPpoly.TM.gnShiftConfig_bit_inside
#print axioms Internal.PsubsetPpoly.TM.gnShiftConfig_bit_outside
#print axioms Internal.PsubsetPpoly.TM.gnShiftConfig_frame_inside
#print axioms Internal.PsubsetPpoly.TM.gnOverlayTape_ext
#print axioms Internal.PsubsetPpoly.TM.gnShiftConfig_ext
#print axioms Internal.PsubsetPpoly.TM.gn_local_step_safe_next_head
#print axioms Internal.PsubsetPpoly.TM.gn_shift_moveHead_val
#print axioms Internal.PsubsetPpoly.TM.gn_shift_write_tape
#print axioms Internal.PsubsetPpoly.TM.gn_delegate_step_shift
#print axioms Internal.PsubsetPpoly.TM.G1RunSafe.empty
#print axioms Internal.PsubsetPpoly.TM.G1RunSafe.succ
#print axioms Internal.PsubsetPpoly.TM.G1RunSafe.add
#print axioms Internal.PsubsetPpoly.TM.G1RunSafe.transport
#print axioms Internal.PsubsetPpoly.TM.G1RunSafe.mono
#print axioms Internal.PsubsetPpoly.TM.G1RunDelegates.mono
#print axioms Internal.PsubsetPpoly.TM.gn_run_safe_endpoint_head
#print axioms Internal.PsubsetPpoly.TM.gn_delegate_run_shift
#print axioms Internal.PsubsetPpoly.TM.gn_delegate_run_shift_outside_prefix
#print axioms Internal.PsubsetPpoly.TM.gn_delegate_run_shift_outside
#print axioms Internal.PsubsetPpoly.TM.gnLocalSpan_room_in_input_of_add_sixteen
#print axioms Internal.PsubsetPpoly.TM.gn_g1_target_room_of_add_sixteen
#print axioms Internal.PsubsetPpoly.TM.gn_g1_target_room_zero_of_add_sixteen
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_inject_injective
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_room
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_head_local
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_source_move
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_step_safe
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_step_delegates
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_source_step_head
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_source_step_move
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.capstone_shifted_one_step
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_run_safe_two
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.cap_run_delegates_two
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.capstone_shifted_short_run
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.capstone_outside_every_prefix
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.capstone_footprint_exact
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.left_zero_head_local
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.left_zero_target_room
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.left_zero_source_next_local
#print axioms Internal.PsubsetPpoly.TM.GNRelocationExamples.capstone_left_zero_unconditional_shift_false

-- S1a, pure layer: the four pass-A residual operations of operand 1 and the
-- bridge from `(tag, operand-2 value, operand-1 value)` to `G1Request.spec`.
-- Pure throughout: no machine, no configuration, no head, no step, no
-- `G1Ctx`, no execution and no correctness claim about the interpreter.  The
-- `const` row of `g1Residual` is filler; every bridge is restricted to
-- non-`const` tags by disequality or explicit tag case, and the counterexample
-- is the concrete
-- canonical request that makes the exclusion load-bearing.  The pass-A
-- control that would consume the residual is deferred to S1b.
#print axioms Internal.PsubsetPpoly.TM.G1Residual.apply_idA
#print axioms Internal.PsubsetPpoly.TM.G1Residual.apply_notA
#print axioms Internal.PsubsetPpoly.TM.G1Residual.apply_constFalse
#print axioms Internal.PsubsetPpoly.TM.G1Residual.apply_constTrue
#print axioms Internal.PsubsetPpoly.TM.G1Residual.card_eq_four
#print axioms Internal.PsubsetPpoly.TM.G1Residual.apply_pairwise_ne
#print axioms Internal.PsubsetPpoly.TM.g1Residual_input
#print axioms Internal.PsubsetPpoly.TM.g1Residual_not
#print axioms Internal.PsubsetPpoly.TM.g1Residual_and_false
#print axioms Internal.PsubsetPpoly.TM.g1Residual_and_true
#print axioms Internal.PsubsetPpoly.TM.g1Residual_or_false
#print axioms Internal.PsubsetPpoly.TM.g1Residual_or_true
#print axioms Internal.PsubsetPpoly.TM.g1Residual_const_filler
#print axioms Internal.PsubsetPpoly.TM.g1Residual_unary_const
#print axioms Internal.PsubsetPpoly.TM.g1Residual_binary_ne
#print axioms Internal.PsubsetPpoly.TM.g1Residual_input_apply
#print axioms Internal.PsubsetPpoly.TM.g1Residual_not_apply
#print axioms Internal.PsubsetPpoly.TM.g1Residual_and_apply
#print axioms Internal.PsubsetPpoly.TM.g1Residual_or_apply
#print axioms Internal.PsubsetPpoly.TM.g1Residual_apply_table
#print axioms Internal.PsubsetPpoly.TM.g1OperandB_input
#print axioms Internal.PsubsetPpoly.TM.g1OperandB_const
#print axioms Internal.PsubsetPpoly.TM.g1OperandB_not
#print axioms Internal.PsubsetPpoly.TM.g1OperandB_and
#print axioms Internal.PsubsetPpoly.TM.g1OperandB_or
#print axioms Internal.PsubsetPpoly.TM.g1OperandB_of_arity_one
#print axioms Internal.PsubsetPpoly.TM.g1OperandB_of_arity_two
#print axioms Internal.PsubsetPpoly.TM.g1OperandB_isSome_of_wellFormed
#print axioms Internal.PsubsetPpoly.TM.g1OperandA_isSome_of_wellFormed
#print axioms Internal.PsubsetPpoly.TM.g1Residual_apply_spec_unary
#print axioms Internal.PsubsetPpoly.TM.g1Residual_apply_spec_binary
#print axioms Internal.PsubsetPpoly.TM.g1Residual_apply_spec
#print axioms Internal.PsubsetPpoly.TM.g1Spec_eq_residual_apply
#print axioms Internal.PsubsetPpoly.TM.g1Residual_input_selects
#print axioms Internal.PsubsetPpoly.TM.g1Residual_not_selects
#print axioms Internal.PsubsetPpoly.TM.g1Residual_const_apply_ne_spec
#print axioms Internal.PsubsetPpoly.TM.g1Residual_spec_capstone

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
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAStart_entry
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAStart_result
#print axioms Internal.PsubsetPpoly.TM.g1Transition_combineStart_output
#print axioms Internal.PsubsetPpoly.TM.g1Transition_outputDone_accept
-- `readAResetStart` is **no longer idle**: Repair-2a makes it the one-step bridge
-- into the repair sweep, writing back what it scans and stepping one cell left
-- into `bRepairSeek .p3` with the whole `G1Ctx` preserved.  It is the only new
-- live activation of that slice, and the machine is still the same fixed
-- zero-parameter program: no runtime argument, no advice, no new state field.
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAResetStart_bridge
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
-- The eleven tuple lemmas of the operand-2 repair sweep, together with the
-- reverse frame table they scrutinise.  The frame-position-`0` decision has
-- **four** outcomes: `spent` is the write handoff, `bof` the terminal handoff,
-- a `G1RepairSkip` frame continues the scan, and every other window — a
-- `blank`, a leftover `cursor`, or one of the three reserved codes, which
-- decode to nothing — enters the *existing* `reject` sink without moving, so
-- the sweep can never cross malformed tape content.  `bRepairDone` enters
-- the `readAStart` boundary; no frame-table row enters any of these five
-- modes, and the only row that does is the `readAResetStart` bridge above.
#print axioms Internal.PsubsetPpoly.TM.g1RepairBackAdvance_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1RepairBackComplete_some
#print axioms Internal.PsubsetPpoly.TM.g1RepairBackComplete_none
#print axioms Internal.PsubsetPpoly.TM.g1RepairBackComplete_reserved
#print axioms Internal.PsubsetPpoly.TM.g1RepairBackComplete_forbidden
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairSeek_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairSeek_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairSeek_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairSeek_p0_spent
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairSeek_p0_bof
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairSeek_p0_skip
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairSeek_p0_bad
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairWrite
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairBack
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairHop
#print axioms Internal.PsubsetPpoly.TM.g1Transition_bRepairDone
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
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_readAStart_entry
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_readAStart_result
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_readAStart_operandB_not_result
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_readAReset_bridge
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
-- the PR2b2 block below, on caller-supplied configurations only.  At that
-- slice no invariant, driver or OOB aggregation existed; they are audited in
-- PR3a–PR3c below.  Repair, pass A, output write and `TM.accepts` remain absent.
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
-- after the right number of rounds.  At that slice the invariant, driver,
-- positive-index read and OOB aggregation did not exist; they are audited in
-- the PR3a–PR3c blocks below.  Repair, pass A, output write and `TM.accepts`
-- remain absent.
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
#print axioms Internal.PsubsetPpoly.TM.g1BLoopSteps_zero
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
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readFramesFinal_count_index
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readFramesFinal_length
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readExample_install_scan_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readExample_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readExample_steps_split
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_vB
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_head
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.readExample_clock_value
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_clock
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.walkExample_framesFinal
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.walkExample_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.walkExample_steps_split
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_two
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_two_vB
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.read_positive_two_clock
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.emptyExample_oob_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.emptyExample_frames
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_empty
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_empty_clock
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oobExample_oob_steps
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oobExample_oob_steps_split
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oobExample_frames
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_nonempty
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_nonempty_head
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.oob_nonempty_clock
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.loopSteps_zero
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.loopSteps_one
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.loopSteps_two
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.loopSteps_three
#print axioms Internal.PsubsetPpoly.TM.G1WalkDriverExamples.loopSteps_two_eq

-- Repair-1: the G1 operand-2 repair control and its generic kernel.  The five
-- repair modes, the reverse repair scanner and the `spent ↦ index` rewrite
-- cycle as genuine instances of the generic kernels, the seven
-- arbitrary-frame-list macros, anchor finish, terminal dispatch and capstone
-- `g1CS_repair_pass_exact` with its closed cost `4m + 13s + 4a + 5`, which is
-- the concrete endpoint of the slice.
-- **The sweep does not cross malformed tape**: `G1RepairSkip` holds for exactly
-- the canonical interior frame kinds, so `g1CS_repair_frame_reject` runs the
-- scan's fourth outcome — a `blank` or a leftover
-- `cursor` sends it to the stable `reject` sink in four genuine steps, with the
-- tape untouched and any `spent` unit behind it left unrepaired — while the
-- three
-- reserved codes, which decode to no frame at all, are pinned at the table
-- level by `g1RepairBackComplete_reserved` above.
-- **Every configuration is caller-supplied here**: `g1_repair_unreachable_forward`
-- and `g1_repair_modes_stuck` show no frame-table row enters the sweep, and
-- nothing in this module mentions `G1M.initialConfig`.  The live entry is the
-- `readAResetStart` bridge, instantiated by the Repair-2a driver audited below.
-- **Deliberately absent from this module**: the request-specific repair
-- driver, any read-to-repair composition, pass A, combine, the
-- output write, and any `TM.accepts`, verdict, full-clock, gate-semantics,
-- acceptance-gate, multi-gate or specification-bridge claim.
#print axioms Internal.PsubsetPpoly.TM.g1_repair_unreachable_forward
#print axioms Internal.PsubsetPpoly.TM.g1_repair_modes_stuck
#print axioms Internal.PsubsetPpoly.TM.g1RepairRevAdvance_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1RepairRevAdvance_reject
#print axioms Internal.PsubsetPpoly.TM.g1RepairStopState_write
#print axioms Internal.PsubsetPpoly.TM.g1RepairStopState_done
#print axioms Internal.PsubsetPpoly.TM.g1RepairStopState_reject
#print axioms Internal.PsubsetPpoly.TM.G1RepairMode.eq
#print axioms Internal.PsubsetPpoly.TM.g1RepairScanner_machine
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_cycle_onList
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_seek_and_repair
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_frame_skip
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_frame_reject
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_frame_reject_idle
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_scan_skip
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_spent_run
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_repairDone
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_finish
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_pass_exact

-- Repair-1b: the all-literal probes of that kernel.  One literal sixteen-frame
-- word — the canonical encoding of `⟨and, 0, 2, [false, true, true]⟩` plus the
-- trailing `blank`, with both operand-2 units consumed — its six split lemmas,
-- the pairwise differences, the literal `spent`/`index` counts, the flipped
-- physical cell `32`, and four exact `G1M` runs on it: the `13`-step cycle
-- (head `35 ↦ 31`), the `37`-step seek+repair (`59 ↦ 31`), the `26`-step
-- two-unit run (`35 ↦ 27`) and the `79`-step whole pass (`59 ↦ 0`) whose
-- endpoint tape is bit-for-bit `encodeG1Frames ⟨and, 0, 2, [false, true,
-- true]⟩ ++ [blank]`.
-- **The narrowed skip predicate is exercised, not bypassed**:
-- `probe_scan_lists_clean` pins that `blank`, `cursor`, `bof` and `spent` are
-- not crossable and that neither canonical scanned list — nor the scanned
-- region as a whole — contains a `blank` or a leftover `cursor`, and
-- `probeTail_beyond_entry` pins that the sixteenth frame
-- — the trailing `blank` — is not crossable, does not occur in the scanned
-- region, and lies entirely to the right of the sweep's entry cell `59`, so it
-- is the kernel's unconstrained, never-read `tail`.
-- **Every configuration is caller-supplied**: every probe starts from an
-- explicit `g1AlignedConfig`, none mentions `G1M.initialConfig`, and
-- the probe stops exactly at `readAStart`; no post-endpoint idle claim remains.
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeInputLen_eq
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probe_safe
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probe_word_cells
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeIndex_eq_encoded
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probe_words_distinct
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probe_counts
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probe_cell32
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeSpent_split
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeIndex_split
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeLeft_skip
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeMid_skip
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probe_scan_lists_clean
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeSpent_scanned_tail
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeTail_beyond_entry
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probe_passSteps
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probe_passSteps_split
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeCycle_split_spent
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeCycle_split_half
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.cycle_probe
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.cycle_probe_ctx
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeRun_split_spent
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.probeRun_split_index
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.run_probe
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.run_probe_tape
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.seek_repair_probe
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.seek_repair_probe_tape
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.pass_probe
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.pass_probe_head
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.pass_probe_tape
#print axioms Internal.PsubsetPpoly.TM.G1RepairKernelExamples.pass_probe_ctx

-- Repair-2a: the request-specific repair driver.  The real layout split
-- `[bof] ++ g1RepairLeft ++ spent^s ++ g1RepairMid ++ g1RepairTail`, its
-- lengths, its `s = 0` value (the canonical word plus the trailing blank) and
-- the repaired word `g1RepairFrames_repaired`, which is **literally** the
-- machine's initial word, not merely a word of the same length.
-- **The narrowed skip predicate is discharged, not assumed**:
-- `g1RepairLeft_skip`/`g1RepairMid_skip` are the kernel's `hleft`/`hmid`, and
-- `g1RepairLeft_clean`/`g1RepairMid_clean` restate them in the contrapositive —
-- no `blank`, no leftover `cursor` in either scanned run.  `g1RepairTail_unread`
-- pins that the tail's `blank` is not crossable, that the scanned region is
-- exactly `g1WalkCursor r arg2 + 1` frames, and that every tail cell lies
-- strictly right of the sweep's entry cell, so the tail is the kernel's
-- unconstrained, never-read argument.
-- `g1CS_repair_sweep_exact` runs the sweep in `4u + 4a1 + 8a + 9s + 22` steps
-- from the post-read handoff at its exact head to head `0` in `readAStart`,
-- tape exactly the canonical word, `G1Ctx` untouched.  Both successful reads
-- compose with it from the **real** `G1M.initialConfig` and meet in the one
-- handoff `g1ReadAConfig r b`; `g1BPassASteps`/`g1ZPassASteps` fit the
-- **unchanged** `g1Clock` with no hypothesis on the request.  The value `b` is
-- the actual `r.vals[r.arg2]`, resolved physically.
-- **The out-of-range boundary is untouched**:
-- `g1CS_readB_positive_oob_unrepaired` pins that it is stable for every extra
-- budget, still carries `m` consumed units, and is a different state from the
-- pass-A handoff.  No repair, no rejection, no verdict is claimed for it.
-- **Deliberately absent from this older repair surface**: operand 1, combine,
-- the output write, and any `TM.accepts`, verdict,
-- full-clock, gate-semantics, acceptance-gate, multi-gate,
-- specification-bridge or padded-tape claim.  The **all-literal** repaired runs
-- from `G1M.initialConfig` are deferred in full to Repair-2b, whose module and
-- probe roots are audited immediately below.
#print axioms Internal.PsubsetPpoly.TM.g1RepairLeft_length
#print axioms Internal.PsubsetPpoly.TM.g1RepairMid_length
#print axioms Internal.PsubsetPpoly.TM.g1RepairTail_length
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_zero
#print axioms Internal.PsubsetPpoly.TM.g1BSpentFrames_repair_split
#print axioms Internal.PsubsetPpoly.TM.g1RepairLeft_skip
#print axioms Internal.PsubsetPpoly.TM.g1RepairMid_skip
#print axioms Internal.PsubsetPpoly.TM.g1Repair_not_skip
#print axioms Internal.PsubsetPpoly.TM.g1RepairLeft_clean
#print axioms Internal.PsubsetPpoly.TM.g1RepairMid_clean
#print axioms Internal.PsubsetPpoly.TM.g1RepairTail_unread
#print axioms Internal.PsubsetPpoly.TM.g1RepairLeft_append
#print axioms Internal.PsubsetPpoly.TM.g1RepairFrames_repaired
#print axioms Internal.PsubsetPpoly.TM.g1RepairSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_sweep_exact
#print axioms Internal.PsubsetPpoly.TM.g1ReadAConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1ReadAConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1ReadAConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1ReadAConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_sweep_readAConfig
#print axioms Internal.PsubsetPpoly.TM.g1BPassASteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1ZPassASteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1BPassASteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ZPassASteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_repaired_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_repaired_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_repaired_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_repaired_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_repaired_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_repaired_tape_initial
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_repaired_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_repaired_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_repaired_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_repaired_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_repaired_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_repaired_common
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_repaired_common_le_clock

-- S1b2a route alignment: `input`/`not` and `const` now enter the canonical
-- Repair-2 rewind and reach head-zero `readAStart` from the real initial
-- configuration.  The constant carries `g1ResultCtx`; the filler residual is
-- not evaluated.  Binary repaired endpoints and OOB behavior are unchanged.
#print axioms Internal.PsubsetPpoly.TM.g1CS_route_rewind_exact
#print axioms Internal.PsubsetPpoly.TM.g1ReadAResultConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1ReadAResultConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1ReadAResultConfig_ctx
#print axioms Internal.PsubsetPpoly.TM.g1ReadAResultConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_unary_repaired_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_const_repaired_exact
#print axioms Internal.PsubsetPpoly.TM.g1UReadASteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ConstReadASteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ReadAState_ne_oob
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_oob_unrepaired

-- Repair-2b: the all-literal repaired reads of that driver.  Three exact `G1M`
-- runs from the **real** `G1M.initialConfig` onto the one canonical pass-A
-- handoff `g1ReadAConfig r true` — `⟨and, 0, 0, [true]⟩` in `172 = 134 + 38`
-- steps, `⟨and, 0, 1, [false, true]⟩` in `294 = 239 + 55` and
-- `⟨and, 0, 2, [false, true, true]⟩` in `400 = 328 + 72` — each with its head,
-- control state, latched `vB`, endpoint word, initial-tape identity, clock
-- bound, plus both arms of the common capstone
-- `g1CS_readB_repaired_common` on literals.
-- **Three lengths are kept apart**: `probe_extents` pins the encoded input length
-- (`44`, `52`, `60`), explicit validation frame-word extent (`48`, `56`, `64`,
-- including the all-false trailing `blank`) and the
-- separately derived physical capacity `G1M.tapeLength (encodeG1 r).length`,
-- whose zero-probe literal is `1037357`.  No root here identifies the physical
-- tape length with the input length.
-- **Nonvacuity is literal**: `zero_repaired_no_net_change` pins no net tape
-- change and an empty rewrite block at `arg2 = 0`; the positive cell theorems
-- pin that the two positive branches genuinely flip a physical cell between the
-- read's terminal tape and the repaired endpoint, `*_selected` pin that the
-- latched bit is the request's own `vals[arg2]`, not `vals[0]`, and
-- `common_branch_literals` pins that the common capstone's branch is real — at
-- the zero-index request the other arm would be `204`, not `172`.
-- **Reuse, not duplication**: the `arg2 = 1` request/read count comes from
-- `GateOneWalkDriverExamples`; the `arg2 = 2` request is the merged
-- `GateOneInstallScanExamples.g1WalkExample`, with endpoint words from Repair-1b.
-- `two_repaired_kernel_words` shows the machine reaches Repair-1b's
-- caller-supplied words from the real initial configuration.
-- **Deliberately absent from the repair-example roots**: operand 1, combine,
-- the output write, and any `TM.accepts`, verdict,
-- full-clock, gate-semantics, acceptance-gate, multi-gate,
-- specification-bridge, out-of-range-repair, non-canonical-word or padded-tape
-- claim.
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.g1ZeroExample_canonical
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.g1ZeroExample_length
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zero_safe
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.one_safe
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.two_safe
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zeroFrames_eq
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zeroFrames_layout
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zeroFrames_counts
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.oneRepairedFrames_eq
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.oneRepairedFrames_counts
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.twoFrames_eq
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.twoRepaired_counts
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.probe_extents
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.repairSteps_zero
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.repairSteps_one
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.repairSteps_two
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.repairSteps_splits
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zeroExample_steps
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zero_repaired
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zero_repaired_projections
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zero_selected
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zero_repaired_tape
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zero_repaired_no_net_change
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.zero_repaired_clock
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.oneExample_steps
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.one_repaired
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.one_repaired_projections
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.one_selected
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.one_repaired_tape
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.one_repaired_cell28
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.one_repaired_clock
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.twoExample_steps
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.two_repaired
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.two_repaired_projections
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.two_selected
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.two_repaired_tape
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.two_repaired_kernel_words
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.two_repaired_cell32
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.two_repaired_clock
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.common_arms_distinct
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.common_branch_literals
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.common_zero_arm
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.common_positive_arm
#print axioms Internal.PsubsetPpoly.TM.G1RepairExamples.common_branch_clock

-- S1b2b, the live pass-A entry.  Twelve pass-A modes, the frame rows
-- that join them, the residual view of the two spare context bits, the result
-- convention, the operation latch, and the executed capstones of all of it on
-- caller-supplied configurations and from the real initial configuration.
-- Every public root of the slice is audited directly here, not only through
-- the capstones that use it.
--
-- `g1Advance_passA` rules out frame-table entry from outside the family;
-- `g1Transition_passA_door` names live `readAStart` as the sole external door,
-- while the predecessor and install-exit theorems prevent residual contexts
-- from being treated as results.
--
-- **No new state, field or advice.**  `res`/`withRes` are a *view* of the
-- existing `pass`/`crossed` pair; `G1Ctx` is the same three Booleans, `vB` is
-- untouched by the latch, and the machine keeps its one closed clock.  The
-- `const` filler row of `g1Residual` is never consumed: `g1AOpMode .const` is
-- `reject`, and `g1CS_passA_const_reject_exact` executes that — a *local* fact
-- about a configuration nothing reaches, not a claim that `const` requests are
-- rejected.  `g1ResultCtx_eq_andFalse_res` records the one real aliasing the
-- two-bit view creates and is the constraint S1b2 inherits.
--
-- This section stops at the residual boundary.  S4's live installation entry,
-- writer and OOB capstones are audited with the installation atoms below.
#print axioms Internal.PsubsetPpoly.TM.G1Ctx.res_withRes
#print axioms Internal.PsubsetPpoly.TM.G1Ctx.withRes_vB
#print axioms Internal.PsubsetPpoly.TM.G1Ctx.withVB_res
#print axioms Internal.PsubsetPpoly.TM.G1Ctx.withRes_res
#print axioms Internal.PsubsetPpoly.TM.g1ResultCtx_pass
#print axioms Internal.PsubsetPpoly.TM.g1ResultCtx_vB
#print axioms Internal.PsubsetPpoly.TM.g1ResultCtx_ne_entry
#print axioms Internal.PsubsetPpoly.TM.g1ResultCtx_eq_andFalse_res
#print axioms Internal.PsubsetPpoly.TM.g1ResultCtx_pass_eq_orTrue_res
#print axioms Internal.PsubsetPpoly.TM.G1PassAMode.not_reject
#print axioms Internal.PsubsetPpoly.TM.g1Advance_passA
#print axioms Internal.PsubsetPpoly.TM.g1Complete_passA
#print axioms Internal.PsubsetPpoly.TM.g1_readAStart_unreachable
#print axioms Internal.PsubsetPpoly.TM.g1_aInstallStart_unreachable
#print axioms Internal.PsubsetPpoly.TM.g1Complete_ne_readAStart
#print axioms Internal.PsubsetPpoly.TM.g1Complete_ne_aInstallStart
#print axioms Internal.PsubsetPpoly.TM.g1AOpMode_const
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aOp
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aInstallStart_live
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAStart_entry
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAStart_result
#print axioms Internal.PsubsetPpoly.TM.g1Transition_passA_door
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAStart_unique
#print axioms Internal.PsubsetPpoly.TM.g1_aResultStart_unreachable
#print axioms Internal.PsubsetPpoly.TM.g1Complete_ne_aResultStart
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aResultStart_apply
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aResultStart_unique
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aResultStart_iff
#print axioms Internal.PsubsetPpoly.TM.g1Transition_readAStart_iff
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aInstallStart_unique
#print axioms Internal.PsubsetPpoly.TM.g1ATagRoute_advance
#print axioms Internal.PsubsetPpoly.TM.g1ATagRoute_validPath
#print axioms Internal.PsubsetPpoly.TM.g1ATagRoute_advance_const
#print axioms Internal.PsubsetPpoly.TM.g1ATagRoute_rejectPath
#print axioms Internal.PsubsetPpoly.TM.g1ATagRoute_unreachable
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_aOp
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_aInstallStart
#print axioms Internal.PsubsetPpoly.TM.g1CS_aTagRescan_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_passA_entry_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_passA_entry_ctx
#print axioms Internal.PsubsetPpoly.TM.g1CS_passA_const_reject_exact
#print axioms Internal.PsubsetPpoly.TM.g1ABofConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1ABofConfig_ctx
#print axioms Internal.PsubsetPpoly.TM.g1AInstallConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1AInstallConfig_res
#print axioms Internal.PsubsetPpoly.TM.g1AInstallConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1AInstallSeekConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1AInstallSeekConfig_res
#print axioms Internal.PsubsetPpoly.TM.g1AInstallSeekConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1CombineConfig_ctx
#print axioms Internal.PsubsetPpoly.TM.g1CS_activate_unary_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_activate_binary_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_activate_binary_not_result
#print axioms Internal.PsubsetPpoly.TM.g1CS_activate_const_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_passA_entry_initial_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aInstall_entry_initial_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_install_unary_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_install_binary_exact
#print axioms Internal.PsubsetPpoly.TM.g1UActivatedSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1BActivatedSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ConstActivatedSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.examples_canonical
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.example_lengths
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.probe_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.input_latch
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.not_latch
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.and_false_latch
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.and_true_latch
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.or_true_latch
#print axioms Internal.PsubsetPpoly.TM.G1PassAControlExamples.const_reject
#print axioms
  Internal.PsubsetPpoly.TM.G1PassAControlExamples.latched_residuals_distinct

-- S1c, the ten real-initial pass-A entry probes.  Every public definition and
-- theorem in `GateOnePassAEntryExamples` is a direct root.  The runs stop at
-- `aInstallStart` or the const `combineStart` bypass; they add no operand-1
-- read, combine execution, output, acceptance, advice or OOB/reject theorem.
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqInputFalse
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqInputTrue
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqNotFalse
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqNotTrue
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqAndFalse
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqAndTrue
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqOrFalse
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqOrTrue
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqConstFalse
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.reqConstTrue
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.requests_canonical
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.selected_literals
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.probe_extents
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.input_false_install
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.input_true_install
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.not_false_install
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.not_true_install
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.and_false_install
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.and_true_install
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.or_false_install
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.or_true_install
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.const_false_result
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.const_true_result
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.endpoint_heads
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.endpoint_states
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.endpoint_tapes
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.and_false_no_wrong_result
#print axioms Internal.PsubsetPpoly.TM.G1PassAEntryExamples.probe_clocks

-- S4 (2026-08-29), live operand-A cursor installation.  The S3b1 atoms remain
-- direct roots, followed by every live entry, real-initial, exact endpoint,
-- OOB, clock, literal and no-wrong-exit theorem.  The writer stops at
-- `aSeekOut .p3`; no normal-walk or repair step executes.
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aInstallAtoms_dormant
#print axioms Internal.PsubsetPpoly.TM.g1Complete_aInstallAtoms_dormant
#print axioms Internal.PsubsetPpoly.TM.g1Complete_aInstallAtoms_reserved
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aLatch
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aIns_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aIns_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aIns_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aIns_p0
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aInstallAtoms_entry_closure
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aInsSeek_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aProbe_data
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aInsSeek_rows
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aProbe_rows
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aInstallAtoms_rejects
#print axioms Internal.PsubsetPpoly.TM.g1AInstallCursorWriter_machine
#print axioms Internal.PsubsetPpoly.TM.g1CS_aInstall_scan
#print axioms Internal.PsubsetPpoly.TM.g1CS_aProbe_latch
#print axioms Internal.PsubsetPpoly.TM.g1CS_aProbe_oob
#print axioms Internal.PsubsetPpoly.TM.g1CS_aInstall_reserved_1101_reject
#print axioms Internal.PsubsetPpoly.TM.g1CS_aInstall_cursor
#print axioms Internal.PsubsetPpoly.TM.g1AInstallSkippedFrames_length
#print axioms Internal.PsubsetPpoly.TM.g1APostWriterConfig_res
#print axioms Internal.PsubsetPpoly.TM.g1APostWriterConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1APostWriterConfig_mode
#print axioms Internal.PsubsetPpoly.TM.g1CS_aInstall_success_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aInstall_oob_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aCursor_unary_initial_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aCursor_binary_initial_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aInstall_unary_oob_initial_exact
#print axioms Internal.PsubsetPpoly.TM.g1A_binary_success_not_empty
#print axioms Internal.PsubsetPpoly.TM.g1AFirstCursorFrames_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1APostWriterConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1APostWriterConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1APostWriterConfig_no_wrong_exit
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryCursorSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ABinaryCursorSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryOOBSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_aCursor_unary_no_wrong_exit
#print axioms Internal.PsubsetPpoly.TM.g1CS_aCursor_binary_no_wrong_exit
#print axioms Internal.PsubsetPpoly.TM.G1ALiveInstallExamples.requests_canonical
#print axioms Internal.PsubsetPpoly.TM.G1ALiveInstallExamples.input_false_cursor_exact
#print axioms Internal.PsubsetPpoly.TM.G1ALiveInstallExamples.not_true_cursor_exact
#print axioms Internal.PsubsetPpoly.TM.G1ALiveInstallExamples.and_false_cursor_exact
#print axioms Internal.PsubsetPpoly.TM.G1ALiveInstallExamples.or_true_cursor_exact
#print axioms Internal.PsubsetPpoly.TM.G1ALiveInstallExamples.input_empty_oob_exact
#print axioms Internal.PsubsetPpoly.TM.G1ALiveInstallExamples.literal_clock_bounds

-- S5 (2026-08-29): every direct theorem root of the pure operand-A walk
-- invariant and its exact S4 transport.  No round, terminal, repair or result.
#print axioms Internal.PsubsetPpoly.TM.g1AGetn
#print axioms Internal.PsubsetPpoly.TM.g1ALength_pos_of_get
#print axioms Internal.PsubsetPpoly.TM.g1AWalkCtx_vB
#print axioms Internal.PsubsetPpoly.TM.g1AWalkCtx_res
#print axioms Internal.PsubsetPpoly.TM.g1AWalkCtx_withVB
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_fields
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand2_eq
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand1_count_index
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand1_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand1_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand1_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand2_count_index
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand2_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand2_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOperand2_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_count_index
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDataFrames_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDataFrames_count
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFramesRestored_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFramesRestored_data
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFramesRestored_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFramesRestored_count_index
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFramesRestored_operand1_count_index
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_length_eq_validation
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_cursor_split
#print axioms Internal.PsubsetPpoly.TM.g1AWalkInvariantCursorPre_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_cursor_at
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_physical_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFrames_physical_length_lt_capacity
#print axioms Internal.PsubsetPpoly.TM.g1AWalkTape_ext
#print axioms Internal.PsubsetPpoly.TM.g1AWalkTape_eq_of_frames_eq
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFramesRestored_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOuterRun_skip
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOuterRun_no_argSep
#print axioms Internal.PsubsetPpoly.TM.g1AWalkInnerRun_skip
#print axioms Internal.PsubsetPpoly.TM.g1AWalkInnerRun_no_index
#print axioms Internal.PsubsetPpoly.TM.g1AWalkInnerRun_no_argSep
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFwdRun_skip
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFwdRun_no_cursor
#print axioms Internal.PsubsetPpoly.TM.g1AWalkInnerRun_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOuterRun_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFwdRun_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_seek
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_mark
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_marked
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_marked_fwd
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_marked_cursor
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_restored_cursor
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_restored_probe
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_restored_oob
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_succ
#print axioms Internal.PsubsetPpoly.TM.g1AWalkMarkPre_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFwdPre_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkCursorPre_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkProbePre_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkCursor_safe
#print axioms Internal.PsubsetPpoly.TM.g1AWalkConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1AWalkConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1AWalkConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1AWalkConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1AWalkConfig_res
#print axioms Internal.PsubsetPpoly.TM.g1AWalkConfig_walkMode
#print axioms Internal.PsubsetPpoly.TM.g1AFirstCursorFrames_eq_sigma0
#print axioms Internal.PsubsetPpoly.TM.g1APostWriterConfig_eq_sigma0
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_sigma0_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_sigma0_unary_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_sigma0_binary_exact
#print axioms Internal.PsubsetPpoly.TM.g1AWalk_unary_sigma0_steps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AWalk_binary_sigma0_steps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AWalk_sigma0_no_success_of_empty
#print axioms Internal.PsubsetPpoly.TM.g1AWalk_binary_success_not_empty
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_sigma0_unary_oob_exact
#print axioms Internal.PsubsetPpoly.TM.g1AInstallOOBConfig_ne_sigma0
#print axioms Internal.PsubsetPpoly.TM.g1AWalk_unary_oob_steps_le_clock
#print axioms Internal.PsubsetPpoly.TM.G1AWalkInvariantExamples.input_false_sigma0_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkInvariantExamples.or_true_sigma0_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkInvariantExamples.input_empty_oob_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkInvariantExamples.input_empty_no_sigma0_success

-- S6 (2026-08-30): exactly one operand-A round.  Normal execution moves the
-- unique designated cursor from slot `j` to `j+1`, restores the old hidden
-- value, re-latches the successor value and preserves the residual.  The
-- successor-data OOB endpoint is the existing `bOOB` on the cursor-free
-- restored tape; operand-index exhaustion stops earlier at local `aExh`.
-- No terminal continuation, A-repair, driver, output or acceptance theorem.
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOOBConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOOBConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOOBConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOOBConfig_res
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOOBConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1AWalkExhaustConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1AWalkExhaustConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1AWalkExhaustConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1AWalkExhaustConfig_res
#print axioms Internal.PsubsetPpoly.TM.g1AWalkExhaustConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_round_prefix_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_round_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_round_oob_exact
#print axioms Internal.PsubsetPpoly.TM.g1AWalkExhaustPre_length
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_exhaust
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_exhaust_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_round_preservation
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_round_oob_preservation
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRoundSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRoundOOBSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AWalkExhaustSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_round_unary_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkRoundExamples.requests_canonical
#print axioms Internal.PsubsetPpoly.TM.G1AWalkRoundExamples.normal_round_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkRoundExamples.normal_round_from_initial_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkRoundExamples.oob_round_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkRoundExamples.exhaust_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkRoundExamples.literal_clock_bounds

-- S7 (2026-08-30): exact finite-sum operand-A induction from merged Sigma-A,
-- real unary/binary prefix compositions, unchanged-clock provenance, separate
-- exhaustion/OOB drivers and the cursor-free S3b2b terminal boundary later
-- consumed by S8b's live repair entry.
-- No transition, A-repair sweep, result, output or acceptance theorem.
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDriverSteps_zero
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDriverSteps_succ
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDriverSteps_eq_sum
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_driver_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_driver_preservation
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_driver_unary_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_driver_binary_exact
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDriverSteps_le_poly
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDriverPoly_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDriverSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryDriverSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ABinaryDriverSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_exhaust_driver_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_oob_driver_exact
#print axioms Internal.PsubsetPpoly.TM.g1AWalkExhaustDriverSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AWalkFullDriverSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRepairStartConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRepairStartConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRepairStartConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRepairStartConfig_res
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRepairStartConfig_vB
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_done
#print axioms Internal.PsubsetPpoly.TM.g1AWalkSplit_exhaust_fwd
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDoneFrames_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_terminal_from_exhaust_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_full_driver_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkDriverExamples.requests_canonical
#print axioms Internal.PsubsetPpoly.TM.G1AWalkDriverExamples.zero_round_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkDriverExamples.one_round_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkDriverExamples.two_round_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkDriverExamples.exhaustion_driver_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkDriverExamples.zero_operand_exhaustion_exact
#print axioms Internal.PsubsetPpoly.TM.G1AWalkDriverExamples.two_round_from_initial_exact

-- S3b2a (2026-08-29): direct source roots for the dormant normal walk.
#print axioms Internal.PsubsetPpoly.TM.FrameScan.ReverseFrameScanner.revWindowStop
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aWalk_dormant
#print axioms Internal.PsubsetPpoly.TM.g1Complete_aWalk_dormant
#print axioms Internal.PsubsetPpoly.TM.g1Complete_aWalk_reserved
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aFwd_cursor
#print axioms Internal.PsubsetPpoly.TM.g1ASeekRevComplete_some
#print axioms Internal.PsubsetPpoly.TM.g1ASeekRevComplete_none
#print axioms Internal.PsubsetPpoly.TM.g1ASeekRevComplete_reserved
#print axioms Internal.PsubsetPpoly.TM.g1ASeekRevAdvance_blank_cursor
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekOut_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekOut_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekOut_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekOut_p0_seekIn
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekOut_p0_argSep
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekOut_p0_other
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekOut_p0_bad
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekOut_p0_none_bad
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p0_dec
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p0_exh
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p0_index
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p0_argSep
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p0_other
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p0_bad
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeekIn_p0_none_bad
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aSeek_p0_reserved_bad
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aDec
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aTurn
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRestore
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aWalk_entry_closure
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aFwd_of_skip
#print axioms Internal.PsubsetPpoly.TM.G1ASeekOutSkip_ne_argSep
#print axioms Internal.PsubsetPpoly.TM.G1ASeekInSkip_ne_index
#print axioms Internal.PsubsetPpoly.TM.G1ASeekInSkip_ne_argSep
#print axioms Internal.PsubsetPpoly.TM.G1ASeekMode.eq
#print axioms Internal.PsubsetPpoly.TM.g1ASeekRevAdvance_out_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1ASeekRevAdvance_in_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_reserved_1101_reject
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_reserved_1101_reject_idle
#print axioms Internal.PsubsetPpoly.TM.g1AWalkScanner_machine
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_seek_index
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_seek_exhaust
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_mark
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_fwd_to_cursor
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_turn
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_restore

-- S3b2b/S8b boundary (2026-08-30): terminal cleanup reaches the unique live
-- door, whose exact one-step execution enters aligned `aRepairSeek .p3`.
#print axioms Internal.PsubsetPpoly.TM.g1AFinMode_ne_restore
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aTerminal_rows
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairStart_live
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aTurnFin
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aFin
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aRet_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_exh_to_cursor
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_turn_fin
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_fin_restore
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_terminal_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepairStart_entry_exact

-- S8b (2026-08-30): live reject-aware operand-A repair.  S8a's caller-supplied
-- macros remain audited, then the direct roots below compose the unique door,
-- S7 terminal driver and real initial unary/successful-binary routes through
-- canonical `aRepairDone` handoff.  S8b itself has no
-- result/combine/output/accept root; S9 consumes the handoff below.
#print axioms Internal.PsubsetPpoly.TM.G1ForwardMode.not_aRepair
#print axioms Internal.PsubsetPpoly.TM.G1ARepairScanMode.eq
#print axioms Internal.PsubsetPpoly.TM.g1ARepairStopState_write
#print axioms Internal.PsubsetPpoly.TM.g1ARepairStopState_done
#print axioms Internal.PsubsetPpoly.TM.g1ARepairStopState_reject
#print axioms Internal.PsubsetPpoly.TM.g1ARepairScanner_machine
#print axioms Internal.PsubsetPpoly.TM.g1ARepairBackAdvance_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1ARepairBackComplete_some
#print axioms Internal.PsubsetPpoly.TM.g1ARepairBackComplete_none
#print axioms Internal.PsubsetPpoly.TM.g1ARepairBackComplete_reserved
#print axioms Internal.PsubsetPpoly.TM.g1ARepairBackComplete_forbidden
#print axioms Internal.PsubsetPpoly.TM.g1Advance_aRepair_predecessor_closure
#print axioms Internal.PsubsetPpoly.TM.g1Complete_aRepair_predecessor_closure
#print axioms Internal.PsubsetPpoly.TM.g1ARepairStart_not_control
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairSeek_p3
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairSeek_p2
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairSeek_p1
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairSeek_p0_spent
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairSeek_p0_bof
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairSeek_p0_skip
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairSeek_p0_bad
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairSeek_p0_reserved_bad
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairWrite
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairBack
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairHop
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairDone_result
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepair_entry_closure
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepair_unique_external_door
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepairStart_entry
#print axioms Internal.PsubsetPpoly.TM.g1Transition_aRepair_external_entry_iff
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_cycle_onList
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_seek_and_repair
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_frame_skip
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_frame_reject
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_frame_reject_idle
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_reserved_1101_reject
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_reserved_1101_reject_idle
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_scan_skip
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_spent_run
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_finish
#print axioms Internal.PsubsetPpoly.TM.g1ARepairPassSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_pass_exact
#print axioms Internal.PsubsetPpoly.TM.g1ARepairLeft_length
#print axioms Internal.PsubsetPpoly.TM.g1ARepairMid_length
#print axioms Internal.PsubsetPpoly.TM.g1ARepair_split_of
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDoneFrames_repair_split
#print axioms Internal.PsubsetPpoly.TM.g1ARepairLeft_skip
#print axioms Internal.PsubsetPpoly.TM.g1ARepairMid_skip
#print axioms Internal.PsubsetPpoly.TM.g1ARepairFrames_repaired
#print axioms Internal.PsubsetPpoly.TM.g1ARepairCanonical_fields
#print axioms Internal.PsubsetPpoly.TM.g1ARepairCanonical_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1ARepairCanonical_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1ARepairCanonical_count_index
#print axioms Internal.PsubsetPpoly.TM.g1ARepairSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_canonical_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_canonical_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_canonical_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_canonical_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_canonical_res
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_canonical_vB
#print axioms Internal.PsubsetPpoly.TM.g1ARepairLiveSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_activation_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_live_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_live_endpoint
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRepairSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_repair_driver_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_unary_initial_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_binary_initial_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_unary_arg1_zero_exact
#print axioms Internal.PsubsetPpoly.TM.g1AWalkRepairSteps_le_poly
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryRepairSteps_le_poly
#print axioms Internal.PsubsetPpoly.TM.g1ABinaryRepairSteps_le_poly
#print axioms Internal.PsubsetPpoly.TM.g1ARepairLivePoly_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryRepairSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1ABinaryRepairSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_oob_driver_stable
#print axioms Internal.PsubsetPpoly.TM.g1AWalkOOBConfig_ne_aRepairDone

-- S9 (2026-08-30): exact three-row non-const result handoff, unchanged const
-- bypass, five pure tag bridges, honest spec-none/OOB separation, exact
-- combine boundary and all-five-tag literal probes.  S10b consumes the
-- boundary; S9 itself has no output/acceptance root.
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_aRepairDone_result
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_aResultStart_apply
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepairDone_combine_exact
#print axioms Internal.PsubsetPpoly.TM.g1BACombineSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1UACombineSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1GateResultSteps_const
#print axioms Internal.PsubsetPpoly.TM.g1GateResultSteps_binary
#print axioms Internal.PsubsetPpoly.TM.g1GateResultSteps_unary
#print axioms Internal.PsubsetPpoly.TM.g1ResultSq_succ
#print axioms Internal.PsubsetPpoly.TM.g1ResultClock_quad
#print axioms Internal.PsubsetPpoly.TM.g1BACombineSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1UACombineSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1GateResultSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_aCombine_binary_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_aCombine_unary_exact
#print axioms Internal.PsubsetPpoly.TM.g1Vals_prefix_witness
#print axioms Internal.PsubsetPpoly.TM.g1Spec_operands_binary
#print axioms Internal.PsubsetPpoly.TM.g1Spec_operand_unary
#print axioms Internal.PsubsetPpoly.TM.g1Spec_input_bridge
#print axioms Internal.PsubsetPpoly.TM.g1Spec_not_bridge
#print axioms Internal.PsubsetPpoly.TM.g1Spec_and_bridge
#print axioms Internal.PsubsetPpoly.TM.g1Spec_or_bridge
#print axioms Internal.PsubsetPpoly.TM.g1Spec_const_bridge
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_binary
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_unary
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_ctx
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_pass_vB
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_tape
#print axioms Internal.PsubsetPpoly.TM.g1Spec_none_of_arg1_oob
#print axioms Internal.PsubsetPpoly.TM.g1Spec_none_of_arg2_oob_binary
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_or_spec_none
#print axioms Internal.PsubsetPpoly.TM.g1CombineState_ne_oob
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_result_false_ne_oob
#print axioms Internal.PsubsetPpoly.TM.G1AResultProbes.literal_canonical
#print axioms Internal.PsubsetPpoly.TM.G1AResultProbes.literal_specs
#print axioms Internal.PsubsetPpoly.TM.G1AResultProbes.literal_steps
#print axioms Internal.PsubsetPpoly.TM.G1AResultProbes.literal_clocks
#print axioms Internal.PsubsetPpoly.TM.G1AResultProbes.literal_results

-- S10a (2026-08-30): reusable strict output scan/turn/write.
-- Definitions are pinned by the surface test; every public theorem is a direct
-- audit root here.  S10b supplies the live result entry and accept exit.
#print axioms Internal.PsubsetPpoly.TM.g1Advance_outputKernel_predecessor
#print axioms Internal.PsubsetPpoly.TM.g1Complete_outputKernel_predecessor
#print axioms Internal.PsubsetPpoly.TM.g1Stuck_of_not_forward
#print axioms Internal.PsubsetPpoly.TM.g1Transition_outTurn
#print axioms Internal.PsubsetPpoly.TM.g1Transition_outWrite
#print axioms Internal.PsubsetPpoly.TM.G1OutputSkip_ne_output
#print axioms Internal.PsubsetPpoly.TM.G1OutputSkip_ne_spent
#print axioms Internal.PsubsetPpoly.TM.G1OutputSkip_ne_cursor
#print axioms Internal.PsubsetPpoly.TM.g1Advance_outSeek_of_skip
#print axioms Internal.PsubsetPpoly.TM.g1Advance_outSeek_output_false
#print axioms Internal.PsubsetPpoly.TM.g1Advance_outSeek_reject_iff
#print axioms Internal.PsubsetPpoly.TM.g1Advance_outSeek_forbidden
#print axioms Internal.PsubsetPpoly.TM.g1Complete_outSeek_malformed_reserved
#print axioms Internal.PsubsetPpoly.TM.g1Transition_outputKernel_predecessor
#print axioms Internal.PsubsetPpoly.TM.g1Transition_combineStart_output_mode
#print axioms Internal.PsubsetPpoly.TM.g1CS_out_scan
#print axioms Internal.PsubsetPpoly.TM.g1CS_out_turn
#print axioms Internal.PsubsetPpoly.TM.g1OutWriter_machine
#print axioms Internal.PsubsetPpoly.TM.g1CS_out_write
#print axioms Internal.PsubsetPpoly.TM.g1OutputFrames_false
#print axioms Internal.PsubsetPpoly.TM.g1OutputFrames_length
#print axioms Internal.PsubsetPpoly.TM.g1OutputBase_eq
#print axioms Internal.PsubsetPpoly.TM.g1OutputPosition_eq_base
#print axioms Internal.PsubsetPpoly.TM.g1OutputBase_pos
#print axioms Internal.PsubsetPpoly.TM.g1OutputBase_safe
#print axioms Internal.PsubsetPpoly.TM.g1OutputExitHead_safe
#print axioms Internal.PsubsetPpoly.TM.g1OutputTape_false
#print axioms Internal.PsubsetPpoly.TM.g1OutputTape_eq_writeCell
#print axioms Internal.PsubsetPpoly.TM.g1OutputTape_at
#print axioms Internal.PsubsetPpoly.TM.g1OutputTape_off
#print axioms Internal.PsubsetPpoly.TM.g1OutputTape_true_ne_initial
#print axioms Internal.PsubsetPpoly.TM.g1OutputTape_false_identity
#print axioms Internal.PsubsetPpoly.TM.g1OutputFrames_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1OutputFrames_count_cursor
#print axioms Internal.PsubsetPpoly.TM.g1OutputFrames_count_index
#print axioms Internal.PsubsetPpoly.TM.g1PrefixFrames_outSkip
#print axioms Internal.PsubsetPpoly.TM.g1PrefixFrames_ne_output
#print axioms Internal.PsubsetPpoly.TM.g1OutputFrames_count_output
#print axioms Internal.PsubsetPpoly.TM.g1OutputFrames_count_other_output
#print axioms Internal.PsubsetPpoly.TM.g1OutputRoute_length
#print axioms Internal.PsubsetPpoly.TM.g1OutputDoneConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1OutputDoneConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1OutputDoneConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1OutputKernelSteps_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_scan_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_turn_write_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_kernel_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_kernel_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_kernel_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_kernel_state
#print axioms Internal.PsubsetPpoly.TM.g1OutputDone_false_ne_reject
#print axioms Internal.PsubsetPpoly.TM.g1OutputDone_false_ne_oob
#print axioms Internal.PsubsetPpoly.TM.g1OutputDone_ne_combine
#print axioms Internal.PsubsetPpoly.TM.G1OutputKernelProbes.literal_frames_false
#print axioms Internal.PsubsetPpoly.TM.G1OutputKernelProbes.literal_frames_true
#print axioms Internal.PsubsetPpoly.TM.G1OutputKernelProbes.literal_steps
#print axioms Internal.PsubsetPpoly.TM.G1OutputKernelProbes.literal_false_run
#print axioms Internal.PsubsetPpoly.TM.G1OutputKernelProbes.literal_true_run
#print axioms Internal.PsubsetPpoly.TM.G1OutputKernelProbes.literal_false_tape
#print axioms Internal.PsubsetPpoly.TM.G1OutputKernelProbes.literal_true_tape

-- S10b (2026-08-30): live one-gate output and literal acceptance.  Definitions
-- are pinned by the surface test; every public theorem is rooted directly.
-- The genuine `TM.accepts` result is forward (`spec = some res`); exact binary
-- arg2-OOB nonacceptance is separate, and no multi-gate claim is made.
#print axioms Internal.PsubsetPpoly.TM.g1Transition_accept_predecessor
#print axioms Internal.PsubsetPpoly.TM.g1Transition_reject_not_accept
#print axioms Internal.PsubsetPpoly.TM.g1Transition_oob_not_accept
#print axioms Internal.PsubsetPpoly.TM.g1Transition_outSeek_malformed_reject
#print axioms Internal.PsubsetPpoly.TM.g1AcceptConfig_state
#print axioms Internal.PsubsetPpoly.TM.g1AcceptConfig_head
#print axioms Internal.PsubsetPpoly.TM.g1AcceptConfig_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_combine_output
#print axioms Internal.PsubsetPpoly.TM.g1CS_step_outputDone_accept
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_accept_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_runConfig_accept_sink
#print axioms Internal.PsubsetPpoly.TM.g1GateAcceptSteps_provenance
#print axioms Internal.PsubsetPpoly.TM.g1GateAcceptSteps_closed
#print axioms Internal.PsubsetPpoly.TM.g1GateAcceptSteps_const
#print axioms Internal.PsubsetPpoly.TM.g1GateAcceptSteps_binary
#print axioms Internal.PsubsetPpoly.TM.g1GateAcceptSteps_unary
#print axioms Internal.PsubsetPpoly.TM.g1GateAcceptSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1GateAccept_clock_unchanged
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_context
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_frames
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_output
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_off
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_true_tape_ne
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_false_tape_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_false_ne_oob
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_accept_false_ne_reject
#print axioms Internal.PsubsetPpoly.TM.g1CS_run_accept_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_accepts_of_spec_some
#print axioms Internal.PsubsetPpoly.TM.g1CS_reject_not_accept
#print axioms Internal.PsubsetPpoly.TM.g1CS_oob_not_accept
#print axioms Internal.PsubsetPpoly.TM.g1CS_outSeek_malformed_reject_stable
#print axioms Internal.PsubsetPpoly.TM.g1CS_outSeek_malformed_not_accept
#print axioms Internal.PsubsetPpoly.TM.g1CS_accepts_false_of_arg2_oob_positive
#print axioms Internal.PsubsetPpoly.TM.g1CS_accepts_false_of_arg2_oob_zero
#print axioms Internal.PsubsetPpoly.TM.G1OutputAcceptProbes.literal_steps
#print axioms Internal.PsubsetPpoly.TM.G1OutputAcceptProbes.literal_clocks
#print axioms Internal.PsubsetPpoly.TM.G1OutputAcceptProbes.literal_accepts
#print axioms Internal.PsubsetPpoly.TM.G1OutputAcceptProbes.literal_false_output
#print axioms Internal.PsubsetPpoly.TM.G1OutputAcceptProbes.literal_true_output

-- GN-3B1 + GN-3B2a + GN-3B2b (2026-08-31): exact result-indexed output-done
-- boundary, plus structural arbitrary-canonical validation and read-only
-- rewind safety through the existing read-B handoff.  This slice does not
-- execute pass-B or claim full-gate/ShiftRunSafe safety.
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_provenance
#print axioms Internal.PsubsetPpoly.TM.g1GateAcceptSteps_eq_done_add_one
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_closed
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_const
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_input
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_not
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_and
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_or
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_le_clock
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_done_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_exact
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_state
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_mode
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_context
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_head
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_tape
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_frames
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_output
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_off
#print axioms Internal.PsubsetPpoly.TM.g1_runConfig_head_le_start_add
#print axioms Internal.PsubsetPpoly.TM.g1_initial_prefix_head_le_steps
#print axioms Internal.PsubsetPpoly.TM.g1_local_right_safe_of_head_le_span_pred
#print axioms Internal.PsubsetPpoly.TM.g1_initial_prefix_right_safe_of_steps_lt_span
#print axioms Internal.PsubsetPpoly.TM.g1Validation_initial_envelope
#print axioms Internal.PsubsetPpoly.TM.g1Validation_envelope_local_safe
#print axioms Internal.PsubsetPpoly.TM.g1Validation_scanner_step_exact
#print axioms Internal.PsubsetPpoly.TM.g1Validation_run_envelope
#print axioms Internal.PsubsetPpoly.TM.g1Validation_run_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_validation_reaches_span_pred
#print axioms Internal.PsubsetPpoly.TM.g1CS_validation_span_pred_moves_left
#print axioms Internal.PsubsetPpoly.TM.g1CS_validation_span_pred_local_safe
#print axioms Internal.PsubsetPpoly.TM.g1Validation_run_safe_through_boundary
#print axioms Internal.PsubsetPpoly.TM.g1CS_validation_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1Validation_rewind_entry_exact
#print axioms Internal.PsubsetPpoly.TM.g1Validation_rewind_entry_envelope
#print axioms Internal.PsubsetPpoly.TM.g1Rewind_microstate_local_safe
#print axioms Internal.PsubsetPpoly.TM.g1Rewind_microstate_step_ranked
#print axioms Internal.PsubsetPpoly.TM.g1Rewind_microstate_step_exact
#print axioms Internal.PsubsetPpoly.TM.g1Rewind_envelope_local_safe
#print axioms Internal.PsubsetPpoly.TM.g1Validation_rewind_entry_ranked
#print axioms Internal.PsubsetPpoly.TM.g1Rewind_microstate_run_safe
#print axioms Internal.PsubsetPpoly.TM.g1ValidationRewindSteps_closed
#print axioms Internal.PsubsetPpoly.TM.g1ValidationRewindSteps_add_boundary
#print axioms Internal.PsubsetPpoly.TM.g1Validation_rewind_run_safe
#print axioms Internal.PsubsetPpoly.TM.g1ValidationRewind_run_safe_to_readB
#print axioms Internal.PsubsetPpoly.TM.g1ValidationRewind_prefix_head_lt
#print axioms Internal.PsubsetPpoly.TM.g1ValidationRewind_no_left_at_zero
#print axioms Internal.PsubsetPpoly.TM.g1CS_validation_rewind_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1TraceSafetyProbes.literal_done_steps
#print axioms Internal.PsubsetPpoly.TM.G1TraceSafetyProbes.literal_false_done
#print axioms Internal.PsubsetPpoly.TM.G1TraceSafetyProbes.literal_true_done
#print axioms Internal.PsubsetPpoly.TM.G1TraceSafetyProbes.literal_false_span_pred_safe
#print axioms Internal.PsubsetPpoly.TM.G1TraceSafetyProbes.literal_true_span_pred_safe

-- GN-3B2c1 (2026-08-31): structural positive-operand-B route/install safety and
-- one successful cursor-walk round.  No arg2 induction, terminal cleanup,
-- repair cycle, full-gate safety, ShiftRunSafe, GN controller or acceptance.
#print axioms Internal.PsubsetPpoly.TM.g1LocalStepSafe_of_interior
#print axioms Internal.PsubsetPpoly.TM.g1LocalStepSafe_at_zero_of_not_left
#print axioms Internal.PsubsetPpoly.TM.g1Forward_microstate_localSafe
#print axioms Internal.PsubsetPpoly.TM.g1Forward_microstate_step
#print axioms Internal.PsubsetPpoly.TM.g1Forward_microstate_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1Forward_scan_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1Walk_reverseFrame_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1Walk_revSkip_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1Walk_seekToMarker_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1RunSafe_of_margins
#print axioms Internal.PsubsetPpoly.TM.g1Forward_frame_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1Forward_scanFrom_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_seek_mark_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_fwd_to_cursor_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_install_scan_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_install_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_iteration_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_one_round_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassBTraceProbes.literal_one_round_trace_safe

-- GN-3B2c2 (2026-08-31): exact successful terminal-B cleanup and one
-- reject-aware repair sweep to the canonical read-A handoff.  No arbitrary
-- operand-2 round induction, pass A, full gate, ShiftRunSafe, controller,
-- clock, output, verdict or acceptance theorem.
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_seek_exhaust_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_exh_to_cursor_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_terminal_turn_restore_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_terminal_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1Repair_reverseFrame_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_scan_skip_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_cycle_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_spent_run_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_finish_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_repair_sweep_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_terminal_repair_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassBTerminalRepairTraceProbes.reqAnd_canonical
#print axioms Internal.PsubsetPpoly.TM.G1PassBTerminalRepairTraceProbes.literal_terminal_repair_trace_safe

-- GN-3B2d (2026-08-31): actual arbitrary-arg2 pass-B safety induction from
-- the real initial configuration, plus the independent zero-index scan/store
-- prefix.  The successful positive and zero branches compose with the merged
-- terminal/repair safety and meet at the canonical head-zero `readAStart`
-- endpoint on the exact conditional schedule.  The selector premise
-- `vals[arg2]? = some b` is required; no OOB, pass-A step, full-gate,
-- `ShiftRunSafe`, controller, output, verdict, or acceptance claim is made.
-- The literal roots are kernel-visible real-initial safe runs of `400` and
-- `172` steps.
#print axioms Internal.PsubsetPpoly.TM.g1CS_walk_loop_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_positive_repaired_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_zero_repaired_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_repaired_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassBDriverTraceProbes.literal_positive_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassBDriverTraceProbes.literal_zero_trace_safe

-- GN-3B2e1a (2026-08-31): nonconstant pass-A dispatch, rescan, latch and live
-- cursor-install safety, retaining the binary capstones through exact
-- `Σᴬ(0)`.  No A round, OOB-success, unary/constant real-initial prefix,
-- repair, output or full-gate claim.
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_install_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_binary_install_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_binary_install_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_binary_install_from_initial_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_binary_install_structure
#print axioms Internal.PsubsetPpoly.TM.G1PassATraceProbes.literal_install_trace_safe

-- GN-3B2e1b (2026-09-01): actual two-mode A reverse-buffer safety, its
-- homogeneous and unique mixed-boundary schedules, and exactly one successful
-- A round.  The real-initial binary capstone stops at `Σᴬ(1)`; no driver,
-- terminal repair, shifted gate, controller, clock or acceptance result.
#print axioms Internal.PsubsetPpoly.TM.g1ASeek_reverseFrame_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1ASeek_revSkip_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1ASeekOut_revSkip_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1ASeekIn_revSkip_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1ASeek_acrossBoundary_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_seek_index_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_fwd_to_cursor_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_round_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_round_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_binary_one_round_from_initial_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassATraceProbes.literal_round_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassATraceProbes.literal_one_round_from_initial_trace_safe

-- GN-3B2e2 (2026-09-01): genuine arbitrary-round A safety, successful
-- exhaustion and cursor cleanup to exact `aRepairStart`, plus the binary
-- real-initial capstone and structural/literal endpoints.  No A-repair step,
-- OOB conflation, unary/constant route, shifted gate, clock or acceptance.
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_driver_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_driver_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_exhaust_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_exhaust_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_exh_to_cursor_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_terminal_turn_restore_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_terminal_from_exhaust_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_exhaust_terminal_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_exhaust_driver_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aWalk_full_driver_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_binary_full_driver_from_initial_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDoneFrames_count_spent
#print axioms Internal.PsubsetPpoly.TM.g1AWalkDoneFrames_count_index
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_binary_full_driver_structure
#print axioms Internal.PsubsetPpoly.TM.G1PassADriverTraceProbes.literal_two_round_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassADriverTraceProbes.literal_exhaustion_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1PassADriverTraceProbes.literal_full_driver_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_steps
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_false_repair_exact
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_true_repair_exact
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_zero_arg1_repair_exact
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_live_steps
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_false_live_exact
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_true_live_exact
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_zero_live_exact
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_false_endpoint_word
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_true_endpoint_word
#print axioms Internal.PsubsetPpoly.TM.G1ARepairExamples.literal_zero_endpoint_word

-- GN-3B2e3 (2026-09-01): actual operand-A reverse-frame, skip, rewrite,
-- anchor and complete live-repair safety through exact head-zero
-- `aRepairDone`, plus the merged e2 binary composition.  The three local
-- literals are 58/58/24; the real-initial binary literal is 541, not a unary
-- total.  No result/combine/output successor, full-gate shifted safety,
-- unary/const route, controller, clock, verdict or acceptance claim.
#print axioms Internal.PsubsetPpoly.TM.g1ARepair_reverseFrame_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_scan_skip_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_cycle_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_spent_run_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_finish_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_pass_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_sweep_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_activation_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_live_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_live_structure
#print axioms Internal.PsubsetPpoly.TM.g1ABinaryRepairSteps_trace_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_binary_initial_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1ARepairTraceProbes.literal_false_local_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1ARepairTraceProbes.literal_true_local_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1ARepairTraceProbes.literal_zero_local_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1ARepairTraceProbes.literal_binary_steps
#print axioms Internal.PsubsetPpoly.TM.G1ARepairTraceProbes.literal_binary_initial_trace_safe

-- GN-3B2e4 (2026-09-01): the three stationary result rows, stationary
-- combine entry, strict forward output scan and local-margin turn/writer,
-- composed from merged e3 for successful canonical binary requests through
-- exact result-indexed output-done.  Literal totals are 606/484/512 and do
-- not include outputDone-to-accept.  No unary/const, five-tag, shifted,
-- controller, clock, verdict or acceptance safety theorem is claimed.
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepairDone_result_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepairDone_combine_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_combine_entry_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_scan_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_turn_write_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_kernel_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_output_done_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_binary_trace_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepairDone_output_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_binary_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_binary_structure
#print axioms Internal.PsubsetPpoly.TM.G1OutputDoneTraceProbes.literal_binary_done_steps
#print axioms Internal.PsubsetPpoly.TM.G1OutputDoneTraceProbes.literal_binary_output_done_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1OutputDoneTraceProbes.literal_binary_false_done_steps
#print axioms Internal.PsubsetPpoly.TM.G1OutputDoneTraceProbes.literal_binary_false_done
#print axioms Internal.PsubsetPpoly.TM.G1OutputDoneTraceProbes.literal_binary_true_done_steps
#print axioms Internal.PsubsetPpoly.TM.G1OutputDoneTraceProbes.literal_binary_true_done

-- GN-3B2fA (2026-09-01): tag-independent validation/forward-route safety and
-- the exact `1 + 4|left| + 5` zero-rewrite rewind, instantiated at unary and
-- constant real-initial routes and their stationary live activations.  Empty
-- unary values/OOB stay separate; const requires `spec = some b` and stops at
-- combine.  The public canonical route lists are definition-pinned, and all
-- six structural facts made public for this slice have direct roots below.
#check @Internal.PsubsetPpoly.TM.g1AUnaryLeft
#check @Internal.PsubsetPpoly.TM.g1AConstLeft
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryLeft_length
#print axioms Internal.PsubsetPpoly.TM.g1AConstLeft_length
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryLeft_skip
#print axioms Internal.PsubsetPpoly.TM.g1AConstLeft_skip
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryLeft_split
#print axioms Internal.PsubsetPpoly.TM.g1AConstLeft_split
#print axioms Internal.PsubsetPpoly.TM.g1CS_readB_forward_route_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_route_rewind_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_unary_repaired_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_const_repaired_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_unary_activate_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_const_activate_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_activate_unary_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_activate_const_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1RouteRewindTraceProbes.literal_route_activation_steps
#print axioms Internal.PsubsetPpoly.TM.G1RouteRewindTraceProbes.literal_input_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1RouteRewindTraceProbes.literal_not_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1RouteRewindTraceProbes.literal_const_false_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1RouteRewindTraceProbes.literal_const_true_trace_safe

-- GN-3B2fB (2026-09-01): unary activation through generic nonconstant A
-- installation, the generic A driver/terminal suffix, and live repair to the
-- exact canonical `aRepairDone` endpoint.  The semantic capstone requires only
-- canonicality, an input/not tag, and `spec = some res`; selected/prefix values
-- are derived.  Empty values remain on the separate OOB route.  No result,
-- combine, output, const/five-tag, shifted-run, controller, clock, verdict or
-- acceptance theorem is claimed.  Literal install/repair totals are 131/192
-- for input and 171/240 for not.
#print axioms Internal.PsubsetPpoly.TM.g1CS_aBof_install_runSafe
#print axioms Internal.PsubsetPpoly.TM.g1CS_readA_unary_install_from_initial_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1AUnaryRepairSteps_trace_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_unary_initial_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_aRepair_unary_spec_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1UnaryARepairTraceProbes.literal_steps
#print axioms Internal.PsubsetPpoly.TM.G1UnaryARepairTraceProbes.literal_input_install_repair_trace_safe
#print axioms Internal.PsubsetPpoly.TM.G1UnaryARepairTraceProbes.literal_not_install_repair_trace_safe

-- GN-3B2fC (2026-09-01): successful canonical input/const/not/and/or
-- real-initial `G1RunSafe` through exact result-indexed output-done.  Unary
-- and const schedules are pinned explicitly; binary reuses e4 unchanged.  The
-- common theorem has only request, canonicality, result and successful spec.
-- Endpoint structure and all 229/151/171/285/484/512/606 literals are direct
-- roots.  There is no output-done-to-accept or relocation theorem here.
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_unary_trace_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_unary_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1GateDoneSteps_const_trace_eq
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_const_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_trace_safe
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_structure
#print axioms Internal.PsubsetPpoly.TM.G1FiveTagTraceProbes.literal_done_steps
#print axioms Internal.PsubsetPpoly.TM.G1FiveTagTraceProbes.literal_input_true_done
#print axioms Internal.PsubsetPpoly.TM.G1FiveTagTraceProbes.literal_const_false_done
#print axioms Internal.PsubsetPpoly.TM.G1FiveTagTraceProbes.literal_const_true_done
#print axioms Internal.PsubsetPpoly.TM.G1FiveTagTraceProbes.literal_not_false_done
#print axioms Internal.PsubsetPpoly.TM.G1FiveTagTraceProbes.literal_and_false_done
#print axioms Internal.PsubsetPpoly.TM.G1FiveTagTraceProbes.literal_or_true_done
#print axioms Internal.PsubsetPpoly.TM.G1FiveTagTraceProbes.literal_binary_a_done

-- GN-E1b (2026-09-01): after the unchanged E1a lexical scan reaches public
-- `wordEnd`, the same fixed finite shell reads exactly one four-cell blank
-- frame, returns four cells left, and enters fixed `scratchEntry`.  This does
-- not reject trailing zeros, equal `decodeGN?`, install/copy work, delegate a
-- selected request, establish total clock adequacy, decide, or accept.
#print axioms Internal.PsubsetPpoly.TM.gnDiscoveryComplete_decode
#print axioms Internal.PsubsetPpoly.TM.gnDiscovery_encodeGNFrames
#print axioms Internal.PsubsetPpoly.TM.gnDiscoveryComplete_reserved
#print axioms Internal.PsubsetPpoly.TM.gnDiscoveryAdvance_start_malformed
#print axioms Internal.PsubsetPpoly.TM.gnCS_startState
#print axioms Internal.PsubsetPpoly.TM.gnTransition_idle
#print axioms Internal.PsubsetPpoly.TM.gnTransition_returnedFalse
#print axioms Internal.PsubsetPpoly.TM.gnTransition_returnedTrue
#print axioms Internal.PsubsetPpoly.TM.gnTransition_accept
#print axioms Internal.PsubsetPpoly.TM.gnTransition_reject
#print axioms Internal.PsubsetPpoly.TM.gnTransition_wordEnd
#print axioms Internal.PsubsetPpoly.TM.gnTransition_blankConfirm_buffer
#print axioms Internal.PsubsetPpoly.TM.gnTransition_blankConfirm_zero
#print axioms Internal.PsubsetPpoly.TM.gnTransition_blankConfirm_rejections
#print axioms Internal.PsubsetPpoly.TM.gnTransition_blankReturn_rows
#print axioms Internal.PsubsetPpoly.TM.gnTransition_delegate_ordinary
#print axioms Internal.PsubsetPpoly.TM.gnTransition_intercept_false
#print axioms Internal.PsubsetPpoly.TM.gnTransition_intercept_true
#print axioms Internal.PsubsetPpoly.TM.g1M_step_done
#print axioms Internal.PsubsetPpoly.TM.g1M_step_accept
#print axioms Internal.PsubsetPpoly.TM.gnM_step_embed_ordinary
#print axioms Internal.PsubsetPpoly.TM.gnM_step_embed_done
#print axioms Internal.PsubsetPpoly.TM.gnInitialTape_eq_frameListTape
#print axioms Internal.PsubsetPpoly.TM.gnCS_encodeGN_wordEnd
#print axioms Internal.PsubsetPpoly.TM.gnCS_wordEnd_nonblank_first_reject
#print axioms Internal.PsubsetPpoly.TM.gnCS_wordEnd_to_scratchEntry_exact
#print axioms Internal.PsubsetPpoly.TM.gnCS_encodeGN_scratchEntry
#print axioms Internal.PsubsetPpoly.TM.gnScratchEntryConfig_structure
#print axioms Internal.PsubsetPpoly.TM.gnValidateSteps_provenance
#print axioms Internal.PsubsetPpoly.TM.gnScanValidateSegment_le_gnClock
#print axioms Internal.PsubsetPpoly.TM.gnScratch_room_of_add_sixteen
#print axioms Internal.PsubsetPpoly.TM.gnFrameScanner_rejectMacrostep
#print axioms Internal.PsubsetPpoly.TM.gnCS_reserved1101_reject_four
#print axioms Internal.PsubsetPpoly.TM.gnTransition_reserved_windows
#print axioms Internal.PsubsetPpoly.TM.gnTransition_start_malformed_windows
#print axioms Internal.PsubsetPpoly.TM.gnCS_reject_stable
#print axioms Internal.PsubsetPpoly.TM.g1CS_gate_done_no_early_outputDone
#print axioms Internal.PsubsetPpoly.TM.gn_g1_gate_done_delegates
#print axioms Internal.PsubsetPpoly.TM.gn_g1_outputDone_not_delegates
#print axioms Internal.PsubsetPpoly.TM.g1InitialConfig_head_lt_gnLocalSpan
#print axioms Internal.PsubsetPpoly.TM.g1OutputDoneConfig_head_lt_gnLocalSpan
#print axioms Internal.PsubsetPpoly.TM.gnCS_gate_shift_exact
#print axioms Internal.PsubsetPpoly.TM.gnCS_gate_shift_outside_every_prefix
#print axioms Internal.PsubsetPpoly.TM.gnCS_step_shifted_outputDone
#print axioms Internal.PsubsetPpoly.TM.gnCS_gate_shift_intercept_exact
#print axioms Internal.PsubsetPpoly.TM.gnCS_gate_shift_intercept_state
#print axioms Internal.PsubsetPpoly.TM.gnCS_gate_shift_intercept_mode
#print axioms Internal.PsubsetPpoly.TM.gnCS_gate_shift_intercept_structure
#print axioms Internal.PsubsetPpoly.TM.GNFixedDelegateProbes.literal_input_true_shifted_intercept
#print axioms Internal.PsubsetPpoly.TM.GNFixedDelegateProbes.literal_const_false_shifted_intercept
#print axioms Internal.PsubsetPpoly.TM.GNFixedDelegateProbes.literal_encodeGN_lengths
#print axioms Internal.PsubsetPpoly.TM.GNFixedDelegateProbes.literal_empty_wordEnd
#print axioms Internal.PsubsetPpoly.TM.GNFixedDelegateProbes.literal_oneConstFalse_wordEnd
#print axioms Internal.PsubsetPpoly.TM.GNFixedDelegateProbes.literal_empty_scratchEntry
#print axioms Internal.PsubsetPpoly.TM.GNFixedDelegateProbes.literal_oneConstFalse_scratchEntry

-- GN-E2-2 owner update (2026-09-02): the same finite GNM shuttle writes the
-- exact boundary image at its destination and restores the original carried
-- frame at its source.  Body-only corollaries retain the old identity shape;
-- finish rows are pinned but not executed in this E2-1b owner slice.  No
-- driver, exit activation, total clock, verdict, or acceptance is present.
#print axioms Internal.PsubsetPpoly.TM.gnInstallImage_laws
#print axioms Internal.PsubsetPpoly.TM.gnCS_copyShuttle_onList
#print axioms Internal.PsubsetPpoly.TM.gnCS_copyShuttle_nextBlank
#print axioms Internal.PsubsetPpoly.TM.gnCS_copyShuttle_body_onList
#print axioms Internal.PsubsetPpoly.TM.gnCS_copyShuttle_body_nextBlank
#print axioms Internal.PsubsetPpoly.TM.gnTransition_install_cursor_destination_restore
#print axioms Internal.PsubsetPpoly.TM.gnTransition_install_finish_destination_restore
#print axioms Internal.PsubsetPpoly.TM.gnTransition_install_forward_none
#print axioms Internal.PsubsetPpoly.TM.gnTransition_install_reverse_none
#print axioms Internal.PsubsetPpoly.TM.gnTransition_install_reserved
#print axioms Internal.PsubsetPpoly.TM.gnTransition_install_marker_modes
#print axioms Internal.PsubsetPpoly.TM.gnCS_install_reject_stable
#print axioms Internal.PsubsetPpoly.TM.gnCS_copyShuttle_tag_run45
#print axioms Internal.PsubsetPpoly.TM.gnCS_copyShuttle_cursor_run37
#print axioms Internal.PsubsetPpoly.TM.gnCS_copyShuttle_finish_run37
#print axioms Internal.PsubsetPpoly.TM.gnCopyShuttle_marker_middle_rejected

-- GN-E2-0 (2026-09-01): pure stage words are pinned to exact physical GNM
-- tapes, E1b is identified with the stage-zero boundary, and the selected
-- first request is identified with the complete base-N shifted physical
-- configuration.  This is representation/geometry infrastructure only: no
-- state/transition activation, installer execution, marker codec, commit,
-- clock adequacy, multigate loop, verdict, or acceptance theorem.
#print axioms Internal.PsubsetPpoly.TM.gnStageWord_length
#print axioms Internal.PsubsetPpoly.TM.gnStageTape_zero
#print axioms Internal.PsubsetPpoly.TM.gnStageTape_cell
#print axioms Internal.PsubsetPpoly.TM.gnStageTape_outside_blank
#print axioms Internal.PsubsetPpoly.TM.GateNTapeState.physical_tape_eq
#print axioms Internal.PsubsetPpoly.TM.GateNTapeState.toPhysical
#print axioms Internal.PsubsetPpoly.TM.gnScratchEntryConfig_stage_zero
#print axioms Internal.PsubsetPpoly.TM.gnScratchEntryConfig_physical_state
#print axioms Internal.PsubsetPpoly.TM.gnCurrentValues_zero
#print axioms Internal.PsubsetPpoly.TM.gnWorkRequest?_zero
#print axioms Internal.PsubsetPpoly.TM.gnFirstRequest_canonical
#print axioms Internal.PsubsetPpoly.TM.gnFirstRequest_width
#print axioms Internal.PsubsetPpoly.TM.gnFirstRequest_add_sixteen_le
#print axioms Internal.PsubsetPpoly.TM.gnFirstRequest_room
#print axioms Internal.PsubsetPpoly.TM.encodeGNAtFrames_zero_first_split
#print axioms Internal.PsubsetPpoly.TM.encodeGNAtFrames_zero_cursor_unique
#print axioms Internal.PsubsetPpoly.TM.encodeGNAtFrames_zero_no_spent
#print axioms Internal.PsubsetPpoly.TM.encodeG1Frames_first_no_internal_markers
#print axioms Internal.PsubsetPpoly.TM.gnFirstInstalledConfig_eq_physical
#print axioms Internal.PsubsetPpoly.TM.gnFirstInstalledPhysicalConfig_structure
#print axioms Internal.PsubsetPpoly.TM.GNFirstInstallProbes.oneConstFalse_first_gate
#print axioms Internal.PsubsetPpoly.TM.GNFirstInstallProbes.oneConstFalse_first_request
#print axioms Internal.PsubsetPpoly.TM.GNFirstInstallProbes.oneConstFalse_width_room
#print axioms Internal.PsubsetPpoly.TM.GNFirstInstallProbes.oneConstFalse_installed_physical
#print axioms Internal.PsubsetPpoly.TM.GNFirstInstallProbes.empty_no_first_gate

-- GN-E2-1c (2026-09-02): strict stage-zero reverse locator and exact
-- read-only real-initial arrivals at firstRecord/noGate.  Its own capstones
-- stop before the live firstRecord door; noGate remains dormant.  The scoped
-- clock facts cover validation+locator only.
#print axioms Internal.PsubsetPpoly.TM.gnLocateComplete_reserved
#print axioms Internal.PsubsetPpoly.TM.gnLocateAdvance_tail_and_edge
#print axioms Internal.PsubsetPpoly.TM.gnLocateAdvance_stageZero_malformed
#print axioms Internal.PsubsetPpoly.TM.encodeGNFrames_firstRecord_split
#print axioms Internal.PsubsetPpoly.TM.encodeGNFrames_noGate_split
#print axioms Internal.PsubsetPpoly.TM.encodeGNFrames_no_blank_no_outputTrue
#print axioms Internal.PsubsetPpoly.TM.encodeGNFrames_cursor_unique
#print axioms Internal.PsubsetPpoly.TM.gnTransition_locate_none
#print axioms Internal.PsubsetPpoly.TM.gnTransition_locate_decoded_reject
#print axioms Internal.PsubsetPpoly.TM.gnTransition_locate_reserved
#print axioms Internal.PsubsetPpoly.TM.gnCS_locate_reserved1101_reject_four
#print axioms Internal.PsubsetPpoly.TM.gnCS_locate_reserved1101_reject_stable
#print axioms Internal.PsubsetPpoly.TM.gnLocate_firstRecord_path
#print axioms Internal.PsubsetPpoly.TM.gnLocate_noGate_path
#print axioms Internal.PsubsetPpoly.TM.gnFirstRecordSteps_provenance
#print axioms Internal.PsubsetPpoly.TM.gnNoGateSteps_provenance
#print axioms Internal.PsubsetPpoly.TM.gnFirstRecordConfig_scratch_blank
#print axioms Internal.PsubsetPpoly.TM.gnNoGateConfig_scratch_blank
#print axioms Internal.PsubsetPpoly.TM.gnFirstRecordConfig_structure
#print axioms Internal.PsubsetPpoly.TM.gnNoGateConfig_structure
#print axioms Internal.PsubsetPpoly.TM.gnFirstRecord_copyShuttle_handoff
#print axioms Internal.PsubsetPpoly.TM.gnCS_scratchEntry_to_firstRecord
#print axioms Internal.PsubsetPpoly.TM.gnCS_scratchEntry_to_noGate
#print axioms Internal.PsubsetPpoly.TM.gnCS_encodeGN_firstRecord
#print axioms Internal.PsubsetPpoly.TM.gnCS_encodeGN_noGate
#print axioms Internal.PsubsetPpoly.TM.gnFirstRecordSteps_le_gnClock
#print axioms Internal.PsubsetPpoly.TM.gnNoGateSteps_le_gnClock
#print axioms Internal.PsubsetPpoly.TM.GNScratchBootstrapProbes.literal_oneConstFalse_firstRecord
#print axioms Internal.PsubsetPpoly.TM.GNScratchBootstrapProbes.literal_empty_noGate

-- GN-E2-2 (2026-09-02): the firstRecord door plus exactly one cursor-to-bof
-- shuttle, ending at the exact install-exit boundary carrying cursor at
-- first-body p0.
-- The source cursor and original GN word are restored.  The five-step 1101
-- rejection and E2-3 handoff are exact; there is no body execution, live
-- finish, exit activation, loop, total installer clock, verdict or acceptance.
#print axioms Internal.PsubsetPpoly.TM.gnTransition_boundary_rows
#print axioms Internal.PsubsetPpoly.TM.gnFirstRecord_image_request_prefix
#print axioms Internal.PsubsetPpoly.TM.gnCS_firstRecord_to_probe_exact
#print axioms Internal.PsubsetPpoly.TM.gnBofSeedSteps_provenance
#print axioms Internal.PsubsetPpoly.TM.gnCS_firstRecord_to_bofSeed_exact
#print axioms Internal.PsubsetPpoly.TM.gnCS_encodeGN_bofSeed_exact
#print axioms Internal.PsubsetPpoly.TM.gnBofSeedConfig_structure
#print axioms Internal.PsubsetPpoly.TM.gnBofSeed_firstBody_handoff
#print axioms Internal.PsubsetPpoly.TM.gnBofSeedSteps_le_gnClock
#print axioms Internal.PsubsetPpoly.TM.gnCS_firstRecord_reserved1101_reject_five
#print axioms Internal.PsubsetPpoly.TM.gnCS_firstRecord_reserved1101_reject_stable
#print axioms Internal.PsubsetPpoly.TM.GNBoundaryShuttleProbes.literal_oneConstFalse_bofSeed

-- GN-E2-3a (2026-09-02): the same finite GNM retains shuttle payloads and
-- activates only a one-round exit dispatcher plus fixed recordDone switch.
-- The proof-level invariant, exact 8d+30/8d+31 rounds, boundary rejection,
-- scoped round clock, and 94/head20 tag literal are direct roots.  There is no
-- arbitrary body driver or real-initial recordDone capstone.
#print axioms Internal.PsubsetPpoly.TM.gnTransition_install_exit_dispatch
#print axioms Internal.PsubsetPpoly.TM.gnBodyRoundConfig_structure
#print axioms Internal.PsubsetPpoly.TM.gnBodyRoundSteps_provenance
#print axioms Internal.PsubsetPpoly.TM.gnBodyRoundMiddle_length_constant
#print axioms Internal.PsubsetPpoly.TM.gnCS_bodyRound_exact
#print axioms Internal.PsubsetPpoly.TM.gnCS_bodyRound_iteration_exact
#print axioms Internal.PsubsetPpoly.TM.gnCS_bodyFinishRound_exact
#print axioms Internal.PsubsetPpoly.TM.gnCS_finishExit_to_recordDone_one
#print axioms Internal.PsubsetPpoly.TM.gnCS_bodyFinishRound_recordDone_exact
#print axioms Internal.PsubsetPpoly.TM.gnCS_install_exit_invalid_reject_one
#print axioms Internal.PsubsetPpoly.TM.gnCS_install_exit_badBuffer_reject_one
#print axioms Internal.PsubsetPpoly.TM.gnCS_install_exit_reserved1101_reject_five
#print axioms Internal.PsubsetPpoly.TM.gnCS_install_exit_reserved1101_reject_stable
#print axioms Internal.PsubsetPpoly.TM.gnBodyTerminalSteps_le_gnClock
#print axioms Internal.PsubsetPpoly.TM.GNBodyRoundProbes.literal_oneConstFalse_tagRound

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
