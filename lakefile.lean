import Lake
open Lake DSL

package pnp3

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"
require fact_locality_lift from "./Facts/LocalityLift"
require fact_sunflower from "./Facts/Sunflower"

@[default_target]
lean_lib PnP3 where
  srcDir := "pnp3"
  globs := #[
    Glob.one `Core.BooleanBasics,
    Glob.one `Core.PDTPartial,
    Glob.one `Core.PDT,
    Glob.one `Core.Atlas,
    Glob.one `Core.SAL_Core,
    Glob.one `Core.ShrinkageWitness,
    Glob.one `Counting.BinomialBounds,
    Glob.one `Counting.CapacityGap,
    Glob.one `Counting.Count_EasyFuncs,
    Glob.one `Counting.CircuitCounting,
    Glob.one `Counting.ShannonCounting,
    Glob.one `Counting.Atlas_to_LB_Core,
    Glob.one `AC0.Formulas,
    -- Multi-switching core: include the shared restriction model plus
    -- the canonical trace helper so downstream modules can import it
    -- without missing `.olean` artifacts.
    Glob.one `AC0.MultiSwitching.Restrictions,
    Glob.one `AC0.MultiSwitching.Duality,
    Glob.one `AC0.MultiSwitching.Definitions,
    Glob.one `AC0.MultiSwitching.BadEvents,
    Glob.one `AC0.MultiSwitching.CanonicalTrace,
    Glob.one `AC0.MultiSwitching.CanonicalDT,
    -- Parameter block for Step 3.2 numerics/encodings.
    Glob.one `AC0.MultiSwitching.Params,
    Glob.one `AC0.MultiSwitching.Numerics,
    Glob.one `AC0.MultiSwitching.Trace,
    Glob.one `AC0.MultiSwitching.TraceBridge,
    Glob.one `AC0.MultiSwitching.CommonBad,
    Glob.one `AC0.MultiSwitching.EncodingCommon,
    Glob.one `AC0.MultiSwitching.CommonBad_Func,
    Glob.one `AC0.MultiSwitching.EncodingCommon_Func,
    Glob.one `AC0.MultiSwitching.Decides,
    Glob.one `AC0.MultiSwitching.Atoms,
    Glob.one `AC0.MultiSwitching.FuncCNF,
    Glob.one `AC0.MultiSwitching.DecidesAtoms,
    Glob.one `AC0.MultiSwitching.CommonCCDT_Func,
    Glob.one `AC0.MultiSwitching.CommonCCDT,
    Glob.one `AC0.MultiSwitching.Counting,
    Glob.one `AC0.MultiSwitching.Encoding,
    Glob.one `AC0.MultiSwitching.ShrinkageFromGood,
    Glob.one `AC0.MultiSwitching.Main,
    Glob.one `Complexity.Promise,
    Glob.one `Complexity.Interfaces,
    Glob.one `Complexity.DagCompose,
    Glob.one `Complexity.PsubsetPpolyInternal.Bitstring,
    Glob.one `Complexity.TMVerifier.GapMCSPVerifier,
    Glob.one `Complexity.PsubsetPpolyInternal.TuringEncoding,
    Glob.one `Complexity.TMVerifier.TuringToolkit.Foundation,
    Glob.one `Complexity.TMVerifier.TuringToolkit.BinaryCounter,
    Glob.one `Complexity.TMVerifier.TuringToolkit.Encoding,
    Glob.one `Complexity.TMVerifier.TuringToolkit.AtomicPrograms,
    Glob.one `Complexity.TMVerifier.TuringToolkit.UnaryAtOffset,
    Glob.one `Complexity.TMVerifier.TuringToolkit.CopyAtOffset,
    Glob.one `Complexity.TMVerifier.TuringToolkit.CombineAtOffset,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateWrappers,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramInitialConfig,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRun,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramAccepts,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAccept,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAcceptExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqListRun,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRunExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqListRunExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridge,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridgeExamples,
    -- Blocker-1 infrastructure: the dependency-closed generic fixed-width
    -- frame-scanner kernel.  `Codec` is the 4-bit alphabet layer, `Kernel`
    -- proves the macrostep and the exact list-scan induction generically in
    -- the program/alphabet/mode/context, and `Probe` is a non-T1 instance
    -- that witnesses the genericity.  None of the three imports any T1
    -- module; `FrameScannerT1` (below `TrueUniformSeek`) is the T1 instance.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerCodec,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerKernel,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerProbe,
    -- Reverse/write half of the same kernel: right-to-left frame scanning and
    -- four-cell frame replacement, with a second non-T1 genericity probe.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerReverse,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerWrite,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerReverseProbe,
    -- Mutation half of the same kernel: leftward writer, seek-until-marker
    -- driver, the exact thirteen-step rewrite cycle, and a non-T1 probe.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerWriteLeft,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerSeek,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameRewriteCycle,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleProbe,
    Glob.one `Complexity.TMVerifier.TuringToolkit.RowConsistencyCheck,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekEncoding,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeek,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerT1,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalControl,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutation,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoop,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoopExamples,
    -- T1b-C: the seek-loop driver (induction, success tail, terminal split).
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriver,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriverExamples,
    -- T1c-2: terminal execution (repair pass, output write, the three
    -- exact terminal theorems).
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminal,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemantics,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemanticsExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekExamples,
    -- T2a, pure layer: the fresh unary one-gate ABI (`GateOneEncoding`) and
    -- the pure gate semantics on top of it (`GateOneSemantics`).  These are
    -- parser/spec modules only; the fixed control and execution layers are
    -- registered immediately below.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneEncoding,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneSemantics,
    -- T2a, control layer: one zero-parameter finite control whose forward
    -- table decides the canonical grammar (`GateOneControl`), and that
    -- control as a genuine instance of the generic frame-scanner kernel
    -- (`GateOneScanner`).  Exact validation/rewind is registered next.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneControl,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneScanner,
    -- T2a, execution layer: the exact validation/rewind capstone from the
    -- real initial configuration (`GateOneValidation`) and the per-tag named
    -- examples (`GateOneExamples`).
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneValidation,
    -- T1/G1 instances of the generic reverse frame-scanner kernel.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerReverseInstances,
    -- T1 instances of the mutation kernel and the exact G1 obligation.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleInstances,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneRouting,
    -- T2b, pass-B execution layer: the exact `TM.runConfig` route capstones
    -- from the real initial configuration (`GateOneReadB`) and the named
    -- per-route examples (`GateOneReadBExamples`).
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneReadB,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneReadBExamples,
    -- T2b-3a, the cursor-walk installation scan: the re-pointed
    -- positive-index route from the real initial configuration
    -- (`GateOneInstallScan`) and its concrete literal probe
    -- (`GateOneInstallScanExamples`).
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneInstallScan,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneInstallScanExamples,
    -- T2b-3a-2, the successor of the installation-scan endpoint: the exact
    -- probe / latch / cursor-install atoms on arbitrary frame-list contexts
    -- (`GateOneProbeInstall`) and their literal encoded-frame probes
    -- (`GateOneProbeInstallExamples`).  Every run there starts from a
    -- caller-supplied configuration; `bSeek` is the reverse-seek entry shape
    -- executed in `GateOneWalkKernel`.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneProbeInstall,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneProbeInstallExamples,
    -- PR2b1, one normal round of the cursor walk behind `bSeek`: the reverse
    -- seek, the `index ↦ spent` writer, the forward scan, the turn and the
    -- cursor restore as exact atoms on arbitrary frame-list contexts
    -- (`GateOneWalkKernel`) and their literal encoded-frame probes
    -- (`GateOneWalkExamples`).  Every run there is caller-supplied too, and the
    -- exhaustion outcome stops at `bExh`.
    -- PR2b2 adds, to the same two modules, the terminal exhaustion path behind
    -- that handoff: the exhaustion scan, the terminal turn and the terminal
    -- restore into `readAResetStart` with no cursor left on the tape.  Those
    -- runs are caller-supplied too; nothing composes a round with them.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkKernel,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkExamples,
    -- PR3a, the cursor-walk tape invariant `Σ(j)`: the exact layout with its
    -- length, counts and structural facts (`GateOneWalkInvariant`), the
    -- installation into `Σ(0)` from the real initial configuration, the
    -- empty-data out-of-range branch, and their literal probes
    -- (`GateOneWalkInvariantExamples`).
    -- PR3b adds, to the same two modules, **exactly one round** on `Σ(j)` from
    -- a caller-supplied configuration: the normal step `Σ(j) → Σ(j+1)` in
    -- `16j + 37` steps and the out-of-range abort in `16j + 32` steps onto an
    -- intermediate, unrepaired tape.  No induction over `j`, no driver, no loop
    -- clock and no verdict are claimed there.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariant,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariantExamples,
    -- PR3c, the cursor-walk driver: the `8k² + 29k` loop clock, the induction
    -- into `Σ(k)` from the real initial configuration, the successful terminal
    -- at `j = arg2`, the public positive-index operand-2 read and the
    -- aggregated out-of-range branch — both inside the unchanged `g1Clock` and
    -- both on a repair-pending tape — with their literal probes.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkDriver,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkDriverExamples,
    -- The thirteen-step rewrite cycle at the G1 control, kept as an
    -- arbitrary-configuration regression: the bridge, the fourteen-step
    -- composed round and one literal frame-list probe.  Unreachable from
    -- `G1M.initialConfig`.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneIndexRound,
    Glob.one `Complexity.PsubsetPpolyInternal.CircuitTree,
    Glob.one `Complexity.PsubsetPpolyInternal.StraightLine,
    Glob.one `Complexity.PsubsetPpolyInternal.TreeToStraight,
    Glob.one `Complexity.PsubsetPpolyInternal.StraightLineBuilder,
    Glob.one `Complexity.PsubsetPpolyInternal.StraightLineSemantics,
    Glob.one `Complexity.PsubsetPpolyInternal.Simulation,
    Glob.one `Complexity.PsubsetPpolyInternal.ComplexityInterfaces,
    Glob.one `Complexity.PpolyDAG_StraightLineCore,
    Glob.one `Complexity.PpolyDAG_from_StraightLine,
    Glob.one `Complexity.PpolyFormula_from_PpolyDAG_FixedSlice,
    Glob.one `Complexity.PsubsetPpolyDAG_Internal,
    Glob.one `Complexity.Simulation.TM_Encoding,
    Glob.one `Complexity.Simulation.Circuit_Compiler,
    Glob.one `Barrier.Relativization,
    Glob.one `Barrier.NaturalProofs,
    Glob.one `Barrier.Algebrization,
    Glob.one `Barrier.Bypass,
    Glob.one `Models.PartialTruthTable,
    Glob.one `Models.Model_PartialMCSP,
    Glob.one `LowerBounds.LB_Formulas,
    Glob.one `LowerBounds.ApproxClassContradiction,
    Glob.one `LowerBounds.ApproxClassNoGo,
    Glob.one `LowerBounds.SingletonProvenanceEndpoint,
    Glob.one `LowerBounds.SingletonDensityEndpoint,
    Glob.one `LowerBounds.SingletonDensityContradiction,
    Glob.one `LowerBounds.AcceptedFamilyBarrier,
    Glob.one `LowerBounds.DAGStableRestrictionProducer,
    Glob.one `LowerBounds.RouteBSourceClosure,
    Glob.one `LowerBounds.FailedRoute_FixedSliceSupportHalfCore,
    Glob.one `LowerBounds.FailedRoute_FixedSliceSupportHalfImpossible,
    Glob.one `LowerBounds.FailedRoute_GapSliceFamilyVacuous,
    Glob.one `LowerBounds.FailedRoute_EventualTableForceSlackObstruction,
    Glob.one `LowerBounds.FailedRoutes,
    Glob.one `LowerBounds.DAGUnconditionalBlocker,
    Glob.one `LowerBounds.AsymptoticDAGBarrierInterfaces,
    Glob.one `LowerBounds.AsymptoticDAGBarrierTheorems,
    Glob.one `LowerBounds.AsymptoticDAGBarrier,
    Glob.one `LowerBounds.MCSPGapLocality,
    Glob.one `LowerBounds.AntiChecker_Partial,
    Glob.one `LowerBounds.LB_Formulas_Core_Partial,
    Glob.one `LowerBounds.AC0_GapMCSP_Final,
    Glob.one `LowerBounds.AC0_GapMCSP,
    Glob.one `Magnification.LocalityInterfaces_Partial,
    Glob.one `Magnification.Facts_Magnification_Partial,
    Glob.one `Magnification.PipelineStatements_Partial,
    Glob.one `Magnification.AC0LocalityBridge,
    Glob.one `Magnification.AC0AtlasBridge,
    Glob.one `Magnification.AC0ApproxFamilyBridge,
    Glob.one `Magnification.LocalityProvider_Partial,
    Glob.one `Magnification.LocalityLift_Partial,
    Glob.one `Magnification.Bridge_to_Magnification_Partial,
    Glob.one `Magnification.AsymptoticFormulaCollapse,
    Glob.one `Magnification.FinalResultMainline,
    Glob.one `Magnification.FinalResultAuditRoutes,
    Glob.one `Magnification.FinalResultWeakRoutes,
    Glob.one `Magnification.FinalResultLegacyTM,
    Glob.one `Magnification.FinalResultCore,
    Glob.one `Magnification.UnconditionalResearchGap,
    Glob.one `Magnification.CanonicalAsymptoticTrackData,
    Glob.one `Magnification.CanonicalAsymptoticDecider,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.ToySeparation,
    Glob.one `Magnification.FinalResult,
    -- Research Governance v0.1, PR 4a: refuted-predicate registry.
    Glob.one `RefutedPredicates.Registry,
    -- Research Governance v0.1, PR 10: FrozenSpec stage 1.
    Glob.one `Spec.FrozenSpec,
    -- Research Governance v0.1, FP-1: FixedParams Probe audit surface.
    Glob.one `Magnification.AuditRoutes.FixedParamsProbe,
    -- v0.4.2 Track A-CL0: CrossLength coherence audit target surface
    -- (research objectives only; no theorems, no NoGoLog entry).
    Glob.one `Magnification.AuditRoutes.CrossLengthCoherence_NoGo,
    -- v0.4.3-followup: 10-engineer parallel attack on FP-3b.2.
    -- Triage wiring; final selection happens at S11 integration.
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Width_NatLog2,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Width_PowOfTwoSlice,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.RenameSize,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.RenameSupport,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.TTFormulaSizeBound,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Family_PowOfTwoSlice,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Diversity_BelowN,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Diversity_Unbounded,
    -- v0.4.3-followup S11 integration: composition of the parallel
    -- engineer outputs into logWidthAdversary_satisfies_diversity.
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Composition,
    -- fp3b4 support-cardinality barrier (post-NOGO-000006 follow-up).
    -- T1..T6 of the 6-slot decomposition, ending in the T6 application.
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringFamily,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringSupport,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringWitness,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.SupportCardinalityOnly,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.Barrier,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.InSupportFunctionalDiversityApplication,
    -- fp3b3 ProvenanceFilter v2 design — Phase 1 paper sketches
    -- (4 directions, single engineer handle gpt55).
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Sketch,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Filter,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesOverbroad,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesPrefixAnd,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesArbitraryPayload,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NonVacuity,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NotSupportCardinalityOnly,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Survivor,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.AdversarialRobustness.RewriteAttack,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NaturalProofsSelfTest.RepresentationSensitivity,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_NormaliseMetaBarrier.Barrier,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_B_gpt55.Sketch,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Sketch,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_D_GPT55.Sketch,
    -- fp3b2 arbitrary-payload strengthening (post-NOGO-000005 follow-up).
    -- T1..T6 of the 6-slot decomposition, ending in the composition theorem.
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssential,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.TTFormulaSupport,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.RenamePayload,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.Family,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.Witness,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.Composition,
    -- fp3b6 distinguisher-matrix provenance audit route (D1/D3 gpt55 + D2 codex,
    -- D4 read-set locality).
    -- (`V_gpt55.MatrixPrimitives` is already declared above, near `FinalResult`.)
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.AntiCollapse,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codex.ToySeparation,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codexd3a.AntiCollapsePrime,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codexd3c.Sharpness,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d4.ReadSetLocality,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d5.LocalGateInvariance,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d6.PayloadBudgetThreshold,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d7.DelocalizationCriterion,
    Glob.one `ThirdPartyFacts.Facts_Switching,
    -- Partial-track bibliography/lemmas used by final magnification result.
    Glob.one `ThirdPartyFacts.PartialTransport,
    Glob.one `ThirdPartyFacts.PartialLocalityLift,
    Glob.one `ThirdPartyFacts.PpolyFormula,
    Glob.one `ThirdPartyFacts.LeafBudget,
    Glob.one `Tests.BarrierAudit,
    Glob.one `Tests.BarrierBypassAudit,
    Glob.one `Tests.AxiomsAudit,
    Glob.one `Tests.AC0PublishableSurface,
    Glob.one `Tests.BridgeLocalityRegression,
    Glob.one `Tests.CanonicalIntegrationTests,
    Glob.one `Tests.RouteSurfaceAudit,
    Glob.one `Tests.CircuitCountTraceBoundProbe,
    Glob.one `Tests.HInDagTrivialityProbe,
    Glob.one `Tests.GlobalHInDagContractProbe,
    Glob.one `Tests.GeneralIsoStrongNoGoProbe,
    Glob.one `Tests.GeneralIsoStrongRouteClosure,
    Glob.one `Tests.PromiseRouteConclusionProbe,
    Glob.one `Tests.WeakRouteSurfaceTests,
    Glob.one `Tests.TMSeqRunSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekMutationSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekMutationLoopSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekMutationDriverSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekTerminalSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekSemanticsSurfaceTests,
    Glob.one `Tests.TMStepBridgeSurfaceTests,
    Glob.one `Tests.TMFrameScannerSurfaceTests,
    Glob.one `Tests.TMFrameScannerReverseSurfaceTests,
    Glob.one `Tests.TMFrameRewriteCycleSurfaceTests,
    Glob.one `Tests.TMGateOnePureSurfaceTests,
    Glob.one `Tests.TMGateOneControlSurfaceTests,
    Glob.one `Tests.TMGateOneRoutingSurfaceTests,
    Glob.one `Tests.TMGateOneExecutionSurfaceTests,
    Glob.one `Tests.TMGateOneReadBSurfaceTests,
    Glob.one `Tests.TMGateOneProbeInstallSurfaceTests,
    Glob.one `Tests.TMGateOneWalkSurfaceTests,
    Glob.one `Tests.TMGateOneWalkInvariantSurfaceTests,
    Glob.one `Tests.TMGateOneWalkDriverSurfaceTests,
    Glob.one `Tests.FormulaSupportBoundsFalsifiabilityProbe,
    Glob.one `Tests.SmokeTests,
    Glob.one `Tests.UnitTests,
    -- Research Governance v0.1, PR 11: target-lock compile-time probe.
    Glob.one `Tests.TargetLockProbe,
    -- Research Governance v0.1, FP-1: FixedParams Probe NoGo smoke skeleton.
    Glob.one `Tests.FixedParams_Probe_NoGo,
    -- v0.4.2 Track A-CL0: regression smoke for the CL-0 target surface.
    Glob.one `Tests.AuditRoutes_CL0_NoGo_Regression,
    -- v0.4.3-followup S11: regression smoke for the log-width adversary
    -- composition + the parallel-engineer outputs it consumes.
    Glob.one `Tests.AuditRoutes_LogWidthAdversary_Smoke,
    Glob.one `Tests.AuditRoutes_ArbitraryLogWidthTT_Smoke,
    Glob.one `Tests.AuditRoutes_SupportCardinalityBarrier_Smoke,
    -- fp3b3.1 + fp3b3.2: smoke for V2-A landing artifacts
    -- (representation-sensitivity self-test + rewrite attack).
    Glob.one `Tests.AuditRoutes_V2A_LandingArtifacts_Smoke
  ]

lean_lib Pnp4 where
  srcDir := "pnp4"
  globs := #[
    Glob.one `Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.Growth,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.SuperPolynomialBridge,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AC0pSuperPolynomialBridge,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AsymptoticSizeLowerBound,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AC0pAsymptoticBridge,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.LocalPRG,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.CoinProblem,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.CoinMaskingTranslation,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSPCoinReduction,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSPCoinReductionContract,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Final,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Quantitative,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AC0pCoinAsymptotic,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.LocalPRGHardnessSpec,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.FormulaCircuitTargetModel,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.FormulaCircuitPublishedLowerBound,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Final,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Theorem2Quantitative,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.FormulaCircuitAsymptotic,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG,
    Glob.one `Pnp4.Frontier.PvsNPBridgeRequirements,
    Glob.one `Pnp4.Frontier.CompressionMagnification,
    Glob.one `Pnp4.Frontier.SearchMCSPMagnification,
    Glob.one `Pnp4.Frontier.SearchMCSPConcreteTargets,
    Glob.one `Pnp4.Frontier.DagSupportCardinality,
    -- Generic signed-support/no-go infrastructure.  These modules use only
    -- the current `DagCompose` / `DagCircuit` layer and carry no one-tape or
    -- streaming-magnification dependency.
    Glob.one `Pnp4.Frontier.SignedSupportNoGo.FiniteSignedSupport,
    Glob.one `Pnp4.Frontier.SignedSupportNoGo.FiniteSetDAG,
    Glob.one `Pnp4.Frontier.SignedSupportNoGo.DenseEasyBarrier,
    Glob.one `Pnp4.Frontier.ContractExpansion.C_DAG_Adapter,
    Glob.one `Pnp4.Frontier.ContractExpansion.QueryComposition,
    Glob.one `Pnp4.Frontier.ContractExpansion.QueryBuilder,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixQueryBuilder,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageNP,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixParserConvention,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSerializer,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixQueryCircuits,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPZeroPrefixBuilder,
    Glob.one `Pnp4.Frontier.ContractExpansion.NaiveGreedySizeSpike,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixStateQueryCircuits,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleStep,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleFold,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyOutputCircuits,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtendableSplit,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPTrueExtensionQuery,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyExtendable,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyTrueOutputCircuits,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPDeciderCorrect,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedySolves,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPBoundedSolver,
    Glob.one `Pnp4.Frontier.ContractExpansion.BoundedSolverFromPpoly,
    Glob.one `Pnp4.Frontier.ContractExpansion.NoSolverContrapositive,
    Glob.one `Pnp4.Frontier.ContractExpansion.ExtractedScheduleGrowth,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConditionalVerifiedSource,
    Glob.one `Pnp4.Frontier.ContractExpansion.WitnessGrowthReduction,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtensionNPWitness,
    Glob.one `Pnp4.Frontier.ContractExpansion.ExplicitConditionalSource,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteCodecGap,
    Glob.one `Pnp4.Frontier.ContractExpansion.CircuitTreeBridge,
    Glob.one `Pnp4.Frontier.ContractExpansion.CircuitEncodingLength,
    Glob.one `Pnp4.Frontier.ContractExpansion.CircuitDecodeDepthFree,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteTreeDirectEvaluator,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteTreeDirectTagProgram,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteTreeCodecSource,
    Glob.one `Pnp4.Frontier.ContractExpansion.ThresholdGrowth,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConsolidatedTreeSeparation,
    -- NP-verifier prerequisites for the prefix-extension language: the semantic
    -- verifier and its input-tape layout, listed in dependency order (the layout
    -- module imports the semantic verifier).
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixVerifierLayout,
    -- The content-truthful prefix-extension language `L'`, its padding-stability
    -- lemmas, and the conditional chain re-routed through it, listed in dependency
    -- order (each module imports only modules listed above it; Coincidence pulls in
    -- the two verifier modules above, Padding stays specification-only, and the
    -- explicitly classical transport module imports both Coincidence and Padding).
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtension,
    -- FEAS-0 slice, part 1: parser field recovery.  It imports only
    -- `ContentPrefixExtension`, so it is listed immediately after it.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentParseFieldRecovery,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionCoincidence,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding,
    -- P0: computable content-side semantic verifier and its specification correctness.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentSemanticVerifier,
    -- D1a: machine-facing tape lemmas and the predicate-parameterized exact-step bridge.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentVerifierTapeInterface,
    -- D1b: the codec-specific bridge alias and the conditional witness repackaging.  It imports
    -- both P0's semantic verifier and D1a's bridge structure, so it is listed after both.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentVerifierBridgeWitness,
    -- FEAS-0 slice, part 2: the concrete accepted-target polynomial bound.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentTargetSizeBound,
    -- GATE-0 slice: non-vacuity of `ContentAccepts` at the concrete codec.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionNonVacuity,
    -- I1: honest convention-length injectivity, gamma canonicity/narrowing,
    -- unconditional length-gate vacuity, and the exact three-value-test residue.
    -- It imports `ContentPrefixExtensionCoincidence`, `ContentPrefixExtensionPadding`,
    -- `ConcreteTreeCodec` and `ThresholdGrowth`, all listed above.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionGateClosure,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPaddingTransport,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionTransfer,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentConsolidatedSource,
    -- Model-audit module: it depends only on the shared complexity interfaces,
    -- so it is listed after the whole contract-expansion chain and before the
    -- test modules that import it.
    Glob.one `Pnp4.Frontier.ModelAudit.RuntimeAdviceBarrier,
    Glob.one `Pnp4.Tests.AlgorithmsToLowerBoundsSurfaceTests,
    Glob.one `Pnp4.Tests.AxiomsAudit
  ]

@[test_driver]
lean_exe test where
  root := `Tests.TestDriver
  srcDir := "pnp3"
