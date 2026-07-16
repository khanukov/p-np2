import Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses
import Pnp4.AlgorithmsToLowerBounds.Growth
import Pnp4.AlgorithmsToLowerBounds.SuperPolynomialBridge
import Pnp4.AlgorithmsToLowerBounds.AC0pSuperPolynomialBridge
import Pnp4.AlgorithmsToLowerBounds.AsymptoticSizeLowerBound
import Pnp4.AlgorithmsToLowerBounds.AC0pAsymptoticBridge
import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP
import Pnp4.AlgorithmsToLowerBounds.LocalPRG
import Pnp4.AlgorithmsToLowerBounds.CoinProblem
import Pnp4.AlgorithmsToLowerBounds.CoinMaskingTranslation
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReduction
import Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReductionContract
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Final
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Quantitative
import Pnp4.AlgorithmsToLowerBounds.AC0pCoinAsymptotic
import Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer
import Pnp4.AlgorithmsToLowerBounds.LocalPRGHardnessSpec
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitTargetModel
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitPublishedLowerBound
import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Final
import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Theorem2Quantitative
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitAsymptotic
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG
import Pnp4.Frontier.PvsNPBridgeRequirements
import Pnp4.Frontier.CompressionMagnification
import Pnp4.Frontier.SearchMCSPMagnification
import Pnp4.Frontier.SearchMCSPConcreteTargets
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter
import Pnp4.Frontier.ContractExpansion.QueryComposition
import Pnp4.Frontier.ContractExpansion.QueryBuilder
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage
import Pnp4.Frontier.ContractExpansion.PrefixQueryBuilder
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime
import Pnp4.Frontier.ContractExpansion.PrefixParserConvention
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSerializer
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixQueryCircuits
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixStateQueryCircuits
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleStep
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleFold
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyOutputCircuits
import Pnp4.Frontier.ContractExpansion.PrefixExtendableSplit
import Pnp4.Frontier.ContractExpansion.TreeMCSPTrueExtensionQuery
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyExtendable
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyTrueOutputCircuits
import Pnp4.Frontier.ContractExpansion.TreeMCSPDeciderCorrect
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedySolves
import Pnp4.Frontier.ContractExpansion.TreeMCSPBoundedSolver
import Pnp4.Frontier.ContractExpansion.BoundedSolverFromPpoly
import Pnp4.Frontier.ContractExpansion.NoSolverContrapositive
import Pnp4.Frontier.ContractExpansion.ExtractedScheduleGrowth
import Pnp4.Frontier.ContractExpansion.ConditionalVerifiedSource
import Pnp4.Frontier.ContractExpansion.WitnessGrowthReduction
import Pnp4.Frontier.ContractExpansion.PrefixExtensionNPWitness
import Pnp4.Frontier.ContractExpansion.ExplicitConditionalSource
import Pnp4.Frontier.ContractExpansion.ConcreteCodecGap
import Pnp4.Frontier.ContractExpansion.CircuitTreeBridge
import Pnp4.Frontier.ContractExpansion.CircuitEncodingLength
import Pnp4.Frontier.ContractExpansion.CircuitDecodeDepthFree
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodecSource
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth
import Pnp4.Frontier.ContractExpansion.ConsolidatedTreeSeparation
import Pnp4.Frontier.ContractExpansion.TreeMCSPZeroPrefixBuilder
import Pnp4.Frontier.ContractExpansion.NaiveGreedySizeSpike
import Pnp4.Frontier.StreamingMagnification.MMWProblem
import Pnp4.Frontier.StreamingMagnification.RuntimeAdviceBarrier
import Pnp4.Frontier.StreamingMagnification.OperationalUniformity
import Pnp4.Frontier.StreamingMagnification.OperationalClockBoundary
import Pnp4.Frontier.StreamingMagnification.OperationalLeftClampProbe
import Pnp4.Frontier.StreamingMagnification.OperationalDynamicScan
import Pnp4.Frontier.StreamingMagnification.OperationalGammaPrefix
import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper
import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperGlobal
import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperActive
import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperContext
import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperActual
import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma
import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaGlobal
import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaActual
import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaPrefixClosure
import Pnp4.Frontier.StreamingMagnification.OperationalRequestHandoff
import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaShapeBarrier
import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaPulse
import Pnp4.Frontier.StreamingMagnification.FinitePHClosure
import Pnp4.Frontier.StreamingMagnification.DAGEvalTrace
import Pnp4.Frontier.StreamingMagnification.StreamMergeChoice
import Pnp4.Frontier.StreamingMagnification.StreamMergeAgreement
import Pnp4.Frontier.StreamingMagnification.StreamMergeTracedCounterexample
import Pnp4.Frontier.StreamingMagnification.StreamMergeDriverCorrectness
import Pnp4.Frontier.StreamingMagnification.StreamMergeWire
import Pnp4.Frontier.StreamingMagnification.StreamMergeOutputFormula
import Pnp4.Frontier.StreamingMagnification.StreamMergeEncodedPrenex
import Pnp4.Frontier.StreamingMagnification.StreamMergePrenexBounds
import Pnp4.Frontier.StreamingMagnification.StreamMergeCertificatePadding
import Pnp4.Frontier.StreamingMagnification.StreamMergeRequestCodec
import Pnp4.Frontier.StreamingMagnification.StreamMergeGlobalPHBridge
import Pnp4.Frontier.OneTapeMagnification.DeterministicComplement
import Pnp4.Frontier.OneTapeMagnification.InputCacheNormalization
import Pnp4.Frontier.OneTapeMagnification.CommunicationSparsity
import Pnp4.Frontier.OneTapeMagnification.LocalPRGToMCSP
import Pnp4.Frontier.OneTapeMagnification.LocalHSGToMCSP
import Pnp4.Frontier.OneTapeMagnification.WeightedPRGSupport
import Pnp4.Frontier.OneTapeMagnification.WeightedPRGToHSG
import Pnp4.Frontier.OneTapeMagnification.SupportAvoidance
import Pnp4.Frontier.OneTapeMagnification.DenseSupportAvoidanceBarrier
import Pnp4.Frontier.OneTapeMagnification.FiniteCheckpointToPpolyDAGBridge
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFamilyBarrier
import Pnp4.Frontier.OneTapeMagnification.UnambiguousAggregateSelectorBarrier
import Pnp4.Frontier.OneTapeMagnification.CanonicalBoundarySelection
import Pnp4.Frontier.OneTapeMagnification.WorkHeadCrossings
import Pnp4.Frontier.OneTapeMagnification.CanonicalCrossingRecords
import Pnp4.Frontier.OneTapeMagnification.CanonicalCutOffsets
import Pnp4.Frontier.OneTapeMagnification.PaddedCanonicalAlpha
import Pnp4.Frontier.OneTapeMagnification.CanonicalBlockGaps
import Pnp4.Frontier.OneTapeMagnification.CanonicalWorkBlocks
import Pnp4.Frontier.OneTapeMagnification.LowRunInputOrder
import Pnp4.Frontier.OneTapeMagnification.ActualRunInputOrder
import Pnp4.Frontier.OneTapeMagnification.StableGroupingPermutation
import Pnp4.Frontier.OneTapeMagnification.StableGroupingRoutingGridBarrier
import Pnp4.Frontier.OneTapeMagnification.ActualSerpentineRoutingGridRealization
import Pnp4.Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture
import Pnp4.Frontier.OneTapeMagnification.CrossingScheduleInputOrder
import Pnp4.Frontier.OneTapeMagnification.ActualCrossingSchedule
import Pnp4.Frontier.OneTapeMagnification.ChronologicalCanonicalAlpha
import Pnp4.Frontier.OneTapeMagnification.TimedCanonicalAlpha
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaWordValidity
import Pnp4.Frontier.OneTapeMagnification.CanonicalPathTranscript
import Pnp4.Frontier.OneTapeMagnification.BoundaryTapeInterface
import Pnp4.Frontier.OneTapeMagnification.LocalBlockReplay
import Pnp4.Frontier.OneTapeMagnification.WorkSlabPersistence
import Pnp4.Frontier.OneTapeMagnification.LocalBlockReplayComposition
import Pnp4.Frontier.OneTapeMagnification.CanonicalBlockSlabs
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutBlockSlabs
import Pnp4.Frontier.OneTapeMagnification.ActualSegmentSlabReplay
import Pnp4.Frontier.OneTapeMagnification.ActualCrossingSegmentAlignment
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaBlockVisitReplay
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCrossingEndpoints
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaVisitSchedule
import Pnp4.Frontier.OneTapeMagnification.ActualAdvertisedCrossingEndpoints
import Pnp4.Frontier.OneTapeMagnification.ActualGroupFixedAlphaVisit
import Pnp4.Frontier.OneTapeMagnification.ActualTimedAlphaVisitSchedule
import Pnp4.Frontier.OneTapeMagnification.CanonicalSlabPersistence
import Pnp4.Frontier.OneTapeMagnification.ActualBlockVisitPersistence
import Pnp4.Frontier.OneTapeMagnification.ActualFixedAlphaBlockVisitCarry
import Pnp4.Frontier.OneTapeMagnification.ActualAllFixedAlphaBlockVisits
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaVisitChecker
import Pnp4.Frontier.OneTapeMagnification.ArbitraryAlphaGlobalGlue
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaGlobalGlue
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutMinimalityChecker
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaCutCounterReplay
import Pnp4.Frontier.OneTapeMagnification.CutCounterStateCount
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaCanonicality
import Pnp4.Frontier.OneTapeMagnification.LocalBlockStateCount
import Pnp4.Frontier.OneTapeMagnification.SeparatorScaleBarrier
import Pnp4.Frontier.OneTapeMagnification.PublishedSeedBarrier
import Pnp4.Frontier.OneTapeMagnification.AdvertisedBlockCandidateGeometry
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaComponent
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaFixedQueryOrder
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaInputPermutation
import Pnp4.Frontier.OneTapeMagnification.OnePassBoundaryCounterVector
import Pnp4.Frontier.OneTapeMagnification.OnlineCanonicalCutExtraction
import Pnp4.Frontier.OneTapeMagnification.WorkHeadCrossingFlowCompression
import Pnp4.Frontier.OneTapeMagnification.CanonicalCutOutputInformationBarrier
import Pnp4.Frontier.OneTapeMagnification.FixedPairedBounceMachine
import Pnp4.Frontier.OneTapeMagnification.OnePassFixedAlphaVisit
import Pnp4.Frontier.OneTapeMagnification.OnePassFixedAlphaBlockList
import Pnp4.Frontier.OneTapeMagnification.OnePassAdvertisedBlockCutCheck
import Pnp4.Frontier.OneTapeMagnification.InPlaceTwoWindowBlockFold
import Pnp4.Frontier.OneTapeMagnification.BlockGroupedCrossingProfile
import Pnp4.Frontier.OneTapeMagnification.NonadjacentBlockCrossingZero
import Pnp4.Frontier.OneTapeMagnification.InPlaceTwoWindowScheduleClosure
import Pnp4.Frontier.OneTapeMagnification.ExecutableInPlaceTimedAlphaComponent
import Pnp4.Frontier.OneTapeMagnification.FullBlockValidatorStateCount
import Pnp4.Frontier.OneTapeMagnification.FiniteLocalCachedStep
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitReplay
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitStreamingVerifier
import Pnp4.Frontier.OneTapeMagnification.FixedVisitOrderRealization
import Pnp4.Frontier.OneTapeMagnification.FixedVisitFreshPrefixSync
import Pnp4.Frontier.OneTapeMagnification.FixedVisitCompilerCorrectness
import Pnp4.Frontier.OneTapeMagnification.PaddedLocalReplayState
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaMultiVisitStateCount
import Pnp4.Frontier.OneTapeMagnification.LayeredQueryProgram
import Pnp4.Frontier.OneTapeMagnification.SilentStepQueryCollapse
import Pnp4.Frontier.OneTapeMagnification.AdaptiveSilentStepQueryCollapse
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedVisitReadOnce
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedVisitCorrectness
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListCompiler
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListReadOnce
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaBlockVisitInputOrder
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListCorrectness
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListSegmentCorrectness
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListSoundness
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListPrefixLiveness
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksOuterCompiler
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksReadOnce
import Pnp4.Frontier.OneTapeMagnification.GuardedFiniteCachedAllBlocksReadOnce
import Pnp4.Frontier.OneTapeMagnification.AcceptedMasterOrderExecution
import Pnp4.Frontier.OneTapeMagnification.AcceptedAllBlocksMasterOrderExecution
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksHomogeneousEmbedding
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitRollingCounters
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListRollingCounters
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksRollingCounters
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceRollingFold
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceCompiler
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceCanonicalCheck
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListRollingOperational
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceOperational
import Pnp4.Frontier.OneTapeMagnification.GuardedFiniteCachedAllBlocksInPlaceCompiler
import Pnp4.Frontier.OneTapeMagnification.GuardedCanonicalAggregateEndpoint
import Pnp4.Frontier.OneTapeMagnification.AcceptingAggregateSemanticRelevance
import Pnp4.Frontier.OneTapeMagnification.ExactMasterGuardedCanonicalComponent
import Pnp4.Frontier.OneTapeMagnification.RejectingGuardedCanonicalAggregateEndpoint
import Pnp4.Frontier.OneTapeMagnification.FiniteRejectingGuardedCanonicalFamily
import Pnp4.Frontier.OneTapeMagnification.MandatoryFixedOrderQueryCollapse
import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDD
import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDRestriction
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDPathCut
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDIndicatorCut
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDIndicatorLocality
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourier
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDFourierFactorization
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy
import Pnp4.Frontier.OneTapeMagnification.GlobalEnergyProjectionBarrier
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDSuffixLaplacian
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDHighDegreeRegrouping
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDPaddedRestriction
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDPerVertexRestrictionBound
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDVertexSumRestrictionBound
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDGlobalEnergyBound
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDGlobalEnergyHighDegreeBound
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDOneRoundHighDegreeBound
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDOneRoundFoolingBound
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDAffineRestrictionIteration
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDConcreteMultiRoundHybrid
import Pnp4.Frontier.OneTapeMagnification.DPTWUnambiguousFBDDHybridBridge
import Pnp4.Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives
import Pnp4.Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed
import Pnp4.Frontier.OneTapeMagnification.GaloisBilinearTensorBridge
import Pnp4.Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredMaskRank
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredRankWeightedDualCorrelation
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge
import Pnp4.Frontier.OneTapeMagnification.FiniteWeightedChargeSpectral
import Pnp4.Frontier.OneTapeMagnification.FiniteWeightedChargeCliqueObstruction
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredPointMassCliqueObstruction
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDFunctionalProjection
import Pnp4.Frontier.OneTapeMagnification.CanonicalAlphaFunctionalRelation
import Pnp4.Frontier.OneTapeMagnification.CanonicalWitnessCutBarrier
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilySelector
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilySelectorUnambiguity
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyComponentDecomposition
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyAcceptedInputPairDecomposition
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyFirstDivergenceCharge
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyAcceptedInputFourier
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyResidualModelMass
import Pnp4.Frontier.OneTapeMagnification.FiniteResidualAcceptedModelCount
import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDResidualRectangle
import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDFixedSuffixResidualRectangle
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyProductivePruning
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorProperties
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalUFBDD
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorCompleteness
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorWeightedCharge
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorEnergyCharge
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualMass
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount
import Pnp4.Frontier.OneTapeMagnification.FiniteSignedResidualAcceptedModelPairKernel
import Pnp4.Frontier.OneTapeMagnification.FiniteResidualLowHighProjection
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualLCPGeometry
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorReverseLCPBucket
import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPTelescope
import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPFourierKernel
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer
import Pnp4.Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation
import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank
import Pnp4.Frontier.OneTapeMagnification.FiniteVectorClaim18ReverseLCPEnergy
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredIndependencePlusOneNoGo
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorFullFieldCorrelation
import Pnp4.Frontier.OneTapeMagnification.SignedDAGLocalGeneratorTransfer
import Pnp4.Frontier.OneTapeMagnification.ReverseOneSidedFoolingSupportEquivalence
import Pnp4.Frontier.OneTapeMagnification.CircuitRecognizableSupportAvoidanceBarrier
import Pnp4.Frontier.OneTapeMagnification.DPTWZeroTailJointLocality
import Pnp4.Frontier.OneTapeMagnification.DPTWZeroTailSurvivorBound
import Pnp4.Frontier.OneTapeMagnification.DPTWIndependentSurvival
import Pnp4.Frontier.OneTapeMagnification.SelectedCutMultiplicity
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaQueryOrder
import Pnp4.Frontier.OneTapeMagnification.OneSidedCutMinimumCheck

namespace Pnp4
namespace Tests

open AlgorithmsToLowerBounds

def check_C_DAG : CircuitFamilyClass :=
  Pnp4.Frontier.ContractExpansion.C_DAG

#check Pnp4.Frontier.ContractExpansion.treePrefixTag
#check Pnp4.Frontier.ContractExpansion.tagLen
#check Pnp4.Frontier.ContractExpansion.gammaLen
#check Pnp4.Frontier.ContractExpansion.idxWidth
#check Pnp4.Frontier.ContractExpansion.natBEField
#check Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
#check Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput
#check Pnp4.Frontier.ContractExpansion.treeMCSPConcretePrefixParser
#print axioms Pnp4.Frontier.ContractExpansion.bitLength_pos_of_pos
#print axioms Pnp4.Frontier.ContractExpansion.nat_lt_two_pow_bitLength
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_zero
#print axioms Pnp4.Frontier.ContractExpansion.be_digit_step
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_slice
#print axioms Pnp4.Frontier.ContractExpansion.gammaBit_zero_prefix
#print axioms Pnp4.Frontier.ContractExpansion.gammaBit_terminator
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_gammaBit_payload
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux_gammaBit
#print axioms Pnp4.Frontier.ContractExpansion.decodeGamma_gammaBit
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux_gammaBit_from_at
#print axioms Pnp4.Frontier.ContractExpansion.prefixLength_lt_two_pow_idxWidth
#print axioms Pnp4.Frontier.ContractExpansion.tableLen_le_treeMCSPPrefixM
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_bad_tag
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_malformed_rejected

noncomputable def check_InPpolyDAG_to_C_DAG_family
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp3.ComplexityInterfaces.InPpolyDAG L) :
    Pnp4.Frontier.ContractExpansion.PolynomiallyBoundedFamily
      Pnp4.Frontier.ContractExpansion.C_DAG L :=
  Pnp4.Frontier.ContractExpansion.InPpolyDAG_to_C_DAG_family h

def check_C_DAG_family_to_InPpolyDAG
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp4.Frontier.ContractExpansion.PolynomiallyBoundedFamily
      Pnp4.Frontier.ContractExpansion.C_DAG L) :
    Pnp3.ComplexityInterfaces.InPpolyDAG L :=
  Pnp4.Frontier.ContractExpansion.C_DAG_family_to_InPpolyDAG h

theorem check_PpolyDAG_decider_as_C_DAG_decider
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp3.ComplexityInterfaces.PpolyDAG L) :
    ∃ c : Nat, ∀ n : Nat, ∃ C : Pnp4.Frontier.ContractExpansion.C_DAG.Family n,
      Pnp4.Frontier.ContractExpansion.C_DAG.size C ≤ n ^ c + c ∧
        ∀ x : AlgorithmsToLowerBounds.BitVec n,
          Pnp4.Frontier.ContractExpansion.C_DAG.eval C x = L n x :=
  Pnp4.Frontier.ContractExpansion.PpolyDAG_decider_as_C_DAG_decider h

section QueryCompositionSurface

open Pnp4.Frontier.ContractExpansion

def check_composeDeciderWithQuery
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    C_DAG.Family inputBits :=
  composeDeciderWithQuery decider queryBit

theorem check_eval_composeDeciderWithQuery
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits)
    (x : AlgorithmsToLowerBounds.BitVec inputBits) :
    C_DAG.eval (composeDeciderWithQuery decider queryBit) x =
      C_DAG.eval decider (fun j => C_DAG.eval (queryBit j) x) :=
  eval_composeDeciderWithQuery decider queryBit x

theorem check_size_composeDeciderWithQuery_le
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    C_DAG.size (composeDeciderWithQuery decider queryBit) ≤
      C_DAG.size decider + ∑ j, C_DAG.size (queryBit j) :=
  size_composeDeciderWithQuery_le decider queryBit

end QueryCompositionSurface

section QueryBuilderSurface

open Pnp4.Frontier.ContractExpansion

def check_QueryCircuitBuilder
    (inputBits queryBits : Nat → Nat) : Type :=
  QueryCircuitBuilder inputBits queryBits

def check_QueryCircuitBuilder_compose
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.Family (inputBits n) :=
  builder.compose n decider

theorem check_QueryCircuitBuilder_eval_compose
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n))
    (x : AlgorithmsToLowerBounds.BitVec (inputBits n)) :
    C_DAG.eval (builder.compose n decider) x =
      C_DAG.eval decider (builder.queryValue n x) :=
  builder.eval_compose n decider x

theorem check_QueryCircuitBuilder_size_compose_le
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.size (builder.compose n decider) ≤
      C_DAG.size decider + ∑ i, C_DAG.size (builder.queryBitCircuit n i) :=
  builder.size_compose_le n decider

theorem check_QueryCircuitBuilder_size_compose_le_bound
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.size (builder.compose n decider) ≤
      C_DAG.size decider + (queryBits n) * builder.sizeBound n :=
  builder.size_compose_le_bound n decider

end QueryBuilderSurface

section PrefixQueryBuilderSurface

open Pnp4.Frontier.ContractExpansion

def check_PrefixQueryBuilder
    (problem : Frontier.SearchMCSPCompressionProblem)
    (parser : PrefixParser problem) : Type :=
  PrefixQueryBuilder problem parser

def check_PrefixQueryBuilder_compose
    {problem : Frontier.SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (pqb : PrefixQueryBuilder problem parser)
    (n : Nat)
    (decider : C_DAG.Family (parser.M n)) :
    C_DAG.Family (problem.instanceBits n) :=
  pqb.compose n decider

theorem check_PrefixQueryBuilder_eval_compose
    {problem : Frontier.SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (pqb : PrefixQueryBuilder problem parser)
    (n : Nat)
    (decider : C_DAG.Family (parser.M n))
    (x : AlgorithmsToLowerBounds.BitVec (problem.instanceBits n)) :
    C_DAG.eval (pqb.compose n decider) x =
      C_DAG.eval decider (pqb.queryValue n x) :=
  pqb.eval_compose n decider x

theorem check_PrefixQueryBuilder_size_compose_le
    {problem : Frontier.SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (pqb : PrefixQueryBuilder problem parser)
    (n : Nat)
    (decider : C_DAG.Family (parser.M n)) :
    C_DAG.size (pqb.compose n decider) ≤
      C_DAG.size decider + ∑ i, C_DAG.size (pqb.builder.queryBitCircuit n i) :=
  pqb.size_compose_le n decider

theorem check_PrefixQueryBuilder_queryValue_parses
    {problem : Frontier.SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (pqb : PrefixQueryBuilder problem parser)
    (n : Nat)
    (x : AlgorithmsToLowerBounds.BitVec (problem.instanceBits n)) :
    ∃ input : PrefixInput problem (parser.M n),
      parsePrefixInput parser (pqb.queryValue n x) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  pqb.queryValue_parses n x

end PrefixQueryBuilderSurface

section TreeMCSPPrefixSerializerSurface

open Pnp4.Frontier.ContractExpansion

def check_zeroPrefixQueryValue
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    PrefixBitVec (treeMCSPPrefixM codec n) :=
  zeroPrefixQueryValue codec n x

theorem check_parse_zeroPrefixQueryValue
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    parseTreeMCSPPrefixInput threshold codec (zeroPrefixQueryValue codec n x) =
      some (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec
        (zeroPrefixFields codec n x)) :=
  parse_zeroPrefixQueryValue codec n x

theorem check_zeroPrefixQueryValue_parses
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    ∃ input : PrefixInput
        (Frontier.treeMCSPSearchProblem threshold
          (Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec n),
      parseTreeMCSPPrefixInput threshold codec (zeroPrefixQueryValue codec n x) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  zeroPrefixQueryValue_parses codec n x

end TreeMCSPPrefixSerializerSurface

section TreeMCSPPrefixQueryCircuitsSurface

open Pnp4.Frontier.ContractExpansion

def check_zeroPrefixQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
  zeroPrefixQueryBitCircuit codec n j

theorem check_eval_zeroPrefixQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (zeroPrefixQueryBitCircuit codec n j) x =
      zeroPrefixQueryValue codec n x j :=
  eval_zeroPrefixQueryBitCircuit codec n x j

theorem check_size_zeroPrefixQueryBitCircuit_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.size (zeroPrefixQueryBitCircuit codec n j) ≤ 2 :=
  size_zeroPrefixQueryBitCircuit_le codec n j

end TreeMCSPPrefixQueryCircuitsSurface

section TreeMCSPPrefixStateQueryCircuitsSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 4 surface: the prefix-state `(i, p)` query string parses back to a
prefix-input about `x` at target length `n`. -/
theorem check_prefixStateQueryValue_parses
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i) :
    ∃ input : PrefixInput
        (Frontier.treeMCSPSearchProblem threshold
          (Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec n),
      parseTreeMCSPPrefixInput threshold codec (prefixStateQueryValue codec n i hi x p) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  prefixStateQueryValue_parses codec n i hi x p

/-- Block 4 surface: the bundle-shape per-bit query circuit, over
`tableLen n + i` inputs (real instance bits ++ prior bundle outputs). -/
def check_prefixStateQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n + i) :=
  prefixStateQueryBitCircuit codec n i hi j

/-- Block 4 surface: evaluating the per-bit circuit on `Fin.append x p` reproduces
the canonical prefix-state query bit. -/
theorem check_eval_prefixStateQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (prefixStateQueryBitCircuit codec n i hi j) (Fin.append x p) =
      prefixStateQueryValue codec n i hi x p j :=
  eval_prefixStateQueryBitCircuit codec n i hi x p j

/-- Block 4 surface: uniform per-bit size bound (`≤ 2`), independent of `i`. -/
theorem check_size_prefixStateQueryBitCircuit_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.size (prefixStateQueryBitCircuit codec n i hi j) ≤ 2 :=
  size_prefixStateQueryBitCircuit_le codec n i hi j

end TreeMCSPPrefixStateQueryCircuitsSurface

section TreeMCSPGreedyBundleStepSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 5 surface: the one-step shared-bundle greedy extension. -/
def check_greedyBundleStep
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i) :
    Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) (i + 1) :=
  greedyBundleStep codec n i hi dec B

/-- Block 5 surface: the step is additive in gate count (prior bundle shared). -/
theorem check_gates_greedyBundleStep
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i) :
    (greedyBundleStep codec n i hi dec B).gates
      = B.gates + (greedyStepHead codec n i hi dec).gates :=
  gates_greedyBundleStep codec n i hi dec B

/-- Block 5 surface: one greedy step adds at most `size dec + 2·M(n)`. -/
theorem check_size_greedyStepHead_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    C_DAG.size (greedyStepHead codec n i hi dec)
      ≤ C_DAG.size dec + 2 * treeMCSPPrefixM codec n :=
  size_greedyStepHead_le codec n i hi dec

/-- Block 5 surface: prior outputs preserved by the step. -/
theorem check_evalOutput_greedyBundleStep_old
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i)
    (o : Fin i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleStep codec n i hi dec B).evalOutput (Fin.castAdd 1 o) x
      = B.evalOutput o x :=
  evalOutput_greedyBundleStep_old codec n i hi dec B o x

/-- Block 5 surface: the new bit is the decider run on the prefix-state `(i, p)`
query, `p` the prior bundle outputs on `x`. -/
theorem check_evalOutput_greedyBundleStep_new
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleStep codec n i hi dec B).evalOutput (Fin.natAdd i (0 : Fin 1)) x
      = C_DAG.eval dec
          (prefixStateQueryValue codec n i hi x (fun k => B.evalOutput k x)) :=
  evalOutput_greedyBundleStep_new codec n i hi dec B x

end TreeMCSPGreedyBundleStepSurface

section TreeMCSPGreedyBundleFoldSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 6 surface: the recursive shared-bundle greedy fold of `i` bits. -/
def check_greedyBundleUpTo
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Nat)
    (hi : i ≤ codec.witnessBits n) :
    Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i :=
  greedyBundleUpTo codec n dec i hi

/-- Block 6 surface (headline): the fold of `i` greedy bits has at most
`i · (size dec + 2·M(n))` gates — linear in `i`, the Option ① size payoff. -/
theorem check_gates_greedyBundleUpTo_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Nat)
    (hi : i ≤ codec.witnessBits n) :
    (greedyBundleUpTo codec n dec i hi).gates
      ≤ i * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) :=
  gates_greedyBundleUpTo_le codec n dec i hi

/-- Block 6 surface: old greedy bits preserved across the fold. -/
theorem check_evalOutput_greedyBundleUpTo_old
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n)
    (o : Fin i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleUpTo codec n dec (i + 1) hi).evalOutput (Fin.castAdd 1 o) x
      = (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).evalOutput o x :=
  evalOutput_greedyBundleUpTo_old codec n i dec hi o x

/-- Block 6 surface: the newest greedy bit = decider run on the prefix-state
`(i, p)` query, `p` the previous fold's outputs on `x`. -/
theorem check_evalOutput_greedyBundleUpTo_new
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleUpTo codec n dec (i + 1) hi).evalOutput (Fin.natAdd i (0 : Fin 1)) x
      = C_DAG.eval dec
          (prefixStateQueryValue codec n i (Nat.le_of_succ_le hi) x
            (fun k => (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).evalOutput k x)) :=
  evalOutput_greedyBundleUpTo_new codec n i dec hi x

end TreeMCSPGreedyBundleFoldSurface

section TreeMCSPGreedyOutputCircuitsSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 7 surface: per-witness-bit output circuit over the instance bits. -/
def check_greedyOutputCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
  greedyOutputCircuit codec n dec i

/-- Block 7 surface: the `i`-th output circuit computes the `i`-th greedy bit. -/
theorem check_eval_greedyOutputCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    C_DAG.eval (greedyOutputCircuit codec n dec i) x
      = (fullGreedyBundle codec n dec).evalOutput i x :=
  eval_greedyOutputCircuit codec n dec i x

/-- Block 7 surface (headline): uniform size bound on every output circuit,
independent of `i`. -/
theorem check_size_greedyOutputCircuit_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.size (greedyOutputCircuit codec n dec i)
      ≤ codec.witnessBits n * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) + 1 :=
  size_greedyOutputCircuit_le codec n dec i

end TreeMCSPGreedyOutputCircuitsSurface

section PrefixExtendableSplitSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 7.5 surface: `PrefixExtendableInput` is `WitnessPrefixExtendable` on the
parsed `(n, x, i, p)` data. -/
theorem check_prefixExtendableInput_iff_witnessPrefixExtendable
    {problem : Frontier.SearchMCSPCompressionProblem} {m : Nat} (input : PrefixInput problem m) :
    PrefixExtendableInput input ↔
      WitnessPrefixExtendable input.n input.x input.prefixLength_le input.p :=
  prefixExtendableInput_iff_witnessPrefixExtendable input

/-- Block 7.5 surface: the greedy split — an extendable prefix has an extendable
next-bit extension. -/
theorem check_witnessPrefixExtendable_split
    {problem : Frontier.SearchMCSPCompressionProblem}
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p true)
      ∨ WitnessPrefixExtendable n x hi' (Fin.snoc p false) :=
  witnessPrefixExtendable_split n x hi' p hp

/-- Block 7.5 surface: the reject branch (false). -/
theorem check_witnessPrefixExtendable_snoc_false_of_not_true
    {problem : Frontier.SearchMCSPCompressionProblem}
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p)
    (hnt : ¬ WitnessPrefixExtendable n x hi' (Fin.snoc p true)) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p false) :=
  witnessPrefixExtendable_snoc_false_of_not_true n x hi' p hp hnt

/-- Block 7.5 surface: the reject branch (true). -/
theorem check_witnessPrefixExtendable_snoc_true_of_not_false
    {problem : Frontier.SearchMCSPCompressionProblem}
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p)
    (hnf : ¬ WitnessPrefixExtendable n x hi' (Fin.snoc p false)) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p true) :=
  witnessPrefixExtendable_snoc_true_of_not_false n x hi' p hp hnf

end PrefixExtendableSplitSurface

section TreeMCSPGreedyExtendableSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 8a surface: the greedy prefix of length `i` (the bundle outputs on `x`). -/
def check_greedyPrefix
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (i : Nat) (hi : i ≤ codec.witnessBits n) :
    PrefixBitVec i :=
  greedyPrefix codec n dec x i hi

/-- Block 8a surface (headline): on a promise instance, with a correct next-bit
decider, the greedy prefix of every length is extendable to a valid witness. -/
theorem check_greedyPrefix_extendable
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec)
    (i : Nat) (hi : i ≤ codec.witnessBits n) :
    WitnessPrefixExtendable (problem := treeProblem codec) n x hi
      (greedyPrefix codec n dec x i hi) :=
  greedyPrefix_extendable codec n dec x hpromise hdec i hi

/-- Block 8a surface: the true-extension query bit equals the encoded `p ++ true`
prefix-state query bit (the alignment that makes `CorrectNextBitDecider`
dischargeable from an ordinary prefix-extension decider). -/
theorem check_eval_prefixTrueExtensionQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i + 1 ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (prefixTrueExtensionQueryBitCircuit codec n i hi j) (Fin.append x p)
      = prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true) j :=
  eval_prefixTrueExtensionQueryBitCircuit codec n i hi x p j

/-- Block 8a surface: one true-extension greedy step adds at most `size dec + 2·M(n)`
gates (feasibility for the corrected greedy). -/
theorem check_size_greedyTrueStepHead_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i + 1 ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    C_DAG.size (greedyTrueStepHead codec n i hi dec)
      ≤ C_DAG.size dec + 2 * treeMCSPPrefixM codec n :=
  size_greedyTrueStepHead_le codec n i hi dec

end TreeMCSPGreedyExtendableSurface

section TreeMCSPGreedyTrueOutputCircuitsSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 7′ surface: the correctness-bearing per-witness-bit output circuit. -/
def check_greedyTrueOutputCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
  greedyTrueOutputCircuit codec n dec i

/-- Block 7′ surface: the `i`-th true-greedy output circuit computes the `i`-th
true-greedy bit. -/
theorem check_eval_greedyTrueOutputCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    C_DAG.eval (greedyTrueOutputCircuit codec n dec i) x
      = (fullGreedyTrueBundle codec n dec).evalOutput i x :=
  eval_greedyTrueOutputCircuit codec n dec i x

/-- Block 7′ surface (headline): uniform size bound on every true-greedy output
circuit, independent of `i`. -/
theorem check_size_greedyTrueOutputCircuit_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.size (greedyTrueOutputCircuit codec n dec i)
      ≤ codec.witnessBits n * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) + 1 :=
  size_greedyTrueOutputCircuit_le codec n dec i

end TreeMCSPGreedyTrueOutputCircuitsSurface

section TreeMCSPDeciderCorrectSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 8b surface: a decider for the prefix-extension language is a correct
next-bit decider (discharges the Block 8a hypothesis). -/
theorem check_correctNextBitDecider_of_decidesLanguage
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hdec : DecidesPrefixExtensionLanguage codec n dec) :
    CorrectNextBitDecider codec n x dec :=
  correctNextBitDecider_of_decidesLanguage codec n dec x hdec

end TreeMCSPDeciderCorrectSurface

section TreeMCSPGreedySolvesSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 8c surface: the full true-greedy prefix is a solving witness. -/
theorem check_greedyPrefix_solves
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec) :
    (treeProblem codec).relation n x
      (greedyPrefix codec n dec x (codec.witnessBits n) (Nat.le_refl _)) :=
  greedyPrefix_solves codec n dec x hpromise hdec

/-- Block 8c surface (headline): the joint output of the true-greedy output circuits
satisfies the search relation. -/
theorem check_greedyTrueOutputCircuit_solves
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec) :
    (treeProblem codec).relation n x
      (Frontier.searchSolverOutput (problem := treeProblem codec) (greedyTrueOutputCircuit codec n dec) x) :=
  greedyTrueOutputCircuit_solves codec n dec x hpromise hdec

end TreeMCSPGreedySolvesSurface

section TreeMCSPBoundedSolverSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9 surface: a language-correct, size-bounded prefix-extension decider
family assembles into a `BoundedSearchSolver` for the tree-MCSP search problem. -/
def check_boundedSearchSolver_of_deciderFamily
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (dec : ∀ n, C_DAG.Family (treeMCSPPrefixM codec n))
    (decSizeBound : Nat → Nat)
    (hlang : ∀ n, DecidesPrefixExtensionLanguage codec n (dec n))
    (hsize : ∀ n, C_DAG.size (dec n) ≤ decSizeBound n) :
    Frontier.BoundedSearchSolver (treeProblem codec) C_DAG
      (boundedSolverSizeBound codec decSizeBound) :=
  boundedSearchSolver_of_deciderFamily codec dec decSizeBound hlang hsize

end TreeMCSPBoundedSolverSurface

section BoundedSolverFromPpolySurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9b surface: if the prefix-extension language is in `PpolyDAG`, a
`BoundedSearchSolver` with the extracted size schedule exists. -/
theorem check_boundedSearchSolver_of_PpolyDAG_prefixExtension
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hPpoly : Pnp3.ComplexityInterfaces.PpolyDAG
      (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))) :
    ∃ c : Nat,
      Nonempty
        (Frontier.BoundedSearchSolver (treeProblem codec) C_DAG
          (fun n =>
            codec.witnessBits n *
                ((treeMCSPPrefixM codec n) ^ c + c + 2 * treeMCSPPrefixM codec n)
              + 1)) :=
  boundedSearchSolver_of_PpolyDAG_prefixExtension codec hPpoly

end BoundedSolverFromPpolySurface

section NoSolverContrapositiveSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9c surface: if no bounded solver exists at any extracted schedule, the
prefix-extension language is not in `PpolyDAG`. -/
theorem check_not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hNo : NoExtractedScheduleSolver codec) :
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)) :=
  not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver codec hNo

end NoSolverContrapositiveSurface

section ExtractedScheduleGrowthSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9d surface: `BoundedSearchSolver` monotonicity in its size schedule. -/
theorem check_nonempty_boundedSearchSolver_mono_sizeBound
    {problem : Frontier.SearchMCSPCompressionProblem} {C : AlgorithmsToLowerBounds.CircuitFamilyClass}
    {small big : Nat → Nat}
    (h : Nonempty (Frontier.BoundedSearchSolver problem C small))
    (hle : ∀ n, small n ≤ big n) :
    Nonempty (Frontier.BoundedSearchSolver problem C big) :=
  nonempty_boundedSearchSolver_mono_sizeBound h hle

/-- Block 9d surface (headline): under explicit polynomial growth assumptions, no
polynomial-size bounded search solver implies the prefix-extension language is not in
`PpolyDAG`. -/
theorem check_not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec) :
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)) :=
  not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver codec hGrowth hNoPoly

end ExtractedScheduleGrowthSurface

section ConditionalVerifiedSourceSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9e surface: under explicit growth assumptions, the open polynomial weak
lower bound, and an explicit `NP`-membership hypothesis, assemble a
`VerifiedNPDAGLowerBoundSource`. -/
noncomputable def check_verifiedSource_of_noPolynomialBoundedSearchSolver
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec)
    (hNP :
      Pnp3.ComplexityInterfaces.NP
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))) :
    AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_noPolynomialBoundedSearchSolver codec hGrowth hNoPoly hNP

/-- Block 9e surface (headline): the same three explicit hypotheses yield the
conditional `NP ⊄ PpolyDAG` separation. -/
theorem check_NP_not_subset_PpolyDAG_of_noPolynomialBoundedSearchSolver
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec)
    (hNP :
      Pnp3.ComplexityInterfaces.NP
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_noPolynomialBoundedSearchSolver codec hGrowth hNoPoly hNP

end ConditionalVerifiedSourceSurface

section WitnessGrowthReductionSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 10a surface: `bitLength m ≤ m`. -/
theorem check_bitLength_le_self (m : Nat) : bitLength m ≤ m :=
  bitLength_le_self m

/-- Block 10a surface: the concrete ambient length is poly-bounded in the
truth-table length given only the witness-length assumption. -/
theorem check_polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hW : PolyBoundedInTable codec.witnessBits) :
    PolyBoundedInTable (treeMCSPPrefixM codec) :=
  polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly codec hW

/-- Block 10a surface (headline): the full extraction growth assumptions follow
from the single witness-length assumption. -/
theorem check_treeMCSPExtractionGrowthAssumptions_of_witnessPoly
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hW : PolyBoundedInTable codec.witnessBits) :
    TreeMCSPExtractionGrowthAssumptions codec :=
  treeMCSPExtractionGrowthAssumptions_of_witnessPoly codec hW

/-- Block 10a surface: the minimal `PolynomialWitnessCodec` interface yields the
extraction growth assumptions. -/
theorem check_PolynomialWitnessCodec_toGrowthAssumptions
    {threshold : Nat → Nat}
    (P : PolynomialWitnessCodec threshold) :
    TreeMCSPExtractionGrowthAssumptions P.codec :=
  P.toGrowthAssumptions

end WitnessGrowthReductionSurface

section PrefixExtensionNPWitnessSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 11a surface (headline): a concrete TM-witness package yields NP-membership
of the prefix-extension language. -/
theorem check_prefixExtensionLanguage_in_NP_of_witness
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    (W : PrefixExtensionNPWitness parser) :
    Pnp3.ComplexityInterfaces.NP (PrefixExtensionLanguage parser) :=
  prefixExtensionLanguage_in_NP_of_witness parser W

end PrefixExtensionNPWitnessSurface

section ExplicitConditionalSourceSurface

open Pnp4.Frontier.ContractExpansion

/-- Capstone surface: the three explicit interfaces (growth-witness codec, no-poly
solver, NP TM-witness) assemble a `VerifiedNPDAGLowerBoundSource`. -/
noncomputable def check_verifiedSource_of_explicit_interfaces
    {threshold : Nat → Nat}
    (wcodec : PolynomialWitnessCodec threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver wcodec.codec)
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold wcodec.codec)) :
    AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_explicit_interfaces wcodec hNoPoly hNPWit

/-- Capstone surface (headline): the three explicit interfaces yield the conditional
`NP ⊄ PpolyDAG` separation. -/
theorem check_NP_not_subset_PpolyDAG_of_explicit_interfaces
    {threshold : Nat → Nat}
    (wcodec : PolynomialWitnessCodec threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver wcodec.codec)
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold wcodec.codec)) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_explicit_interfaces wcodec hNoPoly hNPWit

end ExplicitConditionalSourceSurface

section ConcreteCodecGapSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12a surface: the fixed-width packing round-trip (read-back recovers the
list plus a `false` pad). -/
theorem check_ofFn_listToFixedBitVec
    (l : List Bool) (L : Nat) (hL : l.length ≤ L) :
    List.ofFn (listToFixedBitVec l L) = l ++ List.replicate (L - l.length) false :=
  ofFn_listToFixedBitVec l L hL

/-- Block 12a surface (headline): a self-delimiting circuit code with a width bound
yields a concrete `TreeCircuitWitnessCodec` (the proved padding reduction). -/
def check_SelfDelimitingCircuitCode_toCodec
    {threshold : Nat → Nat}
    (S : SelfDelimitingCircuitCode threshold) :
    Frontier.TreeCircuitWitnessCodec threshold :=
  S.toCodec

end ConcreteCodecGapSurface

section CircuitTreeBridgeSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12b surface: the bridge is a left inverse. -/
theorem check_fromTree_toTree {n : Nat} (c : Pnp3.Models.Circuit n) :
    fromTree (toTree c) = c :=
  fromTree_toTree c

/-- Block 12b surface: the bridge preserves gate count. -/
theorem check_size_toTree {n : Nat} (c : Pnp3.Models.Circuit n) :
    (toTree c).size = Pnp3.Models.Circuit.size c :=
  size_toTree c

/-- Block 12b surface (headline): the native `Circuit` encoder/decoder round-trips
(for all `n`, including `n = 0`). -/
theorem check_decodeCircuit_encodeCircuit (n : Nat) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : Pnp3.Models.Circuit n)
    (d : Nat) (h_d : Pnp3.Models.Circuit.size c ≤ d) (rest : List Bool) :
    decodeCircuit n width d (encodeCircuit width h_width c ++ rest)
      = some (c, rest) :=
  decodeCircuit_encodeCircuit n width h_width c d h_d rest

end CircuitTreeBridgeSurface

section CircuitEncodingLengthSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12c surface (headline): the native `Circuit` encoding has length at most
`(width + 4) · size c`. -/
theorem check_length_encodeCircuit_le {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (c : Pnp3.Models.Circuit n) :
    (encodeCircuit width h_width c).length ≤ (width + 4) * Pnp3.Models.Circuit.size c :=
  length_encodeCircuit_le width h_width c

end CircuitEncodingLengthSurface

section CircuitDecodeDepthFreeSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12d surface: the native encoding-length lower bound. -/
theorem check_length_encodeCircuit_ge {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (c : Pnp3.Models.Circuit n) :
    3 * Pnp3.Models.Circuit.size c ≤ (encodeCircuit width h_width c).length :=
  length_encodeCircuit_ge width h_width c

/-- Block 12d surface (headline): the depth-free decoder round-trips with no
`size ≤ d` side condition (for all `n`, including `n = 0`). -/
theorem check_decodeCircuitFull_encodeCircuit (n : Nat) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : Pnp3.Models.Circuit n) (rest : List Bool) :
    decodeCircuitFull n width (encodeCircuit width h_width c ++ rest)
      = some (c, rest) :=
  decodeCircuitFull_encodeCircuit n width h_width c rest

end CircuitDecodeDepthFreeSurface

section ConcreteTreeCodecSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12e surface (headline): a concrete `TreeCircuitWitnessCodec` exists for
every `threshold`. -/
def check_treeCircuitWitnessCodec (threshold : Nat → Nat) :
    Frontier.TreeCircuitWitnessCodec threshold :=
  treeCircuitWitnessCodec threshold

/-- Block 12e surface: under the single threshold-growth premise, the concrete codec
packages as a `PolynomialWitnessCodec`. -/
def check_treePolynomialWitnessCodec (threshold : Nat → Nat)
    (hT : PolyBoundedInTable threshold) :
    PolynomialWitnessCodec threshold :=
  treePolynomialWitnessCodec threshold hT

end ConcreteTreeCodecSurface

section ConcreteTreeCodecSourceSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12f surface: the concrete-codec verified source from the three explicit
interfaces (threshold growth, no-poly solver, NP TM-witness). -/
noncomputable def check_verifiedSource_of_treeCodec_noPolynomialBoundedSearchSolver
    (threshold : Nat → Nat)
    (hThresholdPoly : PolyBoundedInTable threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec threshold))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold (treeCircuitWitnessCodec threshold))) :
    AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_treeCodec_noPolynomialBoundedSearchSolver
    threshold hThresholdPoly hNoPoly hNPWit

/-- Block 12f surface (headline): the concrete-codec conditional `NP ⊄ PpolyDAG`
separation. -/
theorem check_NP_not_subset_PpolyDAG_of_treeCodec_interfaces
    (threshold : Nat → Nat)
    (hThresholdPoly : PolyBoundedInTable threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec threshold))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold (treeCircuitWitnessCodec threshold))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_treeCodec_interfaces
    threshold hThresholdPoly hNoPoly hNPWit

end ConcreteTreeCodecSourceSurface

section ThresholdGrowthSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 13a surface: the quadratic threshold is polynomially bounded in the
truth-table length. -/
theorem check_polyBoundedInTable_thresholdQuadratic :
    PolyBoundedInTable thresholdQuadratic :=
  polyBoundedInTable_thresholdQuadratic

/-- Block 13a surface (headline): every fixed polynomial threshold `nᵏ + k` is
polynomially bounded in the truth-table length. -/
theorem check_polyBoundedInTable_thresholdPoly (k : Nat) :
    PolyBoundedInTable (thresholdPoly k) :=
  polyBoundedInTable_thresholdPoly k

end ThresholdGrowthSurface

section ConsolidatedTreeSeparationSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 13b surface: at a concrete polynomial threshold, the verified source rests
on only the two genuinely-hard inputs (lower bound + NP witness). -/
noncomputable def check_verifiedSource_treePoly
    (k : Nat)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser (thresholdPoly k) (treeCircuitWitnessCodec (thresholdPoly k)))) :
    AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource :=
  verifiedSource_treePoly k hNoPoly hNPWit

/-- Block 13b surface (headline): the consolidated conditional `NP ⊄ PpolyDAG` at a
concrete polynomial threshold. -/
theorem check_NP_not_subset_PpolyDAG_treePoly
    (k : Nat)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser (thresholdPoly k) (treeCircuitWitnessCodec (thresholdPoly k)))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_treePoly k hNoPoly hNPWit

end ConsolidatedTreeSeparationSurface

section TreeMCSPZeroPrefixBuilderSurface

open Pnp4.Frontier.ContractExpansion

def check_zeroPrefixQueryCircuitBuilder
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold) :
    QueryCircuitBuilder
      (fun n => Pnp3.Models.Partial.tableLen n)
      (fun n => treeMCSPPrefixM codec n) :=
  zeroPrefixQueryCircuitBuilder codec

def check_treeMCSPZeroPrefixQueryBuilder
    (threshold : Nat → Nat)
    (codec : Frontier.TreeCircuitWitnessCodec threshold) :
    PrefixQueryBuilder
      (Frontier.treeMCSPSearchProblem threshold
        (Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPConcretePrefixParser threshold codec) :=
  treeMCSPZeroPrefixQueryBuilder threshold codec

theorem check_treeMCSPZeroPrefixQueryBuilder_queryValue
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (treeMCSPZeroPrefixQueryBuilder threshold codec).queryValue n x =
      zeroPrefixQueryValue codec n x :=
  treeMCSPZeroPrefixQueryBuilder_queryValue codec n x

end TreeMCSPZeroPrefixBuilderSurface

section NaiveGreedySizeSpikeSurface

open Pnp4.Frontier.ContractExpansion
open Pnp3.ComplexityInterfaces (DagCircuit)

theorem check_geometric_lower_bound (f : Nat → Nat)
    (hstep : ∀ i, (∑ k ∈ Finset.range (i + 1), f k) ≤ f (i + 1)) (i : Nat) :
    f 0 * 2 ^ i ≤ f (i + 1) :=
  geometric_lower_bound f hstep i

theorem check_composeDeciderWithQuery_eq_substInputs
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    composeDeciderWithQuery decider queryBit
      = DagCircuit.substInputs decider queryBit :=
  composeDeciderWithQuery_eq_substInputs decider queryBit

theorem check_naiveGreedyModel_size_ge (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) (i : Nat) :
    seed.gates * 2 ^ i ≤ DagCircuit.size (naiveGreedyModel m seed decider (i + 1)) :=
  naiveGreedyModel_size_ge m seed decider i

theorem check_naiveGreedyModel_size_ge_pow (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) (i : Nat) (hseed : 1 ≤ seed.gates) :
    2 ^ i ≤ DagCircuit.size (naiveGreedyModel m seed decider (i + 1)) :=
  naiveGreedyModel_size_ge_pow m seed decider i hseed

theorem check_pow_le_of_linear_witnessBits (W n c : Nat) (h : W ≤ c * n + c) :
    2 ^ W ≤ (2 ^ n) ^ c * 2 ^ c :=
  pow_le_of_linear_witnessBits W n c h

theorem check_pow_quadratic_gt_poly (n c : Nat) (hn : 0 < n) (hc : c < n) :
    (2 ^ n) ^ c < 2 ^ (n * n) :=
  pow_quadratic_gt_poly n c hn hc

end NaiveGreedySizeSpikeSurface

section PrefixExtensionLanguageSurface

open Pnp4.Frontier.ContractExpansion

def check_PrefixParser
    (problem : Frontier.SearchMCSPCompressionProblem) : Type :=
  PrefixParser problem

def check_parsePrefixInput
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : AlgorithmsToLowerBounds.BitVec m) :
    Option (PrefixInput problem m) :=
  parsePrefixInput parser y

def check_PrefixExtendable
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : AlgorithmsToLowerBounds.BitVec m) : Prop :=
  PrefixExtendable parser y

noncomputable def check_PrefixExtensionLanguage
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) : Pnp3.ComplexityInterfaces.Language :=
  PrefixExtensionLanguage parser

theorem check_PrefixExtensionLanguage_rejects_malformed
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : AlgorithmsToLowerBounds.BitVec m)
    (hparse : parsePrefixInput parser y = none) :
    PrefixExtensionLanguage parser m y = false :=
  PrefixExtensionLanguage_rejects_malformed parser y hparse


section PrefixExtensionLanguageRuntimeSurface

open Pnp4.Frontier.ContractExpansion

def check_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) : Nat :=
  treeMCSPPrefixAmbientLength overhead witnessBits padBits n

theorem check_tableLen_le_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength overhead witnessBits padBits n :=
  tableLen_le_treeMCSPPrefixAmbientLength overhead witnessBits padBits n

def check_PolynomiallyBoundedInAmbient
    (M f : Nat → Nat) : Prop :=
  PolynomiallyBoundedInAmbient M f

def check_RuntimeAwareTreeCircuitCodec
    (threshold M : Nat → Nat) : Type :=
  RuntimeAwareTreeCircuitCodec threshold M

def check_RuntimeAwarePrefixParser
    (problem : Frontier.SearchMCSPCompressionProblem)
    (M : Nat → Nat) : Type :=
  RuntimeAwarePrefixParser problem M

def check_TreeMCSPPrefixRuntimeBudget
    (threshold M : Nat → Nat)
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (parser : PrefixParser (Frontier.treeMCSPSearchProblem threshold
      (Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec))) : Type :=
  TreeMCSPPrefixRuntimeBudget threshold M codec parser

end PrefixExtensionLanguageRuntimeSurface

end PrefixExtensionLanguageSurface

def check_NotInClass :
    ∀ (C : CircuitFamilyClass) (L : BitVecLanguage),
      NotInClass C L → NotInClass C L :=
  fun _ _ h => h

def check_maskBit_true (x : Bool) :
    maskBit true x = x :=
  maskBit_true x

def check_maskBit_false (x : Bool) :
    maskBit false x = false :=
  maskBit_false x

def check_maskVec_apply
    {n : Nat} (keep x : AlgorithmsToLowerBounds.BitVec n) (i : Fin n) :
    maskVec keep x i = maskBit (keep i) (x i) :=
  maskVec_apply keep x i

def check_closedUnderInputMasking_eval
    {C : CircuitFamilyClass}
    (closed : ClosedUnderInputMasking C)
    {n : Nat}
    (keep x : AlgorithmsToLowerBounds.BitVec n)
    (c : C.Family n) :
    C.eval (closed.maskCircuit keep c) x = C.eval c (maskVec keep x) :=
  closed.eval_maskCircuit keep c x

def check_closedUnderInputMasking_size
    {C : CircuitFamilyClass}
    (closed : ClosedUnderInputMasking C)
    {n : Nat}
    (keep : AlgorithmsToLowerBounds.BitVec n)
    (c : C.Family n) :
    C.size (closed.maskCircuit keep c) ≤ C.size c :=
  closed.size_maskCircuit keep c

noncomputable def check_expectationProductBias
    {n : Nat}
    (bias : Rat)
    (F : AlgorithmsToLowerBounds.BitVec n → Rat) : Rat :=
  expectationProductBias bias F

theorem check_expectationProductBias_sub
    {n : Nat}
    (bias : Rat)
    (F G : AlgorithmsToLowerBounds.BitVec n → Rat) :
    expectationProductBias bias (fun x => F x - G x) =
      expectationProductBias bias F - expectationProductBias bias G :=
  expectationProductBias_sub bias F G

theorem check_expectationProductBias_le_of_pointwise_le
    {n : Nat}
    {bias bound : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (F : AlgorithmsToLowerBounds.BitVec n → Rat)
    (hF : ∀ x : AlgorithmsToLowerBounds.BitVec n, F x ≤ bound) :
    expectationProductBias bias F ≤ bound :=
  expectationProductBias_le_of_pointwise_le
    hBias_nonneg
    hBias_le_one
    F
    hF

theorem check_exists_max_bitVec_rat
    {n : Nat}
    (F : AlgorithmsToLowerBounds.BitVec n → Rat) :
    ∃ x0 : AlgorithmsToLowerBounds.BitVec n,
      ∀ x : AlgorithmsToLowerBounds.BitVec n, F x ≤ F x0 :=
  exists_max_bitVec_rat F

noncomputable def check_maskedAcceptanceAverage
    {n : Nat}
    (keepBias inputBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) : Rat :=
  maskedAcceptanceAverage keepBias inputBias A

theorem check_maskedAcceptanceAverage_eq_acceptanceProbability_mul
    {n : Nat}
    (keepBias inputBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) :
    maskedAcceptanceAverage keepBias inputBias A =
      acceptanceProbability (keepBias * inputBias) A :=
  maskedAcceptanceAverage_eq_acceptanceProbability_mul keepBias inputBias A

def check_maskingBiasParams_derived
    (params : MaskingBiasParams) :
    Rat × Rat × Rat × Rat × Rat :=
  (params.lowSourceBias,
    params.highSourceBias,
    params.lowTargetBias,
    params.highTargetBias,
    params.keepBias)

theorem check_maskingBiasParams_keepBias_nonneg
    (params : MaskingBiasParams) :
    0 ≤ params.keepBias :=
  params.keepBias_nonneg

theorem check_maskingBiasParams_keepBias_le_one
    (params : MaskingBiasParams) :
    params.keepBias ≤ 1 :=
  params.keepBias_le_one

theorem check_maskingBiasParams_keepBias_mul_highTargetBias
    (params : MaskingBiasParams) :
    params.keepBias * params.highTargetBias = params.highSourceBias :=
  params.keepBias_mul_highTargetBias

theorem check_maskingBiasParams_keepBias_mul_lowTargetBias
    (params : MaskingBiasParams) :
    params.keepBias * params.lowTargetBias = params.lowSourceBias :=
  params.keepBias_mul_lowTargetBias

def check_maskingPushforwardFacts_type
    (n : Nat)
    (params : MaskingBiasParams) : Prop :=
  MaskingPushforwardFacts n params

theorem check_maskingPushforwardFacts_of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    MaskingPushforwardFacts n params :=
  MaskingPushforwardFacts.of_maskingBiasParams params n

noncomputable def check_maskedAcceptanceAdvantage
    {n : Nat}
    (keepBias targetLowBias targetHighBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) : Rat :=
  maskedAcceptanceAdvantage keepBias targetLowBias targetHighBias A

noncomputable def check_fixedMaskAcceptanceAdvantage
    {n : Nat}
    (keep : AlgorithmsToLowerBounds.BitVec n)
    (targetLowBias targetHighBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) : Rat :=
  fixedMaskAcceptanceAdvantage keep targetLowBias targetHighBias A

theorem check_maskedAcceptanceAdvantage_eq_expectation_fixed
    {n : Nat}
    (keepBias targetLowBias targetHighBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) :
    maskedAcceptanceAdvantage keepBias targetLowBias targetHighBias A =
      expectationProductBias keepBias
        (fun keep =>
          fixedMaskAcceptanceAdvantage keep targetLowBias targetHighBias A) :=
  maskedAcceptanceAdvantage_eq_expectation_fixed
    keepBias
    targetLowBias
    targetHighBias
    A

theorem check_maskingPushforwardFacts_masked_advantage_eq_source
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : MaskingPushforwardFacts n params)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) :
    maskedAcceptanceAdvantage
        params.keepBias
        params.lowTargetBias
        params.highTargetBias
        A =
      acceptanceProbability params.highSourceBias A -
        acceptanceProbability params.lowSourceBias A :=
  facts.masked_advantage_eq_source A

def check_maskAveragingContract_type
    (n : Nat)
    (keepBias : Rat) : Prop :=
  MaskAveragingContract n keepBias

theorem check_maskAveragingContract_of_valid_keepBias
    {n : Nat}
    {keepBias : Rat}
    (hKeep_nonneg : 0 ≤ keepBias)
    (hKeep_le_one : keepBias ≤ 1) :
    MaskAveragingContract n keepBias :=
  MaskAveragingContract.of_valid_keepBias hKeep_nonneg hKeep_le_one

theorem check_maskAveragingContract_of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    MaskAveragingContract n params.keepBias :=
  MaskAveragingContract.of_maskingBiasParams params n

def check_coinMaskingTranslationFacts_type
    (params : MaskingBiasParams)
    (n : Nat) : Prop :=
  CoinMaskingTranslationFacts params n

theorem check_coinMaskingTranslationFacts_of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    CoinMaskingTranslationFacts params n :=
  CoinMaskingTranslationFacts.of_maskingBiasParams params n

def check_coinMaskingClassTranslationFacts_type
    (C : CircuitFamilyClass)
    (params : MaskingBiasParams)
    (n : Nat) : Type :=
  CoinMaskingClassTranslationFacts C params n

theorem check_coinMaskingTranslationFacts_exists_mask_with_source_advantage
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : CoinMaskingTranslationFacts params n)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool)
    {adv : Rat}
    (hAdv :
      adv ≤
        acceptanceProbability params.highSourceBias A -
          acceptanceProbability params.lowSourceBias A) :
    ∃ keep : AlgorithmsToLowerBounds.BitVec n,
      adv ≤
        fixedMaskAcceptanceAdvantage
          keep
          params.lowTargetBias
          params.highTargetBias
          A :=
  facts.exists_mask_with_source_advantage A hAdv

noncomputable def check_bestMaskForCircuit
    {C : CircuitFamilyClass}
    {n : Nat}
    (targetLowBias targetHighBias : Rat)
    (c : C.Family n) :
    AlgorithmsToLowerBounds.BitVec n :=
  bestMaskForCircuit targetLowBias targetHighBias c

theorem check_bestMaskForCircuit_max
    {C : CircuitFamilyClass}
    {n : Nat}
    (targetLowBias targetHighBias : Rat)
    (c : C.Family n) :
    ∀ keep : AlgorithmsToLowerBounds.BitVec n,
      fixedMaskAcceptanceAdvantage
        keep
        targetLowBias
        targetHighBias
        (fun x => C.eval c x) ≤
      fixedMaskAcceptanceAdvantage
        (bestMaskForCircuit targetLowBias targetHighBias c)
        targetLowBias
        targetHighBias
        (fun x => C.eval c x) :=
  bestMaskForCircuit_max targetLowBias targetHighBias c

theorem check_source_advantage_le_bestMask_fixed_advantage
    {C : CircuitFamilyClass}
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : CoinMaskingTranslationFacts params n)
    (c : C.Family n)
    {adv : Rat}
    (hSourceAdv :
      adv ≤
        acceptanceProbability params.highSourceBias (fun x => C.eval c x) -
          acceptanceProbability params.lowSourceBias (fun x => C.eval c x)) :
    adv ≤
      fixedMaskAcceptanceAdvantage
        (bestMaskForCircuit params.lowTargetBias params.highTargetBias c)
        params.lowTargetBias
        params.highTargetBias
        (fun x => C.eval c x) :=
  source_advantage_le_bestMask_fixed_advantage facts c hSourceAdv

def check_coinMaskingTranslationSetup_type
    (source : CoinDistinguisherFamily)
    (target : HalfVsFairTruthTableCoinHardness) : Type :=
  CoinMaskingTranslationSetup source target

noncomputable def check_coinTranslationPreservesClass_of_maskingSetup
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {target : HalfVsFairTruthTableCoinHardness}
    (closed : ClosedUnderInputMasking C)
    (setup : CoinMaskingTranslationSetup source target)
    (facts :
      ∀ n : Nat,
        CoinMaskingTranslationFacts (setup.params n) (source.sampleBits n)) :
    CoinTranslationPreservesClass C source target :=
  coinTranslationPreservesClass_of_maskingSetup closed setup facts

def check_AC0pFamilyModelWithMasking_to_model
    (model : AC0pFamilyModelWithMasking) :
    AC0pFamilyModel :=
  model.toAC0pFamilyModel

def check_AC0pFamilyModelWithMasking_closed
    (model : AC0pFamilyModelWithMasking)
    (p depth : Nat) :
    ClosedUnderInputMasking (model.toAC0pFamilyModel.classOf p depth) :=
  model.closed p depth

noncomputable def check_coinTranslationPreservesClass_of_maskingSetup_AC0p
    {source : CoinDistinguisherFamily}
    {target : HalfVsFairTruthTableCoinHardness}
    (model : AC0pFamilyModelWithMasking)
    (p depth : Nat)
    (setup : CoinMaskingTranslationSetup source target)
    (facts :
      ∀ n : Nat,
        CoinMaskingTranslationFacts (setup.params n) (source.sampleBits n)) :
    CoinTranslationPreservesClass
      (model.toAC0pFamilyModel.classOf p depth)
      source
      target :=
  coinTranslationPreservesClass_of_maskingSetup_AC0p
    model
    p
    depth
    setup
    facts

theorem check_false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_maskingSetup
    {hardness : HalfVsFairTruthTableCoinHardness}
    (model : AC0pFamilyModelWithMasking)
    (contract :
      AC0pHalfVsFairCoinLowerBoundContract
        model.toAC0pFamilyModel
        hardness)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (setup :
      CoinMaskingTranslationSetup
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
        hardness)
    (maskFacts :
      ∀ m : Nat,
        CoinMaskingTranslationFacts
          (setup.params m)
          ((CoinDistinguisherFamily.of_adjacentBiasMCSP facts).sampleBits m))
    (circuit :
      ∀ m : Nat,
        (model.toAC0pFamilyModel.classOf p depth).Family
          (Pnp3.Models.Partial.tableLen m))
    (computes :
      ∀ m : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen m),
        (model.toAC0pFamilyModel.classOf p depth).eval (circuit m) x =
          exactTreeMCSPThresholdHardDecision m (facts.threshold m) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ m : Nat,
        (model.toAC0pFamilyModel.classOf p depth).size (circuit m) ≤
          sizeBound m)
    (hSize :
      sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_maskingSetup
    model
    contract
    facts
    hp
    setup
    maskFacts
    circuit
    computes
    sizeBound
    size_le
    hSize

def check_adjacentBiasToHalfVsFairMaskingSetupFacts_type
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (hardness : HalfVsFairTruthTableCoinHardness) : Prop :=
  AdjacentBiasToHalfVsFairMaskingSetupFacts facts hardness

def check_maskingParams_of_adjacentBiasToHalfVsFair
    {facts : AdjacentBiasMCSPThresholdSeparationFacts}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (setupFacts :
      AdjacentBiasToHalfVsFairMaskingSetupFacts facts hardness)
    (n : Nat) :
    MaskingBiasParams :=
  maskingParams_of_adjacentBiasToHalfVsFair setupFacts n

def check_coinMaskingTranslationSetup_of_adjacentBiasToHalfVsFair
    {facts : AdjacentBiasMCSPThresholdSeparationFacts}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (setupFacts :
      AdjacentBiasToHalfVsFairMaskingSetupFacts facts hardness) :
    CoinMaskingTranslationSetup
      (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
      hardness :=
  CoinMaskingTranslationSetup.of_adjacentBiasToHalfVsFair setupFacts

theorem check_false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_adjacentMaskingSetup
    {hardness : HalfVsFairTruthTableCoinHardness}
    (model : AC0pFamilyModelWithMasking)
    (contract :
      AC0pHalfVsFairCoinLowerBoundContract
        model.toAC0pFamilyModel
        hardness)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (setupFacts :
      AdjacentBiasToHalfVsFairMaskingSetupFacts facts hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (circuit :
      ∀ m : Nat,
        (model.toAC0pFamilyModel.classOf p depth).Family
          (Pnp3.Models.Partial.tableLen m))
    (computes :
      ∀ m : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen m),
        (model.toAC0pFamilyModel.classOf p depth).eval (circuit m) x =
          exactTreeMCSPThresholdHardDecision m (facts.threshold m) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ m : Nat,
        (model.toAC0pFamilyModel.classOf p depth).size (circuit m) ≤
          sizeBound m)
    (hSize :
      sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_adjacentMaskingSetup
    model
    contract
    facts
    setupFacts
    hp
    circuit
    computes
    sizeBound
    size_le
    hSize

def check_quasiPolyLower_superPolynomialGrowth :
    SuperPolynomialGrowth QuasiPolyLower :=
  quasiPolyLower_superPolynomialGrowth

def check_not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {lower : Nat → Nat}
    (hLB : SizeLowerBound C L lower)
    (hGrowth : SuperPolynomialGrowth lower) :
    ¬ HasPolynomialSizeFamily C L :=
  not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound hLB hGrowth

def check_not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    (hLB : SizeLowerBound C L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily C L :=
  not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound hLB

def check_not_hasPolynomialSizeFamily_of_eventual_superPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {lower : Nat → Nat}
    (hLB : EventuallySizeLowerBound C L lower)
    (hGrowth : SuperPolynomialGrowth lower) :
    ¬ HasPolynomialSizeFamily C L :=
  not_hasPolynomialSizeFamily_of_eventual_superPolynomial_lowerBound hLB hGrowth

def check_not_hasPolynomialSizeFamily_of_eventual_quasiPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    (hLB : EventuallySizeLowerBound C L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily C L :=
  not_hasPolynomialSizeFamily_of_eventual_quasiPolynomial_lowerBound hLB

def check_eventuallySizeLowerBound_weaken
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {strong weak : Nat → Nat}
    (hLB : EventuallySizeLowerBound C L strong)
    (hDom : EventuallyDominates strong weak) :
    EventuallySizeLowerBound C L weak :=
  EventuallySizeLowerBound.weaken hLB hDom

def check_not_depth_d_AC0p_of_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p depth : Nat)
    (L : BitVecLanguage)
    (hLB : SizeLowerBound (model.classOf p depth) L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily (model.classOf p depth) L :=
  not_depth_d_AC0p_of_quasiPoly_lowerBound model p depth L hLB

def check_not_in_AC0p_of_depthwise_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p : Nat)
    (L : BitVecLanguage)
    (hLB : ∀ depth : Nat,
      SizeLowerBound (model.classOf p depth) L QuasiPolyLower) :
    ¬ InAC0p model p L :=
  not_in_AC0p_of_depthwise_quasiPoly_lowerBound model p L hLB

def check_not_in_AC0p_from_quasiPolynomial_contract
    {model : AC0pFamilyModel}
    {L : BitVecLanguage}
    (contract : AC0pQuasiPolynomialLowerBoundContract model L)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p L :=
  not_in_AC0p_from_quasiPolynomial_contract contract p hp

def check_not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p depth : Nat)
    (L : BitVecLanguage)
    (hLB :
      EventuallySizeLowerBound (model.classOf p depth) L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily (model.classOf p depth) L :=
  not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound model p depth L hLB

def check_not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p : Nat)
    (L : BitVecLanguage)
    (hLB : ∀ depth : Nat,
      EventuallySizeLowerBound (model.classOf p depth) L QuasiPolyLower) :
    ¬ InAC0p model p L :=
  not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound model p L hLB

def check_not_in_AC0p_from_asymptotic_quasiPolynomial_contract
    {model : AC0pFamilyModel}
    {L : BitVecLanguage}
    (contract : AC0pAsymptoticQuasiPolynomialLowerBoundContract model L)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p L :=
  not_in_AC0p_from_asymptotic_quasiPolynomial_contract contract p hp

def check_treeMCSPPredicate
    (n s : Nat) (tt : TruthTable n) : Prop :=
  treeMCSPPredicate n s tt

def check_verified_source :
    VerifiedNPDAGLowerBoundSource →
      Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_verified_source

def check_verified_source_to_pne_np :
    VerifiedNPDAGLowerBoundSource →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_verified_source

def check_ac0p_restricted_source_restrictedConclusion
    (src : Frontier.AC0pRestrictedLowerBoundSource) :
    ¬ InAC0p src.model src.p src.L :=
  src.restrictedConclusion

def check_pnp4_bridge_requirement_to_pne_np :
    Frontier.PvsNPBridgeRequirement →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_pnp4_bridge_requirement

def check_restricted_source_with_dag_bridge_to_pne_np
    (restricted : Frontier.AC0pRestrictedLowerBoundSource) :
    Frontier.RestrictedToVerifiedDAGBridge restricted →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_restricted_source_and_dag_bridge restricted

def check_P_ne_NP_of_NP_not_subset_Ppoly :
    Frontier.NP_not_subset_Ppoly →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_NP_not_subset_Ppoly

def check_searchMCSPWeakLowerBound_to_np_not_subset
    (src : Frontier.SearchMCSPWeakLowerBound) :
    Frontier.NP_not_subset_Ppoly :=
  Frontier.NP_not_subset_Ppoly_of_searchMCSPWeakLowerBound src

def check_searchMCSPWeakLowerBound_to_pne_np
    (src : Frontier.SearchMCSPWeakLowerBound) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_searchMCSPWeakLowerBound src

def check_mainlineProgress_of_searchMCSPWeakLowerBound
    (src : Frontier.SearchMCSPWeakLowerBound) :
    Frontier.PvsNPMainlineProgress :=
  Frontier.PvsNPMainlineProgress.of_searchMCSPWeakLowerBound src

def check_mainlineProgress_to_pne_np :
    Frontier.PvsNPMainlineProgress →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_mainlineProgress

def check_searchMCSPWeakCircuitTarget_noBoundedSolver
    (target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget) : Prop :=
  target.noBoundedSolver

def check_searchProblemNoBoundedSolver
    (problem : Frontier.SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass)
    (sizeBound : Nat → Nat) : Prop :=
  Frontier.SearchProblemNoBoundedSolver problem C sizeBound

def check_searchMCSPWeakLowerBound_of_weakCircuitLowerBound
    {target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : Frontier.SearchMCSPWeakCircuitLowerBound target)
    (hMag : Frontier.SearchMCSPMagnificationContract target) :
    Frontier.SearchMCSPWeakLowerBound :=
  Frontier.SearchMCSPWeakLowerBound.of_weakCircuitLowerBound hWeak hMag

def check_weakCircuitLowerBound_to_np_not_subset
    {target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : Frontier.SearchMCSPWeakCircuitLowerBound target)
    (hMag : Frontier.SearchMCSPMagnificationContract target) :
    Frontier.NP_not_subset_Ppoly :=
  Frontier.NP_not_subset_Ppoly_of_weakCircuitLowerBound hWeak hMag

def check_weakCircuitLowerBound_to_pne_np
    {target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : Frontier.SearchMCSPWeakCircuitLowerBound target)
    (hMag : Frontier.SearchMCSPMagnificationContract target) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_weakCircuitLowerBound hWeak hMag

def check_mainlineProgress_of_weakCircuitLowerBound
    {target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : Frontier.SearchMCSPWeakCircuitLowerBound target)
    (hMag : Frontier.SearchMCSPMagnificationContract target) :
    Frontier.PvsNPMainlineProgress :=
  Frontier.PvsNPMainlineProgress.of_weakCircuitLowerBound hWeak hMag

def check_treeMCSPSearchProblem
    (threshold : Nat → Nat)
    (encoding : Frontier.TreeMCSPSearchWitnessEncoding threshold) :
    Frontier.SearchMCSPCompressionProblem :=
  Frontier.treeMCSPSearchProblem threshold encoding

def check_treeCircuitWitnessCodec_verifies
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : AlgorithmsToLowerBounds.BitVec (codec.witnessBits n)) : Prop :=
  codec.verifies n tt w

def check_treeCircuitWitnessCodec_sound
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : AlgorithmsToLowerBounds.BitVec (codec.witnessBits n)) :
    codec.verifies n tt w →
      treeMCSPPredicate n (threshold n) tt :=
  codec.sound n tt w

def check_treeMCSPSearchWitnessEncoding_ofCodec
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold) :
    Frontier.TreeMCSPSearchWitnessEncoding threshold :=
  Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec

def check_treeMCSPSearchWeakLowerBoundTarget
    (threshold : Nat → Nat)
    (encoding : Frontier.TreeMCSPSearchWitnessEncoding threshold)
    (C : CircuitFamilyClass)
    (sizeBound : Nat → Nat) :
    Frontier.SearchMCSPWeakCircuitLowerBoundTarget :=
  Frontier.treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound

def check_treeMCSPSearchSource_to_np_not_subset
    (src : Frontier.TreeMCSPSearchMagnificationSource) :
    Frontier.NP_not_subset_Ppoly :=
  Frontier.NP_not_subset_Ppoly_of_treeMCSPSearchMagnificationSource src

def check_treeMCSPSearchSource_to_pne_np
    (src : Frontier.TreeMCSPSearchMagnificationSource) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_treeMCSPSearchMagnificationSource src

def check_mainlineProgress_of_treeMCSPSearchSource
    (src : Frontier.TreeMCSPSearchMagnificationSource) :
    Frontier.PvsNPMainlineProgress :=
  Frontier.PvsNPMainlineProgress.of_treeMCSPSearchMagnificationSource src

def check_uniform_vs_biased_coin_instance
    (sampleBits : Nat) (ε : Rat)
    (hεpos : 0 < ε) (hεhalf : ε ≤ (1 : Rat) / 2) :
    CoinProblemInstance :=
  uniformVsBiasedCoinInstance sampleBits ε hεpos hεhalf

def check_half_vs_fair_coin_instance
    (sampleBits : Nat) (ε : Rat)
    (hεpos : 0 < ε) (hεone : ε ≤ (1 : Rat)) :
    CoinProblemInstance :=
  halfVsFairCoinInstance sampleBits ε hεpos hεone

def check_truth_table_coin_instance
    (n : Nat) (low high : Rat)
    (hlow : 0 ≤ low) (hhigh : high ≤ 1) (hgap : low < high) :
    CoinProblemInstance :=
  truthTableCoinInstance n low high hlow hhigh hgap

def check_truth_table_local_prg_image_bound
    {n : Nat}
    (prg : TruthTableLocalPRG n) :
    Nat :=
  prg.imageSizeBound

def check_one_sided_fools_of_fools
    {n : Nat}
    {prg : TruthTableLocalPRG n}
    {C : CircuitFamilyClass}
    {maxSize : Nat}
    {epsilon : Rat} :
    FoolsBoundedTruthTableClass prg C maxSize epsilon →
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon :=
  oneSidedFoolsBoundedTruthTableClass_of_foolsBounded

def check_class_solves_coin_problem_of_implemented_threshold_oracle
    {C : CircuitFamilyClass} {n : Nat}
    {low high : Rat}
    {hlow : 0 ≤ low}
    {hhigh : high ≤ 1}
    {hgap : low < high}
    {adv : Rat}
    (impl : ImplementedThresholdOracle C n) :
    SolvesCoinProblem
        (truthTableCoinInstance n low high hlow hhigh hgap)
        impl.decide
        adv →
      ClassSolvesCoinProblem
        C
        (truthTableCoinInstance n low high hlow hhigh hgap)
        adv :=
  impl.classSolvesCoinProblem_of_advantage

def check_class_solves_coin_problem_of_bounded
    {C : CircuitFamilyClass}
    {inst : CoinProblemInstance}
    {adv : Rat}
    {maxSize : Nat} :
    BoundedClassSolvesCoinProblem C inst adv maxSize →
      ClassSolvesCoinProblem C inst adv :=
  classSolvesCoinProblem_of_bounded

def check_solvesCoinProblem_of_acceptanceProbability_bounds
    {inst : CoinProblemInstance}
    {A : AlgorithmsToLowerBounds.BitVec inst.sampleBits → Bool}
    {adv lowAcceptanceUpper highAcceptanceLower : Rat}
    (hLow :
      acceptanceProbability inst.lowBias A ≤ lowAcceptanceUpper)
    (hHigh :
      highAcceptanceLower ≤ acceptanceProbability inst.highBias A)
    (hGap :
      adv + lowAcceptanceUpper ≤ highAcceptanceLower) :
    SolvesCoinProblem inst A adv :=
  solvesCoinProblem_of_acceptanceProbability_bounds hLow hHigh hGap

def check_acceptanceProbability_mono
    {n : Nat}
    {bias : Rat}
    {A B : AlgorithmsToLowerBounds.BitVec n → Bool}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (hAB :
      ∀ x : AlgorithmsToLowerBounds.BitVec n, A x = true → B x = true) :
    acceptanceProbability bias A ≤ acceptanceProbability bias B :=
  acceptanceProbability_mono hBias_nonneg hBias_le_one hAB

def check_productBiasWeight_total
    (bias : Rat)
    (n : Nat) :
    (∑ x : AlgorithmsToLowerBounds.BitVec n, productBiasWeight bias x) = 1 :=
  productBiasWeight_total bias n

def check_acceptanceProbability_true
    {n : Nat}
    (bias : Rat) :
    acceptanceProbability bias (fun _ : AlgorithmsToLowerBounds.BitVec n => true) = 1 :=
  acceptanceProbability_true bias

def check_acceptanceProbability_not
    {n : Nat}
    (bias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) :
    acceptanceProbability bias (fun x => ! A x) =
      1 - acceptanceProbability bias A :=
  acceptanceProbability_not bias A

def check_acceptanceProbability_not_le_of_one_sub_le
    {n : Nat}
    {bias : Rat}
    {A : AlgorithmsToLowerBounds.BitVec n → Bool}
    {q : Rat}
    (hMass : 1 - q ≤ acceptanceProbability bias A) :
    acceptanceProbability bias (fun x => ! A x) ≤ q :=
  acceptanceProbability_not_le_of_one_sub_le hMass

def check_acceptanceProbability_fair_eq_bitVecAcceptanceProbability
    {m : Nat}
    (A : AlgorithmsToLowerBounds.BitVec m → Bool) :
    acceptanceProbability ((1 : Rat) / 2) A =
      bitVecAcceptanceProbability A :=
  acceptanceProbability_fair_eq_bitVecAcceptanceProbability A

def check_bitVecAcceptanceProbability_not
    {m : Nat}
    (A : AlgorithmsToLowerBounds.BitVec m → Bool) :
    bitVecAcceptanceProbability (fun x => ! A x) =
      1 - bitVecAcceptanceProbability A :=
  bitVecAcceptanceProbability_not A

def check_one_sub_upper_le_acceptanceProbability_fair_not
    {m : Nat}
    {A : AlgorithmsToLowerBounds.BitVec m → Bool}
    {q : Rat}
    (hA : acceptanceProbability ((1 : Rat) / 2) A ≤ q) :
    1 - q ≤ acceptanceProbability ((1 : Rat) / 2) (fun x => ! A x) :=
  one_sub_upper_le_acceptanceProbability_fair_not hA

def check_mcspThresholdOracle_accepts_of_treeMCSPPredicate
    {n : Nat}
    (oracle : MCSPThresholdOracle n)
    {tt : TruthTable n}
    (hEasy : treeMCSPPredicate n oracle.threshold tt) :
    oracle.decide tt = true :=
  MCSPThresholdOracle.accepts_of_treeMCSPPredicate oracle hEasy

def check_mcspThresholdOracle_rejects_of_not_treeMCSPPredicate
    {n : Nat}
    (oracle : MCSPThresholdOracle n)
    {tt : TruthTable n}
    (hHard : ¬ treeMCSPPredicate n oracle.threshold tt) :
    oracle.decide tt = false :=
  MCSPThresholdOracle.rejects_of_not_treeMCSPPredicate oracle hHard

def check_ac0p_coin_contract_excludes_small_solver
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    :
    ¬ BoundedClassSolvesCoinProblem
        (model.classOf p depth)
        (hardness.instance n)
        (hardness.advantage n)
        (contract.sizeBound depth n) :=
  contract.excludes_small_solver hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_lower_bound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :=
  noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound
    contract hp w

def check_size_lower_bound_exact_tree_mcsp_threshold_language_of_ac0p_coin_lower_bound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (exactTreeMCSPThresholdLanguage n w.oracle.threshold)
      (exactTreeMCSPThresholdLowerBound n (contract.sizeBound depth n)) :=
  sizeLowerBound_exactTreeMCSPThresholdLanguage_of_AC0pCoinLowerBound
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_lower_bound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (exactTreeMCSPThresholdLanguage n w.oracle.threshold)
      (exactTreeMCSPThresholdLowerBound n (contract.sizeBound depth n)) :=
  MCSP_lower_bound_from_AC0pCoinLowerBound
    contract hp w

def check_half_vs_fair_mcsp_coin_reduction_contract
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness) :
    Nat → Nat :=
  contract.threshold

def check_half_vs_fair_mcsp_coin_acceptance_profile
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinAcceptanceProfile hardness) :
    (Nat → Nat) × (Nat → Rat) × (Nat → Rat) :=
  (profile.threshold, profile.lowAcceptanceUpper, profile.fairAcceptanceLower)

def check_half_vs_fair_mcsp_coin_acceptance_profile_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinAcceptanceProfile hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (profile.threshold n))
      (hardness.advantage n) :=
  profile.exact_solvesCoin n

def check_half_vs_fair_mcsp_coin_rejection_profile_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinRejectionProfile hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdHardDecision n (profile.threshold n))
      (hardness.advantage n) :=
  profile.hard_solvesCoin n

def check_half_vs_fair_mcsp_coin_reduction_contract_of_distributionFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_acceptance_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (exactTreeMCSPThresholdDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_acceptance_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (exactTreeMCSPThresholdDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinReductionContract hardness :=
  HalfVsFairMCSPCoinReductionContract.of_distributionFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_acceptance_le
    fair_acceptance_ge
    advantage_gap

def check_half_vs_fair_mcsp_coin_rejection_contract_of_distributionFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_rejection_acceptance_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (exactTreeMCSPThresholdHardDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_rejection_acceptance_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (exactTreeMCSPThresholdHardDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_distributionFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_rejection_acceptance_le
    fair_rejection_acceptance_ge
    advantage_gap

def check_half_vs_fair_mcsp_coin_reduction_contract_of_treeMCSPPredicateMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_mass_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_mass_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (treeMCSPPredicateDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinReductionContract hardness :=
  HalfVsFairMCSPCoinReductionContract.of_treeMCSPPredicateMassFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_mass_le
    fair_mass_ge
    advantage_gap

def check_half_vs_fair_mcsp_coin_rejection_contract_of_notTreeMCSPPredicateMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_not_mass_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (notTreeMCSPPredicateDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_not_mass_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (notTreeMCSPPredicateDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_notTreeMCSPPredicateMassFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_not_mass_le
    fair_not_mass_ge
    advantage_gap

def check_half_vs_fair_mcsp_coin_rejection_contract_of_treeMCSPPredicateBiasedLower_and_fairCounting
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_lowComplexity_mass_ge :
      ∀ n : Nat,
        1 - lowAcceptanceUpper n ≤
          acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n)))
    (fair_count_ratio_le :
      ∀ n : Nat,
        treeMCSPCountRatio n (threshold n) ≤
          1 - fairAcceptanceLower n)
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_treeMCSPPredicateBiasedLower_and_fairCounting
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_lowComplexity_mass_ge
    fair_count_ratio_le
    advantage_gap

def check_half_vs_fair_biased_low_complexity_mass_facts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper : Nat → Rat)
    (low_lowComplexity_mass_ge :
      ∀ n : Nat,
        1 - lowAcceptanceUpper n ≤
          acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n))) :
    HalfVsFairBiasedLowComplexityMassFacts hardness where
  threshold := threshold
  lowAcceptanceUpper := lowAcceptanceUpper
  low_lowComplexity_mass_ge := low_lowComplexity_mass_ge

def check_adjacent_bias_mcsp_threshold_separation_instance
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (n : Nat) :
    CoinProblemInstance :=
  facts.instance n

def check_adjacent_bias_mcsp_threshold_separation_solves_coin
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (n : Nat) :
    SolvesCoinProblem
      (facts.instance n)
      (exactTreeMCSPThresholdHardDecision n (facts.threshold n))
      (facts.advantage n) :=
  facts.toSolvesCoin n

def check_coin_distinguisher_family_instance
    (family : CoinDistinguisherFamily)
    (n : Nat) :
    CoinProblemInstance :=
  family.instance n

def check_coin_distinguisher_family_solves_instance
    (family : CoinDistinguisherFamily)
    (n : Nat) :
    SolvesCoinProblem
      (family.instance n)
      (family.algorithm n)
      (family.advantage n) :=
  family.solves_instance n

def check_circuit_coin_distinguisher_family_solves
    {C : CircuitFamilyClass}
    {family : CoinDistinguisherFamily}
    (realized : CircuitCoinDistinguisherFamily C family)
    (n : Nat) :
    SolvesCoinProblem
      (family.instance n)
      (fun x => C.eval (realized.circuit n) x)
      (family.advantage n) :=
  realized.solves n

def check_circuit_coin_distinguisher_family_bounded_solves
    {C : CircuitFamilyClass}
    {family : CoinDistinguisherFamily}
    (realized : CircuitCoinDistinguisherFamily C family)
    (n : Nat) :
    BoundedClassSolvesCoinProblem
      C
      (family.instance n)
      (family.advantage n)
      (realized.sizeBound n) :=
  realized.boundedSolves n

def check_boundedClassSolvesCoinProblem_mono_size
    {C : CircuitFamilyClass}
    {inst : CoinProblemInstance}
    {adv : Rat}
    {smallBound largeBound : Nat}
    (hSolve : BoundedClassSolvesCoinProblem C inst adv smallBound)
    (hLe : smallBound ≤ largeBound) :
    BoundedClassSolvesCoinProblem C inst adv largeBound :=
  BoundedClassSolvesCoinProblem.mono_size hSolve hLe

noncomputable def check_coin_distinguisher_family_of_adjacentBiasMCSP
    (facts : AdjacentBiasMCSPThresholdSeparationFacts) :
    CoinDistinguisherFamily :=
  CoinDistinguisherFamily.of_adjacentBiasMCSP facts

noncomputable def check_circuit_coin_distinguisher_family_of_adjacentBiasMCSP_circuit
    (C : CircuitFamilyClass)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (circuit :
      ∀ n : Nat, C.Family (Pnp3.Models.Partial.tableLen n))
    (computes :
      ∀ n : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen n),
        C.eval (circuit n) x =
          exactTreeMCSPThresholdHardDecision n (facts.threshold n) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ n : Nat,
        C.size (circuit n) ≤ sizeBound n) :
    CircuitCoinDistinguisherFamily
      C
      (CoinDistinguisherFamily.of_adjacentBiasMCSP facts) :=
  CircuitCoinDistinguisherFamily.of_adjacentBiasMCSP_circuit
    C
    facts
    circuit
    computes
    sizeBound
    size_le

noncomputable def check_coin_distinguisher_family_of_adjacentBiasMCSP_solves
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (n : Nat) :
    SolvesCoinProblem
      ((CoinDistinguisherFamily.of_adjacentBiasMCSP facts).instance n)
      ((CoinDistinguisherFamily.of_adjacentBiasMCSP facts).algorithm n)
      ((CoinDistinguisherFamily.of_adjacentBiasMCSP facts).advantage n) :=
  (CoinDistinguisherFamily.of_adjacentBiasMCSP facts).solves_instance n

def check_coin_distinguisher_to_half_vs_fair_translation_contract
    (source : CoinDistinguisherFamily)
    (hardness : HalfVsFairTruthTableCoinHardness) :
    Type :=
  CoinDistinguisherToHalfVsFairTranslationContract source hardness

def check_coin_translation_preserves_class
    (C : CircuitFamilyClass)
    (source : CoinDistinguisherFamily)
    (hardness : HalfVsFairTruthTableCoinHardness) :
    Type :=
  CoinTranslationPreservesClass C source hardness

def check_coin_distinguisher_to_half_vs_fair_translation_solves
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (translation :
      CoinDistinguisherToHalfVsFairTranslationContract source hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (translation.translatedAlgorithm n)
      (hardness.advantage n) :=
  translation.solvesCoin n

noncomputable def check_half_vs_fair_coin_distinguisher_family
    (hardness : HalfVsFairTruthTableCoinHardness)
    (A : ∀ n : Nat, AlgorithmsToLowerBounds.BitVec (hardness.instance n).sampleBits → Bool)
    (hSolves :
      ∀ n : Nat,
        SolvesCoinProblem
          (hardness.instance n)
          (A n)
          (hardness.advantage n)) :
    CoinDistinguisherFamily :=
  halfVsFairCoinDistinguisherFamily hardness A hSolves

noncomputable def check_circuit_coin_distinguisher_family_translate_to_halfVsFair
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (realized : CircuitCoinDistinguisherFamily C source)
    (translation : CoinTranslationPreservesClass C source hardness) :
    CircuitCoinDistinguisherFamily
      C
      (halfVsFairCoinDistinguisherFamily
        hardness
        (fun n x =>
          C.eval (translation.translateCircuit n (realized.circuit n)) x)
        (fun n =>
          translation.solvesTarget_of_solvesSource
            n
            (realized.circuit n)
            (realized.solves n))) :=
  realized.translate_to_halfVsFair translation

def check_boundedClassSolvesCoinProblem_of_translated_realization
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (realized : CircuitCoinDistinguisherFamily C source)
    (translation : CoinTranslationPreservesClass C source hardness)
    (n : Nat) :
    BoundedClassSolvesCoinProblem
      C
      (hardness.instance n)
      (hardness.advantage n)
      (realized.sizeBound n) :=
  BoundedClassSolvesCoinProblem_of_translated_realization
    realized
    translation
    n

def check_false_of_translated_realization_and_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    {source : CoinDistinguisherFamily}
    {p depth n : Nat}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (hp : Nat.Prime p)
    (realized :
      CircuitCoinDistinguisherFamily
        (model.classOf p depth)
        source)
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        source
        hardness)
    (hSize :
      realized.sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_translated_realization_and_AC0pCoinLowerBound
    contract
    hp
    realized
    translation
    hSize

def check_false_of_adjacentBias_realization_translation_and_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    {facts : AdjacentBiasMCSPThresholdSeparationFacts}
    {p depth n : Nat}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (hp : Nat.Prime p)
    (realized :
      CircuitCoinDistinguisherFamily
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts))
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
        hardness)
    (hSize :
      realized.sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_adjacentBias_realization_translation_and_AC0pCoinLowerBound
    contract
    hp
    realized
    translation
    hSize

def check_false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
        hardness)
    (circuit :
      ∀ m : Nat,
        (model.classOf p depth).Family (Pnp3.Models.Partial.tableLen m))
    (computes :
      ∀ m : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen m),
        (model.classOf p depth).eval (circuit m) x =
          exactTreeMCSPThresholdHardDecision m (facts.threshold m) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ m : Nat,
        (model.classOf p depth).size (circuit m) ≤ sizeBound m)
    (hSize :
      sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision
    contract
    facts
    hp
    translation
    circuit
    computes
    sizeBound
    size_le
    hSize

noncomputable def check_adjacent_bias_to_half_vs_fair_coin_solver_translation_contract
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (hardness : HalfVsFairTruthTableCoinHardness) :
    Type :=
  AdjacentBiasToHalfVsFairCoinSolverTranslationContract facts hardness

def check_adjacent_bias_to_half_vs_fair_rejection_translation_contract
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (hardness : HalfVsFairTruthTableCoinHardness) :
    Type :=
  AdjacentBiasToHalfVsFairRejectionTranslationContract facts hardness

def check_half_vs_fair_mcsp_coin_rejection_contract_of_adjacentBiasSeparation_and_translation
    {hardness : HalfVsFairTruthTableCoinHardness}
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (translation :
      AdjacentBiasToHalfVsFairRejectionTranslationContract facts hardness) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_adjacentBiasSeparation_and_translation
    facts
    translation

def check_treeMCSPCountRatio_le_one_sub_self_fairLower
    (n threshold : Nat) :
    treeMCSPCountRatio n threshold ≤
      1 - (1 - treeMCSPCountRatio n threshold) :=
  treeMCSPCountRatio_le_one_sub_self_fairLower n threshold

noncomputable def check_half_vs_fair_mcsp_coin_rejection_contract_of_biasedLowComplexityMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (facts : HalfVsFairBiasedLowComplexityMassFacts hardness)
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + facts.lowAcceptanceUpper n ≤
          1 - treeMCSPCountRatio n (facts.threshold n)) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_biasedLowComplexityMassFacts
    facts
    advantage_gap

def check_halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    acceptanceProbability (hardness.instance n).highBias
        (treeMCSPPredicateDecision n threshold) ≤
      treeMCSPCountRatio n threshold :=
  halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio n threshold

def check_one_sub_countRatio_le_halfVsFair_highBias_notTreeMCSPPredicateDecision
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    1 - treeMCSPCountRatio n threshold ≤
      acceptanceProbability (hardness.instance n).highBias
        (notTreeMCSPPredicateDecision n threshold) :=
  one_sub_countRatio_le_halfVsFair_highBias_notTreeMCSPPredicateDecision
    n threshold

def check_one_sub_countRatio_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    1 - treeMCSPCountRatio n threshold ≤
      acceptanceProbability (hardness.instance n).highBias
        (exactTreeMCSPThresholdHardDecision n threshold) :=
    one_sub_countRatio_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
    n threshold

def check_halfVsFair_lowBias_notTreeMCSPPredicateDecision_le_of_treeMCSPPredicate_mass_lower
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hMass :
      1 - q ≤
        acceptanceProbability (hardness.instance n).lowBias
          (treeMCSPPredicateDecision n threshold)) :
    acceptanceProbability (hardness.instance n).lowBias
        (notTreeMCSPPredicateDecision n threshold) ≤ q :=
  halfVsFair_lowBias_notTreeMCSPPredicateDecision_le_of_treeMCSPPredicate_mass_lower
    hMass

def check_halfVsFair_lowBias_exactTreeMCSPThresholdHardDecision_le_of_treeMCSPPredicate_mass_lower
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hMass :
      1 - q ≤
        acceptanceProbability (hardness.instance n).lowBias
          (treeMCSPPredicateDecision n threshold)) :
    acceptanceProbability (hardness.instance n).lowBias
        (exactTreeMCSPThresholdHardDecision n threshold) ≤ q :=
  halfVsFair_lowBias_exactTreeMCSPThresholdHardDecision_le_of_treeMCSPPredicate_mass_lower
    hMass

def check_half_vs_fair_mcsp_coin_reduction_contract_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (contract.threshold n))
      (hardness.advantage n) :=
  contract.exact_solvesCoin n

def check_half_vs_fair_mcsp_coin_rejection_contract_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinRejectionContract hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdHardDecision n (contract.threshold n))
      (hardness.advantage n) :=
  contract.hard_solvesCoin n

noncomputable def check_half_vs_fair_mcsp_coin_language
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) : BitVecLanguage :=
  halfVsFairMCSPCoinLanguage contract n

noncomputable def check_half_vs_fair_mcsp_coin_asymptotic_language
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness) :
    BitVecLanguage :=
  halfVsFairMCSPCoinAsymptoticLanguage contract

def check_half_vs_fair_mcsp_coin_lower_bound
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n maxSize : Nat) : Nat → Nat :=
  halfVsFairMCSPCoinLowerBound contract n maxSize

def check_mcsp_lower_bound_from_ac0p_coin_lower_bound_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (lowerBound : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (halfVsFairMCSPCoinLowerBound reduction n (lowerBound.sizeBound depth n)) :=
  MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction
    lowerBound reduction hp

def check_not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract_and_growth
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    (hGrowth :
      ∀ depth : Nat,
        BeatsEveryPolynomialSizeBoundAtSomeTableLength
          (fun n => ac0pCoinLowerEnvelope contract.envelopeConst depth n))
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p (halfVsFairMCSPCoinAsymptoticLanguage reduction) :=
  not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract_and_growth
    contract reduction hGrowth p hp

def check_ac0pCoinLowerEnvelope_beatsEveryPolynomial
    (envelopeConst depth : Nat) :
    BeatsEveryPolynomialSizeBoundAtArbitrarilyLargeTableLengths
      (fun n => ac0pCoinLowerEnvelope envelopeConst depth n) :=
  ac0pCoinLowerEnvelope_beatsEveryPolynomial_at_arbitrarilyLarge_tableLengths
    envelopeConst depth

def check_not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p (halfVsFairMCSPCoinAsymptoticLanguage reduction) :=
  not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract
    contract reduction p hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_lower_bound_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (lowerBound : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ lowerBound.sizeBound depth n ∧
        impl.threshold = reduction.threshold n :=
  noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound_and_reduction
    lowerBound reduction hp

def check_ac0p_coin_lower_envelope
    (c depth n : Nat) : Nat :=
  ac0pCoinLowerEnvelope c depth n

def check_eventually_at_least_ac0p_coin_lower_envelope
    (sizeBound : Nat → Nat → Nat) : Prop :=
  EventuallyAtLeastAC0pCoinLowerEnvelope sizeBound

def check_eventually_at_least_ac0p_coin_lower_envelope_self
    (c : Nat) : Prop :=
  EventuallyAtLeastAC0pCoinLowerEnvelope (ac0pCoinLowerEnvelope c)

def check_ac0p_coin_bias_gap_envelope
    (c n : Nat) : Rat :=
  ac0pCoinBiasGapEnvelope c n

def check_eventually_at_most_ac0p_coin_bias_gap_envelope
    (biasGap : Nat → Rat) : Prop :=
  EventuallyAtMostAC0pCoinBiasGapEnvelope biasGap

def check_eventually_at_least_positive_coin_advantage
    (advantage : Nat → Rat) : Prop :=
  EventuallyAtLeastPositiveCoinAdvantage advantage

def check_ac0p_coin_published_half_vs_fair_regime
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : AC0pCoinPublishedHalfVsFairRegime hardness) :
    EventuallyAtMostAC0pCoinBiasGapEnvelope hardness.biasGap ∧
      EventuallyAtLeastPositiveCoinAdvantage hardness.advantage :=
  ⟨profile.biasGap_profile, profile.advantage_profile⟩

def check_ac0p_coin_quantitative_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness) :
    Prop :=
  EventuallyAtLeastAC0pCoinLowerEnvelope contract.sizeBound

def check_ac0p_coin_published_exp_lower_bound_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness) :
    contract.base.sizeBound = ac0pCoinLowerEnvelope contract.envelopeConst ∧
      EventuallyAtMostAC0pCoinBiasGapEnvelope hardness.biasGap ∧
      EventuallyAtLeastPositiveCoinAdvantage hardness.advantage :=
  ⟨contract.sizeBound_eq,
    contract.hardness_profile.biasGap_profile,
    contract.hardness_profile.advantage_profile⟩

noncomputable def check_ac0p_coin_quantitative_language
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n : Nat}
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    BitVecLanguage :=
  AC0pCoinQuantitativeLanguage w

def check_ac0p_coin_quantitative_lower_bound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (depth n : Nat) : Nat → Nat :=
  AC0pCoinQuantitativeLowerBound contract depth n

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_quantitative_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :=
  noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_quantitative_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (AC0pCoinQuantitativeLanguage w)
      (AC0pCoinQuantitativeLowerBound contract depth n) :=
  MCSP_lower_bound_from_AC0pCoinQuantitativeContract
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_quantitative_contract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (halfVsFairMCSPCoinLowerBound reduction n (contract.sizeBound depth n)) :=
  MCSP_lower_bound_from_AC0pCoinQuantitativeContract_and_reduction
    contract reduction hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_quantitative_contract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
        impl.threshold = reduction.threshold n :=
  noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract_and_reduction
    contract reduction hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_published_exp_lower_bound_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤
          ac0pCoinLowerEnvelope contract.envelopeConst depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :=
  noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_published_exp_lower_bound_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (AC0pCoinQuantitativeLanguage w)
      (exactTreeMCSPThresholdLowerBound
        n
        (ac0pCoinLowerEnvelope contract.envelopeConst depth n)) :=
  MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_published_exp_lower_bound_contract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (exactTreeMCSPThresholdLowerBound
        n
        (ac0pCoinLowerEnvelope contract.envelopeConst depth n)) :=
  MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract_and_reduction
    contract reduction hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_published_exp_lower_bound_contract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤
          ac0pCoinLowerEnvelope contract.envelopeConst depth n ∧
        impl.threshold = reduction.threshold n :=
  noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract_and_reduction
    contract reduction hp

def check_exact_tree_mcsp_threshold_decision_accepts
    {n threshold : Nat}
    {tt : TruthTable n}
    (hEasy : treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdDecision n threshold tt = true :=
  exactTreeMCSPThresholdDecision_accepts_of_treeMCSPPredicate hEasy

noncomputable def check_treeMCSPPredicateDecision
    (n threshold : Nat) :
    TruthTable n → Bool :=
  treeMCSPPredicateDecision n threshold

def check_treeMCSPPredicateDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    treeMCSPPredicateDecision n threshold tt = true ↔
      treeMCSPPredicate n threshold tt :=
  treeMCSPPredicateDecision_spec tt

def check_notTreeMCSPPredicateDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    notTreeMCSPPredicateDecision n threshold tt = true ↔
      ¬ treeMCSPPredicate n threshold tt :=
  notTreeMCSPPredicateDecision_spec tt

def check_exactTreeMCSPThresholdHardDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    exactTreeMCSPThresholdHardDecision n threshold tt = true ↔
      ¬ treeMCSPPredicate n threshold tt :=
  exactTreeMCSPThresholdHardDecision_spec tt

def check_exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision
    (n threshold : Nat) :
    exactTreeMCSPThresholdHardDecision n threshold =
      notTreeMCSPPredicateDecision n threshold :=
  exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision n threshold

noncomputable def check_treeMCSPPredicateOracle
    (n threshold : Nat) :
    MCSPThresholdOracle n :=
  treeMCSPPredicateOracle n threshold

def check_uniformTruthTableAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
    (n threshold : Nat) :
    uniformTruthTableAcceptanceProbability (treeMCSPPredicateDecision n threshold) ≤
      (Pnp3.Models.circuitCountBound n threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) :=
  uniformTruthTableAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
    n threshold

def check_fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
    (n threshold : Nat) :
    acceptanceProbability ((1 : Rat) / 2) (treeMCSPPredicateDecision n threshold) ≤
      (Pnp3.Models.circuitCountBound n threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) :=
  fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio n threshold

def check_one_sub_countRatio_le_fairAcceptanceProbability_notTreeMCSPPredicateDecision
    (n threshold : Nat) :
    1 -
        (Pnp3.Models.circuitCountBound n threshold : Rat) /
          (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) ≤
      acceptanceProbability ((1 : Rat) / 2)
        (notTreeMCSPPredicateDecision n threshold) :=
  one_sub_countRatio_le_fairAcceptanceProbability_notTreeMCSPPredicateDecision
    n threshold

def check_exact_tree_mcsp_threshold_decision_rejects
    {n threshold : Nat}
    {tt : TruthTable n}
    (hHard : ¬ treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdDecision n threshold tt = false :=
  exactTreeMCSPThresholdDecision_rejects_of_not_treeMCSPPredicate hHard

def check_exact_tree_mcsp_threshold_hard_decision_accepts
    {n threshold : Nat}
    {tt : TruthTable n}
    (hHard : ¬ treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdHardDecision n threshold tt = true :=
  exactTreeMCSPThresholdHardDecision_accepts_of_not_treeMCSPPredicate hHard

def check_exact_tree_mcsp_threshold_hard_decision_rejects
    {n threshold : Nat}
    {tt : TruthTable n}
    (hEasy : treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdHardDecision n threshold tt = false :=
  exactTreeMCSPThresholdHardDecision_rejects_of_treeMCSPPredicate hEasy

def check_acceptanceProbability_exactTreeMCSPThresholdDecision_le_treeMCSPPredicateDecision
    {n threshold : Nat}
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1) :
    acceptanceProbability bias (exactTreeMCSPThresholdDecision n threshold) ≤
      acceptanceProbability bias (treeMCSPPredicateDecision n threshold) :=
  acceptanceProbability_exactTreeMCSPThresholdDecision_le_treeMCSPPredicateDecision
    hBias_nonneg hBias_le_one

def check_treeMCSPPredicateDecision_le_acceptanceProbability_exactTreeMCSPThresholdDecision
    {n threshold : Nat}
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1) :
    acceptanceProbability bias (treeMCSPPredicateDecision n threshold) ≤
      acceptanceProbability bias (exactTreeMCSPThresholdDecision n threshold) :=
  treeMCSPPredicateDecision_le_acceptanceProbability_exactTreeMCSPThresholdDecision
    hBias_nonneg hBias_le_one

def check_uniform_truth_table_acceptance_probability_le_count_ratio_of_tree_mcsp_oracle
    {n : Nat}
    (oracle : MCSPThresholdOracle n) :
    uniformTruthTableAcceptanceProbability oracle.decide ≤
      (Pnp3.Models.circuitCountBound n oracle.threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) :=
  uniformTruthTableAcceptanceProbability_le_countRatio_of_treeMCSPOracle oracle

def check_no_small_implemented_threshold_oracle_of_local_prg_transfer
    {C : CircuitFamilyClass}
    {n maxSize : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (hFool :
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon) :
    ¬ ∃ impl : ImplementedThresholdOracle C n,
        C.size impl.circuit ≤ maxSize ∧
        prg.imageSizeBound ≤ impl.threshold ∧
        epsilon <
          1 - ((Pnp3.Models.circuitCountBound n impl.threshold : Rat) /
                (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) :=
  noSmallImplementedThresholdOracle_of_localPRGTransfer prg hFool

def check_no_small_implemented_threshold_oracle_of_fools_local_prg_transfer
    {C : CircuitFamilyClass}
    {n maxSize : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (hFool :
      FoolsBoundedTruthTableClass prg C maxSize epsilon) :
    ¬ ∃ impl : ImplementedThresholdOracle C n,
        C.size impl.circuit ≤ maxSize ∧
        prg.imageSizeBound ≤ impl.threshold ∧
        epsilon <
          1 - ((Pnp3.Models.circuitCountBound n impl.threshold : Rat) /
                (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) :=
  noSmallImplementedThresholdOracle_of_foolsLocalPRGTransfer prg hFool

noncomputable def check_tree_mcsp_count_ratio
    (n threshold : Nat) : Rat :=
  treeMCSPCountRatio n threshold

noncomputable def check_exact_tree_mcsp_threshold_language
    (n threshold : Nat) : BitVecLanguage :=
  exactTreeMCSPThresholdLanguage n threshold

def check_exact_tree_mcsp_threshold_lower_bound
    (n maxSize : Nat) : Nat → Nat :=
  exactTreeMCSPThresholdLowerBound n maxSize

def check_size_lower_bound_exact_tree_mcsp_threshold_language_of_local_prg_transfer
    {C : CircuitFamilyClass}
    {n maxSize threshold : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (hThreshold : prg.imageSizeBound ≤ threshold)
    (hFool :
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon)
    (hEpsSmall :
      epsilon <
        1 - ((Pnp3.Models.circuitCountBound n threshold : Rat) /
              (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat))) :
    SizeLowerBound
      C
      (exactTreeMCSPThresholdLanguage n threshold)
      (exactTreeMCSPThresholdLowerBound n maxSize) :=
  sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer
    prg hThreshold hFool hEpsSmall

def check_published_local_prg_route_to_one_sided
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec} :
    PublishedLocalPRGRouteContract model spec →
      PublishedOneSidedLocalPRGRouteContract model spec :=
  PublishedLocalPRGRouteContract.toOneSided

def check_formulaCircuit_target_family_model :
    LocalPRGTargetFamilyModel :=
  formulaCircuitTargetFamilyModel

def check_formulaCircuit_published_local_prg_route_contract
    (spec : LocalPRGHardnessSpec) :
    Type :=
  FormulaCircuitPublishedLocalPRGRouteContract spec

def check_formulaCircuit_slice_spec
    (threshold sizeBound : Nat → Nat) :
    FormulaCircuitSliceSpec :=
  ⟨threshold, sizeBound⟩

def check_formulaCircuit_published_lower_bound_contract
    (spec : FormulaCircuitSliceSpec) :
    Prop :=
  FormulaCircuitPublishedLowerBoundContract spec

def check_CKLM_formulaCircuit_published_route_contract
    (spec : CKLMFormulaCircuitHardnessSpec) :
    Type :=
  CKLMFormulaCircuitPublishedRouteContract spec

def check_CKLM_formulaCircuit_theorem2_contract
    (spec : CKLMFormulaCircuitHardnessSpec) :
    Prop :=
  CKLMFormulaCircuitPublishedTheorem2Contract spec

def check_cklm_formula_theorem2_lower_envelope
    (c n : Nat) : Nat :=
  cklmFormulaTheorem2LowerEnvelope c n

def check_eventually_at_least_cklm_formula_theorem2_lower_envelope
    (sizeBound : Nat → Nat) : Prop :=
  EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope sizeBound

def check_CKLM_formulaCircuit_theorem2_hardness
    (threshold sizeBound : Nat → Nat)
    (hProfile : EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope sizeBound) :
    CKLMFormulaCircuitTheorem2Hardness :=
  ⟨threshold, sizeBound, hProfile⟩

def check_CKLM_formulaCircuit_localPRG_source_spec
    (threshold sizeBound : Nat → Nat)
    (epsilon : Nat → Rat)
    (hEpsSmall :
      ∀ n : Nat, epsilon n < 1 - treeMCSPCountRatio n (threshold n))
    (hProfile : EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope sizeBound) :
    CKLMFormulaCircuitLocalPRGSourceSpec where
  threshold := threshold
  sizeBound := sizeBound
  epsilon := epsilon
  epsilon_small := hEpsSmall
  theorem2_profile := hProfile

def check_CKLM_formulaCircuit_localPRG_source_contract
    (source : CKLMFormulaCircuitLocalPRGSourceSpec) :
    Type :=
  CKLMFormulaCircuitLocalPRGSourceContract source

def check_CKLM_formulaCircuit_localPRG_source_to_route
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    FormulaCircuitPublishedLocalPRGRouteContract
      source.toLocalPRGHardnessSpec :=
  contract.toPublishedRoute

def check_CKLM_formulaCircuit_theorem2_contract_of_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    CKLMFormulaCircuitPublishedTheorem2Contract
      source.toCKLMFormulaCircuitHardnessSpec :=
  CKLMFormulaCircuitPublishedTheorem2Contract.ofLocalPRGSource contract

def check_CKLM_formulaCircuit_theorem2_quantitative_contract_of_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    CKLMFormulaCircuitPublishedTheorem2QuantitativeContract
      source.toTheorem2Hardness :=
  CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofLocalPRGSource
    contract

def check_CKLM_formulaCircuit_theorem2_quantitative_contract
    (hardness : CKLMFormulaCircuitTheorem2Hardness) :
    Prop :=
  CKLMFormulaCircuitPublishedTheorem2QuantitativeContract hardness

noncomputable def check_CKLM_formulaCircuit_language
    (spec : CKLMFormulaCircuitHardnessSpec)
    (n : Nat) : BitVecLanguage :=
  CKLMFormulaCircuitLanguage spec n

def check_CKLM_formulaCircuit_lower_bound
    (spec : CKLMFormulaCircuitHardnessSpec)
    (n : Nat) : Nat → Nat :=
  CKLMFormulaCircuitLowerBound spec n

noncomputable def check_CKLM_formulaCircuit_quantitative_language
    (hardness : CKLMFormulaCircuitTheorem2Hardness)
    (n : Nat) : BitVecLanguage :=
  CKLMFormulaCircuitQuantitativeLanguage hardness n

def check_CKLM_formulaCircuit_quantitative_lower_bound
    (hardness : CKLMFormulaCircuitTheorem2Hardness)
    (n : Nat) : Nat → Nat :=
  CKLMFormulaCircuitQuantitativeLowerBound hardness n

noncomputable def check_formulaCircuit_asymptotic_language
    (spec : LocalPRGHardnessSpec) :
    Pnp3.ComplexityInterfaces.Language :=
  formulaCircuitAsymptoticLanguage spec

def check_beats_every_ppoly_bound_at_some_table_length
    (sizeBound : Nat → Nat) :
    Prop :=
  BeatsEveryPpolyBoundAtSomeTableLength sizeBound

def check_mcsp_lower_bound_from_published_local_prg_route
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec}
    (contract : PublishedLocalPRGRouteContract model spec)
    (n : Nat) :
    SizeLowerBound
      (model.classOf n)
      (thresholdMCSPLanguage spec n)
      (thresholdMCSPLowerBound spec n) :=
  MCSP_lower_bound_from_publishedLocalPRGRoute contract n

def check_formulaCircuit_mcsp_lower_bound_from_published_local_prg_route
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (thresholdMCSPLanguage spec n)
      (thresholdMCSPLowerBound spec n) :=
  formulaCircuit_MCSP_lower_bound_from_publishedLocalPRGRoute contract n

def check_formulaCircuit_mcsp_lower_bound_from_published_lower_bound_contract
    {spec : FormulaCircuitSliceSpec}
    (contract : FormulaCircuitPublishedLowerBoundContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (formulaCircuitThresholdLanguage spec n)
      (formulaCircuitThresholdLowerBound spec n) :=
  formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract contract n

def check_formulaCircuit_mcsp_lower_bound_from_CKLM_formula_route
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedRouteContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitLanguage spec n)
      (CKLMFormulaCircuitLowerBound spec n) :=
  formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitRoute
    contract n

def check_formulaCircuit_mcsp_lower_bound_from_CKLM_formula_theorem2_contract
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedTheorem2Contract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitLanguage spec n)
      (CKLMFormulaCircuitLowerBound spec n) :=
  formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2Contract
    contract n

def check_formulaCircuit_mcsp_lower_bound_from_CKLM_formula_theorem2_quantitative_contract
    {hardness : CKLMFormulaCircuitTheorem2Hardness}
    (contract : CKLMFormulaCircuitPublishedTheorem2QuantitativeContract hardness)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitQuantitativeLanguage hardness n)
      (CKLMFormulaCircuitQuantitativeLowerBound hardness n) :=
  formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2QuantitativeContract
    contract n

def check_formulaCircuit_mcsp_lower_bound_from_CKLM_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitQuantitativeLanguage source.toTheorem2Hardness n)
      (CKLMFormulaCircuitQuantitativeLowerBound source.toTheorem2Hardness n) :=
  formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitLocalPRGSource
    contract n

def check_no_small_implemented_threshold_oracle_of_published_local_prg_route
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec}
    (contract : PublishedLocalPRGRouteContract model spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf n) n,
        (model.classOf n).size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_publishedLocalPRGRoute contract n

def check_no_small_implemented_threshold_oracle_of_formulaCircuit_published_local_prg_route
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_formulaCircuitPublishedLocalPRGRoute
    contract n

def check_no_small_implemented_threshold_oracle_of_published_formulaCircuit_lower_bound_contract
    {spec : FormulaCircuitSliceSpec}
    (contract : FormulaCircuitPublishedLowerBoundContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_publishedLowerBoundContract
    contract n

def check_no_small_implemented_threshold_oracle_of_CKLM_formula_route
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedRouteContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitRoute
    contract n

def check_no_small_implemented_threshold_oracle_of_CKLM_formula_theorem2_contract
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedTheorem2Contract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2Contract
    contract n

def check_no_small_implemented_threshold_oracle_of_CKLM_formula_theorem2_quantitative_contract
    {hardness : CKLMFormulaCircuitTheorem2Hardness}
    (contract : CKLMFormulaCircuitPublishedTheorem2QuantitativeContract hardness)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ hardness.sizeBound n ∧
        impl.threshold = hardness.threshold n :=
  noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2QuantitativeContract
    contract n

def check_no_small_implemented_threshold_oracle_of_CKLM_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ source.sizeBound n ∧
        impl.threshold = source.threshold n :=
  noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitLocalPRGSource
    contract n

def check_no_ppolyFormula_of_formulaCircuit_published_local_prg_route
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength spec.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage spec) :=
  no_PpolyFormula_of_formulaCircuitPublishedLocalPRGRoute_and_growth
    contract hGrowth

def check_no_ppolyFormula_of_cklm_formula_or_branching_program_route
    {spec : FormulaOrBranchingProgramLocalPRGHardnessSpec}
    (contract :
      FormulaCircuitPublishedLocalPRGRouteContract spec.toLocalPRGHardnessSpec)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength spec.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage spec.toLocalPRGHardnessSpec) :=
  no_PpolyFormula_of_CKLM_formulaOrBranchingProgramRoute_and_growth
    contract hGrowth

def check_no_ppolyFormula_of_CKLM_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength source.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage source.toLocalPRGHardnessSpec) :=
  no_PpolyFormula_of_CKLMFormulaCircuitLocalPRGSource_and_growth
    contract hGrowth

def check_not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope
    (c : Nat) :
    ¬ BeatsEveryPpolyBoundAtSomeTableLength (cklmFormulaTheorem2LowerEnvelope c) :=
  not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope c

def check_not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope
    (c : Nat) :
    ¬ BeatsEveryPpolyBoundFrequentlyAtSomeTableLength
        (cklmFormulaTheorem2LowerEnvelope c) :=
  not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope c

def check_no_uniform_cklmEnvelopeFrequentEscape :
    (∀ c : Nat,
      BeatsEveryPpolyBoundFrequentlyAtSomeTableLength
        (cklmFormulaTheorem2LowerEnvelope c)) → False :=
  no_uniform_cklmEnvelopeFrequentEscape

#print axioms AlgorithmsToLowerBounds.NP_not_subset_PpolyDAG_of_verified_source
#print axioms AlgorithmsToLowerBounds.P_ne_NP_of_verified_source
#print axioms AlgorithmsToLowerBounds.maskBit_true
#print axioms AlgorithmsToLowerBounds.maskBit_false
#print axioms AlgorithmsToLowerBounds.maskVec_apply
#print axioms AlgorithmsToLowerBounds.expectationProductBias_sub
#print axioms AlgorithmsToLowerBounds.expectationProductBias_le_of_pointwise_le
#print axioms AlgorithmsToLowerBounds.exists_max_bitVec_rat
#print axioms AlgorithmsToLowerBounds.maskedAcceptanceAverage_eq_acceptanceProbability_mul
#print axioms AlgorithmsToLowerBounds.MaskingBiasParams.keepBias_nonneg
#print axioms AlgorithmsToLowerBounds.MaskingBiasParams.keepBias_le_one
#print axioms AlgorithmsToLowerBounds.MaskingBiasParams.keepBias_mul_highTargetBias
#print axioms AlgorithmsToLowerBounds.MaskingBiasParams.keepBias_mul_lowTargetBias
#print axioms AlgorithmsToLowerBounds.maskedAcceptanceAdvantage_eq_expectation_fixed
#print axioms AlgorithmsToLowerBounds.MaskAveragingContract.of_valid_keepBias
#print axioms AlgorithmsToLowerBounds.MaskAveragingContract.of_maskingBiasParams
#print axioms AlgorithmsToLowerBounds.MaskingPushforwardFacts.of_maskingBiasParams
#print axioms AlgorithmsToLowerBounds.CoinMaskingTranslationFacts.of_maskingBiasParams
#print axioms AlgorithmsToLowerBounds.MaskingPushforwardFacts.masked_advantage_eq_source
#print axioms AlgorithmsToLowerBounds.CoinMaskingTranslationFacts.exists_mask_with_source_advantage
#print axioms AlgorithmsToLowerBounds.bestMaskForCircuit
#print axioms AlgorithmsToLowerBounds.bestMaskForCircuit_max
#print axioms AlgorithmsToLowerBounds.source_advantage_le_bestMask_fixed_advantage
#print axioms AlgorithmsToLowerBounds.coinTranslationPreservesClass_of_maskingSetup
#print axioms AlgorithmsToLowerBounds.AC0pFamilyModelWithMasking.closed
#print axioms AlgorithmsToLowerBounds.coinTranslationPreservesClass_of_maskingSetup_AC0p
#print axioms AlgorithmsToLowerBounds.false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_maskingSetup
#print axioms AlgorithmsToLowerBounds.maskingParams_of_adjacentBiasToHalfVsFair
#print axioms AlgorithmsToLowerBounds.CoinMaskingTranslationSetup.of_adjacentBiasToHalfVsFair
#print axioms AlgorithmsToLowerBounds.false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_adjacentMaskingSetup
#print axioms AlgorithmsToLowerBounds.quasiPolyLower_superPolynomialGrowth
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound
#print axioms AlgorithmsToLowerBounds.EventuallySizeLowerBound.weaken
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_of_eventual_superPolynomial_lowerBound
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_of_eventual_quasiPolynomial_lowerBound
#print axioms AlgorithmsToLowerBounds.not_depth_d_AC0p_of_quasiPoly_lowerBound
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_of_depthwise_quasiPoly_lowerBound
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_from_quasiPolynomial_contract
#print axioms AlgorithmsToLowerBounds.not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_from_asymptotic_quasiPolynomial_contract
#print axioms AlgorithmsToLowerBounds.productBiasWeight_total
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_true
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_not
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_not_le_of_one_sub_le
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_mono
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_mono_lowBias
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_mono_highBias
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_fair_eq_bitVecAcceptanceProbability
#print axioms AlgorithmsToLowerBounds.bitVecAcceptanceProbability_not
#print axioms AlgorithmsToLowerBounds.one_sub_upper_le_acceptanceProbability_fair_not
#print axioms AlgorithmsToLowerBounds.solvesCoinProblem_of_acceptanceProbability_bounds
#print axioms AlgorithmsToLowerBounds.MCSPThresholdOracle.accepts_of_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.MCSPThresholdOracle.rejects_of_not_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.ImplementedThresholdOracle.classSolvesCoinProblem_of_advantage
#print axioms AlgorithmsToLowerBounds.classSolvesCoinProblem_of_bounded
#print axioms AlgorithmsToLowerBounds.BoundedClassSolvesCoinProblem.mono_size
#print axioms AlgorithmsToLowerBounds.AC0pHalfVsFairCoinLowerBoundContract.excludes_small_solver
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinReductionContract.of_distributionFacts
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinReductionContract.of_treeMCSPPredicateMassFacts
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionProfile.hard_solvesCoin
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.of_notTreeMCSPPredicateMassFacts
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.of_treeMCSPPredicateBiasedLower_and_fairCounting
#print axioms AlgorithmsToLowerBounds.CoinDistinguisherFamily.solves_instance
#print axioms AlgorithmsToLowerBounds.CircuitCoinDistinguisherFamily.solves
#print axioms AlgorithmsToLowerBounds.CircuitCoinDistinguisherFamily.boundedSolves
#print axioms AlgorithmsToLowerBounds.AdjacentBiasMCSPThresholdSeparationFacts.toSolvesCoin
#print axioms AlgorithmsToLowerBounds.CoinDistinguisherFamily.of_adjacentBiasMCSP
#print axioms AlgorithmsToLowerBounds.CircuitCoinDistinguisherFamily.of_adjacentBiasMCSP_circuit
#print axioms AlgorithmsToLowerBounds.CoinDistinguisherToHalfVsFairTranslationContract.solvesCoin
#print axioms AlgorithmsToLowerBounds.halfVsFairCoinDistinguisherFamily
#print axioms AlgorithmsToLowerBounds.CircuitCoinDistinguisherFamily.translate_to_halfVsFair
#print axioms AlgorithmsToLowerBounds.BoundedClassSolvesCoinProblem_of_translated_realization
#print axioms AlgorithmsToLowerBounds.false_of_translated_realization_and_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.false_of_adjacentBias_realization_translation_and_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.of_adjacentBiasSeparation_and_translation
#print axioms AlgorithmsToLowerBounds.treeMCSPCountRatio_le_one_sub_self_fairLower
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.of_biasedLowComplexityMassFacts
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.hard_solvesCoin
#print axioms AlgorithmsToLowerBounds.treeMCSPPredicateDecision_spec
#print axioms AlgorithmsToLowerBounds.notTreeMCSPPredicateDecision_spec
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdHardDecision_spec
#print axioms AlgorithmsToLowerBounds.uniformTruthTableAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
#print axioms AlgorithmsToLowerBounds.fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
#print axioms AlgorithmsToLowerBounds.one_sub_countRatio_le_fairAcceptanceProbability_notTreeMCSPPredicateDecision
#print axioms AlgorithmsToLowerBounds.halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio
#print axioms AlgorithmsToLowerBounds.one_sub_countRatio_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
#print axioms AlgorithmsToLowerBounds.halfVsFair_lowBias_exactTreeMCSPThresholdHardDecision_le_of_treeMCSPPredicate_mass_lower
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdDecision_accepts_of_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdDecision_rejects_of_not_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdHardDecision_accepts_of_not_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdHardDecision_rejects_of_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_exactTreeMCSPThresholdDecision_le_treeMCSPPredicateDecision
#print axioms AlgorithmsToLowerBounds.treeMCSPPredicateDecision_le_acceptanceProbability_exactTreeMCSPThresholdDecision
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.sizeLowerBound_exactTreeMCSPThresholdLanguage_of_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound_and_reduction
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinQuantitativeContract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract_and_reduction
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinQuantitativeContract_and_reduction
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract_and_reduction
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract_and_reduction
#print axioms AlgorithmsToLowerBounds.halfVsFairMCSPCoinAsymptoticLanguage_eq_slice_at_tableLen
#print axioms AlgorithmsToLowerBounds.ac0pCoinLowerEnvelope_beatsEveryPolynomial_at_arbitrarilyLarge_tableLengths
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_halfVsFairMCSPCoinAsymptoticLanguage
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract_and_growth
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract
#print axioms AlgorithmsToLowerBounds.uniformTruthTableAcceptanceProbability_le_countRatio_of_treeMCSPOracle
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_localPRGTransfer
#print axioms AlgorithmsToLowerBounds.sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_publishedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_publishedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_publishedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_formulaCircuitPublishedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_publishedLowerBoundContract
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitRoute
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitRoute
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2Contract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2Contract
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2QuantitativeContract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2QuantitativeContract
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitLocalPRGSource
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitLocalPRGSource
#print axioms AlgorithmsToLowerBounds.no_PpolyFormula_of_formulaCircuitPublishedLowerBoundContract_and_growth
#print axioms AlgorithmsToLowerBounds.no_PpolyFormula_of_formulaCircuitPublishedLocalPRGRoute_and_growth
#print axioms AlgorithmsToLowerBounds.no_PpolyFormula_of_CKLM_formulaOrBranchingProgramRoute_and_growth
#print axioms AlgorithmsToLowerBounds.no_PpolyFormula_of_CKLMFormulaCircuitLocalPRGSource_and_growth
#print axioms AlgorithmsToLowerBounds.not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope
#print axioms AlgorithmsToLowerBounds.not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope
#print axioms AlgorithmsToLowerBounds.no_uniform_cklmEnvelopeFrequentEscape

#check Pnp4.Frontier.ContractExpansion.CanonicalRawTreeMCSPPrefixFields
#check Pnp4.Frontier.ContractExpansion.encodeTreeMCSPPrefixFields
#check Pnp4.Frontier.ContractExpansion.CanonicalRawTreeMCSPPrefixFields.toPrefixInput
#print axioms Pnp4.Frontier.ContractExpansion.encodeTreeMCSPPrefixFields_length_convention
#print axioms Pnp4.Frontier.ContractExpansion.bitLength_pos_of_pos
#print axioms Pnp4.Frontier.ContractExpansion.nat_lt_two_pow_bitLength
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_eq_of_readBit_eq
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_tail
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_zero
#print axioms Pnp4.Frontier.ContractExpansion.be_digit_step
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_slice
#print axioms Pnp4.Frontier.ContractExpansion.gammaBit_zero_prefix
#print axioms Pnp4.Frontier.ContractExpansion.gammaBit_terminator
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_gammaBit_payload
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux_gammaBit
#print axioms Pnp4.Frontier.ContractExpansion.decodeGamma_gammaBit
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux_gammaBit_from_at
#print axioms Pnp4.Frontier.ContractExpansion.prefixLength_lt_two_pow_idxWidth
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_encode_tag
#print axioms Pnp4.Frontier.ContractExpansion.sliceBits_encode_x
#print axioms Pnp4.Frontier.ContractExpansion.sliceBits_encode_p
#print axioms Pnp4.Frontier.ContractExpansion.parse_encodeTreeMCSPPrefixFields_partial_obligation
#print axioms Pnp4.Frontier.ContractExpansion.parse_encodeTreeMCSPPrefixFields
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_length_convention
#check Pnp4.Frontier.ContractExpansion.treeMCSPRuntimeAwarePrefixParser

section StreamingAndOneTapeMagnificationSurface

open Frontier.StreamingMagnification

/-! Exact standard-DAG carrier, paper-basis filter, and frozen-DAG conversion. -/
#check StandardDAG.FlatGate.InPaperBasis
#check StandardDAG.FlatCircuit.UsesOnlyAndOrNot
#check StandardDAG.FlatCircuit.toDag_ofDag
#check StandardDAG.FlatCircuit.ofDag_toDag
#check StandardDAG.FlatCircuit.gateCount_le_iff_toDag_size_le_succ

/-! Local shared-DAG evaluation traces for the future Sigma-3 matrix. -/
#check DAGEvalTrace.check_eq_true_iff
#check DAGEvalTrace.canonicalValues_isTrace
#check DAGEvalTrace.isTrace_unique
#check DAGEvalTrace.outputValue_eq_eval_of_isTrace
#check DAGEvalTrace.flat_exists_isTrace_and_outputValue_eq_iff
#check FixedBitstringCodec.unrank_rank
#check FixedBitstringCodec.rank_unrank
#check FixedBitstringCodec.unrank_eq_lexInput
#check PaddedDAGEvalTrace.check_eq_true_iff
#check PaddedDAGEvalTrace.exists_isPaddedTrace_and_outputValue_eq_iff

/-! Canonical fixed-length DAG codec. -/
#check DAGCodec.decode_encode
#check DAGCodec.encode_injective
#check DAGCodec.codeLength_le
#check DAGCodec.card_code

/-! Executable total search: both directions for both result branches. -/
#check EncodedTotalSearch.referenceSolver_found_sound
#check EncodedTotalSearch.referenceSolver_found_complete
#check EncodedTotalSearch.referenceSolver_noCircuit_sound
#check EncodedTotalSearch.referenceSolver_noCircuit_complete
#check EncodedTotalSearch.referenceDecision_eq_true_iff

/-! Operational streaming boundaries, accounting, and exact eventual normal form. -/
#check StreamingRAM.firstReadBoundaryGap
#check StreamingRAM.consecutiveReadBoundaryGap
#check StreamingRAM.immediateReportBoundaryGap
#check StreamingRAM.closedGap_le_extendedMaximum
#check StreamingRAM.CompletedRun.spaceUsed
#check StreamingRAM.CompletedRun.maxUpdateGap
#check StreamingRAM.CompletedRun.reportTime
#check PolynomialBounds.polyStreamingSolvable_iff
#check PolynomialBounds.noPolyStreamingSolver_iff
#check MMWProblem.completedRun_decision_iff
#check RuntimeAdviceBarrier.lengthAdviceLanguage_in_repo_P
#check Pnp3.ComplexityInterfaces.concatBitstring_castAdd
#check Pnp3.ComplexityInterfaces.concatBitstring_natAdd
#check OperationalUniformity.OperationalTM.complement_accepts
#check OperationalUniformity.OperationalTM.ofRepoCore
#check OperationalUniformity.CanonicalClockTM.toRepoTM_runTime
#check OperationalUniformity.CanonicalClockTM.toOperationalTM_accepts
#check OperationalUniformity.uniformP_complement
#check OperationalUniformity.canonicalUniformP_subset_repoP
#check OperationalUniformity.canonicalUniformNP_subset_repoNP
#check OperationalUniformity.canonicalUniformP_subset_uniformP
#check OperationalUniformity.canonicalUniformNP_subset_uniformNP
#check OperationalUniformity.constantLanguage_in_uniformP
#check OperationalClockBoundary.initialConfig_zeroExtend_agree
#check OperationalClockBoundary.crossConfigAgree_run
#check OperationalClockBoundary.canonicalRun_preStep_has_right_room
#check OperationalClockBoundary.canonicalRun_moveHead_right_eq_succ
#check OperationalClockBoundary.operational_zeroExtend_same_trace_prefix
#check OperationalClockBoundary.operational_zeroExtend_same_short_clock
#check OperationalClockBoundary.accepts_eq_output_of_early_pulse
#check OperationalClockBoundary.zeroExtend_zeroInput
#check OperationalClockBoundary.timingOnlyToggle_distinguishes_zero_extension
#check OperationalLeftClampProbe.leftClampProbe_state_card
#check OperationalLeftClampProbe.leftClampProbe_clock
#check OperationalLeftClampProbe.natRun_six
#check OperationalLeftClampProbe.probeFiniteNatAgree_step
#check OperationalLeftClampProbe.runConfig_six_exact
#check OperationalLeftClampProbe.runConfig_six_output
#check OperationalDynamicScan.scanUntilOne_clock
#check OperationalDynamicScan.scanUntilOne_state_card
#check OperationalDynamicScan.stepConfig_done
#check OperationalDynamicScan.runConfig_scans_zero_prefix
#check OperationalDynamicScan.runConfig_first_one
#check OperationalDynamicScan.accepts_eq_true_iff
#check OperationalDynamicScan.containsOneLanguage_in_uniformP
#check OperationalGammaPrefix.gammaPrefixWalker_state_card
#check OperationalGammaPrefix.natRun_progress_round
#check OperationalGammaPrefix.run_eq_finished_of_zero_prefix
#check OperationalGammaPrefix.accepts_eq_false_of_all_zero
#check OperationalGammaPrefix.accepts_truncated_zero_payload
#check OperationalGammaPrefix.accepts_canonical_gammaBit
#check OperationalGammaPrefix.canonical_gammaBit_run_head_eq_gammaLen
#check OperationalGammaZipper.gammaZipper_state_card
#check OperationalGammaZipper.cycleFrame_length_eq_total
#check OperationalGammaZipper.remaining_eq_one_iff_unprocessed_nil
#check OperationalGammaZipper.natRun_backwardPair
#check OperationalGammaZipper.natRun_shiftDelimiter
#check OperationalGammaZipper.natRun_forwardBubble
#check OperationalGammaZipper.natRun_finalC
#check OperationalGammaZipper.natRun_backwardPairs
#check OperationalGammaZipper.natRun_forwardPairs
#check OperationalGammaZipper.natRun_canonicalCycle_nonfinal
#check OperationalGammaZipper.natRun_canonicalCycle_final
#check OperationalGammaZipper.natRun_cycles_to_final
#check OperationalGammaZipper.natRun_gammaZipper_standalone
#check OperationalGammaZipper.natRun_scanFirst_active
#check OperationalGammaZipper.natRun_contextualScanFirst
#check OperationalGammaZipper.natRun_contextualScanFirst_active
#check OperationalGammaZipper.gammaExecution_runConfig_finish
#check OperationalGammaZipper.gammaZipper_accepts_frame
#check OperationalTaggedGamma.taggedGamma_state_card
#check OperationalTaggedGamma.requestTagList_eq_codec
#check OperationalTaggedGamma.step_first_finalC
#check OperationalTaggedGamma.step_second_finalC
#check OperationalTaggedGamma.step_third_finalC
#check OperationalTaggedGamma.tripleInitialFrame_length
#check OperationalTaggedGamma.tripleFinalFrame_length
#check OperationalTaggedGamma.afterFirst_drop
#check OperationalTaggedGamma.afterSecond_drop
#check OperationalTaggedGamma.taggedNatRun_canonicalTag
#check OperationalTaggedGamma.taggedNatRun_lift
#check OperationalTaggedGamma.taggedNatRun_scanFirst
#check OperationalTaggedGamma.taggedNatRun_contextualPhase
#check OperationalTaggedGamma.taggedNatRun_firstField
#check OperationalTaggedGamma.taggedNatRun_secondField
#check OperationalTaggedGamma.taggedNatRun_thirdField
#check OperationalTaggedGamma.taggedNatRun_triple
#check OperationalTaggedGamma.taggedTripleTime_lt_tapeLength
#check OperationalTaggedGamma.taggedExecution_runConfig_triple
#check OperationalTaggedGamma.taggedExecution_run_state_done
#check OperationalTaggedGamma.taggedGamma_accepts_canonical_triple
#check OperationalTaggedGamma.taggedExtendedInitialConfig_finiteNatAgree
#check OperationalTaggedGamma.taggedExecution_runConfig_extendedTriple
#check OperationalTaggedGamma.taggedExecution_extended_run_state_done
#check OperationalTaggedGamma.taggedGamma_accepts_canonical_prefix_with_suffix
#check OperationalTaggedGamma.codecGammaWord_eq_gammaBody
#check OperationalTaggedGamma.encodeRequest_list_eq_tripleInitialFrame_append_tail
#check OperationalTaggedGamma.startOffset_eq_codecTripleFootprint
#check OperationalTaggedGamma.encodedLength_eq_startOffset_add_tail
#check OperationalTaggedGamma.encodeRequest_drop_startOffset_eq_rawTail
#check OperationalTaggedGamma.encodeRequest_take_startOffset_eq_tripleInitialFrame
#check OperationalTaggedGamma.encodeRequest_initialConfig_finiteNatAgree
#check OperationalTaggedGamma.taggedNatRun_encodeRequest_handoff
#check OperationalTaggedGamma.taggedExecution_runConfig_encodeRequest_handoff
#check OperationalTaggedGamma.taggedExecution_runConfig_encodeRequest_head_eq_startOffset
#check OperationalTaggedGamma.zippedBody_empty_true_collision
#check OperationalTaggedGamma.tripleFinalFrame_empty_true_collision
#check OperationalTaggedGamma.taggedTripleTime_zero_one_collision
#check OperationalTaggedGamma.transformedHandoffConfig_empty_true_collision
#check OperationalTaggedGamma.taggedNatRun_empty_true_convergence
#check OperationalTaggedGamma.no_tripleFinalFrame_ordered_width_recovery
#check OperationalTaggedGamma.taggedGammaPulse_state_card
#check OperationalTaggedGamma.taggedNatRun_triple_active
#check OperationalTaggedGamma.pulseNatRun_triple
#check OperationalTaggedGamma.pulseNatRun_triple_succ
#check OperationalTaggedGamma.pulseExecution_runConfig_triple
#check OperationalTaggedGamma.taggedTripleTime_add_clockDelay
#check OperationalTaggedGamma.taggedClockDelay_pos
#check OperationalTaggedGamma.taggedClockDelay_eq_sub
#check OperationalTaggedGamma.taggedTripleTime_add_distributionEqualizer
#check OperationalTaggedGamma.taggedClockDelay_decomposition
#check OperationalTaggedGamma.taggedEqualizedTime_add_quarticFiller
#check OperationalTaggedGamma.taggedEqualizedTime_add_cubicFiller
#check OperationalTaggedGamma.no_postParse_lengthOnlyTaggedClockDelay
#check OperationalTaggedGamma.taggedGammaPulse_rejects_canonical_triple
#check OperationalTaggedGamma.taggedGammaPulse_rejects_canonical_prefix_with_suffix
#check FinitePHClosure.existsProject_eq_true_iff
#check FinitePHClosure.uniformP_existsProject
#check FinitePHClosure.forallProject_eq_true_iff
#check FinitePHClosure.uniformNPCollapse_of_class_eq
#check FinitePHClosure.uniformP_existsProject_of_collapse
#check FinitePHClosure.uniformP_forallProject_of_collapse
#check FinitePHClosure.uniformP_eaeProject_of_collapse
#check FinitePHClosure.uniformP_eaeProject_of_class_eq

/-! Stream-Merge block semantics, invariant, driver, and result wire. -/
#check StreamMerge.paperBlockLength_pos
#check StreamMerge.referenceStreamMerge_found_optimal
#check StreamMerge.referenceStreamMerge_found_prefixAgreement
#check StreamMerge.referenceStreamMerge_final_found_iff_hasCircuit
#check StreamMerge.referenceStreamMerge_final_noCircuit_iff
#check StreamMergeChoice.selectCode_eq_some_iff_isOptimal
#check StreamMergeChoice.referenceStreamMerge_found_iff_isOptimal
#check StreamMergeChoice.referenceStreamMerge_noCircuit_iff_forall_not_codeFits
#check StreamMergeAgreement.expectedBit_prefix
#check StreamMergeAgreement.expectedBit_block
#check StreamMergeAgreement.fits_iff_usesOnlyAndOrNot_and_pointwiseAgreement
#check StreamMergeAgreement.not_fits_iff_exists_counterexample
#check StreamMergeTracedCounterexample.flatOutputValue_eq_candidateBit_of_isTrace
#check StreamMergeTracedCounterexample.tracedExpectedBit_eq_expectedBit_of_isTrace
#check StreamMergeTracedCounterexample.not_fits_iff_hasTracedCounterexample
#check StreamMergeFailureMatrix.check_eq_true_iff
#check StreamMergeFailureMatrix.not_codeFits_iff_exists_failureWitness

/-! Interpreter regression: the logical `FailureMatrix` contains a dependent
branch, but its reflected checker must compile and execute without referring
to a private generated splitter. -/
private def failureCheckSmokeData : StandardDAG.FlatCircuitData :=
  { gateCount := 0, gates := [], output := 0 }

private def failureCheckSmokeCircuit : StandardDAG.FlatCircuit 1 :=
  Subtype.mk failureCheckSmokeData (by decide)

private def failureCheckSmokeBounded : DAGCodec.BoundedCircuit 1 0 :=
  Subtype.mk failureCheckSmokeCircuit (by decide)

private def failureCheckSmokeWindow :
    StreamMerge.WindowWellFormed 1 0 0 [] := by decide

#eval StreamMergeFailureMatrix.check failureCheckSmokeBounded []
  failureCheckSmokeWindow (DAGCodec.encode failureCheckSmokeBounded)
  (StreamMergeFailureMatrix.zeroWitness 1 0)

#check StreamMergeAgreementMatrix.fits_iff_usesOnlyAndOrNot_and_forall_exists_agreementMatrix
#check StreamMergeOptimalityMatrix.forall_exists_competitorMatrix_iff_minimality
#check StreamMergePrenexWire.queryTag_packQuery
#check StreamMergePrenexWire.queryCoordinate_packQuery
#check StreamMergePrenexWire.queryCode_packQuery
#check StreamMergePrenexBounds.codeLength_le_coarseCodeBound
#check StreamMergePrenexBounds.three_mul_le_codeLength
#check StreamMergePrenexBounds.choiceLength_le_commonWireBound
#check StreamMergePrenexBounds.queryLength_le_commonWireBound
#check StreamMergePrenexBounds.innerLength_le_commonWireBound
#check StreamMergePrenexBounds.commonWireBound_le_of_parameters_le
#check StreamMergePrenexBounds.commonWireBound_le_certificateLength
#check StreamMergeEncodedPrenex.check_eq_true_iff
#check StreamMergeEncodedPrenex.referenceOutputBit_eq_true_iff_encodedEAEShell
#check StreamMergeEncodedPrenex.referenceOutputBit_eq_true_iff_encodedEAECheck
#check StreamMergeCertificatePadding.certificateLength_mono_input
#check StreamMergeCertificatePadding.slice_zeroExtend
#check StreamMergeCertificatePadding.zeroExtend_slice_of_hasZeroPadding
#check StreamMergeCertificatePadding.choiceLength_le_outerCertificateLength
#check StreamMergeCertificatePadding.queryLength_le_middleCertificateLength
#check StreamMergeCertificatePadding.innerLength_le_innerCertificateLength
#check StreamMergeCertificatePadding.paddedOutputBitMatrix_noncanonicalQuery_iff
#check StreamMergeCertificatePadding.paddedOutputBitMatrix_pad_iff
#check StreamMergeCertificatePadding.exists_forall_exists_outputBitMatrix_iff_padded
#check StreamMergeCertificatePadding.encodedEAEShell_iff_paddedCertificateEAEShell
#check StreamMergeCertificatePadding.referenceOutputBit_eq_true_iff_paddedCertificateEAEShell

private def requestCodecSmoke : StreamMergeRequestCodec.RequestFields where
  n := 1
  s := 0
  blockLength := 0
  start := 0
  start_le := by norm_num
  priorCode := DAGCodec.encode failureCheckSmokeBounded
  prior := failureCheckSmokeBounded
  prior_decode := DAGCodec.decode_encode failureCheckSmokeBounded
  blockBits := fun _ => false
  position := ⟨0, by
    unfold StreamMergeWire.wireLength
    omega⟩

#eval
  (StreamMergeRequestCodec.parseRequest
    (StreamMergeRequestCodec.encodeRequest requestCodecSmoke)).isSome

#check StreamMergeRequestCodec.n_le_requestLength
#check StreamMergeRequestCodec.s_le_requestLength
#check StreamMergeRequestCodec.parse_encodeRequest
#check StreamMergeRequestCodec.parseRequest_length_exact
#check StreamMergeRequestCodec.outputBitLanguage_rejects_parse_failure
#check StreamMergeRequestCodec.outputBitLanguage_eq_true_iff_encodedEAEShell_of_parse
#check StreamMergeRequestCodec.outputBitLanguage_eq_true_iff_encodedEAECheck_of_parse
#check StreamMergeRequestCodec.outputBitLanguage_eq_true_iff_paddedCertificateEAEShell_of_parse
#check StreamMergeRequestCodec.outputBitLanguage_eq_true_iff_globalPaddedEAEShell
#check StreamMergeGlobalPHBridge.fullInputLength_strictMono
#check StreamMergeGlobalPHBridge.recoverBaseLength_sound
#check StreamMergeGlobalPHBridge.recoverBaseLength_fullInputLength
#check StreamMergeGlobalPHBridge.unpackRowInput_packRowInput
#check StreamMergeGlobalPHBridge.globalPaddedRowLanguage_pack_eq_true_iff_of_parse
#check StreamMergeGlobalPHBridge.eaeProject_eq_true_iff_packed_rows
#check StreamMergeGlobalPHBridge.eaeProject_eq_true_iff_globalPaddedEAEShell
#check StreamMergeGlobalPHBridge.outputBitLanguage_eq_true_iff_eaeProject
#check StreamMergeGlobalPHBridge.outputBitLanguage_eq_eaeProject
#check StreamMergeGlobalPHBridge.outputBitLanguage_in_uniformP_of_row_and_class_eq
#check StreamMergeGlobalPHBridge.outputBitLanguage_in_uniformP_of_canonicalRow_and_class_eq
#check StreamMergeDriver.referenceStreamDriver_found_iff_hasCircuit
#check StreamMergeDriver.referenceStreamDriver_noCircuit_iff
#check StreamMergeWire.parse_serialize
#check StreamMergeWire.serialize_injective
#check StreamMergeWire.outputBitGraph_functional
#check StreamMergeWire.referenceOutputBitGraph_functional
#check StreamMergeOutputFormula.referenceOutputBit_eq_true_iff

/-! Concrete one-tape/random-tape semantics and the finite local-HSG route. -/
#check Frontier.OneTapeMagnification.inputHead_le_runFrom
#check Frontier.OneTapeMagnification.readOnlyHeads_le_randomizedRunFrom
#check Frontier.OneTapeMagnification.acceptanceProbability_mem_unitInterval
#check Frontier.OneTapeMagnification.localGenerator_acceptance_gap_gt_one_sixth
#check Frontier.OneTapeMagnification.not_foolsWithin_one_sixth_of_localGenerator_gap
#check Frontier.OneTapeMagnification.Counting.card_easyTablesByCode_le
#check Frontier.OneTapeMagnification.Counting.four_mul_card_easyTablesByCode_lt
#check Frontier.OneTapeMagnification.Counting.uniformMachineAcceptance_lt_half_of_code_count
#check Frontier.OneTapeMagnification.CommunicationSparsity.sparse_membership_row_count_le_card_add_one
#check Frontier.OneTapeMagnification.CommunicationSparsity.sparse_membership_row_count_le_two_pow_add_one
#check Frontier.OneTapeMagnification.CommunicationSparsity.sparse_membership_row_count_le_two_pow_succ
#check Frontier.OneTapeMagnification.CommunicationSparsity.split_membership_row_count_le_card_add_one
#check Frontier.OneTapeMagnification.CommunicationSparsity.mem_semanticEasyTables
#check Frontier.OneTapeMagnification.CommunicationSparsity.semanticEasyTables_subset_easyTablesByCode
#check Frontier.OneTapeMagnification.CommunicationSparsity.split_rows_card_le_two_pow_codeLength_add_one_of_subset_easyTablesByCode
#check Frontier.OneTapeMagnification.CommunicationSparsity.split_rows_card_le_two_pow_codeLength_succ_of_subset_easyTablesByCode
#check Frontier.OneTapeMagnification.CommunicationSparsity.semantic_mcsp_split_row_count_le_two_pow_codeLength_add_one
#check Frontier.OneTapeMagnification.CommunicationSparsity.semantic_mcsp_split_row_count_le_two_pow_codeLength_succ
#check Frontier.OneTapeMagnification.localGenerator_fooling_excludes_boundedErrorMCSP
#check Frontier.OneTapeMagnification.cachedInputMachine_state_card
#check Frontier.OneTapeMagnification.cachedInputTransition_stay_independent_general
#check Frontier.OneTapeMagnification.cachedInputMachine_step_cachedConfiguration
#check Frontier.OneTapeMagnification.cachedInputMachine_run_succ
#check Frontier.OneTapeMagnification.cachedInputMachine_accepting_run_succ_iff
#check Frontier.OneTapeMagnification.cachedInputMachine_acceptsWithin_succ_iff
#check Frontier.OneTapeMagnification.complementMachine_run
#check Frontier.OneTapeMagnification.complementMachine_acceptsWithin_iff_rejectsWithin
#check Frontier.OneTapeMagnification.complementMachine_rejectsWithin_iff_acceptsWithin
#check Frontier.OneTapeMagnification.card_hardWitnessTables_gt_half
#check Frontier.OneTapeMagnification.coMCSP_denseAboveHalf
#check Frontier.OneTapeMagnification.localGenerator_does_not_hit_coMCSP
#check Frontier.OneTapeMagnification.localGenerator_denseHitting_excludes_exactCoMCSP
#check Frontier.OneTapeMagnification.complementMachine_exactCoMCSPBehavior_of_exactMCSPDecision
#check Frontier.OneTapeMagnification.localGenerator_denseHitting_excludes_exactMCSPDecision
#check Frontier.OneTapeMagnification.weightedGeneratorAverage_eq_zero_of_support_rejects
#check Frontier.OneTapeMagnification.weightedGeneratorAverage_eq_zero_of_nonzero_support_rejects
#check Frontier.OneTapeMagnification.ComponentQueryTree.card_le_depth_of_computesPromisedUnambiguousOr
#check Frontier.OneTapeMagnification.twoDisjointComponent_aggregate_error_eq_sum_errors
#check Frontier.OneTapeMagnification.weightedApproximation_support_hits
#check Frontier.OneTapeMagnification.deterministicTableAcceptanceIndicator_eq_true_iff
#check Frontier.OneTapeMagnification.uniform_deterministicAcceptanceIndicator_gt_half
#check Frontier.OneTapeMagnification.signedWeightedApproximation_nonzeroSupport_hits_denseAcceptance
#check Frontier.OneTapeMagnification.signedWeightedApproximation_hitsDenseOneTapeAcceptance
#check Frontier.OneTapeMagnification.signedWeightedApproximation_excludes_exactMCSPDecision
#check Frontier.OneTapeMagnification.not_hits_avoidSupport
#check Frontier.OneTapeMagnification.card_avoidSupport_true_lower_bound
#check Frontier.OneTapeMagnification.exists_avoidSupport_eq_true_of_card_lt
#check Frontier.OneTapeMagnification.singletonComponents_disjoint
#check Frontier.OneTapeMagnification.exists_singletonComponent_eq_true_iff
#check Frontier.OneTapeMagnification.existsUnique_singletonComponent_iff
#check Frontier.OneTapeMagnification.fullBucketBoundary_injective
#check Frontier.OneTapeMagnification.canonicalBoundary_mem_bucket
#check Frontier.OneTapeMagnification.canonicalBoundary_is_minimum
#check Frontier.OneTapeMagnification.canonicalBoundary_tie_leftmost
#check Frontier.OneTapeMagnification.canonicalBoundary_adjacent_gap_lt_two_mul
#check Frontier.OneTapeMagnification.canonicalBoundary_charging_le_total
#check Frontier.OneTapeMagnification.sum_canonicalBoundary_le_div
#check Frontier.OneTapeMagnification.sum_workBoundaryCrossingCount_le_steps
#check Frontier.OneTapeMagnification.sum_canonicalWorkBoundaryCrossings_le_div
#check Frontier.OneTapeMagnification.mem_canonicalCrossingEvents_iff
#check Frontier.OneTapeMagnification.canonicalCutDescription_apply
#check Frontier.OneTapeMagnification.canonicalCrossingRecordOfOccurrence_physicalCut
#check Frontier.OneTapeMagnification.length_canonicalCrossingRecords_eq_sum
#check Frontier.OneTapeMagnification.length_canonicalCrossingRecords_le_div
#check Frontier.OneTapeMagnification.card_ambientCrossingPayloadVector
#check Frontier.OneTapeMagnification.card_ambientCanonicalAlpha
#check Frontier.OneTapeMagnification.canonicalBoundary_existsUnique_offset
#check Frontier.OneTapeMagnification.canonicalCutDescription_eq_cutDescriptionOfOffsets
#check Frontier.OneTapeMagnification.card_canonicalCutOffsets
#check Frontier.OneTapeMagnification.card_ambientCanonicalOffsetAlpha
#check Frontier.OneTapeMagnification.decode_encodePaddedWord
#check Frontier.OneTapeMagnification.mem_canonicalCrossingRecords_physicalCut_recovered
#check Frontier.OneTapeMagnification.decode_canonicalPaddedAlpha_word
#check Frontier.OneTapeMagnification.card_paddedCanonicalAlpha
#check Frontier.OneTapeMagnification.canonicalBoundary_all_gaps
#check Frontier.OneTapeMagnification.workBlockAt_canonicalBoundary
#check Frontier.OneTapeMagnification.workCell_sameBlock_spatial_diameter_lt_two_mul
#check Frontier.OneTapeMagnification.workBlockAt_ne_iff_crosses_selectedBoundary
#check Frontier.OneTapeMagnification.canonicalWorkBlockAtTime_change_iff_selectedCrossing
#check Frontier.OneTapeMagnification.actualCanonicalWorkBlockAtTime
#check Frontier.OneTapeMagnification.freshInputPositions_eq_filterMap
#check Frontier.OneTapeMagnification.stableGroupedFreshInputPositions_has_at_most_K_add_one_strict_runs
#check Frontier.OneTapeMagnification.HasObliviousReadOnceInputOrder
#check Frontier.OneTapeMagnification.actualRunInputEvents_fresh_positions_pairwise_lt
#check Frontier.OneTapeMagnification.actualRun_stableGroupedFresh_has_at_most_K_add_one_strict_runs
#check Frontier.OneTapeMagnification.cachedRun_stay_instruction_independent_of_unread
#check Frontier.OneTapeMagnification.stableGroupedInputEvents_perm
#check Frontier.OneTapeMagnification.stableGroupedFreshInputPositions_perm
#check Frontier.OneTapeMagnification.actualRun_stableGroupedFreshInputPositions_nodup
#check Frontier.OneTapeMagnification.chronologicalCrossingScheduleInputOrder_eq_range'
#check Frontier.OneTapeMagnification.stableGroupedCrossingScheduleInputOrder_perm
#check Frontier.OneTapeMagnification.FixedCrossingSchedule.readOnceInputOrder_nodup
#check Frontier.OneTapeMagnification.length_actualSelectedBoundaryCrossingTimes_le_div
#check Frontier.OneTapeMagnification.length_actualCanonicalWorkBlockRuns_le_div_add_one
#check Frontier.OneTapeMagnification.length_actualCrossingScheduleSegments_le_div_add_one
#check Frontier.OneTapeMagnification.flatten_actualCanonicalWorkBlockRuns
#check Frontier.OneTapeMagnification.actualFixedCrossingSchedule
#check Frontier.OneTapeMagnification.freshInputPositions_actualRunInputEvents_eq_range
#check Frontier.OneTapeMagnification.chronological_actualCrossingScheduleInputOrder_eq_fresh
#check Frontier.OneTapeMagnification.actualFixedCrossingSchedule_readOnceInputOrder_perm_fresh
#check Frontier.OneTapeMagnification.existsUnique_actualSelectedBoundaryAtTime
#check Frontier.OneTapeMagnification.chronologicalCanonicalCrossingEntries_times_pairwise_lt
#check Frontier.OneTapeMagnification.length_chronologicalCanonicalCrossingRecords_le_div
#check Frontier.OneTapeMagnification.mem_chronologicalCanonicalCrossingRecords_physicalCut_recovered
#check Frontier.OneTapeMagnification.decode_chronologicalCanonicalPaddedAlpha_word
#check Frontier.OneTapeMagnification.map_sourceTime_chronologicalTimedCanonicalCrossingTokens
#check Frontier.OneTapeMagnification.chronologicalTimedCanonicalCrossingTokens_times_pairwise_lt
#check Frontier.OneTapeMagnification.decode_chronologicalTimedCanonicalAlpha_word
#check Frontier.OneTapeMagnification.card_ambientTimedCanonicalAlpha
#check Frontier.OneTapeMagnification.length_decodePaddedWord_le
#check Frontier.OneTapeMagnification.timedAlphaWordSyntacticCheck_eq_true_iff
#check Frontier.OneTapeMagnification.chronologicalTimedCanonicalAlpha_word_syntacticallyValid
#check Frontier.OneTapeMagnification.sum_runCrossingCount_le_time
#check Frontier.OneTapeMagnification.sum_extracted_canonical_cut_crossings_le_div
#check Frontier.OneTapeMagnification.accepting_run_has_unique_canonical_path_transcript
#check Frontier.OneTapeMagnification.cached_run_state_at_succ
#check Frontier.OneTapeMagnification.BoundedWorkTape.card
#check Frontier.OneTapeMagnification.run_workTape_eq_blank_of_time_le_cell
#check Frontier.OneTapeMagnification.card_machineBoundaryTapeInterface
#check Frontier.OneTapeMagnification.decode_boundaryTapeInterfaceAt_eq_run
#check Frontier.OneTapeMagnification.run_split_through_boundaryTapeInterface
#check Frontier.OneTapeMagnification.restrictWorkSlab_workTape_write_of_mem
#check Frontier.OneTapeMagnification.step_sameOnWorkSlab
#check Frontier.OneTapeMagnification.runFrom_sameOnWorkSlab
#check Frontier.OneTapeMagnification.runFrom_sameOnWorkSlab_same_input
#check Frontier.OneTapeMagnification.restrictWorkSlab_runFrom_eq_of_avoids
#check Frontier.OneTapeMagnification.restrictWorkSlab_runFrom_eq_of_sameOn_disjoint_visitedSlab
#check Frontier.OneTapeMagnification.runFrom_sameOn_two_workSlabs
#check Frontier.OneTapeMagnification.runFrom_sameOn_two_workSlabs_of_sameOnTwoAtMidpoint
#check Frontier.OneTapeMagnification.workBlockAt_eq_iff_workCellInCanonicalSlab
#check Frontier.OneTapeMagnification.canonicalBlockWidth_le_two_mul
#check Frontier.OneTapeMagnification.workHeadTrajectoryFrom_in_canonicalBlockSlab
#check Frontier.OneTapeMagnification.workHeadTrajectory_in_canonicalBlockSlab
#check Frontier.OneTapeMagnification.actualCanonicalWorkBlockGroup_map_val_eq_range'
#check Frontier.OneTapeMagnification.actualCanonicalWorkBlockGroup_label_constant
#check Frontier.OneTapeMagnification.actualCanonicalWorkBlockGroup_workHead_in_slab
#check Frontier.OneTapeMagnification.runFrom_sameOn_actualCanonicalWorkBlockGroup
#check Frontier.OneTapeMagnification.isActualProperGroupStop_iff_chronologicalCrossingPostTime
#check Frontier.OneTapeMagnification.lastTransition_mem_selectedCrossingTimes_iff
#check Frontier.OneTapeMagnification.workCrossingDirectionOf_eq_leftToRight_iff_workBlocks
#check Frontier.OneTapeMagnification.workCrossingDirectionOf_eq_rightToLeft_iff_workBlocks
#check Frontier.OneTapeMagnification.mem_chronologicalCanonicalCrossingEntries_endpoint_data
#check Frontier.OneTapeMagnification.actualCrossingScheduleSegments_eq_append_group
#check Frontier.OneTapeMagnification.chronologicalEntry_postInputHead_eq_groupSegmentStop
#check Frontier.OneTapeMagnification.actualFixedCrossingSchedule_initial_terminal_endpoints
#check Frontier.OneTapeMagnification.canonicalBlockUpperExclusive_le_total_add_one
#check Frontier.OneTapeMagnification.canonicalBlockSlabsDisjoint_of_ne
#check Frontier.OneTapeMagnification.canonicalBlockSlab_eq_full_of_div_eq_zero
#check Frontier.OneTapeMagnification.canonicalBlockSlab_zero_time
#check Frontier.OneTapeMagnification.advertisedBlockUpperExclusive_le_total_add_one
#check Frontier.OneTapeMagnification.advertisedBlockWidth_le_two_mul
#check Frontier.OneTapeMagnification.advertisedBlockSlabsDisjoint_of_ne
#check Frontier.OneTapeMagnification.workCell_existsUnique_advertisedBlockSlab
#check Frontier.OneTapeMagnification.advertisedBlockWidth_canonicalCutOffsets
#check Frontier.OneTapeMagnification.restrictWorkSlab_workTapeOfWorkSlab
#check Frontier.OneTapeMagnification.fixedAlphaBlockVisitCheck_eq_true_iff
#check Frontier.OneTapeMagnification.fixedAlphaBlockVisitValid_replays_matching_entry
#check Frontier.OneTapeMagnification.fixedAlphaBlockVisitValid_of_matching_concrete_replay
#check Frontier.OneTapeMagnification.fixedAlphaBlockVisitReplayCheck_eq_true_iff
#check Frontier.OneTapeMagnification.fixedAlphaBlockVisitListCheck_eq_true_iff
#check Frontier.OneTapeMagnification.fixedAlphaBlockVisits_zero_time_eq_nil
#check Frontier.OneTapeMagnification.advertisedTimedCrossing_sourceBlock_ne_destinationBlock
#check Frontier.OneTapeMagnification.advertisedTimedCrossing_preWorkHead_in_sourceSlab
#check Frontier.OneTapeMagnification.advertisedTimedCrossing_postWorkHead_in_destinationSlab
#check Frontier.OneTapeMagnification.TimedAlphaVisitScheduleValid
#check Frontier.OneTapeMagnification.timedAlphaScheduledVisits_pairwise_precedes
#check Frontier.OneTapeMagnification.timedAlphaBlockVisits_chronological_of_chained
#check Frontier.OneTapeMagnification.TimedAlphaVisitScheduleValid.blockVisitsChronological
#check Frontier.OneTapeMagnification.actualTimedEntry_advertisedPhysicalCut
#check Frontier.OneTapeMagnification.actualTimedEntry_advertisedPreWorkHead
#check Frontier.OneTapeMagnification.actualTimedEntry_advertisedPostWorkHead
#check Frontier.OneTapeMagnification.actualTimedEntry_advertisedPostEndpoint_matches
#check Frontier.OneTapeMagnification.actualCanonicalWorkBlockGroupVisit_valid
#check Frontier.OneTapeMagnification.actualCanonicalWorkBlockGroupVisit_outputSlab
#check Frontier.OneTapeMagnification.actualCanonicalFirstWorkBlockGroupVisit_valid_from_blank
#check Frontier.OneTapeMagnification.actualProperGroupStopTimes_eq_timedTokenPostTimes
#check Frontier.OneTapeMagnification.actualProperEntryTokenFold_from_groups
#check Frontier.OneTapeMagnification.actualTimedEntry_sourceBlock_eq_groupLabel
#check Frontier.OneTapeMagnification.actualTimedEntry_destinationBlock_eq_nextGroupLabel
#check Frontier.OneTapeMagnification.actualTimedEntry_advertisedPostEndpoint_eq_runEndpoint
#check Frontier.OneTapeMagnification.timedAlphaScheduledVisitAt_actualGroup
#check Frontier.OneTapeMagnification.exists_actualTimedAlphaVisitScheduleValid_of_no_terminal
#check Frontier.OneTapeMagnification.exists_actualTimedAlphaVisitScheduleValid_of_terminal
#check Frontier.OneTapeMagnification.exists_actualTimedAlphaVisitScheduleValid
#check Frontier.OneTapeMagnification.restrictOtherCanonicalBlock_runFrom_eq_of_sameOn_actualGroup
#check Frontier.OneTapeMagnification.groupsSlice_map_val_eq_range'_of_flatten_eq_finRange
#check Frontier.OneTapeMagnification.actualCanonicalWorkBlockGroupsSlice_map_val_eq_range'
#check Frontier.OneTapeMagnification.targetCanonicalSlab_eq_between_actualVisits
#check Frontier.OneTapeMagnification.actualTwoTargetBlockVisits_strictlySeparated
#check Frontier.OneTapeMagnification.actualTargetBlockVisit_outputSlab_eq_nextEntrySlab
#check Frontier.OneTapeMagnification.actualTwoTargetBlockVisits_replayAccepted
#check Frontier.OneTapeMagnification.actualTwoTargetBlockVisits_listAccepted
#check Frontier.OneTapeMagnification.replayActualTwoTargetBlockVisits_eq_secondExitSlab
#check Frontier.OneTapeMagnification.actualFixedAlphaBlockSlabAtTime_eq_after_away_group
#check Frontier.OneTapeMagnification.actualProperTimedTokenFold_with_schedule
#check Frontier.OneTapeMagnification.timedAlphaFinalScheduledVisit_eq_actualLastGroup
#check Frontier.OneTapeMagnification.timedAlphaScheduledVisitAtCrossing_eq_actualLastGroup
#check Frontier.OneTapeMagnification.exists_actualTimedAlphaVisitScheduleValid_with_groups
#check Frontier.OneTapeMagnification.ActualTimedAlphaScheduledVisitsFromGroups.blockVisits_scan
#check Frontier.OneTapeMagnification.ActualFixedAlphaBlockVisitsFromGroups.chronological
#check Frontier.OneTapeMagnification.actualFixedAlphaBlockVisitsFromGroups_replayAccepted_and_result
#check Frontier.OneTapeMagnification.ActualFixedAlphaBlockVisitsFromGroups.listAccepted
#check Frontier.OneTapeMagnification.exists_allActualFixedAlphaBlockVisits_listAcceptedFromBlank
#check Frontier.OneTapeMagnification.exists_actualTimedAlphaVisitScheduleValid_allBlockVisitsAccepted
#check Frontier.OneTapeMagnification.executeTimedAlphaTokenVisitFold_eq_some_iff
#check Frontier.OneTapeMagnification.finishTimedAlphaVisitSchedule_eq_some_iff
#check Frontier.OneTapeMagnification.buildTimedAlphaVisitSchedule_eq_some_iff
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleCheck_eq_true_iff
#check Frontier.OneTapeMagnification.timedAlphaAllBlockVisitsCheckFromBlank_eq_true_iff
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
#check Frontier.OneTapeMagnification.exists_actualTimedAlphaVisitScheduleAllBlockVisitsCheck_eq_true
#check Frontier.OneTapeMagnification.fixedAlphaAcceptedVisit_globalStep
#check Frontier.OneTapeMagnification.allScheduledVisitsReplayAccepted_globalReplay
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleValid_allBlockVisitsAccepted_matchesGlobalRun
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleValid_allBlockVisitsAccepted_globalGlue
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCheck_matchesGlobalRun
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCheck_globalGlue
#check Frontier.OneTapeMagnification.advertisedCutOffsetLeftmostMinimumCheck_eq_true_iff
#check Frontier.OneTapeMagnification.advertisedCutOffsetIsLeftmostMinimum_iff_eq_canonicalBoundaryOffset
#check Frontier.OneTapeMagnification.advertisedCutOffsetsAreLeftmostMinimum_iff_eq_canonical
#check Frontier.OneTapeMagnification.advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
#check Frontier.OneTapeMagnification.advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_physicalCuts_eq
#check Frontier.OneTapeMagnification.advertisedTimedAlphaCutMinimalityCheck_actual_eq_true
#check Frontier.OneTapeMagnification.streamingWorkBoundaryCrossingCountFrom_add
#check Frontier.OneTapeMagnification.streamingWorkBoundaryCrossingCountFrom_eq
#check Frontier.OneTapeMagnification.fixedAlphaBlockVisitStreamingCrossingCount_eq_concrete
#check Frontier.OneTapeMagnification.fixedAlphaScheduledVisitsStreamingCrossingCount_eq_globalFrom
#check Frontier.OneTapeMagnification.fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_actual_of_check
#check Frontier.OneTapeMagnification.replayedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
#check Frontier.OneTapeMagnification.fixedAlphaScheduledVisitsBucketCrossingCounters_eq_actual
#check Frontier.OneTapeMagnification.fixedAlphaScheduledVisitsBucketCrossingCounter_le_horizon
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true_iff
#check Frontier.OneTapeMagnification.exists_actualTimedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true
#check Frontier.OneTapeMagnification.card_bucketCutCounterState
#check Frontier.OneTapeMagnification.card_localReplayCutCounterState
#check Frontier.OneTapeMagnification.card_localReplayCutCounterState_product
#check Frontier.OneTapeMagnification.canonicalLocalReplayCutCounterState_card_le
#check Frontier.OneTapeMagnification.bucketCutCounterStateOfAcceptedReplay_apply_val
#check Frontier.OneTapeMagnification.bucketCutCounterStateOfAcceptedReplay_apply_val_eq_actual
#check Frontier.OneTapeMagnification.TimedAlphaTokenVisitFold.actualCrossingsExactly
#check Frontier.OneTapeMagnification.acceptedTimedAlphaFinalVisit_no_selectedCrossing
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleValid_allBlockVisitsAccepted_decode_eq_actual
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCheck_eq_chronologicalAlpha
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCheck_cutCheck_eq_chronologicalAlpha
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_chronologicalAlpha
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_unique
#check Frontier.OneTapeMagnification.leftBucketTailCandidate_strictlyInsideAdvertisedBlock
#check Frontier.OneTapeMagnification.timedAlphaAcceptingComponentMultiplicity_eq_acceptanceBit
#check Frontier.OneTapeMagnification.acceptedTimedAlphaStableGroupedQueryOrder_perm_range
#check Frontier.OneTapeMagnification.acceptedTimedAlphaFiniteInputQueryOrder_perm_finRange
#check Frontier.OneTapeMagnification.onePassAdjacentBucketCutCounters_apply_val_eq_actual
#check Frontier.OneTapeMagnification.onePassFixedAlphaBlockVisitCheck_eq_fixedAlphaBlockVisitCheck
#check Frontier.OneTapeMagnification.onePassFixedAlphaBlockList_timed_counter_val
#check Frontier.OneTapeMagnification.onePassAdvertisedBlockTwoWindowCheck_eq_true_iff_adjacentCuts
#check Frontier.OneTapeMagnification.inPlaceTwoWindowClosedBucketTrace_eq_finRange
#check Frontier.OneTapeMagnification.sourceBlockSummedCrossingProfile_eq_actual
#check Frontier.OneTapeMagnification.timedAlphaBlockVisits_nonadjacent_crossingContribution_eq_zero
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleAllBlockVisitsCheck_inPlaceTwoWindowFold_iff_actualCuts
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff
#check Frontier.OneTapeMagnification.timedAlphaInPlaceCanonicalComponentCheck_eq_true_iff
#check Frontier.OneTapeMagnification.exists_timedAlphaInPlaceAcceptingComponentCheck_iff
#check Frontier.OneTapeMagnification.card_cachedFullBlockValidatorState
#check Frontier.OneTapeMagnification.finiteLocalCachedFinalStep_stepped_materialize
#check Frontier.OneTapeMagnification.finiteCachedFixedAlphaVisitCertificate_iff
#check Frontier.OneTapeMagnification.compileFiniteCachedFixedAlphaVisit_eval_eq_true_iff_of_realizes
#check Frontier.OneTapeMagnification.fixedVisitFiniteQueryOrder_perm_finRange
#check Frontier.OneTapeMagnification.finiteCachedVisitComparisonTarget_halted
#check Frontier.OneTapeMagnification.fixedVisitFiniteQueryOrder_realizes_of_prefix_closes
#check Frontier.OneTapeMagnification.compileFixedVisitFiniteQueryOrder_eval_eq_true_of_valid_of_prefix_closes
#check Frontier.OneTapeMagnification.FiniteStreamingVerifier.ExactFreshTrace.closeAfterAnswers
#check Frontier.OneTapeMagnification.fixedVisitFreshPrefixClosesToComparison_of_valid
#check Frontier.OneTapeMagnification.compileFixedVisitFiniteQueryOrder_eval_eq_true_of_valid
#check Frontier.OneTapeMagnification.freshQuery_at_expectedInputHead_precludes_acceptance
#check Frontier.OneTapeMagnification.compileFixedVisitFiniteQueryOrder_entryInputHead_le_exitInputHead
#check Frontier.OneTapeMagnification.advertisedLocalReplayState_card_le_padded
#check Frontier.OneTapeMagnification.LayeredQueryProgram.isReadOnce_of_fixedQueryOrder_nodup
#check Frontier.OneTapeMagnification.FiniteStreamingVerifier.compileFixedOrderList_isReadOnce
#check Frontier.OneTapeMagnification.FiniteStreamingVerifier.compileAdaptive_width
#check Frontier.OneTapeMagnification.FiniteStreamingVerifier.isReadOnce_of_freshQueriesStrictlyIncrease
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaVisit_query?_eq_some_iff
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaVisit_isReadOnce
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_iff
#check Frontier.OneTapeMagnification.card_finiteCachedBlockVisitListStreamingState
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitListFuel_le_two_mul_horizon
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_width_eq
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_eval
#check Frontier.OneTapeMagnification.finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
#check Frontier.OneTapeMagnification.finiteCachedFixedAlphaBlockVisitListStreamingFromBlank_iff
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_isReadOnce
#check Frontier.OneTapeMagnification.timedAlphaBlockVisits_inputHeadsOrdered_of_allBlockListsAccepted
#check Frontier.OneTapeMagnification.compileAdaptiveAcceptedTimedAlphaBlockVisitList_isReadOnce
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitList_inputDrivenCore_prepend
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitList_inputDrivenCore_empty
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitList_inputDrivenCore_active_eq_streaming
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitList_inputDrivenCore_completed_of_certificate
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_eval_eq_true_of_replayAccepted
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_eval_eq_true_iff_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitList_liveBefore_of_replayAccepted
#check Frontier.OneTapeMagnification.card_finiteCachedAllBlocksStreamingState
#check Frontier.OneTapeMagnification.fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksStreamingStep_completed_next
#check Frontier.OneTapeMagnification.finiteCachedAllBlocks_inputDrivenCore_advance_of_replayAccepted_of_live
#check Frontier.OneTapeMagnification.finiteCachedAllBlocks_inputDrivenCore_advance_of_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedAllBlocks_inputDrivenCore_completed_iff_replayAccepted
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_width
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_eval
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_eval_eq_true_iff_replayAccepted
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_eval_eq_allBlockVisitsCheck_of_valid
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleAllBlocksReflects_canonical_of_valid
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleFiniteOuterInPlaceCheck_eq_true_iff
#check Frontier.OneTapeMagnification.timedAlphaVisitScheduleFiniteOuterInPlaceCheck_canonical_eq_true_iff
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_isReadOnce_of_traceRefines
#check Frontier.OneTapeMagnification.LayeredQueryProgram.guardByMasterOrder_eval_eq_of_follows
#check Frontier.OneTapeMagnification.FiniteStreamingVerifier.ExactAdaptiveQueryOrder.compileAdaptive_queryTrace_eq
#check Frontier.OneTapeMagnification.LayeredQueryProgram.executionQueriesFollowMaster_of_exactAdaptiveQueryOrder
#check Frontier.OneTapeMagnification.finiteCachedFixedAlphaVisit_exactAdaptiveQueryOrder_of_valid
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitList_exactAdaptiveQueryOrder_of_certificate
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_queryTrace_eq_advertised_of_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitListExactTraceMatchesAdvertisedOrder_of_replayAccepted
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_executionQueriesFollowAdvertisedOrder_of_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleMasterQueryOrder_eq_blockVisits
#check Frontier.OneTapeMagnification.finiteCachedAllBlocks_exactAdaptiveQueryOrder_of_replayAccepted
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_queryTrace_eq_blockVisits_of_replayAccepted
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_queryTrace_eq_master_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleExecutionQueriesFollowMaster_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_base_of_valid_acceptedFromBlank_canonical
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_true_of_valid_acceptedFromBlank_canonical
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks_isReadOnce
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks_width
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_isReadOnce
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_true_of_accepted
#check Frontier.OneTapeMagnification.encodeFiniteCachedAllBlocksWithFoldState_injective
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleWithFoldEmbedding
#check Frontier.OneTapeMagnification.finiteCachedVisitStreamingRollingCounterStep_inside_global
#check Frontier.OneTapeMagnification.finiteCachedVisitStreamingRollingCounterStep_final_global
#check Frontier.OneTapeMagnification.finiteCachedVisitStreamingRollingCounterStep_halted_global
#check Frontier.OneTapeMagnification.finiteCachedVisitStreamingRollingCounterStep_final_halted_global
#check Frontier.OneTapeMagnification.runFiniteCachedVisitStreamingRollingCountersWithUnreads_counters_eq_onePassFixedAlphaVisitFrom_of_completed
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitListStreamingRollingCounterStep_completed_next
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitListStreamingRollingCounterStep_completed_last
#check Frontier.OneTapeMagnification.runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_certificate
#check Frontier.OneTapeMagnification.runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksStreamingRollingCounterStep_completed_next_counters
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksStreamingRollingCounterStep_completed_last
#check Frontier.OneTapeMagnification.runFiniteCachedAllBlocksRollingCounters_eq_onePass_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.runFiniteCachedAllBlocksRollingCountersFromWithTransport_eq_onePass
#check Frontier.OneTapeMagnification.onePassFixedAlphaAllBlocksCountersWithTransport_eq_inPlace_counters
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRollingStreamingStep_completed_next
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRollingStreamingStep_completed_last
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRollingBlockStep_eq_inPlace_of_accepted
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRollingFold_eq_inPlace_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleInPlaceRollingEmbedding
#check Frontier.OneTapeMagnification.card_finiteCachedTimedAlphaScheduleInPlaceRollingState_le
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_width
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_width_le_two_pow
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaScheduleInPlaceRollingTotal_width_le_two_pow
#check Frontier.OneTapeMagnification.eraseFiniteCachedAllBlocksInPlaceRolling_inputDrivenCore
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitListRolling_inputDrivenCore_active_eq_streaming
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitListRolling_inputDrivenCore_head_completed_of_stepCertificate
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitListRolling_inputDrivenCore_completed_of_certificate
#check Frontier.OneTapeMagnification.finiteCachedBlockVisitListRolling_inputDrivenCore_completed_of_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_one_active
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_advance_of_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_prefix_of_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_completed_of_replayAccepted
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_completed_eq_inPlace_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_eq_inPlace_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_isReadOnce
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_width_le_two_pow_of_valid
#check Frontier.OneTapeMagnification.finiteCachedAllBlocksInPlaceRollingExactAdaptiveQueryOrder_erase
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_queryTrace_eq_master_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleInPlaceRollingExecutionQueriesFollowMaster_of_acceptedFromBlank
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_base_of_valid_acceptedFromBlank_canonical
#check Frontier.OneTapeMagnification.compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_timedAlphaFold_of_valid_acceptedFromBlank_canonical
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck_eq_existing_of_valid
#check Frontier.OneTapeMagnification.finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck_eq_true_iff_of_valid
#check Frontier.OneTapeMagnification.card_inPlaceTwoWindowFoldState
#check Frontier.OneTapeMagnification.card_fixedAlphaMultiVisitValidatorState
#check Frontier.OneTapeMagnification.card_fixedAlphaMultiVisitValidatorState_le_two_pow
#check Frontier.OneTapeMagnification.advertisedSelectedCutMultiplicity_eq_actual_of_componentCheck
#check Frontier.OneTapeMagnification.exists_staticTimedAlphaFiniteInputQueryOrder_of_componentCheck
#check Frontier.OneTapeMagnification.oneSidedLeftmostMinimumCheck_eq_advertisedCutCheck
#check Frontier.OneTapeMagnification.card_localReplayState
#check Frontier.OneTapeMagnification.canonicalLocalReplayState_card_bounds
#check Frontier.OneTapeMagnification.singleScale_time_le_max_cost_squared
#check Frontier.OneTapeMagnification.singleScale_time_le_budget_squared
#check Frontier.OneTapeMagnification.singleScale_budget_exceeded_on_one_side
#check Frontier.OneTapeMagnification.published_viola_chmy_square_root_time_exponent
#check Frontier.OneTapeMagnification.published_viola_chmy_parameters_do_not_certify_small_threshold
#check Frontier.OneTapeMagnification.avoidSupport_denseAboveHalf_of_image_space_lt_half
#check Frontier.OneTapeMagnification.not_hitsEveryDenseTruthTablePredicate_of_seedBits_succ_lt
#check Frontier.OneTapeMagnification.image_covers_half_of_hitsEveryDenseTruthTablePredicate
#check Frontier.OneTapeMagnification.truthTableLength_le_seedBits_succ_of_hitsEveryDense
#check Frontier.OneTapeMagnification.dagLocalGenerator_not_hitsEveryDenseTruthTablePredicate
#check Frontier.OneTapeMagnification.argmin_boundedCounters_eq_some_leftmost
#check Frontier.OneTapeMagnification.onePassCanonicalBoundaryOffset_eq_actual
#check Frontier.OneTapeMagnification.onePassAllFullBucketCounterVectorsFrom_apply
#check Frontier.OneTapeMagnification.onePassAllCanonicalCutOffsets_eq_canonical
#check Frontier.OneTapeMagnification.timedAlphaCanonicalComponentCheck_true_offsets_eq_onePassAll
#check Frontier.OneTapeMagnification.card_allFullBucketCounterVectors
#check Frontier.OneTapeMagnification.allFullBucketCounterVectors_card_le_of_leftInverse
#check Frontier.OneTapeMagnification.timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff
#check Frontier.OneTapeMagnification.acceptingTimedAlphaReachableAfterPrefix_iff_exists_residual_true
#check Frontier.OneTapeMagnification.timedAlphaInPlaceAcceptingComponentPrefixResidual_injectiveOn_reachable
#check Frontier.OneTapeMagnification.chronologicalTimedCanonicalAlpha_ne_of_terminalEndpoint_ne
#check Frontier.OneTapeMagnification.chronologicalTimedCanonicalAlpha_ne_of_finalWorkHead_ne
#check Frontier.OneTapeMagnification.routeBranch_componentPrefixResiduals_ne
#check Frontier.OneTapeMagnification.routeBranch_acceptingAggregate_erases_route_semantics
#check Frontier.OneTapeMagnification.cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff_guardedFused
#check Frontier.OneTapeMagnification.cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_baseAcceptanceIndicator
#check Frontier.OneTapeMagnification.masterGuardedFusedAcceptingComponentCertificate_alpha_eq
#check Frontier.OneTapeMagnification.hitsSingleMasterGuardedCachedCanonicalAggregate_iff_hitsDenseOneTapeAcceptance
#check Frontier.OneTapeMagnification.signedWeightedApproximation_hits_singleMasterGuardedCachedCanonicalAggregate
#check Frontier.OneTapeMagnification.signedWeightedSingleMasterGuardedCachedCanonicalAggregateApproximation_excludes_exactMCSPDecision
#check Frontier.OneTapeMagnification.streamingWorkBoundary_directional_flow
#check Frontier.OneTapeMagnification.workBoundaryCrossingCount_eq_two_mul_left_add_endpoint
#check Frontier.OneTapeMagnification.workBoundaryCrossingCount_mod_two_eq_endpoint
#check Frontier.OneTapeMagnification.two_mul_workBoundaryCrossingCount_div_two_add_endpoint
#check Frontier.OneTapeMagnification.sum_onePassAllFullBucketCutCounters_le_horizon
#check Frontier.OneTapeMagnification.actualGeometryConsistentAllFullBucketCounterState
#check Frontier.OneTapeMagnification.normalizeGeometryConsistentAllFullBucketCounterState_injective
#check Frontier.OneTapeMagnification.card_geometryConsistentAllFullBucketCounterState_le
#check Frontier.OneTapeMagnification.sum_normalizedGeometryConsistentCounters_le_half
#check Frontier.OneTapeMagnification.card_totalBudgetCounterVector_le_choose
#check Frontier.OneTapeMagnification.card_budgetedAllFullBucketCounterVectors_le_choose
#check Frontier.OneTapeMagnification.choose_fullBucketCrossingBudget_le_two_pow
#check Frontier.OneTapeMagnification.two_pow_fullBucketCrossingBudget_le_two_pow_two_mul
#check Frontier.OneTapeMagnification.card_budgetedAllFullBucketCounterVectors_le_two_pow_two_mul
#check Frontier.OneTapeMagnification.card_geometryConsistentAllFullBucketCounterVector_le_min
#check Frontier.OneTapeMagnification.card_geometryConsistentAllFullBucketCounterVector_le_two_pow_two_mul
#check Frontier.OneTapeMagnification.actualGeometryConsistentAllFullBucketCounterVector
#check Frontier.OneTapeMagnification.eval_paperBasisConstantDAG
#check Frontier.OneTapeMagnification.hardwireSeedCircuit_gateCount
#check Frontier.OneTapeMagnification.hardwireSeedCircuit_eval
#check Frontier.OneTapeMagnification.hardwireSeedCircuit_usesOnlyAndOrNot
#check Frontier.OneTapeMagnification.circuitTruthTable_hardwireSeedCircuit
#check Frontier.OneTapeMagnification.dagLocalGeneratorOfJointCircuit
#check Frontier.OneTapeMagnification.not_PpolyDAG_of_oneTape_checkpoint_and_behavior_extraction
#check Frontier.OneTapeMagnification.not_PpolyDAG_of_C_DAG_localPRG_slices
#check Frontier.OneTapeMagnification.NP_not_subset_PpolyDAG_of_C_DAG_localPRG_slices
#check Frontier.OneTapeMagnification.P_ne_NP_of_C_DAG_localPRG_slices
#check Frontier.OneTapeMagnification.legalBoundaryWord_pairedBounceBoundaryWord
#check Frontier.OneTapeMagnification.count_pairedBounceBoundaryWord_eq_pairedCrossingProfile
#check Frontier.OneTapeMagnification.pairedCanonicalCutOffsets_injective
#check Frontier.OneTapeMagnification.two_pow_le_card_of_recovers_legal_pairedBoundaryWords
#check Frontier.OneTapeMagnification.bitBudget_of_recovers_legal_pairedBoundaryWords
#check Frontier.OneTapeMagnification.bitBudget_of_card_le_two_pow_of_recovers_legal_pairedBoundaryWords
#check Frontier.OneTapeMagnification.card_fixedPairedBounceState
#check Frontier.OneTapeMagnification.streaming_fixedPairedBounceMachine_count_eq_word_count
#check Frontier.OneTapeMagnification.workBoundaryCrossingCount_fixedPairedBounceMachine
#check Frontier.OneTapeMagnification.fixedPairedBounceMachineCanonicalCutOffsets_eq
#check Frontier.OneTapeMagnification.fixedPairedBounceMachineCanonicalCutOffsets_injective
#check Frontier.OneTapeMagnification.two_pow_le_card_of_recovers_fixedPairedBounceMachineOffsets
#check Frontier.OneTapeMagnification.bitBudget_of_recovers_fixedPairedBounceMachineOffsets
#check Frontier.OneTapeMagnification.bitBudget_of_card_le_two_pow_of_recovers_fixedPairedBounceMachineOffsets
#check Frontier.OneTapeMagnification.lowerWeightedApproximation_support_hits
#check Frontier.OneTapeMagnification.reverseOneSidedWeightedApproximation_hits_singleMasterGuardedCachedCanonicalAggregate
#check Frontier.OneTapeMagnification.reverseOneSidedWeightedSingleMasterGuardedCachedCanonicalAggregateApproximation_excludes_exactMCSPDecision
#check Frontier.OneTapeMagnification.uniformPredicateAverage_gt_half_of_dense
#check Frontier.OneTapeMagnification.ReverseOneSidedFoolsDAGLocalGenerator
#check Frontier.OneTapeMagnification.DAGLocalGenerator.weaken
#check Frontier.OneTapeMagnification.dagLocalGeneratorOfJointCircuitAtThreshold
#check Frontier.OneTapeMagnification.not_PpolyDAG_of_signed_DAGLocalGenerator_slices
#check Frontier.OneTapeMagnification.verifiedNPDAGLowerBoundSource_of_signed_DAGLocalGenerator_slices
#check Frontier.OneTapeMagnification.uniformPredicateAverage_mem_unitInterval
#check Frontier.OneTapeMagnification.scaledConstantCardWeight_reverseOneSided_of_hitsAboveMass
#check Frontier.OneTapeMagnification.HitsDAGPredicatesAboveUniformMass
#check Frontier.OneTapeMagnification.exists_reverseOneSidedFoolsDAGLocalGenerator_iff_hits
#check Frontier.OneTapeMagnification.HitsEveryAboveHalfDAGPredicate
#check Frontier.OneTapeMagnification.HitsDenseDAGPredicates
#check Frontier.OneTapeMagnification.EveryDenseDAGPredicateAcceptsEasyTable
#check Frontier.OneTapeMagnification.easyTableEnumerator
#check Frontier.OneTapeMagnification.exists_hitsDenseDAGLocalGenerator_iff_everyDenseAcceptsEasy
#check Frontier.OneTapeMagnification.not_PpolyDAG_of_dense_DAGLocalGenerator_slices
#check Frontier.OneTapeMagnification.not_PpolyDAG_of_aboveHalf_DAGLocalGenerator_slices
#check Frontier.OneTapeMagnification.not_PpolyDAG_of_dense_easy_intersection_slices
#check Frontier.OneTapeMagnification.avoidFiniteSetDAG
#check Frontier.OneTapeMagnification.eval_avoidFiniteSetDAG
#check Frontier.OneTapeMagnification.size_avoidFiniteSetDAG_le
#check Frontier.OneTapeMagnification.avoidEasyTablesByCodeDAG
#check Frontier.OneTapeMagnification.avoidEasyTablesByCodeDAG_rejects_hasCircuit
#check Frontier.OneTapeMagnification.avoidEasyTablesByCodeDAG_denseAboveHalf
#check Frontier.OneTapeMagnification.not_hitsDenseDAGPredicates_of_codecAvoider_fits
#check Frontier.OneTapeMagnification.not_exists_DAGLocalGenerator_hitsDense_of_codecAvoider_fits
#check Frontier.OneTapeMagnification.not_everyDenseDAGPredicateAcceptsEasyTable_of_codecAvoider_fits
#check Frontier.OneTapeMagnification.not_exists_DAGLocalGenerator_hitsDense_polynomial_of_codecBudget
#check Frontier.OneTapeMagnification.not_everyDenseDAGPredicateAcceptsEasyTable_polynomial_of_codecBudget
#check Frontier.OneTapeMagnification.not_allExponent_hitsDense_of_codeLength_linear
#check Frontier.OneTapeMagnification.not_allExponent_everyDenseDAGPredicateAcceptsEasyTable_of_codeLength_linear
#check Frontier.OneTapeMagnification.not_allExponent_everyDenseDAGPredicateAcceptsEasyTable_of_codeLength_eventuallyLinear
#check Frontier.OneTapeMagnification.LayeredQueryProgram.guardByMasterOrder_can_create_false_positive
#check Frontier.OneTapeMagnification.LayeredQueryProgram.rejectingGuardByMasterOrder_width
#check Frontier.OneTapeMagnification.LayeredQueryProgram.rejectingGuardByMasterOrder_eval_true_implies_base
#check Frontier.OneTapeMagnification.LayeredQueryProgram.rejectingGuardByMasterOrder_eval_eq_of_follows
#check Frontier.OneTapeMagnification.LayeredQueryProgram.rejectingGuardByMasterOrder_isReadOnce
#check Frontier.OneTapeMagnification.compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_true_implies_replayAccepted
#check Frontier.OneTapeMagnification.compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_isReadOnce
#check Frontier.OneTapeMagnification.compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_true_implies_replayAccepted
#check Frontier.OneTapeMagnification.compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_isReadOnce
#check Frontier.OneTapeMagnification.compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_inPlaceCanonicalCutCheck
#check Frontier.OneTapeMagnification.RejectingMasterGuardedFusedAcceptingComponentCertificate
#check Frontier.OneTapeMagnification.rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
#check Frontier.OneTapeMagnification.rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_eq
#check Frontier.OneTapeMagnification.exists_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
#check Frontier.OneTapeMagnification.cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff_rejectingGuardedFused
#check Frontier.OneTapeMagnification.rejectingMasterGuardedFusedAcceptingComponentCertificate_pair_unique
#check Frontier.OneTapeMagnification.rejectingMasterGuardedFusedAcceptingComponentCertificates_disjoint
#check Frontier.OneTapeMagnification.existsUnique_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
#check Frontier.OneTapeMagnification.LayeredQueryProgram.completeMasterOrder_perm_finRange_of_nodup
#check Frontier.OneTapeMagnification.LayeredQueryProgram.collapseToMandatoryFixedOrder_hasFixedQueryOrder
#check Frontier.OneTapeMagnification.LayeredQueryProgram.collapseToMandatoryFixedOrder_isReadOnce
#check Frontier.OneTapeMagnification.LayeredQueryProgram.collapseToMandatoryFixedOrder_eval_eq_physicalResult
#check Frontier.OneTapeMagnification.LayeredQueryProgram.rejectingGuardByMasterOrder_eval_eq_physicalResult
#check Frontier.OneTapeMagnification.LayeredQueryProgram.collapseToMandatoryFixedOrder_eval_eq_rejectingGuard
#check Frontier.OneTapeMagnification.LayeredQueryProgram.collapseToMandatoryFixedOrder_width
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.queryEvents_append
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.queryVars_append
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.compatible_append
#check Frontier.OneTapeMagnification.BooleanPartialAssignment.mem_freeVariables_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.restrictBy_vertex_card
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.queryTrace_eq_filter_toOriginal
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.toOriginal_injective
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.restrictBy_accepts_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.restrictBy_preVars_subset_original_inter_freeVariables
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.restrictBy_postVars_subset_original_inter_freeVariables
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.restrictBy_isSyntacticallyReadOnce
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.restrictBy_isUnambiguous
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.queryVars_subset_preVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.queryVars_subset_postVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.preVars_disjoint_postVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.alphaEvents_length_eq_inter_card
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.existsUnique_isLocalAlphaCut_of_subset
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.split_of_queryEvents_eq_append_cons
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.alpha_inter_preVars_eq_inter_queryVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.alpha_subset_preVars_union_postVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.AcceptingPath.existsUnique_alphaCut
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.hasFilteredAlphaCut_iff_isAlphaCut
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.AcceptingPath.existsUnique_hasFilteredAlphaCut
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.existsUnique_hasFilteredAlphaCut_of_accepts
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.AcceptingPath.sum_filteredAlphaCutIndicator_eq_one
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.compatible_iff_of_eq_on_queryVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.hasCompatiblePrefix_iff_of_eq_on_preVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.hasCompatibleAcceptingSuffix_iff_of_eq_on_postVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.filteredAlphaCutIndicator_eq_prefix_mul_suffix_mul_static
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.indicatorDependencySets_disjoint_of_syntacticallyReadOnce
#check Frontier.OneTapeMagnification.FiniteBooleanFourier.character_flipCoordinate
#check Frontier.OneTapeMagnification.FiniteBooleanFourier.coefficient_eq_zero_of_not_subset_of_dependsOnlyOn
#check Frontier.OneTapeMagnification.FiniteBooleanFourier.subset_of_coefficient_ne_zero_of_dependsOnlyOn
#check Frontier.OneTapeMagnification.FiniteBooleanFourier.separatedProductCoefficient_eq_mul_localCoefficient
#check Frontier.OneTapeMagnification.FiniteBooleanFourier.coefficient_mul_eq_mul_localCoefficient_of_partition
#check Frontier.OneTapeMagnification.FiniteBooleanFourier.coefficient_mul_eq_mul_coefficient_of_disjoint
#check Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment.finiteAverage_abs_sq_le_average_sq
#check Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment.character_maskedInput
#check Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment.restrictedCharacterAverage_gram
#check Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment.homogeneousPolynomial_restriction_secondMoment_eq
#check Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment.homogeneousPolynomial_restriction_absMoment_sq_le
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence.IsKWisePatternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence.character_average_eq_zero_of_patternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence.hDOrthogonal_of_twoKWisePatternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence.hTMask_of_kWisePatternFalseBiased
#check Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization.dependsOnlyOn_maskedInput
#check Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization.finiteAverage_mul_maskedInput_eq_mul
#check Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization.abs_finiteAverage_mul_maskedInput_le
#check Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy.finiteAverage_character_mul_character
#check Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy.fourier_inversion
#check Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy.parseval
#check Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy.degreeEnergy_le_one
#check Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy.ratCompatiblePrefixIndicator_restriction_absMoment_sq_le_pow
#check Frontier.OneTapeMagnification.GlobalEnergyProjectionBarrier.prefix_disjoint
#check Frontier.OneTapeMagnification.GlobalEnergyProjectionBarrier.aggregate_and_component_energies_exact
#check Frontier.OneTapeMagnification.GlobalEnergyProjectionBarrier.disjoint_prefixes_and_energy_subadditivity_fails
#check Frontier.OneTapeMagnification.FiniteBooleanSuffixLaplacian.coordinateLaplacian
#check Frontier.OneTapeMagnification.FiniteBooleanSuffixLaplacian.coordinateFourierFilter
#check Frontier.OneTapeMagnification.FiniteBooleanSuffixLaplacian.coordinateLaplacian_eq_fourierFilter
#check Frontier.OneTapeMagnification.FiniteBooleanSuffixLaplacian.coordinateFourierFilter_eq_sum_powerset
#check Frontier.OneTapeMagnification.FiniteBooleanSuffixLaplacian.coordinateLaplacian_eq_fourierFilter_on_support
#check Frontier.OneTapeMagnification.FiniteBooleanSuffixLaplacian.coordinateLaplacian_dependsOnlyOn
#check Frontier.OneTapeMagnification.FiniteBooleanSuffixLaplacian.abs_coordinateLaplacian_le_half
#check Frontier.OneTapeMagnification.FiniteBooleanSuffixLaplacian.homogeneousPolynomial_coefficient_dependsOnlyOn
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratCompatiblePrefixHomogeneousSlice
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratCompatiblePrefixHomogeneousSlice_dependsOnlyOn_preVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.suffixFourierFilter
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.suffixLaplacian
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.suffixLaplacian_eq_fourierFilter_of_node_eq_query
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.suffixLaplacian_eq_fourierFilter
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.suffixLaplacian_dependsOnlyOn_postVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.abs_suffixLaplacian_le_half
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.abs_suffixLaplacian_le_one
#check Frontier.OneTapeMagnification.FiniteBooleanCutReindex.sum_cutSupports_eq_sum_product
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.queryIndex_not_mem_preVars_of_node_eq_query
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.highDegree_staticFactor_sum_eq_prefixSlice_mul_suffixFourierFilter
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratHighDegreeFourierTail
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixFourierFilter
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixFourierFilter
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
#check Frontier.OneTapeMagnification.FiniteUFBDDNode.paddedRestrictBy
#check Frontier.OneTapeMagnification.FiniteUFBDDNode.hasChild_of_paddedRestrictBy_hasChild
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_vertex_card
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_compatibleEdge_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.PaddedRestrictionWalk.toOriginal
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.PaddedRestrictionWalk.toOriginal_queryEvents
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.PaddedRestrictionWalk.toOriginal_queryTrace
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.PaddedRestrictionWalk.toOriginal_queryVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_accepts_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_accepts_iff_restrictBy_accepts
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_ratAcceptanceIndicator_eq_override
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_ratAcceptanceIndicator_eq_restrictBy
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_isSyntacticallyReadOnce
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_isUnambiguous
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_acceptingPath_queryVars_eq_univ
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.paddedRestrictBy_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_paddedRestrictBy_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
#check Frontier.OneTapeMagnification.FiniteBooleanPerVertexRestrictionBound.finiteAverage_const
#check Frontier.OneTapeMagnification.FiniteBooleanPerVertexRestrictionBound.finiteAverage_mono
#check Frontier.OneTapeMagnification.FiniteBooleanPerVertexRestrictionBound.finiteAverage_nonneg
#check Frontier.OneTapeMagnification.FiniteBooleanPerVertexRestrictionBound.abs_finiteAverage_le_finiteAverage_abs
#check Frontier.OneTapeMagnification.FiniteBooleanPerVertexRestrictionBound.abs_finiteAverage_le_of_pointwise_abs_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.abs_finiteAverage_suffixLaplacian_maskedInput_le_half
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.abs_finiteAverage_suffixLaplacian_maskedInput_le_one
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.abs_finiteAverage_prefixSlice_mul_suffixLaplacian_maskedInput_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.prefixSlice_mul_suffixLaplacian_restriction_absMoment_sq_le_pow
#check Frontier.OneTapeMagnification.FiniteBooleanVertexSumRestrictionBound.le_of_sq_le_sq_of_nonneg
#check Frontier.OneTapeMagnification.FiniteBooleanVertexSumRestrictionBound.finiteAverage_abs_finset_sum_le_sum_finiteAverage_abs
#check Frontier.OneTapeMagnification.FiniteBooleanVertexSumRestrictionBound.finiteAverage_abs_fintype_sum_le_sum_finiteAverage_abs
#check Frontier.OneTapeMagnification.FiniteBooleanVertexSumRestrictionBound.finiteAverage_abs_fintype_sum_le_card_mul_of_bound
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.vertexRestrictionContribution
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.vertexRestrictionContribution_evenDegree_absMoment_le_pow
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.vertexRestrictionContribution_sum_evenDegree_absMoment_le_card_mul_pow
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.prefixDegreeEnergySum
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.four_mul_vertexRestrictionContribution_sq_le_prefixAverage_sq
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.four_mul_vertexRestrictionContribution_sum_secondMoment_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.four_mul_vertexRestrictionContribution_sum_absMoment_sq_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.four_mul_ratHighDegreeFourierTail_maskedAverage_secondMoment_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.four_mul_ratHighDegreeFourierTail_maskedAverage_absMoment_sq_le
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_four_mul_ratHighDegreeFourierTail_maskedAverage_secondMoment_le
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_four_mul_ratHighDegreeFourierTail_maskedAverage_absMoment_sq_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratHighDegreeFourierTail_maskedAverage_eq_sum_vertexRestrictionContribution
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratHighDegreeFourierTail_maskedAverage_evenDegree_absMoment_le_card_mul_pow
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_ratHighDegreeFourierTail_maskedAverage_eq_sum_vertexRestrictionContribution
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_ratHighDegreeFourierTail_maskedAverage_evenDegree_absMoment_le_card_mul_pow
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.ratLowDegreeNonemptyFourierPart
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.fourier_inversion_eq_constant_add_lowDegreeNonempty_add_highDegree
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.coefficient_empty_eq_finiteAverage
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.finiteAverage_add
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.finiteAverage_sub
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.finiteAverage_fintype_sum
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.finiteAverage_character_maskedInput_eq_character_mul_indicator
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.finiteAverage_restrictedCharacter_eq_zero_of_patternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.ratLowDegreeNonemptyFourierPart_oneRoundAverage_eq_zero
#check Frontier.OneTapeMagnification.FiniteBooleanOneRoundFoolingBound.oneRoundAverage_eq_uniformAverage_add_highDegreeAverage
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratAcceptanceIndicator_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_ratAcceptanceIndicator_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.restrictedCharacterAverage_gram_of_fullPatternLaws
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.ratHighDegreeFourierTail_restriction_secondMoment_eq
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.ratHighDegreeFourierTail_restriction_secondMoment_le_pow
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.ratHighDegreeFourierTail_restriction_absMoment_sq_le_pow
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.ratHighDegreeFourierTail_eq_zero_of_inputBits_le_cutoff
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.oneRoundAverage_eq_uniformAverage_of_fullPatternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.surjective_of_fullPatternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.two_pow_le_card_seed_of_fullPatternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.inputBits_le_seedBits_of_fullPatternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.localPatternProductMass_pos_of_between
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.surjective_of_fullPatternFalseBiased
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.two_pow_le_card_seed_of_fullPatternFalseBiased
#check Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction.two_pow_two_mul_le_card_prod_seed_of_fullPatternLaws
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.restrictedCharacterAverage_pairMoment_eq
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.farPair_maskAllZeroIndicator_average_le_pow
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.abs_restrictedCharacterAverage_pairMoment_le_pow_of_far
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.abs_highTailFarPairCorrelation_le_pow_mul_l1_sq
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.highTail_restriction_secondMoment_eq_diagonal_add_far
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.highTail_diagonalEnergy_le_pow_succ
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.highTail_restriction_secondMoment_le_pow_succ_add_abs_far
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.highTail_restriction_secondMoment_le_pow_succ_add_pow_mul_l1_sq
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.structured_highTail_restriction_secondMoment_le_pow_succ_add_abs_far
#check Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail.structured_highTail_restriction_secondMoment_le_pow_succ_add_pow_mul_l1_sq
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.ratComponentAcceptanceIndicator
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selector_ratAcceptanceIndicator_eq_sum_components
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.ratHighDegreeFourierTail_fintype_sum
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.componentHighTailAverage
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selector_highTailAverage_eq_sum_components
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.finiteAverage_sq_fintype_sum_eq_sum_pair
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selector_highTailAverage_secondMoment_eq_sum_componentPairs
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.sigmaComponentModelEquivAcceptedModel
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.card_acceptedModel_eq_sum_componentModels
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selector_ratAcceptanceIndicator_eq_sum_acceptedPoints
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selector_highTailAverage_secondMoment_eq_sum_acceptedPointPairs
#check Frontier.OneTapeMagnification.FiniteFirstDivergenceCharge.sum_pair_eq_sum_diagonal_add_sum_fibers
#check Frontier.OneTapeMagnification.FiniteFirstDivergenceCharge.sum_pair_le_diagonalBudget_add_weightedFiberCharge
#check Frontier.OneTapeMagnification.FiniteFirstDivergenceCharge.sum_pair_le_of_firstDivergenceCharge
#check Frontier.OneTapeMagnification.FiniteFirstDivergenceCharge.selector_highTailAverage_secondMoment_le_of_residualPairCharge
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.coefficient_ratAcceptedPointIndicator_eq_character_div
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.sum_sq_coefficient_ratAcceptedPointIndicator_eq_inv_pow
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.acceptedPoint_highTail_diagonalEnergy_le_invPow_mul_pow_succ
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.sum_acceptedPoint_highTail_diagonalEnergy_le_pow_succ
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation.DualFarBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation.structuredSecondMoment_le_pow_of_dualFarBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation.oneRoundError_le_pow_of_dualFarBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation.GeneratedPrefixDualFarBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation.GeneratedPrefixDualFarBoundUpTo
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation.abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBoundUpTo
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation.abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorWeightedCharge.SelectorWeightedRowChargeBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorWeightedCharge.dualFarBound_of_selectorWeightedRowChargeBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorWeightedCharge.GeneratedPrefixSelectorWeightedRowChargeBoundUpTo
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorWeightedCharge.generatedPrefixDualFarBoundUpTo_of_selectorWeightedRowChargeBoundUpTo
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorWeightedCharge.abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixSelectorWeightedRowChargeBoundUpTo
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorFullFieldCorrelation.dualFarBound_fullCoordinates
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorFullFieldCorrelation.generatedPrefixDualFarBoundUpTo_fullCoordinates
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorFullFieldCorrelation.abs_value_sub_value_zero_le_rounds_mul_pow_fullCoordinates
#check Frontier.OneTapeMagnification.FiniteUFBDDNode.affinePaddedRestrictBy
#check Frontier.OneTapeMagnification.FiniteUFBDDNode.hasChild_of_affinePaddedRestrictBy_hasChild
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictBy
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictBy_vertex_card
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictBy_compatibleEdge_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.AffinePaddedRestrictionWalk.toOriginal
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.AffinePaddedRestrictionWalk.toOriginal_queryEvents
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.AffinePaddedRestrictionWalk.toOriginal_queryTrace
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.AffinePaddedRestrictionWalk.toOriginal_queryVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictBy_accepts_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictBy_ratAcceptanceIndicator_eq_maskedInput
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictBy_isSyntacticallyReadOnce
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictBy_isUnambiguous
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictBy_acceptingPath_queryVars_eq_univ
#check Frontier.OneTapeMagnification.AffineRestrictionRound
#check Frontier.OneTapeMagnification.applyAffineRestrictionRounds
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictByRounds
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_vertex_card
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_isSyntacticallyReadOnce
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_isUnambiguous
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_acceptingPath_queryVars_eq_univ
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
#check Frontier.OneTapeMagnification.FiniteRoundTelescoping.abs_value_sub_initial_le_rounds_mul
#check Frontier.OneTapeMagnification.FiniteRoundTelescoping.abs_initial_sub_terminal_le_rounds_mul_add
#check Frontier.OneTapeMagnification.FiniteRoundTelescoping.abs_initial_sub_zeroTail_le_dptw_shape
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.Seeds
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.roundOfSeed
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.roundsOfSeeds
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.applyAffineRestrictionRounds_append
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.affinePaddedRestrictByRounds_append_ratAcceptanceIndicator_eq
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.affinePaddedRestrictByRounds_append_one_ratAcceptanceIndicator_eq
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.value
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.value_eq_nested_maskedInput_average
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.value_zero
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.value_succ_eq_prefixAverage_oneRound
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.abs_value_succ_sub_value_le_card_mul_pow
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.abs_value_sub_value_zero_le_rounds_mul_card_mul_pow
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.abs_uniformAverage_sub_terminal_le_rounds_mul_card_mul_pow_add
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.abs_uniformAverage_sub_zeroTail_le_dptw_shape
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.abs_value_sub_dptwZeroTailAverage_le_marginal_pow_of_packed_eq
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.abs_uniformAverage_sub_dptwZeroTailAverage_le_of_packed_eq
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.seedsHeadTailEquiv
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.seedToSeedsOneEquiv
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.roundsOfSeeds_eq_head_cons_tail
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.dptwPackedSeedsEquiv
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.dptwPackedSeedsEquiv_zero_apply
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.seedsHeadTailEquiv_dptwPackedSeedsEquiv_succ
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.dptwASeedBSeedTailEquiv_a
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.dptwASeedBSeedTailEquiv_b
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.dptwASeedBSeedTailEquiv_tail
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.applyAffineRestrictionRounds_dptwPackedSeedsEquiv_eq
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.finiteAverage_comp_equiv
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.value_dptw_generateWithTail_rational_average
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.value_dptw_generateWithTail_eq_uniformPredicateAverage
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.abs_value_dptw_sub_zeroTailAverage_le_marginal_pow
#check Frontier.OneTapeMagnification.FiniteAffineRestrictionHybrid.abs_uniformAverage_sub_dptwZeroTailAverage_le
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.finiteBitTapeBlockEquiv
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.finiteAverage_comp_equiv
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.dyadicProductSource_isKWisePatternFalseBiased
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.dyadicHalfProductSource_isKWisePatternUnbiased
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.eval_paperTruthTableCircuit
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.paperTruthTableCircuit_usesOnlyAndOrNot
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.coordinatePrimitiveOfGenerate_jointCircuit_gateCount
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.dyadicProductPrimitive_generate
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.dyadicHalfProductPrimitive_patternUnbiased
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.dyadicProductPrimitive_patternFalseBiased
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.dyadicProductPrimitive_uniformCoordinateMarginal
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.dyadicDPTWPair_exactLaws
#check Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives.abs_uniformAverage_sub_dyadicZeroTailAverage_le
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.finiteAverage_comp_surjectiveAddHom
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.supportEvaluationLinearMap_surjective
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.finiteAverage_supportEvaluation
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.polynomialSubsetSource_isKWisePatternFalseBiased
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.binaryPolynomialSeed_card
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.binaryPolynomialBitSource_isKWisePatternFalseBiased
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.binaryHalfPolynomialBitSource_isKWisePatternUnbiased
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.binaryTruthTablePolynomialBitSource_patternFalseBiased
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.binaryTruthTableHalfPolynomialBitSource_patternUnbiased
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.binaryTruthTableDPTWPair_exactLaws
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.binaryDyadicTailFalseMass
#check Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed.binaryTruthTableDPTWDyadicTailPair_exactLaws
#check Frontier.OneTapeMagnification.GaloisBilinearTensorBridge.zmodTwoEquivBool_add
#check Frontier.OneTapeMagnification.GaloisBilinearTensorBridge.zmodTwoEquivBool_mul
#check Frontier.OneTapeMagnification.GaloisBilinearTensorBridge.gfTwoBoolCoordinates_bijective
#check Frontier.OneTapeMagnification.GaloisBilinearTensorBridge.gfTwoBoolCoordinates_symm_eq_sum
#check Frontier.OneTapeMagnification.GaloisBilinearTensorBridge.gfTwoCoordinates_mul
#check Frontier.OneTapeMagnification.GaloisBilinearTensorBridge.gfTwoBoolCoordinates_mul
#check Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe.evalOutput_bilinearAffineHeadBundle_eq_vectorValue
#check Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe.evalOutput_polynomialHornerBundle
#check Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe.polynomialHornerBundle_gates_le
#check Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe.polynomialHornerBundle_noConst
#check Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe.eval_polynomialZeroPrefixDAG_eq_false_iff
#check Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe.polynomialZeroPrefixCircuit_usesOnlyAndOrNot
#check Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe.polynomialZeroPrefixPrimitive_jointCircuit_gateCount_le
#check Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe.polynomialZeroPrefixPrimitive_generate_eq_false_iff
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.structuredPolynomialBitSeedEquiv_coefficient
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.structuredTruthTableNode_injective
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.structuredPolynomialSubsetSource_isKWisePatternFalseBiased
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.zeroPrefixFalseSet_card
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.zeroPrefixFalseSet_exactMass
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.bilinearVectorValue_gfTwo_mul
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.fieldDescendingHorner_eq_sum
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.polynomialHornerValue_eq_gfTwo_polynomialEval
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.structuredDyadicPrimitive_generate
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.structuredDyadicPrimitive_patternFalseBiased
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.structuredDyadicPrimitive_jointCircuit_gateCount_le
#check Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive.structuredDPTWPair_exactLaws
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structuredSupportAddChar
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.isStructuredDualSupport_iff
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.finiteAverage_structuredSupportAddChar
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structuredUnbiasedPrimitive_generate_eq_evaluationBit
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structuredUnbiasedPrimitive_characterAverage_eq_dualIndicator
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structuredUnbiasedPrimitive_characterPairAverage_eq_dualIndicator
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structured_highTailFarPairCorrelation_eq_dual
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structured_highTail_restriction_secondMoment_eq_diagonal_add_dual
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.not_isStructuredDualSupport_of_nonempty_card_le
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structuredSupportPowerSum
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.structuredSupportEvaluationSum_eq_coefficients_powerSums
#check Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode.isStructuredDualSupport_iff_powerSums_eq_zero
#check Frontier.OneTapeMagnification.DPTWStructuredMaskRank.structuredDyadicPrimitive_maskSurvival_eq_invPowRank
#check Frontier.OneTapeMagnification.DPTWStructuredMaskRank.supportPrefixConstraintRank_lowerBound
#check Frontier.OneTapeMagnification.DPTWStructuredMaskRank.structuredDyadicPrimitive_pairUnionMaskSurvival_le_invPow
#check Frontier.OneTapeMagnification.DPTWStructuredMaskRank.structuredDyadicPrimitive_fullMaskSurvival_exact
#check Frontier.OneTapeMagnification.DPTWStructuredMaskRank.structuredDyadicPrimitive_pairUnionFullMaskSurvival_exact
#check Frontier.OneTapeMagnification.DPTWStructuredRankWeightedDualCorrelation.structuredRankWeightedDualFarPairCorrelation
#check Frontier.OneTapeMagnification.DPTWStructuredRankWeightedDualCorrelation.structuredDualFarPairCorrelation_eq_rankWeighted
#check Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge.signedQuadraticSum_le_budget_mul_energy
#check Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge.structuredPositivePairKernel
#check Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge.structuredRankWeightedDualFarPairCorrelation_le_positivePairSum
#check Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge.structuredDualFarPairCorrelation_le_positiveRowBudget
#check Frontier.OneTapeMagnification.FiniteWeightedChargeSpectral.signedQuadraticSum_le_variableBudgetEnergy
#check Frontier.OneTapeMagnification.FiniteWeightedChargeSpectral.signedQuadraticSum_positivePair_eq_localBudgetEnergy
#check Frontier.OneTapeMagnification.FiniteWeightedChargeSpectral.structuredDualFarPairCorrelation_le_of_localBudgetEnergy
#check Frontier.OneTapeMagnification.FiniteWeightedChargeSpectral.symmetricRowSqMass_le_budget_sq
#check Frontier.OneTapeMagnification.FiniteWeightedChargeCliqueObstruction.card_sub_one_mul_edgeFloor_le_budget_of_subset
#check Frontier.OneTapeMagnification.DPTWStructuredPointMassCliqueObstruction.no_positiveRowChargeWeights_zeroPointIndicator
#check Frontier.OneTapeMagnification.DPTWStructuredPointMassCliqueObstruction.structuredDualFarPairCorrelation_zeroPointIndicator_le_half
#check Frontier.OneTapeMagnification.DPTWStructuredPointMassCliqueObstruction.not_selectorWeightedRowChargeBound_of_zeroPointIndicator
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.maskedAverage_ratAcceptanceIndicator_eq_residualAcceptedMass
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selector_highTailAverage_eq_residualAcceptedMass_sub_lowDegreePredictor
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.residualAcceptedMass_deviation_secondMoment_eq_highTailSecondMoment
#check Frontier.OneTapeMagnification.FiniteResidualAcceptedModelCount.finiteAverage_pointIndicator_masked
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.residualAcceptedMass_sq_eq_pairCount_div_pow_two_mul_liveSupport
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.normalizedResidualAcceptedModelCount_sub_sq_eq_pairCount_sub_cross
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.residualRectangleEquiv
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.card_fiber_mul_card_residualSuffix_le_acceptedModel
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.frozenResidualRectangleEquiv
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.card_frozenFixedPostPrefix_mul_card_frozenResidualSuffix_le_residualAcceptedModelCount
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.card_frozenFiber_mul_card_frozenResidualSuffix_le_residualAcceptedModelCount
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.fixedSuffixResidualRectangleEquiv
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.frozenFixedSuffixResidualRectangleEquiv
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.card_frozenFixedSuffixFiber_mul_residual_le_residualAcceptedModelCount
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualMass.ResidualMassL2Bound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualMass.oneRoundError_le_pow_of_residualMassL2Bound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualMass.abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixResidualMassL2BoundUpTo
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount.ResidualModelCountL2Bound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount.residualModelCountL2Bound_iff_residualMassL2Bound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount.residualCount_deviation_sq_eq_pairCount_sub_cross
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount.residualModelCountL2Bound_iff_pairCountCrossBudget
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount.abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixResidualModelCountL2BoundUpTo
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_eq_sum_pointDeviations
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_sq_eq_sum_signedPairKernels
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.residualDeviation_secondMoment_eq_sum_signedPairKernelAverages
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount.residualModelCountL2Bound_iff_signedPairKernelBudget
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.queryVars_eq_postVars_of_append_queryVars_eq_univ
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.eq_on_postVars_of_inputLabelledQueryTrace_eq
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_walk_queryVars_eq_univ
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_walk_queryVars_eq_univ
#check Frontier.OneTapeMagnification.prefixedMandatoryCanonicalSelector_suffix_queryVars_eq_postVars
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.inputLabelledFullTrace_filterMap_queryEvent?
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.canonicalAcceptingWalk_eq_of_compatible
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.card_frozenFullLabelledCompleteSuffixFiber_mul_residual_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.card_frozenCanonicalLabelledSuffixBucket_mul_residual_le
#check Frontier.OneTapeMagnification.prefixedMandatoryCanonicalSelector_card_frozenCanonicalLabelledSuffixBucket_mul_residual_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix_isSuffix_left
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.Walk.exists_split_of_isSuffix_inputLabelledFullTrace
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.canonicalPairReverseLCPKey_maximal
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.compatiblePairReverseLCPBucket_disjoint_of_ne
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.sum_card_compatiblePairReverseLCPBuckets_eq_pairCount
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.sum_card_referenceFibers_eq_pairReverseLCPBucket_card
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.reverseLCPFiberWalkLift_of_nonempty
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.exists_card_frozenReferenceReverseLCPFiber_mul_residual_le
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.exists_reference_and_maximalReverseLCPFiber_capacity_of_key_mem
#check Frontier.OneTapeMagnification.prefixedMandatoryCanonicalSelector_exists_maximalReverseLCPFiber_capacity
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.lowHighRestrictionCrossCorrelation_eq_characterMaskSum
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.structured_lowHighRestrictionCrossCorrelation_eq_dualAliases
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.structured_lowHighRestrictionCrossCorrelation_halfOneAddCharacter_eq
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.structured_lowHighRestrictionCrossCorrelation_support01_eq_one_div_sixteen
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.lowHighRestrictionCrossCorrelation_eq_zero_of_fullPatternUnbiased
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.structured_lowHighRestrictionCrossCorrelation_eq_zero_of_noDualAlias
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.maskedAverage_mul_predictor_eq_predictorSq_add_cross
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.deviation_secondMoment_eq_averageSq_sub_predictorSq_sub_twoCross
#check Frontier.OneTapeMagnification.FiniteBooleanResidualMass.deviation_secondMoment_le_maskedAverage_secondMoment_of_cross_eq_zero
#check Frontier.OneTapeMagnification.FiniteResidualQuotientCharge.signedQuadraticSum_le_pow_mul_pow_three_div_four
#check Frontier.OneTapeMagnification.FiniteResidualQuotientCharge.signedQuadraticSum_le_inversePow_square_of_dimension_le
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPTelescope.exactLCSPairCharge_eq_suffixConeMass_sq_sub_children
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPTelescope.sum_exactLCSPairCharge_realizedLCSKeys_eq_totalWeight_sq
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPTelescope.sum_suffixSquareDrops_realizedLCSKeys_eq_totalWeight_sq
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.canonicalExactLCPSignedPairCharge_eq_sum_signedPairKernels_on_key
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.canonicalExactLCPSignedPairCharge_eq_suffixSquareDrop
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_sq_eq_sum_canonicalExactLCPCharges
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.residualDeviation_secondMoment_eq_sum_canonicalExactLCPChargeAverages
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount.residualModelCountL2Bound_iff_canonicalExactLCPChargeBudget
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.isCanonicalResidualSuffixConeInput_iff_prefix_and_fixedSuffix
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.canonicalResidualSuffixConeIndicator_eq_prefix_mul_suffixCylinder
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.coefficient_ratFixedLabelledSuffixCylinderIndicator_eq_character_div
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.abs_coefficient_ratFixedLabelledSuffixCylinderIndicator_eq_inv_pow
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_character_div_of_complete
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.abs_coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_div_pow_of_complete
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.canonicalResidualDeviationSuffixConeMass_eq_highTailAverage
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.canonicalResidualDeviationSuffixConeMass_secondMoment_eq_structuredEnergy
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.canonicalExactLCPSignedPairCharge_average_eq_structuredEnergyDrop
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorFourierKernel.prefixedMandatoryCanonicalSelector_coneCoefficient_eq_prefix_mul_character_div
#check Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer.coefficient_mul_eq_symmDiff_convolution
#check Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer.disjoint_symmDiff_convolution_eq_zero
#check Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer.weightedSignAlias_decomposition
#check Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer.WeightedVariationUpperObligation
#check Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer.weightedHighHighAliasSum_le_budget_of_variationUpperObligation
#check Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer.sum_complementFiberConvolution_eq_zero_of_disjoint
#check Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer.highHigh_emptyComplementFiber_eq_middleSplit
#check Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation.dyadicVariation_eq_neg_sum_rankTails
#check Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation.dyadicVariation_le_weightedTailBudgets
#check Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation.dyadicVariation_le_uniformTailBudget
#check Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation.supportPrefixConstraintRank_mono
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank.canonicalDistinctSiblingConeIndicators_mul_eq_zero
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank.canonicalDistinctSiblingCone_symmDiffConvolution_eq_zero
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank.canonicalDistinctSiblingCone_weightedHighHighTransfer
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank.structuredHighTailCrossMoment_eq_dualRankCrossForm
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank.structuredDualRankCrossForm_eq_diagonal_add_distinct
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank.canonicalSiblingConeCrossMoment_le_iff_dualRankCoefficientBudget
#check Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank.abs_realizedConeDistinctDualRankEntry_le
#check Frontier.OneTapeMagnification.FiniteVectorClaim18.homogeneousPolynomial_restriction_globalReverseLCPEnergy_eq
#check Frontier.OneTapeMagnification.FiniteVectorClaim18.canonicalAcceptedModelReverseLCP_firstHighLayer_le_pow
#check Frontier.OneTapeMagnification.FiniteVectorClaim18.not_structuredDegreeThree_gramOrthogonal
#check Frontier.OneTapeMagnification.DPTWStructuredIndependencePlusOneNoGo.structuredUnbiasedSourcePlusOne_degree_two_mul_add_one_gram_diagonal
#check Frontier.OneTapeMagnification.DPTWStructuredIndependencePlusOneNoGo.not_structuredUnbiasedSourcePlusOne_strictAboveBottom_gramOrthogonal
#check Frontier.OneTapeMagnification.DPTWStructuredIndependencePlusOneNoGo.plusOneBooleanConeIndicator_offDiagonalRestrictedContribution_pos
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorEnergyCharge.SelectorPositiveEdgeEnergyBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorEnergyCharge.dualFarBound_of_selectorPositiveEdgeEnergyBound
#check Frontier.OneTapeMagnification.MandatoryCanonicalSelectorEnergyCharge.abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixSelectorPositiveEdgeEnergyBoundUpTo
#check Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation.structuredDualFarPairCorrelation_full_eq_pow_mul_allFalse
#check Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation.abs_structuredDualFarPairCorrelation_full_le_four_mul_pow
#check Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation.structuredDualFarPairCorrelation_full_le_dualFarBudget
#check Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation.structured_fullField_highTail_restriction_secondMoment_le_pow
#check Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation.structured_fullField_highTail_restriction_absMoment_le_pow
#check Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation.structured_fullField_oneRoundError_le_pow
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredPrimitiveHornerGateBudget
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailJointGateBudget
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailHardwiredGateBudget
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailJointCircuit_gateCount
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailJointCircuit_gateCount_le
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailHardwired_gateCount
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailHardwired_gateCount_le
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailRawThreshold_le
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailDAGLocalGenerator
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailDAGLocalGenerator_seedBits_eq
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.structuredZeroTailDAGLocalGenerator_generate
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.abs_uniformAverage_sub_structuredZeroTailGeneratorAverage_le
#check Frontier.OneTapeMagnification.DPTWStructuredHybridCapstone.abs_uniformAverage_sub_structuredZeroTailGeneratorSeedAverage_le
#check Frontier.OneTapeMagnification.FiniteUFBDDNode.forgetRightQueries
#check Frontier.OneTapeMagnification.FiniteUFBDDNode.forgetRightQueries_hasChild_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_start
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_accept
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_rank
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.RightFunctional
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.leftIndex?
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.compatible_congr_of_eq_on_queryTrace
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.exists_compatible_of_queryTrace_nodup
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.toOriginal
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.toProjected
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.toProjected_toOriginal
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.toOriginal_injective
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.queryTrace_eq_filterMap_leftIndex?
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.queryTrace_nodup_of_toOriginal_queryTrace_nodup
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.toProjected_compatible
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.toOriginal_compatible_join_rightSlice
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.FunctionalProjectionWalk.exists_rightInput_compatible_toOriginal
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_vertex_card
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_accepts_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_isSyntacticallyReadOnce
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_isUnambiguous_of_rightFunctional
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.index_card_le_two_pow_witnessBitWidth
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.decodeWitnessCode_eq_some_iff
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.encodedAcceptingRelation_rightFunctional
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.existsUnique_encodedAcceptingRelation_iff_existsUnique_index
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.encodedAcceptingRelation_witnessCode_iff
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.acceptingIndices
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.witnessFirstFactorization_acceptingIndices_injective
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.card_acceptingIndices_le_of_witnessFirstFactorization
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.card_acceptingIndices_le_two_pow_of_witnessFirstFactorization
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.witnessBits_le_summaryBits_of_witnessFirstFactorization
#check Frontier.OneTapeMagnification.canonicalAlphaWitnessBitWidth_le_ambient
#check Frontier.OneTapeMagnification.decodeFiniteRejectingGuardedCanonicalAlpha?_encode
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFunctionalRelation_rightFunctional
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFunctionalRelation_decodes_actualAlpha
#check Frontier.OneTapeMagnification.existsUnique_finiteRejectingGuardedCanonicalFunctionalRelation_iff
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.RealizesFiniteRejectingGuardedCanonicalFunctionalRelation
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.rightFunctional_of_realizesFiniteRejectingGuardedCanonicalRelation
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_accepts_iff_canonicalFamilyEval_of_realizesRelation
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_accepts_iff_cachedAcceptance_of_realizesCanonicalRelation
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_isUnambiguous_of_realizesCanonicalRelation
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.forgetRightQueries_vertex_card_canonicalWitnessWidth
#check Frontier.OneTapeMagnification.stableRoutingGrid_le_twoOrderRoutingGraph
#check Frontier.OneTapeMagnification.stableTwoOrderRoutingGraph_hasPairedContractionModel
#check Frontier.OneTapeMagnification.stableRoutingGrid_hasPairedContractionModel
#check Frontier.OneTapeMagnification.run_serpentineSweepMachine
#check Frontier.OneTapeMagnification.canonicalBoundaryOffset_one
#check Frontier.OneTapeMagnification.serpentineEventTime_bijective
#check Frontier.OneTapeMagnification.actualSerpentineInputEvent_workBlock_val
#check Frontier.OneTapeMagnification.actualSerpentineInputEvent_advances
#check Frontier.OneTapeMagnification.actualSerpentineTwoOrderRoutingGraph_eq
#check Frontier.OneTapeMagnification.stableRoutingGrid_le_actualSerpentineTwoOrderRoutingGraph
#check Frontier.OneTapeMagnification.actualSerpentine_horizon_eq
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.cachedSerpentineSweepMachine_run_not_accepting
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.card_builtRejectingGuardedCanonicalAlphaIndex_serpentine_eq_zero
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.finiteRejectingGuardedCanonicalFunctionalRelation_serpentine_false
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.twoSinkRejectUFBDD_isSyntacticallyReadOnce
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.twoSinkRejectUFBDD_isUnambiguous
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.twoSinkRejectUFBDD_realizes_serpentineCanonicalRelation
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.mandatoryCanonicalUFBDD_serpentine_not_accepts
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.mandatoryCanonicalUFBDD_serpentine_vertex_card
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.no_injective_serpentineGrid_to_mandatoryCanonicalUFBDD
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.actualSerpentineGrid_with_twoVertexExactFunctionalRealizer
#check Frontier.OneTapeMagnification.SerpentineCanonicalCounterarchitecture.actualSerpentineGrid_with_tinyMandatoryCanonicalValidator
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.ratAcceptanceIndicator_eq_sum_ratFilteredAlphaCutIndicator
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.coefficient_ratFilteredAlphaCutIndicator_eq_static_mul_prefix_mul_suffix
#check Frontier.OneTapeMagnification.FiniteUnambiguousFBDD.coefficient_ratAcceptanceIndicator_eq_sum_static_mul_prefix_mul_suffix
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_ratAcceptanceIndicator_eq_sum_filteredCut
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_coefficient_ratAcceptanceIndicator_eq_sum_filteredCut
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_coefficient_ratAcceptanceIndicator_eq_sum_factored
#check Frontier.OneTapeMagnification.builtTimedAlphaVisitSchedule_eq_of_valid
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.layeredStateSlotCount_le_card_mul
#check Frontier.OneTapeMagnification.card_builtRejectingGuardedCanonicalAlphaIndex_le_ambient
#check Frontier.OneTapeMagnification.card_builtRejectingGuardedCanonicalAlphaIndex_le_formula
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFamily_component_width
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFamily_layeredStateSlotCount_eq_sum
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFamily_isReadOnce
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFamily_program_eval_eq_true_iff_certificate
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFamily_eval_eq_true_iff
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFamily_accepting_index_unique
#check Frontier.OneTapeMagnification.finiteRejectingGuardedCanonicalFamily_isUnambiguous
#check Frontier.OneTapeMagnification.existsUnique_finiteRejectingGuardedCanonicalFamily_index_iff
#check Frontier.OneTapeMagnification.builtRejectingGuardedCanonicalIndex_master_nodup
#check Frontier.OneTapeMagnification.mandatoryBuiltRejectingGuardedCanonicalComponent
#check Frontier.OneTapeMagnification.mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family
#check Frontier.OneTapeMagnification.mandatoryBuiltRejectingGuardedCanonicalComponent_isReadOnce
#check Frontier.OneTapeMagnification.mandatoryBuiltRejectingGuardedCanonicalComponent_width
#check Frontier.OneTapeMagnification.mandatoryFiniteRejectingGuardedCanonicalFamily
#check Frontier.OneTapeMagnification.mandatoryFiniteRejectingGuardedCanonicalFamily_isReadOnce
#check Frontier.OneTapeMagnification.mandatoryFiniteRejectingGuardedCanonicalFamily_isUnambiguous
#check Frontier.OneTapeMagnification.mandatoryFiniteRejectingGuardedCanonicalFamily_eval_eq_true_iff
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorNode_rank_child
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorFBDD_vertex_card
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorComponentExecutionWalk_compatible
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorComponentExecution_result_eq
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorFBDD_accepts_of_component_eval_true
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorFBDD_accepts_of_eval_eq_true
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorComponentWalk_to_accept_implies_eval_true
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorFBDD_eval_eq_true_of_accepts
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorFBDD_accepts_iff_eval_eq_true
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorFBDD_isUnambiguous_of_family
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.productiveSubfamily_eval
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.productiveSubfamily_isUnambiguous
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.productiveAcceptingInput_injective
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.card_productiveIndex_le_two_pow
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.productiveSubfamily_selectorFBDD_accepts_iff
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.productiveSubfamily_selectorFBDD_vertex_card
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorFBDD_isSyntacticallyReadOnce_of_fixedMandatoryOrder
#check Frontier.OneTapeMagnification.mandatoryBuiltRejectingGuardedCanonicalComponent_hasFixedQueryOrder
#check Frontier.OneTapeMagnification.mandatoryBuiltRejectingGuardedCanonicalQueryOrder_nodup
#check Frontier.OneTapeMagnification.mandatoryFiniteRejectingGuardedCanonicalSelector_isSyntacticallyReadOnce
#check Frontier.OneTapeMagnification.mandatoryFiniteRejectingGuardedCanonicalSelector_vertex_card
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_isUnambiguous
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_vertex_card
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorComponentStartWalk_to_accept_queryTrace_eq_of_fixedMandatoryOrder
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorRootWalk_to_accept_exists_queryTrace_eq_of_fixedMandatoryOrder
#check Frontier.OneTapeMagnification.FiniteLayeredQueryProgramFamily.selectorAcceptingPath_queryVars_eq_univ_of_fixedMandatoryOrder
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
#check Frontier.OneTapeMagnification.mandatoryCanonicalUFBDD_alpha_subset_acceptingPath_queryVars
#check Frontier.OneTapeMagnification.DPTWCoordinatePrimitive
#check Frontier.OneTapeMagnification.dptwZeroTailLevelHead
#check Frontier.OneTapeMagnification.eval_dptwZeroTailLevelHead
#check Frontier.OneTapeMagnification.dptwZeroTailGenerate
#check Frontier.OneTapeMagnification.dptwZeroTailGenerate_final
#check Frontier.OneTapeMagnification.dptwZeroTailGenerate_step
#check Frontier.OneTapeMagnification.dptwZeroTailJointCircuit
#check Frontier.OneTapeMagnification.dptwZeroTailJointCircuit_eval
#check Frontier.OneTapeMagnification.dptwZeroTailJointCircuit_gateCount
#check Frontier.OneTapeMagnification.dptwZeroTailJointCircuit_usesOnlyAndOrNot
#check Frontier.OneTapeMagnification.dptwZeroTailHardwired_gateCount
#check Frontier.OneTapeMagnification.dptwZeroTailDAGLocalGenerator
#check Frontier.OneTapeMagnification.dptwZeroTailDAGLocalGenerator_threshold_eq
#check Frontier.OneTapeMagnification.dptwZeroTailDAGLocalGenerator_seedBits
#check Frontier.OneTapeMagnification.dptwZeroTailDAGLocalGenerator_generate
#check Frontier.OneTapeMagnification.dptwGenerateWithTail
#check Frontier.OneTapeMagnification.dptwSurvivesAllBLevels
#check Frontier.OneTapeMagnification.dptwGenerateWithTail_eq_xor_zeroTail_survivor
#check Frontier.OneTapeMagnification.dptwGenerateWithTail_zero_eq_zeroTail
#check Frontier.OneTapeMagnification.dptwGenerateWithTail_eq_zeroTail_of_all_killed
#check Frontier.OneTapeMagnification.dptwGenerateWithTail_ne_zeroTail_iff
#check Frontier.OneTapeMagnification.dptwGenerateWithTail_ne_zeroTail_iff_exists
#check Frontier.OneTapeMagnification.abs_uniformPredicateAverage_sub_le_disagreement
#check Frontier.OneTapeMagnification.uniformPredicateAverage_exists_le_sum
#check Frontier.OneTapeMagnification.dptwZeroTail_test_average_sub_le_sum_survival
#check Frontier.OneTapeMagnification.dptwZeroTail_test_average_sub_le_tableLength_mul
#check Frontier.OneTapeMagnification.finiteBitTapeAddEquiv
#check Frontier.OneTapeMagnification.uniformPredicateAverage_comp_equiv
#check Frontier.OneTapeMagnification.uniformPredicateAverage_prod_and
#check Frontier.OneTapeMagnification.dptwSurvivesAllBLevels_zero_average
#check Frontier.OneTapeMagnification.dptwSurvivesAllBLevels_average_eq_pow
#check Frontier.OneTapeMagnification.dptwSurvivesAllBLevels_average_eq_pow_of_marginal
#check Frontier.OneTapeMagnification.dptwZeroTail_test_average_sub_le_marginal_pow
#check Frontier.OneTapeMagnification.dptwZeroTail_product_test_average_sub_le_marginal_pow

/-! Small reducible computations pin down the integer and final-block conventions. -/
example : DAGCodec.codeLength 0 0 = 2 := by
  norm_num [DAGCodec.codeLength, DAGCodec.slotWidth, DAGCodec.wordWidth]

example : StreamMerge.expectedLength 2 10 0 = 4 := by rfl

example : StreamMerge.expectedLength 2 3 3 = 1 := by rfl

example : StreamMerge.paperBlockLength 2 1 = 4 := by
  norm_num [StreamMerge.paperBlockLength]

example :
    StreamMergeWire.parse
        (StreamMergeWire.serialize
          (StreamMerge.Result.noCircuit : StreamMerge.Result 0 0)) =
      some StreamMerge.Result.noCircuit := by
  simp

end StreamingAndOneTapeMagnificationSurface

end Tests
end Pnp4
