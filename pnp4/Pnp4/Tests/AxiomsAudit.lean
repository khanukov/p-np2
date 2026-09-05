import Pnp4.AlgorithmsToLowerBounds.AC0pAsymptoticBridge
import Pnp4.AlgorithmsToLowerBounds.AC0pSuperPolynomialBridge
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Final
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Quantitative
import Pnp4.AlgorithmsToLowerBounds.AC0pCoinAsymptotic
import Pnp4.AlgorithmsToLowerBounds.CoinMaskingTranslation
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReductionContract
import Pnp4.AlgorithmsToLowerBounds.LocalPRGHardnessSpec
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitPublishedLowerBound
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitTargetModel
import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Final
import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Theorem2Quantitative
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitAsymptotic
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG
import Pnp4.Frontier.PvsNPBridgeRequirements
import Pnp4.Frontier.CompressionMagnification
import Pnp4.Frontier.SearchMCSPMagnification
import Pnp4.Frontier.SearchMCSPConcreteTargets
import Pnp4.Frontier.DagSupportCardinality
import Pnp4.Frontier.SignedSupportNoGo.DenseEasyBarrier
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
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixVerifierLayout
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtension
import Pnp4.Frontier.ContractExpansion.ContentVirtualZeroTailReaderCore
import Pnp4.Frontier.ContractExpansion.ContentCappedArithmetic
import Pnp4.Frontier.ContractExpansion.ContentCappedSizes
import Pnp4.Frontier.ContractExpansion.ContentParseFieldRecovery
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionCoincidence
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding
import Pnp4.Frontier.ContractExpansion.ContentSemanticVerifier
import Pnp4.Frontier.ContractExpansion.ContentVerifierTapeInterface
import Pnp4.Frontier.ContractExpansion.ContentVerifierBridgeWitness
import Pnp4.Frontier.ContractExpansion.ContentTargetSizeBound
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixExplicitCap
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionNonVacuity
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionGateClosure
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPaddingTransport
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionTransfer
import Pnp4.Frontier.ContractExpansion.ContentConsolidatedSource
import Pnp4.Frontier.ContractExpansion.ExplicitConditionalSource
import Pnp4.Frontier.ContractExpansion.ConcreteCodecGap
import Pnp4.Frontier.ContractExpansion.CircuitTreeBridge
import Pnp4.Frontier.ContractExpansion.CircuitEncodingLength
import Pnp4.Frontier.ContractExpansion.CircuitDecodeDepthFree
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ConcreteTreeDirectTagProgram
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodecSource
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth
import Pnp4.Frontier.ContractExpansion.TreeCircuitContentWitnessRelation
import Pnp4.Frontier.ContractExpansion.ConsolidatedTreeSeparation
import Pnp4.Frontier.ContractExpansion.TreeMCSPZeroPrefixBuilder
import Pnp4.Frontier.ContractExpansion.NaiveGreedySizeSpike
import Pnp4.Frontier.ModelAudit.RuntimeAdviceBarrier

namespace Pnp4
namespace Tests

-- Dependency-closed DAG support cardinality.  Infrastructure only: these
-- theorems neither supply nor reduce a P-vs-NP lower-bound source obligation.
#print axioms Pnp4.Frontier.DagSupportCardinality.supportAt_subset_directInputCover
#print axioms Pnp4.Frontier.DagSupportCardinality.support_subset_directInputCover
#print axioms Pnp4.Frontier.DagSupportCardinality.directInputCover_card_le_two_mul_size
#print axioms Pnp4.Frontier.DagSupportCardinality.support_card_le_two_mul_size
#print axioms Pnp4.Frontier.DagSupportCardinality.exists_small_evaluation_support

-- Generic signed-support/no-go infrastructure.  The finite-set construction
-- and finite sums use the standard classical finite-data axioms only; no
-- project axiom or separation source is introduced.
#print axioms Pnp4.Frontier.SignedSupportNoGo.uniformPredicateAverage_mem_unitInterval
#print axioms Pnp4.Frontier.SignedSupportNoGo.boolIndicator_nonneg
#print axioms Pnp4.Frontier.SignedSupportNoGo.boolIndicator_le_one
#print axioms Pnp4.Frontier.SignedSupportNoGo.uniformPredicateAverage_le_one
#print axioms Pnp4.Frontier.SignedSupportNoGo.weightedGeneratorAverage_eq_zero_of_nonzero_support_rejects
#print axioms Pnp4.Frontier.SignedSupportNoGo.lowerWeightedApproximation_support_hits
#print axioms Pnp4.Frontier.SignedSupportNoGo.exists_reverseOneSidedFoolsDAG_iff_hits
#print axioms Pnp4.Frontier.SignedSupportNoGo.eval_equalsTableDAG
#print axioms Pnp4.Frontier.SignedSupportNoGo.gates_equalsTableDAG_le
#print axioms Pnp4.Frontier.SignedSupportNoGo.eval_avoidListDAG
#print axioms Pnp4.Frontier.SignedSupportNoGo.size_avoidListDAG_le
#print axioms Pnp4.Frontier.SignedSupportNoGo.uniformPredicateAverage_gt_half_of_dense
#print axioms Pnp4.Frontier.SignedSupportNoGo.everyDenseDAGPredicateAcceptsEasyTable_of_hitsDense
#print axioms Pnp4.Frontier.SignedSupportNoGo.not_everyDenseDAGPredicateAcceptsEasyTable_of_cover_fits
#print axioms Pnp4.Frontier.SignedSupportNoGo.not_exists_reverseOneSidedFoolsDAG_of_easyImage_cover_fits
#print axioms Pnp4.Frontier.SignedSupportNoGo.not_allExponent_everyDenseDAGPredicateAcceptsEasyTable_of_coverBits_eventuallyLinear

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
#print axioms AlgorithmsToLowerBounds.smallCircuit_contradiction_of_localPRGTransfer
#print axioms AlgorithmsToLowerBounds.sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_publishedOneSidedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_publishedLocalPRGRoute
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
#print axioms AlgorithmsToLowerBounds.BoundedClassSolvesCoinProblem.mono_size
#print axioms AlgorithmsToLowerBounds.MCSPThresholdOracle.accepts_of_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.MCSPThresholdOracle.rejects_of_not_treeMCSPPredicate
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
#print axioms AlgorithmsToLowerBounds.P_ne_NP_of_verified_source
#print axioms Frontier.AC0pRestrictedLowerBoundSource.restrictedConclusion
#print axioms Frontier.P_ne_NP_of_pnp4_bridge_requirement
#print axioms Frontier.P_ne_NP_of_restricted_source_and_dag_bridge
#print axioms Frontier.P_ne_NP_of_NP_not_subset_Ppoly
#print axioms Frontier.SearchMCSPWeakLowerBound.verifiedSource
#print axioms Frontier.NP_not_subset_Ppoly_of_searchMCSPWeakLowerBound
#print axioms Frontier.P_ne_NP_of_searchMCSPWeakLowerBound
#print axioms Frontier.P_ne_NP_of_mainlineProgress
#print axioms Frontier.PvsNPMainlineProgress.of_searchMCSPWeakLowerBound
#print axioms Frontier.SearchMCSPWeakLowerBound.of_weakCircuitLowerBound
#print axioms Frontier.SearchMCSPWeakCircuitLowerBound.verifiedSource
#print axioms Frontier.NP_not_subset_Ppoly_of_weakCircuitLowerBound
#print axioms Frontier.P_ne_NP_of_weakCircuitLowerBound
#print axioms Frontier.PvsNPMainlineProgress.of_weakCircuitLowerBound
#print axioms Frontier.treeMCSPSearchProblem
#print axioms Frontier.treeMCSPSearchWeakLowerBoundTarget
#print axioms Frontier.TreeCircuitWitnessCodec.sound
#print axioms Frontier.TreeCircuitWitnessCodec.complete
#print axioms Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
#print axioms Frontier.TreeMCSPSearchMagnificationSource.verifiedSource
#print axioms Frontier.NP_not_subset_Ppoly_of_treeMCSPSearchMagnificationSource
#print axioms Frontier.P_ne_NP_of_treeMCSPSearchMagnificationSource
#print axioms Frontier.PvsNPMainlineProgress.of_treeMCSPSearchMagnificationSource

end Tests
end Pnp4

#print axioms Pnp4.Frontier.ContractExpansion.InPpolyDAG_to_C_DAG_family
#print axioms Pnp4.Frontier.ContractExpansion.C_DAG_family_to_InPpolyDAG
#print axioms Pnp4.Frontier.ContractExpansion.PpolyDAG_decider_as_C_DAG_decider

#print axioms Pnp4.Frontier.ContractExpansion.eval_composeDeciderWithQuery
#print axioms Pnp4.Frontier.ContractExpansion.size_composeDeciderWithQuery_le

#print axioms Pnp4.Frontier.ContractExpansion.QueryCircuitBuilder.eval_compose
#print axioms Pnp4.Frontier.ContractExpansion.QueryCircuitBuilder.size_compose_le
#print axioms Pnp4.Frontier.ContractExpansion.QueryCircuitBuilder.size_compose_le_bound

#print axioms Pnp4.Frontier.ContractExpansion.PrefixQueryBuilder.eval_compose
#print axioms Pnp4.Frontier.ContractExpansion.PrefixQueryBuilder.size_compose_le
#print axioms Pnp4.Frontier.ContractExpansion.PrefixQueryBuilder.queryValue_parses

#print axioms Pnp4.Frontier.ContractExpansion.parse_zeroPrefixQueryValue
#print axioms Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue_parses

#print axioms Pnp4.Frontier.ContractExpansion.eval_zeroPrefixQueryBitCircuit
#print axioms Pnp4.Frontier.ContractExpansion.size_zeroPrefixQueryBitCircuit_le

#print axioms Pnp4.Frontier.ContractExpansion.parse_prefixStateQueryValue
#print axioms Pnp4.Frontier.ContractExpansion.prefixStateQueryValue_parses
#print axioms Pnp4.Frontier.ContractExpansion.eval_prefixStateQueryBitCircuit
#print axioms Pnp4.Frontier.ContractExpansion.size_prefixStateQueryBitCircuit_le

#print axioms Pnp4.Frontier.ContractExpansion.gates_greedyBundleStep
#print axioms Pnp4.Frontier.ContractExpansion.size_greedyStepHead_le
#print axioms Pnp4.Frontier.ContractExpansion.evalOutput_greedyBundleStep_old
#print axioms Pnp4.Frontier.ContractExpansion.evalOutput_greedyBundleStep_new

#print axioms Pnp4.Frontier.ContractExpansion.gates_greedyBundleUpTo_succ
#print axioms Pnp4.Frontier.ContractExpansion.gates_greedyBundleUpTo_le
#print axioms Pnp4.Frontier.ContractExpansion.evalOutput_greedyBundleUpTo_old
#print axioms Pnp4.Frontier.ContractExpansion.evalOutput_greedyBundleUpTo_new

#print axioms Pnp4.Frontier.ContractExpansion.eval_greedyOutputCircuit
#print axioms Pnp4.Frontier.ContractExpansion.size_greedyOutputCircuit_le

#print axioms Pnp4.Frontier.ContractExpansion.prefixExtendableInput_iff_witnessPrefixExtendable
#print axioms Pnp4.Frontier.ContractExpansion.witnessPrefixExtendable_split
#print axioms Pnp4.Frontier.ContractExpansion.witnessPrefixExtendable_snoc_false_of_not_true
#print axioms Pnp4.Frontier.ContractExpansion.witnessPrefixExtendable_snoc_true_of_not_false

#print axioms Pnp4.Frontier.ContractExpansion.eval_prefixTrueExtensionQueryBitCircuit
#print axioms Pnp4.Frontier.ContractExpansion.size_prefixTrueExtensionQueryBitCircuit_le
#print axioms Pnp4.Frontier.ContractExpansion.size_greedyTrueStepHead_le
#print axioms Pnp4.Frontier.ContractExpansion.greedyPrefix_succ
#print axioms Pnp4.Frontier.ContractExpansion.greedyPrefix_extendable

#print axioms Pnp4.Frontier.ContractExpansion.gates_greedyTrueBundleUpTo_le
#print axioms Pnp4.Frontier.ContractExpansion.eval_greedyTrueOutputCircuit
#print axioms Pnp4.Frontier.ContractExpansion.size_greedyTrueOutputCircuit_le

#print axioms Pnp4.Frontier.ContractExpansion.correctNextBitDecider_of_decidesLanguage

#print axioms Pnp4.Frontier.ContractExpansion.greedyPrefix_solves
#print axioms Pnp4.Frontier.ContractExpansion.searchSolverOutput_greedyTrueOutputCircuit
#print axioms Pnp4.Frontier.ContractExpansion.greedyTrueOutputCircuit_solves

#print axioms Pnp4.Frontier.ContractExpansion.boundedSearchSolver_of_deciderFamily
#print axioms Pnp4.Frontier.ContractExpansion.boundedSearchSolver_of_PpolyDAG_prefixExtension
#print axioms Pnp4.Frontier.ContractExpansion.not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver

#print axioms Pnp4.Frontier.ContractExpansion.nonempty_boundedSearchSolver_mono_sizeBound
#print axioms Pnp4.Frontier.ContractExpansion.noExtractedScheduleSolver_of_noPolynomial
#print axioms Pnp4.Frontier.ContractExpansion.not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver

#print axioms Pnp4.Frontier.ContractExpansion.verifiedSource_of_noPolynomialBoundedSearchSolver
#print axioms Pnp4.Frontier.ContractExpansion.NP_not_subset_PpolyDAG_of_noPolynomialBoundedSearchSolver

#print axioms Pnp4.Frontier.ContractExpansion.bitLength_le_self
#print axioms Pnp4.Frontier.ContractExpansion.polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPExtractionGrowthAssumptions_of_witnessPoly
#print axioms Pnp4.Frontier.ContractExpansion.PolynomialWitnessCodec.toGrowthAssumptions

#print axioms Pnp4.Frontier.ContractExpansion.prefixExtensionLanguage_in_NP_of_witness
-- The content-truthful prefix-extension language L' (bricks R1/R2): membership read through the
-- blank padding at content-computed offsets, with no *explicit* gate on the ambient physical length
-- (the strict parser's own m = treeMCSPPrefixM equality gate survives inside contentInput?, applied
-- to the computed window rather than to the ambient N; I1 proves this equality gate vacuous after a
-- successful header decode, leaving exactly three tag/index/padding read-value tests), plus its
-- NP-witness interface.  That interface stays an unproved hypothesis -- no TM, runtime bound, or
-- TM.accepts bridge is built anywhere.  GATE-0 establishes concrete ContentAccepts non-vacuity.
#print axioms Pnp4.Frontier.ContractExpansion.padRead_lt
#print axioms Pnp4.Frontier.ContractExpansion.padRead_ge
#print axioms Pnp4.Frontier.ContractExpansion.padWord_apply
#print axioms Pnp4.Frontier.ContractExpansion.padWord_self
#print axioms Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
#print axioms Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage_accepts_iff
#print axioms Pnp4.Frontier.ContractExpansion.contentPrefixExtensionLanguage_in_NP_of_witness
-- Repair brick R3: the coincidence lemma -- under BOTH hypotheses, hparse (the strict parse of the
-- query succeeds) and hn : input.n = n (the parsed target is the ambient one), L' agrees with the
-- length-gated language at treeMCSPPrefixM codec n.  hn does NOT follow from hparse: inversion
-- yields only treeMCSPPrefixM codec input.n = treeMCSPPrefixM codec n, and injectivity of
-- treeMCSPPrefixM codec is not proved.  Listed with its reader-monotonicity, parse-inversion
-- and window-computation ingredients.  The three monotonicity lemmas and parse inversion are
-- Classical-free (nothing / [propext] / [propext, Quot.sound]); the lemmas about a concatenated
-- word inherit Classical.choice from the noncomputable concatBitstring.  The predicate-level
-- coincidence theorem avoids both Boolean language wrappers; the language-level headline adds
-- those wrappers only at its outermost step.
#print axioms Pnp4.Frontier.ContractExpansion.readBit?_mono
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_mono
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux?_mono
#print axioms Pnp4.Frontier.ContractExpansion.decodeGamma?_concat_pad
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_inversion
#print axioms Pnp4.Frontier.ContractExpansion.padWord_concat_left
#print axioms Pnp4.Frontier.ContractExpansion.contentWitness_concat
#print axioms Pnp4.Frontier.ContractExpansion.contentInput?_concat_of_parse
#print axioms Pnp4.Frontier.ContractExpansion.ContentPrefixExtendable_iff_of_parse
#print axioms Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage_eq_of_parse
-- Repair brick R4: the extraction transfer -- an L'-decider drives the same greedy machinery (by
-- coincidence at the constructed queries), so the same open no-solver hypotheses pin L' outside
-- PpolyDAG.  Still the one-way PpolyDAG -> solver direction; no converse.
#print axioms Pnp4.Frontier.ContractExpansion.correctNextBitDecider_of_decidesContentLanguage
#print axioms Pnp4.Frontier.ContractExpansion.boundedSearchSolver_of_deciderFamilyCT
#print axioms Pnp4.Frontier.ContractExpansion.boundedSearchSolver_of_PpolyDAG_contentPrefixExtension
#print axioms Pnp4.Frontier.ContractExpansion.not_PpolyDAG_contentPrefixExtension_of_noExtractedScheduleSolver
#print axioms Pnp4.Frontier.ContractExpansion.not_PpolyDAG_contentPrefixExtension_of_noPolynomialBoundedSearchSolver
-- Repair brick R5: the CT sources -- the conditional chain re-routed through L'.  The two open
-- inputs are input (1) unchanged and the CONTENT-TRUTHFUL NP witness; both stay explicit
-- hypotheses.  Both the generic source and the concrete-threshold specialization are audited.
#print axioms Pnp4.Frontier.ContractExpansion.verifiedSourceCT_of_noPolynomialBoundedSearchSolver
#print axioms Pnp4.Frontier.ContractExpansion.verifiedSourceCT_treePoly
#print axioms Pnp4.Frontier.ContractExpansion.NP_not_subset_PpolyDAG_treePolyCT
-- Specification-side obligation: padding stability of ContentAccepts -- the blank-tail lemma is
-- proved, and the headline says any two COMPLETE finite words with the same blank-padded tape are
-- content-accepted alike.  The fuel side condition N + 1 <= fuel' + zeros is an EXPLICIT HYPOTHESIS
-- of decodeGammaAux?_padWord_canonical, not a proved fact: what the induction proves is that the
-- scan step PRESERVES it, and the two callers in the module discharge its initial instance at their
-- concrete fuel 2 * width + 2 with zeros = 0.  This closes the residual ambient-N dependence of
-- ContentAccepts on the SPECIFICATION side only.  It does NOT give padding invariance of the
-- language wrapper ContentPrefixExtensionLanguage (L'), whose membership at length m quantifies
-- over certificates of length certificateLength m 1 concatenated at offset m, both moving with m;
-- it does NOT build a verifier TM, a runtime bound, or a TM.accepts bridge; the pnp3 model is not
-- length-blind; and stability is agreement INCLUDING on failure, so it does not by itself show the
-- strict parser's m = treeMCSPPrefixM codec n_dec gate inside contentInput? is vacuous.  I1 proves
-- that equality gate vacuous separately and leaves exactly three tag/index/padding read-value tests.
-- This
-- entire module is axiom-light: readBit?_padWord_of_lt is axiom-free and the other fourteen entries
-- are [propext, Quot.sound], with no Classical.choice theorem.
#print axioms Pnp4.Frontier.ContractExpansion.padRead_padWord_of_le
#print axioms Pnp4.Frontier.ContractExpansion.padWord_padWord_of_le
#print axioms Pnp4.Frontier.ContractExpansion.eq_padWord_of_padRead_eq
#print axioms Pnp4.Frontier.ContractExpansion.lt_of_padRead_eq_true
#print axioms Pnp4.Frontier.ContractExpansion.readBit?_padWord_of_lt
#print axioms Pnp4.Frontier.ContractExpansion.readBit?_padWord_of_ge
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_padWord_transfer
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux?_padWord_support
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux?_padWord_canonical
#print axioms Pnp4.Frontier.ContractExpansion.contentHeader?_padWord_of_le
#print axioms Pnp4.Frontier.ContractExpansion.contentInput?_padWord_of_le
#print axioms Pnp4.Frontier.ContractExpansion.contentWitness_padWord_of_le
#print axioms Pnp4.Frontier.ContractExpansion.ContentAccepts_padWord_of_le
#print axioms Pnp4.Frontier.ContractExpansion.ContentAccepts_iff_of_padRead_eq
#print axioms Pnp4.Frontier.ContractExpansion.contentHeader?_of_decodeGamma
-- P0 content-side semantic verifier.  These must stay within the standard
-- [propext, Classical.choice, Quot.sound] triple or a subset.  The Boolean definition itself is
-- separately exercised by a concrete #eval in AlgorithmsToLowerBoundsSurfaceTests.lean.
#print axioms Pnp4.Frontier.ContractExpansion.contentSemanticAccepts_eq_true_iff
#print axioms Pnp4.Frontier.ContractExpansion.contentSemanticAccepts_eq_false_of_contentInput_none
#print axioms Pnp4.Frontier.ContractExpansion.contentSemanticAccepts_padWord_of_le
#print axioms Pnp4.Frontier.ContractExpansion.contentSemanticAccepts_correct
-- D1a machine-facing tape interface.  The first theorem inherits Classical.choice from the
-- noncomputable concatenation used in its statement; the second is the padding theorem restated
-- for machine consumers.  `ContentVerifierBridgeFor` is a data structure rather than a proved
-- theorem: it names an exact-step, predicate-parameterized obligation and supplies no instance.
-- Its polynomial field does not formally enforce runtime-advice avoidance.
#print axioms Pnp4.Frontier.ContractExpansion.initialConfig_tape_eq_padRead
#print axioms Pnp4.Frontier.ContractExpansion.contentAccepts_of_initialConfig_tape_eq
-- D1b bridge specialization and witness repackaging.  `ContentVerifierBridge` is an abbreviation
-- for the D1a structure at P0's acceptance predicate, so it has no separate proof to audit; the
-- repackaging below carries the proof obligation and inherits Classical.choice from the
-- noncomputable language wrapper and concatenation used in its statement.  It is CONDITIONAL on a
-- supplied bridge: it constructs no machine, runtime bound, or TM.accepts proof, and consumes
-- runTime_poly verbatim rather than establishing it.  Its expected footprint is the standard
-- [propext, Classical.choice, Quot.sound] triple or lighter.
#print axioms Pnp4.Frontier.ContractExpansion.contentPrefixExtensionNPWitness_of_bridge
-- Explicitly classical conditional transport module.  The theorem derives ContentPrefixExtendable
-- directly through ContentPrefixExtendable_iff_of_parse, without either Boolean language wrapper.
-- Its statement still necessarily inherits Classical.choice from the pre-existing noncomputable
-- concatBitstring.  It is conditional on hparse, hn, hext, and hT, so is not the unconditional
-- non-vacuity result; GATE-0 supplies that separately.
#print axioms Pnp4.Frontier.ContractExpansion.ContentAccepts_padWord_of_prefixExtendable
-- FEAS-0 slice, part 1 (ContentParseFieldRecovery.lean, plan section 1.0): parser field recovery.
-- parseTreeMCSPPrefixInput_inversion above keeps only the length gate and the gamma decode; these
-- two re-walk the same success cascade and keep the x branch, so the parsed truth table is pinned to
-- the canonical x-slice of the ambient vector and, content-side, to blank-padded reads of z itself.
-- The gamma width is SYMBOLIC: both conjuncts of the first theorem live under one existential
-- consumed, and neither statement says consumed = gammaLen input.n nor relates pr.2.n to the header
-- value pr.1 -- no injectivity of treeMCSPPrefixM codec and no gamma canonicity is used (plan
-- stop/go F0b).  Both entries are axiom-light: [propext, Quot.sound], no Classical.choice, lighter
-- than the standard triple.  Scope: recovery only; the separate part-2 audit below now covers the
-- FEAS-0 target bound.  They do not themselves show ContentAccepts is satisfiable and build no
-- verifier TM, runtime bound or TM.accepts bridge; GATE-0 separately supplies non-vacuity.
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_x_slice
#print axioms Pnp4.Frontier.ContractExpansion.contentInput?_x_apply

-- FEAS-0 slice, part 2 (ContentTargetSizeBound.lean, plan section 1.0): all-blank concrete decode,
-- input-zero truth-table forcing, physical-support forcing, equality of convention lengths at the
-- parsed target r := pr.2.n, and the polynomial headline.  This is I1-free: it uses M n_header =
-- M r and never n_header = r.  These are infrastructure theorems.  They freeze the content target
-- but do not construct a verifier TM, prove L' in NP, themselves establish non-vacuity, or
-- discharge either lower-bound source obligation.  GATE-0 establishes non-vacuity separately.
#print axioms Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec_decode_blank_zero
#print axioms Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec_decode_blank_pos
#print axioms Pnp4.Frontier.ContractExpansion.bitVecToNat_all_true
#print axioms Pnp4.Frontier.ContractExpansion.input_zero_computes_forces_last_true
#print axioms Pnp4.Frontier.ContractExpansion.contentInput?_target_length
#print axioms Pnp4.Frontier.ContractExpansion.contentWitness_eq_false_of_lt
#print axioms Pnp4.Frontier.ContractExpansion.contentAccepts_parsed_tableLen_le_of_header_target_wide
#print axioms Pnp4.Frontier.ContractExpansion.contentAccepts_target_poly_treePoly

-- GATE-0 (ContentPrefixExtensionNonVacuity.lean, plan section 4.1): ContentAccepts is
-- UNCONDITIONALLY satisfiable.  zeroPrefixQueryValue_parses supplies both hparse and hn (input.n =
-- n) for contentInput?_concat_of_parse -- the parsed object is the canonical toPrefixInput -- so no
-- injectivity of treeMCSPPrefixM codec and no gamma canonicity is used; prefix agreement is vacuous
-- at i = 0; the relation conjunct is TreeCircuitWitnessCodec.complete; the concrete discharge is
-- Circuit.const false of size 1 against 1 <= thresholdPoly k n.  These are infrastructure theorems
-- about WHICH words are accepted, not about the cost of deciding acceptance: they construct no
-- verifier TM, runtime bound or TM.accepts bridge, give no ContentPrefixExtensionNPWitness instance
-- and no NP membership for L'.  This module handles the re-decode gate only on its constructed
-- zero-prefix words; I1 separately proves the convention-length equality gate vacuous in general
-- after successful header decoding.  No lower-bound source obligation is discharged.
-- Infrastructure only; no P != NP claim.
#print axioms Pnp4.Frontier.ContractExpansion.contentAccepts_zeroPrefixQuery_of_predicate
#print axioms Pnp4.Frontier.ContractExpansion.contentPrefixExtensionLanguage_zeroPrefixQuery
#print axioms Pnp4.Frontier.ContractExpansion.contentAccepts_nonvacuous_treePoly

-- I1 gate closure (ContentPrefixExtensionGateClosure.lean, plan section 4.3).  Injectivity is
-- audited only under monotone witness width and at the concrete polynomial codec; no false generic
-- codec theorem exists.  Canonicity is hypothesis-free after successful decoding, narrowing uses
-- the consumed-based transfer correction, proves the convention-length equality gate vacuous, and
-- exposes exactly the three tag/index/pad-zero read-value tests.  Infrastructure only: no verifier,
-- NP-membership, or lower-bound source obligation is discharged; GATE-0 supplies non-vacuity
-- independently.
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM_strictMono
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM_injective_of_monotone
#print axioms Pnp4.Frontier.ContractExpansion.witnessBits_monotone_treePoly
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM_injective_treePoly
#print axioms Pnp4.Frontier.ContractExpansion.ContentPrefixExtendable_iff_of_parse'
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_lt_two_pow
#print axioms Pnp4.Frontier.ContractExpansion.decodeGamma?_consumed_eq_gammaLen
#print axioms Pnp4.Frontier.ContractExpansion.contentHeader?_consumed_eq_gammaLen
#print axioms Pnp4.Frontier.ContractExpansion.decodeGamma?_padWord_narrow
#print axioms Pnp4.Frontier.ContractExpansion.contentInput?_lengthGate_vacuous
#print axioms Pnp4.Frontier.ContractExpansion.contentInput?_isSome_iff_of_header

#print axioms Pnp4.Frontier.ContractExpansion.verifiedSource_of_explicit_interfaces
#print axioms Pnp4.Frontier.ContractExpansion.NP_not_subset_PpolyDAG_of_explicit_interfaces

#print axioms Pnp4.Frontier.ContractExpansion.ofFn_listToFixedBitVec
#print axioms Pnp4.Frontier.ContractExpansion.SelfDelimitingCircuitCode.toCodec

#print axioms Pnp4.Frontier.ContractExpansion.fromTree_toTree
#print axioms Pnp4.Frontier.ContractExpansion.toTree_fromTree
#print axioms Pnp4.Frontier.ContractExpansion.size_toTree
#print axioms Pnp4.Frontier.ContractExpansion.decodeCircuit_encodeCircuit

#print axioms Pnp4.Frontier.ContractExpansion.length_encodeCircuitTree_le
#print axioms Pnp4.Frontier.ContractExpansion.length_encodeCircuit_le

#print axioms Pnp4.Frontier.ContractExpansion.length_encodeCircuit_ge
#print axioms Pnp4.Frontier.ContractExpansion.decodeCircuitFull_encodeCircuit

#print axioms Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
#print axioms Pnp4.Frontier.ContractExpansion.polyBoundedInTable_treeWitnessBits_of_thresholdPoly
#print axioms Pnp4.Frontier.ContractExpansion.treePolynomialWitnessCodec

-- CVB-ARCH-1 verdict BLOCK.  These are reusable functional-evaluator/tag-microprogram
-- infrastructure results; they do not construct ContentVerifierBridge or a full TM evaluation run.
#print axioms Pnp4.Frontier.ContractExpansion.directEvalLoop_visit
#print axioms Pnp4.Frontier.ContractExpansion.directCircuitEval_correct
#print axioms Pnp4.Frontier.ContractExpansion.nativeEval_spec
#print axioms Pnp4.Frontier.ContractExpansion.nativeEvalList_rejects_short_tag
#print axioms Pnp4.Frontier.ContractExpansion.nativeEvalList_rejects_tag101
#print axioms Pnp4.Frontier.ContractExpansion.nativeEvalList_rejects_tag110
#print axioms Pnp4.Frontier.ContractExpansion.nativeEvalList_rejects_tag111
#print axioms Pnp4.Frontier.ContractExpansion.nativeEvalList_rejects_short_input_field
#print axioms Pnp4.Frontier.ContractExpansion.nativeEvalList_rejects_truncated_const
#print axioms Pnp4.Frontier.ContractExpansion.nativeEvalList_rejects_invalid_input_index
#print axioms Pnp4.Frontier.ContractExpansion.nativeEvalBounded_rejects_threshold_overflow
#print axioms Pnp4.Frontier.ContractExpansion.directEvalLoop_rejects_not_underflow
#print axioms Pnp4.Frontier.ContractExpansion.directEvalLoop_rejects_and_underflow
#print axioms Pnp4.Frontier.ContractExpansion.directEvalLoop_rejects_or_underflow
#print axioms Pnp4.Frontier.ContractExpansion.directEvalCost_le_two_mul_size
#print axioms Pnp4.Frontier.ContractExpansion.decodeCircuitTreeAtDepth_consumed_ge
#print axioms Pnp4.Frontier.ContractExpansion.decodeCircuitFull_directEvalCost_le_length

#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_authoritative
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_input
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_const
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_not
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_and
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_or
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_bad101
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_bad110
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_bad111
#print axioms Pnp4.Frontier.ContractExpansion.decodeDirectTreeTag_eq_root_of_decode
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_timeBound
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_tapeLength
#print axioms Pnp4.Frontier.ContractExpansion.directTagCell_val
#print axioms Pnp4.Frontier.ContractExpansion.directTagCellAt_val
#print axioms Pnp4.Frontier.ContractExpansion.directTagInputCell_val
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_step0
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_step1
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_step2
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_step3
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_step4_accepts_iff
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_runConfig_home
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_runConfig_at
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_runConfig_input_at
#print axioms Pnp4.Frontier.ContractExpansion.directTagProgram_runConfig_five_accepts_iff

#print axioms Pnp4.Frontier.ContractExpansion.verifiedSource_of_treeCodec_noPolynomialBoundedSearchSolver
#print axioms Pnp4.Frontier.ContractExpansion.NP_not_subset_PpolyDAG_of_treeCodec_interfaces

#print axioms Pnp4.Frontier.ContractExpansion.polyBoundedInTable_thresholdLinear
#print axioms Pnp4.Frontier.ContractExpansion.polyBoundedInTable_thresholdQuadratic
#print axioms Pnp4.Frontier.ContractExpansion.polyBoundedInTable_thresholdPoly

#print axioms Pnp4.Frontier.ContractExpansion.verifiedSource_treePoly
#print axioms Pnp4.Frontier.ContractExpansion.NP_not_subset_PpolyDAG_treePoly

#print axioms Pnp4.Frontier.ContractExpansion.zeroPrefixQueryCircuitBuilder
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPZeroPrefixQueryBuilder
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPZeroPrefixQueryBuilder_queryValue

#print axioms Pnp4.Frontier.ContractExpansion.geometric_lower_bound
#print axioms Pnp4.Frontier.ContractExpansion.composeDeciderWithQuery_eq_substInputs
#print axioms Pnp4.Frontier.ContractExpansion.naiveGreedyModel_size_ge
#print axioms Pnp4.Frontier.ContractExpansion.naiveGreedyModel_size_ge_pow
#print axioms Pnp4.Frontier.ContractExpansion.pow_le_of_linear_witnessBits
#print axioms Pnp4.Frontier.ContractExpansion.pow_quadratic_gt_poly

#print axioms Pnp4.Frontier.ModelAudit.RuntimeAdviceBarrier.lengthAdviceTM_runTime_le_one
#print axioms Pnp4.Frontier.ModelAudit.RuntimeAdviceBarrier.lengthAdviceTM_accepts
#print axioms Pnp4.Frontier.ModelAudit.RuntimeAdviceBarrier.lengthAdviceLanguage_in_repo_P

#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalGateAt_congr
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.snocBundleSubst_gates
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_snocBundleSubst_new
#print axioms Pnp3.ComplexityInterfaces.DagCircuit.evalOutput_snocBundleSubst_old

#print axioms Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage_accepts_iff
#print axioms Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage_rejects_malformed
#print axioms Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage_accepts_of_parse_and_witness
#print axioms Pnp4.Frontier.ContractExpansion.tableLen_le_treeMCSPPrefixAmbientLength
#check Pnp4.Frontier.ContractExpansion.RuntimeAwareTreeCircuitCodec
#check Pnp4.Frontier.ContractExpansion.RuntimeAwarePrefixParser
#check Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixRuntimeBudget
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
#print axioms Pnp4.Frontier.ContractExpansion.tableLen_le_treeMCSPPrefixM
#check Pnp4.Frontier.ContractExpansion.natBEField
#check Pnp4.Frontier.ContractExpansion.CanonicalRawTreeMCSPPrefixFields
#check Pnp4.Frontier.ContractExpansion.encodeTreeMCSPPrefixFields
#check Pnp4.Frontier.ContractExpansion.CanonicalRawTreeMCSPPrefixFields.toPrefixInput
#print axioms Pnp4.Frontier.ContractExpansion.encodeTreeMCSPPrefixFields_length_convention
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_encode_tag
#print axioms Pnp4.Frontier.ContractExpansion.sliceBits_encode_x
#print axioms Pnp4.Frontier.ContractExpansion.sliceBits_encode_p
#print axioms Pnp4.Frontier.ContractExpansion.parse_encodeTreeMCSPPrefixFields_partial_obligation
#print axioms Pnp4.Frontier.ContractExpansion.parse_encodeTreeMCSPPrefixFields
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_bad_tag
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_length_convention
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_malformed_rejected
#check Pnp4.Frontier.ContractExpansion.treeMCSPConcretePrefixParser
#check Pnp4.Frontier.ContractExpansion.treeMCSPRuntimeAwarePrefixParser

-- Semantic verifier for the prefix-extension language (NP-verifier track, PR 1).
-- Standard axiom set [propext, Classical.choice, Quot.sound] throughout.  The arithmetic /
-- prefix-agreement helpers are Classical-free; the codec-verification path inherits
-- Classical.choice from the pre-existing verifiesDecidable, and the headline equivalence
-- additionally from the classical PrefixExtensionLanguage wrapper.
#print axioms Pnp4.Frontier.ContractExpansion.witnessBits_le_treeMCSPPrefixM
#print axioms Pnp4.Frontier.ContractExpansion.prefixAgreesBool_eq_true_iff
#print axioms Pnp4.Frontier.ContractExpansion.verifiesBool_eq_true_iff
#print axioms Pnp4.Frontier.ContractExpansion.sliceBits?_zero
#print axioms Pnp4.Frontier.ContractExpansion.witnessBits_le_certificateLength
#print axioms Pnp4.Frontier.ContractExpansion.extractWitness_eq
#print axioms Pnp4.Frontier.ContractExpansion.treePrefixSemanticAccepts_eq_of_parse_extract
#print axioms Pnp4.Frontier.ContractExpansion.treePrefixSemanticAccepts_eq_false_of_extract_none
#print axioms Pnp4.Frontier.ContractExpansion.treePrefixSemanticAccepts_rejects_malformed
#print axioms Pnp4.Frontier.ContractExpansion.treePrefixSemanticAccepts_correct

-- Verifier input-tape layout (NP-verifier track); layout arithmetic only, no machine.  The
-- offset/fit lemmas are Classical-free; the concatBitstring / tape projections inherit
-- Classical.choice from the noncomputable concatBitstring itself.
#print axioms Pnp4.Frontier.ContractExpansion.prefixVerifierInputLen_eq
#print axioms Pnp4.Frontier.ContractExpansion.prefixVerifierWitnessRegion_within_input
#print axioms Pnp4.Frontier.ContractExpansion.concatBitstring_left
#print axioms Pnp4.Frontier.ContractExpansion.concatBitstring_right
#print axioms Pnp4.Frontier.ContractExpansion.verifierTape_left
#print axioms Pnp4.Frontier.ContractExpansion.verifierTape_right
#print axioms Pnp4.Frontier.ContractExpansion.queryPrefixOffset_add_witnessBits
#print axioms Pnp4.Frontier.ContractExpansion.queryPrefixOffset_le
-- Gamma/x field-fit bounds (gamma-decode phase layout preconditions); Classical-free arithmetic.
#print axioms Pnp4.Frontier.ContractExpansion.queryXOffset_le_treeMCSPPrefixM
#print axioms Pnp4.Frontier.ContractExpansion.queryIdxOffset_le_treeMCSPPrefixM
#print axioms Pnp4.Frontier.ContractExpansion.gammaLen_le_treeMCSPPrefixM
#print axioms Pnp4.Frontier.ContractExpansion.instanceSize_lt_treeMCSPPrefixM
-- Gamma payload-read geometry (counter-representation scheme); Classical-free arithmetic.
#print axioms Pnp4.Frontier.ContractExpansion.gammaLen_eq_two_mul_gammaZeros_add_one
#print axioms Pnp4.Frontier.ContractExpansion.gammaTermOffset_lt_queryXOffset
#print axioms Pnp4.Frontier.ContractExpansion.gammaTermOffset_le_treeMCSPPrefixM
#print axioms Pnp4.Frontier.ContractExpansion.gammaMirror_mem

-- P2-4a: direct declaration roots only. Computation uses the computable
-- concatenator. Roots may still report `Classical.choice`: generic relations
-- inherit it from `verifiesBool` (`decide (codec.verifies …)`), threshold
-- instances additionally from `treeCircuitWitnessCodec`, and compatibility
-- theorems from `concatBitstring`.
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.v1ToInterfaceBitstring
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.v1ToPrefixBitVec
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.interfaceToPrefixBitVec
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.concatV1ToPrefixBitVec
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.treePrefixWitnessRelation
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdTreePrefixWitnessRelation
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.concatV1ToPrefixBitVec_eq_concatBitstring
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation_at_certificateLength
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation_at_certificateLength_concatBitstring
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation_of_wrongLength
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.treePrefixWitnessRelation_at_certificateLength
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.treePrefixWitnessRelation_of_wrongLength
-- G0-B1: transparent content-window exponents and explicit acceptance caps.
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPPrefixTableExponent
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPPrefixPowAddExponent
#print axioms Pnp4.Frontier.ContractExpansion.contentCapExponent
#print axioms Pnp4.Frontier.ContractExpansion.tableLen_eq_two_pow_explicit
#print axioms Pnp4.Frontier.ContractExpansion.thresholdPoly_eq_explicit
#print axioms Pnp4.Frontier.ContractExpansion.treeCircuitWitnessBits_thresholdPoly_eq_explicit
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM_thresholdPoly_eq_explicit
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM_thresholdPoly_table_explicit
#print axioms Pnp4.Frontier.ContractExpansion.polyBoundedInTable_treeMCSPPrefixM_thresholdPoly_explicit
#print axioms Pnp4.Frontier.ContractExpansion.powAddNormalize_allBases
#print axioms Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM_thresholdPoly_powAdd_explicit
#print axioms Pnp4.Frontier.ContractExpansion.contentSemanticAccepts_header_target_of_powAdd
#print axioms Pnp4.Frontier.ContractExpansion.contentSemanticAccepts_header_target_explicit
#print axioms Pnp4.Frontier.ContractExpansion.contentSemanticAccepts_successful_input_target_explicit
#print axioms Pnp4.Frontier.ContractExpansion.contentSemanticAccepts_has_bounded_input_target_explicit
-- G0-B2a: all public virtual-zero-tail reader/parser declarations.
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.readBit?
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.readBit?_eq_padWord
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.readNatBE
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.readNatBE_eq_padWord
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.sliceBits?
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.sliceBits?_eq_padWord
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.allZeroSlice?
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.allZeroSlice?_eq_padWord
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.decodeGammaAux?
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.decodeGammaAux?_eq_padWord
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.decodeGamma?
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.decodeGamma?_eq_padWord
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.contentHeader?
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.contentHeader?_eq_padWord
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.contentHeader?_eq
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.parseTreeMCSPPrefixInput
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.parseTreeMCSPPrefixInput_eq_padWord
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.readNatBELoopBound
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.allZeroLoopBound
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.gammaLoopBound
#print axioms Pnp4.Frontier.ContractExpansion.VirtualZeroTailReader.contentHeader_gammaLoopBound
-- G0-B2b1: capped arithmetic declarations and exact success/overflow contracts.
#print axioms Pnp4.Frontier.ContractExpansion.checkedNat
#print axioms Pnp4.Frontier.ContractExpansion.checkedAdd
#print axioms Pnp4.Frontier.ContractExpansion.checkedMul
#print axioms Pnp4.Frontier.ContractExpansion.checkedPow
#print axioms Pnp4.Frontier.ContractExpansion.checkedBitLength
#print axioms Pnp4.Frontier.ContractExpansion.checkedNat_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedNat_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedAdd_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedAdd_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedMul_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedMul_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedPow_recursiveArgument_lt
#print axioms Pnp4.Frontier.ContractExpansion.checkedPow_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedPow_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedBitLength_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedBitLength_eq_none_iff

-- G0-B2b2: concrete capped size-record declarations and exact contracts.
#print axioms Pnp4.Frontier.ContractExpansion.checkedThresholdPoly
#print axioms Pnp4.Frontier.ContractExpansion.checkedThresholdPoly_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedThresholdPoly_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedTableLen
#print axioms Pnp4.Frontier.ContractExpansion.checkedTableLen_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedTableLen_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedTreeWitnessBits
#print axioms Pnp4.Frontier.ContractExpansion.checkedTreeWitnessBits_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedTreeWitnessBits_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.CheckedGammaSizes
#print axioms Pnp4.Frontier.ContractExpansion.exactGammaSizes
#print axioms Pnp4.Frontier.ContractExpansion.checkedGammaSizes
#print axioms Pnp4.Frontier.ContractExpansion.checkedGammaSizes_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedGammaSizes_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedGammaLen
#print axioms Pnp4.Frontier.ContractExpansion.checkedGammaLen_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedGammaLen_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedIndexWidth
#print axioms Pnp4.Frontier.ContractExpansion.checkedIndexWidth_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.checkedIndexWidth_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.ContentSizes
#print axioms Pnp4.Frontier.ContractExpansion.exactContentSizes
#print axioms Pnp4.Frontier.ContractExpansion.ContentSizes.Exact
#print axioms Pnp4.Frontier.ContractExpansion.exactContentSizes_exact
#print axioms Pnp4.Frontier.ContractExpansion.ContentSizes.Exact.eq_exactContentSizes
#print axioms Pnp4.Frontier.ContractExpansion.ContentSizes.Exact.witnessBits_le_M
#print axioms Pnp4.Frontier.ContractExpansion.ContentSizes.Exact.tableLen_le_M
#print axioms Pnp4.Frontier.ContractExpansion.computeContentSizesCapped
#print axioms Pnp4.Frontier.ContractExpansion.computeContentSizesCapped_eq_some_iff
#print axioms Pnp4.Frontier.ContractExpansion.computeContentSizesCapped_eq_none_iff
#print axioms Pnp4.Frontier.ContractExpansion.computeContentSizesCapped_witnessBits_le_M
#print axioms Pnp4.Frontier.ContractExpansion.computeContentSizesCapped_tableLen_le_M
#print axioms Pnp4.Frontier.ContractExpansion.computeContentSizesCapped_components_le_cap
#print axioms Pnp4.Frontier.ContractExpansion.CappedContentSizesCertificate
#print axioms Pnp4.Frontier.ContractExpansion.CappedContentSizesCertificate.ofSuccess
