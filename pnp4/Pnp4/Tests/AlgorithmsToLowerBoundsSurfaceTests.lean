import Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses
import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP
import Pnp4.AlgorithmsToLowerBounds.LocalPRG
import Pnp4.AlgorithmsToLowerBounds.CoinProblem
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReduction
import Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReductionContract
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Final
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Quantitative
import Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer
import Pnp4.AlgorithmsToLowerBounds.LocalPRGHardnessSpec
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitTargetModel
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitPublishedLowerBound
import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Final
import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Theorem2Quantitative
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitAsymptotic
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG

namespace Pnp4
namespace Tests

open AlgorithmsToLowerBounds

def check_NotInClass :
    ∀ (C : CircuitFamilyClass) (L : BitVecLanguage),
      NotInClass C L → NotInClass C L :=
  fun _ _ h => h

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

def check_half_vs_fair_mcsp_coin_reduction_contract_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (contract.threshold n))
      (hardness.advantage n) :=
  contract.exact_solvesCoin n

noncomputable def check_half_vs_fair_mcsp_coin_language
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) : BitVecLanguage :=
  halfVsFairMCSPCoinLanguage contract n

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

#print axioms AlgorithmsToLowerBounds.NP_not_subset_PpolyDAG_of_verified_source
#print axioms AlgorithmsToLowerBounds.P_ne_NP_of_verified_source
#print axioms AlgorithmsToLowerBounds.ImplementedThresholdOracle.classSolvesCoinProblem_of_advantage
#print axioms AlgorithmsToLowerBounds.classSolvesCoinProblem_of_bounded
#print axioms AlgorithmsToLowerBounds.AC0pHalfVsFairCoinLowerBoundContract.excludes_small_solver
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

end Tests
end Pnp4
