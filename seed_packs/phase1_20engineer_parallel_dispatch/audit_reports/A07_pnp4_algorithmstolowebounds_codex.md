# A07 audit report: `pnp4/Pnp4/AlgorithmsToLowerBounds/`

Task: A07
Engineer handle: codex
Branch: `khanukov/phase1-A07-codex`
Scope: markdown-only Phase 0 audit; no Lean/source edits.

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL.**

The audited directory contains a substantial kernel-checked library for finite truth-table MCSP slices, coin problems, masking translations, local-PRG transfer lemmas, and formula/AC0[p] lower-bound wrappers. It is not an end-to-end unconditional AC0[p] → MCSP → `NP_not_subset_PpolyDAG` proof: the published lower bounds and reductions are mostly represented as explicit contract structures with Prop fields, and the only bridge to `NP_not_subset_PpolyDAG` requires a fully supplied `VerifiedNPDAGLowerBoundSource`. The formula route includes an explicit kernel-checked no-go result showing the currently encoded CKLM envelope cannot beat every polynomial-size formula witness, so that asymptotic path is diagnostic unless its growth hypothesis is changed by a real mathematical result. The safe reuse value is high for local finite-slice transfer infrastructure, but future workers must not advertise these restricted lower bounds as P-vs-NP mainline progress without an explicit `PpolyDAG`/`VerifiedNPDAGLowerBoundSource` bridge.

## 2. Executive summary

This is **not** a complete end-to-end AC0[p] → MCSP lower-bound formalization in the sense of an unconditional theorem closing an NP lower bound against `PpolyDAG`. It is a typed pipeline that can turn supplied contract data into finite-slice `SizeLowerBound` statements and non-membership statements for abstract pnp4 circuit classes such as `AC0pFamilyModel`, plus a separate bridge file that says an explicit NP language with a verified `¬ PpolyDAG` proof implies the pnp3 final targets.

The AC0[p] side has real Lean proofs for: probability algebra over coin problems, finite masking/averaging facts, conversion from coin lower-bound contracts to MCSP threshold-oracle contradictions, and conversion from quantitative/published-envelope contracts to exact truth-table-slice lower bounds. The LocalPRG/formula side has real Lean proofs for: PRG easy-image/fooling transfer to thresholded MCSP oracle lower bounds, and formula-class specializations. However, the central published results are not proved from raw literature inside this directory; they are staged as structures such as `AC0pHalfVsFairCoinLowerBoundContract`, `HalfVsFairMCSPCoinReductionContract`, `PublishedLocalPRGRouteContract`, and `FormulaCircuitPublishedLowerBoundContract`.

`BridgeToPpolyDAG.lean` is honest and minimal: it proves that if one supplies `VerifiedNPDAGLowerBoundSource`, then `NP_not_subset_PpolyDAG` and then `P_ne_NP` follow by existing pnp3 interfaces. It does **not** construct such a source from the MCSP/AC0[p]/formula pipeline. Therefore the audited area is mostly infrastructure plus conditional theorem surfaces, not mainline P-vs-NP progress by itself.

## 3. Pipeline diagram

```text
BasicCircuitClasses
  ├─ CircuitFamilyClass / SizeLowerBound / NotInClass
  └─ ClosedUnderInputMasking

TruthTableMCSP
  ├─ TruthTable n := BitVec (tableLen n)
  ├─ treeCircuitClass from pnp3 partial MCSP model
  └─ MCSPPredicate / treeMCSPPredicate

CoinProblem
  ├─ product Bernoulli weights and acceptanceProbability
  ├─ CoinProblemInstance / SolvesCoinProblem
  └─ BoundedClassSolvesCoinProblem / CircuitCoinDistinguisherFamily

CoinMaskingTranslation
  ├─ exact finite expectation/averaging lemmas
  ├─ MaskingBiasParams / MaskingPushforwardFacts
  └─ CoinMaskingTranslationFacts + bestMaskForCircuit

MCSPCoinReduction + MCSP_LocalPRG_Transfer
  ├─ ImplementedThresholdOracle / HalfVsFairMCSPCoinReductionWitness
  ├─ exactTreeMCSPThresholdDecision / exactTreeMCSPThresholdLanguage
  ├─ treeMCSPCountRatio / Shannon-counting transfer
  └─ sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer

AC0[p] route
  AC0pCoinLowerBound
    └─ AC0pHalfVsFairCoinLowerBoundContract (published lower-bound contract)
  MCSPCoinReductionContract
    └─ HalfVsFairMCSPCoinReductionContract / rejection and masking variants
  MCSP_AC0p_Final
    └─ MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction
  MCSP_AC0p_Quantitative
    └─ quantitative/envelope variants
  AC0pCoinAsymptotic + AC0pSuperPolynomialBridge + AC0pAsymptoticBridge
    └─ not-in-AC0[p] statements for abstract pnp4 `InAC0p`

Local PRG / formula route
  LocalPRG
    └─ TruthTableLocalPRG + FoolsBounded / OneSidedFoolsBounded
  LocalPRGHardnessSpec
    └─ Published(Local/OneSided)LocalPRGRouteContract → MCSP lower bound
  FormulaCircuitTargetModel
    └─ concrete formulaCircuitFamilyClass wrapper
  FormulaCircuitPublishedLowerBound
    └─ FormulaCircuitPublishedLowerBoundContract → exact formula MCSP lower bound
  MCSP_Formula_Final + MCSP_Formula_Theorem2Quantitative
    └─ CKLM theorem-facing contract wrappers
  FormulaCircuitAsymptotic
    └─ no-PpolyFormula bridge if an extra growth hypothesis holds;
       current encoded CKLM envelope has kernel-checked no-go theorems

Final pnp3 bridge
  BridgeToPpolyDAG
    └─ VerifiedNPDAGLowerBoundSource
        → NP_not_subset_PpolyDAG
        → P_ne_NP

Missing arrow:
  No theorem in this directory constructs `VerifiedNPDAGLowerBoundSource` from the
  AC0[p], local-PRG, formula, or MCSP finite-slice lower-bound pipeline.
```

## 4. Files audited

All 24 files in `pnp4/Pnp4/AlgorithmsToLowerBounds/` were inspected. I read the bridge and final files in detail, read theorem/structure signatures and main proof shapes for every file, and searched all files for hard-payload, refuted/vacuous/legacy, and hidden-payload patterns.

| File | Approximate role | Inspection depth | Reason if not fully read proof-by-proof |
|---|---|---:|---|
| `AC0pAsymptoticBridge.lean` | Converts eventual quasi-polynomial lower bounds into `¬ InAC0p`. | Read structurally; key theorems checked. | Small file; proof bodies are straightforward wrappers. |
| `AC0pCoinAsymptotic.lean` | Asymptotic language for AC0[p] coin route and polynomial-family exclusion. | Read structurally; key growth proof shape checked. | Arithmetic details skimmed after identifying theorem statements. |
| `AC0pCoinLowerBound.lean` | Abstract AC0[p] model and coin lower-bound contract. | Read fully enough for contract fields and theorem. | Small interface file. |
| `AC0pSuperPolynomialBridge.lean` | Pointwise quasi-polynomial lower bound to `¬ InAC0p`. | Read structurally. | Simple bridge. |
| `AsymptoticSizeLowerBound.lean` | Eventual lower-bound version of super-polynomial bridge. | Read structurally. | Small arithmetic bridge. |
| `BasicCircuitClasses.lean` | Core pnp4 circuit-class interface. | Read fully. | Foundational local interface. |
| `BridgeToPpolyDAG.lean` | Final bridge from explicit NP DAG source to pnp3 targets. | Read fully and in detail. | Critical trust-adjacent file. |
| `CoinMaskingTranslation.lean` | Finite product-bias masking and averaging lemmas. | Read structurally; key structures and `Classical.choose` use checked. | Large probability-algebra file; did not rederive every inequality. |
| `CoinProblem.lean` | Coin-problem probabilities, solvers, and class-solver notions. | Read structurally; main definitions/theorems checked. | Many elementary probability lemmas; no hidden final payload found. |
| `FormulaCircuitAsymptotic.lean` | Formula asymptotic bridge, including CKLM-envelope no-go. | Read key theorem bodies and statements. | Arithmetic no-go proof inspected at high level, not independently rederived. |
| `FormulaCircuitPublishedLowerBound.lean` | Published formula slice lower-bound shortcut contract and consequences. | Read fully enough for contract risk. | Medium file. |
| `FormulaCircuitTargetModel.lean` | Concrete formula-family target model and PRG-route specializations. | Read structurally. | Wrapper file. |
| `Growth.lean` | Growth predicates and quasi-polynomial lower schedule. | Read structurally. | Small arithmetic definitions. |
| `LocalPRG.lean` | Truth-table local PRG and fooling definitions. | Read structurally. | Probability helper proofs skimmed. |
| `LocalPRGHardnessSpec.lean` | Published local-PRG contract to MCSP lower-bound compiler. | Read fully enough for theorem chain. | Medium bridge. |
| `MCSPCoinReduction.lean` | Threshold-oracle reduction witness from MCSP to coin solving. | Read structurally. | Small contract/witness file. |
| `MCSPCoinReductionContract.lean` | Large coin/MCSP/masking reduction contract library. | Read structurally; important structure fields and theorem surfaces checked. | 1419 lines; did not inspect every proof body. |
| `MCSP_AC0p_Final.lean` | Final AC0[p] finite-slice lower-bound theorem wrappers. | Read fully. | Critical final theorem surface. |
| `MCSP_AC0p_Quantitative.lean` | Quantitative/envelope AC0[p] contract and final wrappers. | Read structurally; key final theorems checked. | Arithmetic envelope details skimmed. |
| `MCSP_Formula_Final.lean` | Final formula finite-slice lower-bound theorem wrappers. | Read fully. | Critical final theorem surface. |
| `MCSP_Formula_Theorem2Quantitative.lean` | CKLM theorem-2 quantitative wrappers and local-PRG source contract. | Read structurally. | Mostly contract adapters. |
| `MCSP_LocalPRG_Transfer.lean` | Local PRG transfer to exact tree-MCSP lower bound. | Read structurally; main transfer theorem bodies checked. | 715 lines; arithmetic/probability details not fully rederived. |
| `SuperPolynomialBridge.lean` | Pointwise lower bounds to `¬ HasPolynomialSizeFamily`. | Read structurally. | Small bridge. |
| `TruthTableMCSP.lean` | Truth-table MCSP predicate definitions. | Read fully. | Small core definition file. |

## 5. File-by-file audit

### `BasicCircuitClasses.lean`

Defines the local pnp4 `BitVecLanguage`, `CircuitFamilyClass`, masking primitives, `ClosedUnderInputMasking`, `NonuniformComputes`, `SizeLowerBound`, and `NotInClass`. These are harmless, reusable interfaces; they do not mention pnp3 `NP`, `PpolyDAG`, `ResearchGapWitness`, or final endpoints.

Key declarations: `CircuitFamilyClass`, `ClosedUnderInputMasking`, `NonuniformComputes`, `SizeLowerBound`, `NotInClass`.

### `TruthTableMCSP.lean`

Defines `TruthTable n` as a pnp3 bit-vector of length `tableLen n`, wraps the existing pnp3 partial MCSP tree-circuit model as `treeCircuitClass`, and defines `MCSPPredicate`/`treeMCSPPredicate`. The only legacy/partial hit is the import/comment referencing `Models.Model_PartialMCSP`; it is used as a concrete tree-circuit model, not as a refuted route.

Key declarations: `treeCircuitClass`, `truthTableFunction`, `ComputesTruthTable`, `circuitComplexityLE`, `MCSPPredicate`, `treeMCSPPredicate`, `treeMCSPPredicate_mono`.

### `CoinProblem.lean`

Provides finite Bernoulli product weights over bit-vectors, acceptance probabilities, coin-problem instances, solver predicates, and class-bounded solver predicates. The proofs are ordinary finite-probability and monotonicity/congruence facts; the noncomputable definitions are finite sums/propositions, not payload providers.

Key declarations: `productBiasWeight`, `acceptanceProbability`, `CoinProblemInstance`, `acceptanceGap`, `SolvesCoinProblem`, `CoinDistinguisherFamily`, `ClassSolvesCoinProblem`, `BoundedClassSolvesCoinProblem`, `CircuitCoinDistinguisherFamily`.

### `CoinMaskingTranslation.lean`

Formalizes the finite masking translation: expected product bias, masked acceptance averages, bias-parameter algebra, pushforward facts, mask-averaging, and extraction of a best/fixed mask. This contains the main `Classical.choose` hotspot (`bestMaskForCircuit`), but it chooses a maximum over finite `BitVec`s from `exists_max_bitVec_rat`; it is standard finite maximization infrastructure, not a hidden complexity-theoretic witness.

Key declarations: `MaskingBiasParams`, `MaskingPushforwardFacts`, `MaskAveragingContract`, `CoinMaskingTranslationFacts`, `CoinMaskingClassTranslationFacts`, `bestMaskForCircuit`, `source_advantage_le_bestMask_fixed_advantage`.

### `MCSPCoinReduction.lean`

Defines the thresholded MCSP oracle/witness surface used to turn a threshold oracle into a half-vs-fair coin distinguisher. This is a reduction interface: it does not prove the published distribution/masking facts on its own.

Key declarations: `ThresholdOracle`, `ImplementedThresholdOracle`, `HalfVsFairMCSPCoinReductionWitness`, plus helper theorems connecting witness oracles to `SolvesCoinProblem`.

### `MCSP_LocalPRG_Transfer.lean`

Contains the strongest local finite proof work in the directory. It proves the fair-distribution equivalence between coin acceptance and uniform truth-table acceptance, defines exact threshold decisions/languages, proves that local PRG easy-image plus one-sided fooling and Shannon-counting slack rules out a small implemented threshold oracle, and packages this as a `SizeLowerBound` for `exactTreeMCSPThresholdLanguage`.

Key declarations: `treeMCSPCountRatio`, `exactTreeMCSPThresholdDecision`, `exactTreeMCSPThresholdHardDecision`, `treeMCSPPredicateDecision`, `exactTreeMCSPThresholdLanguage`, `implementedThresholdOracleOfCircuit`, `smallImplementedThresholdOracle_contradiction_of_localPRGTransfer`, `noSmallImplementedThresholdOracle_of_localPRGTransfer`, `sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer`.

### `LocalPRG.lean`

Defines truth-table local PRGs and uniform/seed acceptance probabilities. The fooling definitions are Prop-level contracts over a supplied circuit class, size bound, and epsilon; two-sided fooling is kernel-checked to imply the one-sided inequality consumed by `MCSP_LocalPRG_Transfer`.

Key declarations: `TruthTableLocalPRG`, `FoolsBoundedTruthTableClass`, `OneSidedFoolsBoundedTruthTableClass`, `oneSidedFoolsBoundedTruthTableClass_of_foolsBounded`.

### `LocalPRGHardnessSpec.lean`

Defines the paper-facing local-PRG hardness specification and contracts. It compiles `PublishedOneSidedLocalPRGRouteContract` or `PublishedLocalPRGRouteContract` into exact thresholded MCSP oracle contradictions and `SizeLowerBound` statements. The hard literature content remains a contract field: a PRG family, image-bound proof, fooling proof, and epsilon-slack proof must be supplied.

Key declarations: `LocalPRGHardnessSpec`, `LocalPRGTargetFamilyModel`, `PublishedOneSidedLocalPRGRouteContract`, `PublishedLocalPRGRouteContract`, `thresholdMCSPLanguage`, `thresholdMCSPLowerBound`, `noSmallImplementedThresholdOracle_of_publishedOneSidedLocalPRGRoute`, `MCSP_lower_bound_from_publishedLocalPRGRoute`.

### `AC0pCoinLowerBound.lean`

Defines abstract AC0[p] family models, optional input-masking closure, and half-vs-fair truth-table coin hardness. The published lower-bound content is staged in `AC0pHalfVsFairCoinLowerBoundContract`, whose key field is a size-threshold function plus an exclusion theorem for bounded class solvers.

Key declarations: `AC0pFamilyModel`, `AC0pFamilyModelWithMasking`, `AC0pCircuitClass`, `HalfVsFairTruthTableCoinHardness`, `AC0pHalfVsFairCoinLowerBoundContract`, `AC0pHalfVsFairCoinLowerBoundContract.excludes_small_solver`.

### `MCSPCoinReductionContract.lean`

This is the large adapter library connecting adjacent-bias MCSP profiles, masking translation, half-vs-fair acceptance/rejection contracts, and AC0[p] lower-bound contradictions. Much of it is honest staging: structures package distribution facts, masking setup facts, or reduction contracts; theorems then derive solver contradictions or `HalfVsFairMCSPCoinReductionContract` values from those facts.

Key declarations: `HalfVsFairMCSPCoinAcceptanceProfile`, `HalfVsFairMCSPCoinRejectionProfile`, `HalfVsFairMCSPCoinReductionContract`, `HalfVsFairMCSPCoinRejectionContract`, `HalfVsFairBiasedLowComplexityMassFacts`, `AdjacentBiasMCSPThresholdSeparationFacts`, `CoinDistinguisherToHalfVsFairTranslationContract`, `CoinMaskingTranslationSetup`, `CoinTranslationPreservesClass`, `false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision`, `HalfVsFairMCSPCoinReductionContract.of_distributionFacts`, `HalfVsFairMCSPCoinRejectionContract.of_biasedLowComplexityMassFacts`, `halfVsFairMCSPCoinLanguage`, `halfVsFairMCSPCoinLowerBound`, `HalfVsFairMCSPCoinReductionContract.toWitness`.

### `MCSP_AC0p_Final.lean`

Provides final finite-slice AC0[p] route wrappers. Given an `AC0pHalfVsFairCoinLowerBoundContract`, a prime modulus, and either a reduction witness or `HalfVsFairMCSPCoinReductionContract`, it proves no small implemented threshold oracle exists and derives `SizeLowerBound` for `exactTreeMCSPThresholdLanguage` / `halfVsFairMCSPCoinLanguage`.

Key declarations: `noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound`, `smallCircuit_contradiction_of_AC0pCoinLowerBound`, `sizeLowerBound_exactTreeMCSPThresholdLanguage_of_AC0pCoinLowerBound`, `MCSP_lower_bound_from_AC0pCoinLowerBound`, `MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction`, `noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound_and_reduction`.

### `MCSP_AC0p_Quantitative.lean`

Adds concrete-looking quantitative schedules/envelopes for the AC0[p] coin route and adapters from published envelope contracts to finite-slice lower bounds. The file does not prove the published lower bound from scratch; `AC0pCoinPublishedExpLowerBoundContract` and `AC0pHalfVsFairCoinQuantitativeContract` package the hard lower-bound data.

Key declarations: `ac0pCoinLowerEnvelope`, `EventuallyAtLeastAC0pCoinLowerEnvelope`, `AC0pCoinPublishedHalfVsFairRegime`, `AC0pHalfVsFairCoinQuantitativeContract`, `AC0pCoinPublishedExpLowerBoundContract`, `AC0pCoinQuantitativeLanguage`, `AC0pCoinQuantitativeLowerBound`, `MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract_and_reduction`, `noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract_and_reduction`.

### `AC0pSuperPolynomialBridge.lean`

Defines `InAC0p` for the abstract pnp4 AC0[p] model and converts per-depth quasi-polynomial `SizeLowerBound` data into `¬ InAC0p`. This is a class-separation bridge only inside the pnp4 abstract model; it is not a pnp3 `PpolyDAG` bridge.

Key declarations: `InAC0p`, `not_depth_d_AC0p_of_quasiPoly_lowerBound`, `not_in_AC0p_of_depthwise_quasiPoly_lowerBound`, `AC0pQuasiPolynomialLowerBoundContract`, `not_in_AC0p_from_quasiPolynomial_contract`.

### `AC0pAsymptoticBridge.lean`

The eventual version of the AC0[p] bridge. It takes `EventuallySizeLowerBound` data and proves depthwise and all-depth `¬ InAC0p`; the contract form remains conditional on per-depth eventual lower-bound fields.

Key declarations: `not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound`, `not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound`, `AC0pAsymptoticQuasiPolynomialLowerBoundContract`, `not_in_AC0p_from_asymptotic_quasiPolynomial_contract`.

### `AC0pCoinAsymptotic.lean`

Builds one asymptotic language from the half-vs-fair MCSP coin reduction and proves that the published-envelope AC0[p] coin route can exclude polynomial-size families / `InAC0p` when the growth schedule beats polynomial bounds on suitable truth-table lengths. It also proves the concrete `ac0pCoinLowerEnvelope` beats every polynomial bound at arbitrarily large table lengths for the encoded envelope.

Key declarations: `halfVsFairMCSPCoinAsymptoticLanguage`, `BeatsEveryPolynomialSizeBoundAtSomeTableLength`, `BeatsEveryPolynomialSizeBoundAtArbitrarilyLargeTableLengths`, `ac0pCoinLowerEnvelope_beatsEveryPolynomial_at_arbitrarilyLarge_tableLengths`, `not_hasPolynomialSizeFamily_halfVsFairMCSPCoinAsymptoticLanguage`, `not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract`.

### `Growth.lean`

Defines the generic growth predicates and schedules used by bridge files. It is infrastructure only and carries no complexity lower bound by itself.

Key declarations: `PolynomialUpperBound`, `SuperPolynomialGrowth`, `QuasiPolyLower` and supporting arithmetic facts.

### `SuperPolynomialBridge.lean`

Converts a pointwise `SizeLowerBound` with super-polynomial growth into `¬ HasPolynomialSizeFamily`, with a specialized quasi-polynomial version. This is a reusable finite-language/circuit-class bridge, not a pnp3 complexity-class bridge.

Key declarations: `HasPolynomialSizeFamily`, `not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound`, `not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound`.

### `FormulaCircuitTargetModel.lean`

Specializes the local-PRG target-family model to the in-repo formula circuit class and provides one-sided/two-sided route abbreviations. It is an adapter layer from generic local-PRG contracts to concrete formula-family lower-bound statements.

Key declarations: `formulaCircuitFamilyClass`, `formulaCircuitTargetModel`, `FormulaCircuitPublishedOneSidedLocalPRGRouteContract`, `FormulaCircuitPublishedLocalPRGRouteContract`, formula-specific `noSmall...` and `formulaCircuit_MCSP_lower_bound...` theorems.

### `FormulaCircuitPublishedLowerBound.lean`

Defines a smaller published lower-bound shortcut contract for formula circuits after forgetting PRG internals. It is useful but riskier than the PRG-source contract because `FormulaCircuitPublishedLowerBoundContract.sliceLowerBound` directly packages the exact slice lower bound as a field.

Key declarations: `FormulaCircuitSliceSpec`, `LocalPRGHardnessSpec.toFormulaCircuitSliceSpec`, `formulaCircuitThresholdLanguage`, `formulaCircuitThresholdLowerBound`, `FormulaCircuitPublishedLowerBoundContract`, `formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract`, `noSmallImplementedThresholdOracle_of_publishedLowerBoundContract`, `formulaCircuitPublishedLowerBoundContract_of_publishedLocalPRGRoute`.

### `MCSP_Formula_Final.lean`

Provides the theorem-facing CKLM formula-route wrappers. From either a local-PRG route contract or the smaller theorem-2 lower-bound contract, it proves no small implemented threshold oracle and a `SizeLowerBound` for `CKLMFormulaCircuitLanguage` at a fixed slice.

Key declarations: `CKLMFormulaCircuitHardnessSpec.toFormulaCircuitSliceSpec`, `CKLMFormulaCircuitLanguage`, `CKLMFormulaCircuitLowerBound`, `CKLMFormulaCircuitPublishedTheorem2Contract.ofRoute`, `noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitRoute`, `formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2Contract`.

### `MCSP_Formula_Theorem2Quantitative.lean`

Adds CKLM theorem-2 quantitative envelopes and adapters from local-PRG source specs/contracts to theorem-facing contracts. This is mostly typed staging: it can compile a source contract into exact formula lower bounds, but the hard source contract itself must be supplied.

Key declarations: `cklmFormulaTheorem2LowerEnvelope`, `EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope`, `CKLMFormulaCircuitTheorem2Hardness`, `CKLMFormulaCircuitLocalPRGSourceSpec`, `CKLMFormulaCircuitLocalPRGSourceContract`, `CKLMFormulaCircuitPublishedTheorem2QuantitativeContract`, `formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2QuantitativeContract`, `formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitLocalPRGSource`.

### `FormulaCircuitAsymptotic.lean`

Attempts to bridge finite formula MCSP slice lower bounds to pnp3 `¬ PpolyFormula` for an asymptotic language, under a growth hypothesis that beats every pnp3 polynomial witness on some truth-table length. Crucially, it proves `not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope` and `not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope`, so the currently encoded CKLM theorem-2 envelope cannot satisfy the required growth condition; routes depending on that condition are diagnostic/vacuous for this envelope.

Key declarations: `BeatsEveryPpolyBoundAtSomeTableLength`, `BeatsEveryPpolyBoundFrequentlyAtSomeTableLength`, `not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope`, `no_uniform_cklmEnvelopeFrequentEscape`, `formulaCircuitAsymptoticLanguageOfSliceSpec`, `no_PpolyFormula_of_formulaCircuitPublishedLowerBoundContract_and_growth`, `formulaCircuitAsymptoticLanguage`, `no_PpolyFormula_of_CKLMFormulaCircuitLocalPRGSource_and_growth`.

### `BridgeToPpolyDAG.lean`

Defines `VerifiedNPDAGLowerBoundSource` and proves two downstream facts: such a source gives `NP_not_subset_PpolyDAG`, and then gives pnp3 `P_ne_NP` using `P_ne_NP_of_nonuniform_dag_separation` plus `proved_P_subset_PpolyDAG_internal`. It does not import the AC0[p], formula, or local-PRG final modules and does not construct a source from them.

Key declarations: `DagLanguage`, `VerifiedNPDAGLowerBoundSource`, `NP_not_subset_PpolyDAG_of_verified_source`, `P_ne_NP_of_verified_source`.

## 6. Top-level theorem / structure inventory

| Declaration | File | Type/signature summary | Classification | Hard payload dependency |
|---|---|---|---|---|
| `CircuitFamilyClass` | `BasicCircuitClasses.lean` | family/eval/size interface | canonical | none |
| `SizeLowerBound` | `BasicCircuitClasses.lean` | exact per-length lower-bound predicate | canonical | none |
| `ClosedUnderInputMasking` | `BasicCircuitClasses.lean` | mask circuit without size increase | conditional interface | none |
| `treeCircuitClass` | `TruthTableMCSP.lean` | wrapper for pnp3 tree model | canonical adapter | depends on pnp3 partial MCSP model, not final payload |
| `treeMCSPPredicate` | `TruthTableMCSP.lean` | truth-table MCSP predicate for tree circuits | canonical | none |
| `CoinProblemInstance` | `CoinProblem.lean` | low/high bias + advantage contract | canonical | none |
| `SolvesCoinProblem` | `CoinProblem.lean` | Prop that an algorithm distinguishes a coin instance | canonical | none |
| `BoundedClassSolvesCoinProblem` | `CoinProblem.lean` | class has bounded-size solver | canonical/conditional | none |
| `MaskingBiasParams` | `CoinMaskingTranslation.lean` | bias algebra package | canonical infrastructure | none |
| `MaskingPushforwardFacts` | `CoinMaskingTranslation.lean` | facts about masked source/target biases | staged Prop | none |
| `CoinMaskingTranslationFacts` | `CoinMaskingTranslation.lean` | averaging facts for masking | staged Prop / honest staging | none |
| `bestMaskForCircuit` | `CoinMaskingTranslation.lean` | finite argmax mask | canonical noncomputable infrastructure | finite `Classical.choose`; no final payload |
| `ImplementedThresholdOracle` | `MCSPCoinReduction.lean` | circuit plus exact threshold-decision correctness | canonical interface | none |
| `HalfVsFairMCSPCoinReductionWitness` | `MCSPCoinReduction.lean` | threshold oracle solving half-vs-fair coin | staged witness | no pnp3 hard payload |
| `TruthTableLocalPRG` | `LocalPRG.lean` | generator plus easy-image proof | staged interface | no final payload |
| `FoolsBoundedTruthTableClass` | `LocalPRG.lean` | two-sided fooling Prop | staged Prop | no final payload |
| `OneSidedFoolsBoundedTruthTableClass` | `LocalPRG.lean` | one-sided fooling Prop | staged Prop | no final payload |
| `smallImplementedThresholdOracle_contradiction_of_localPRGTransfer` | `MCSP_LocalPRG_Transfer.lean` | local PRG + fooling + slack contradicts small oracle | conditional theorem | depends on supplied PRG/fooling/slack, not final payload |
| `sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer` | `MCSP_LocalPRG_Transfer.lean` | converts transfer contradiction into `SizeLowerBound` | conditional theorem | supplied PRG/fooling/slack |
| `LocalPRGHardnessSpec` | `LocalPRGHardnessSpec.lean` | threshold/size/epsilon schedule with slack | staged Prop field | no final payload |
| `PublishedLocalPRGRouteContract` | `LocalPRGHardnessSpec.lean` | PRG family + image + fooling fields | staged Prop / potential wrapper risk | no final payload, but hard PRG proof packaged |
| `MCSP_lower_bound_from_publishedLocalPRGRoute` | `LocalPRGHardnessSpec.lean` | contract → exact MCSP `SizeLowerBound` | conditional theorem | depends on route contract |
| `AC0pFamilyModel` | `AC0pCoinLowerBound.lean` | abstract depth/modulus-indexed class | canonical interface | none |
| `AC0pHalfVsFairCoinLowerBoundContract` | `AC0pCoinLowerBound.lean` | size-bound plus no bounded solver theorem | staged Prop / potential wrapper risk | packages hard AC0[p] lower bound |
| `HalfVsFairMCSPCoinReductionContract` | `MCSPCoinReductionContract.lean` | per-slice reduction to coin witness | staged interface | packages hard reduction data |
| `MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction` | `MCSP_AC0p_Final.lean` | AC0[p] lower-bound contract + reduction → exact MCSP `SizeLowerBound` | conditional theorem | depends on lower-bound and reduction contracts |
| `AC0pCoinPublishedExpLowerBoundContract` | `MCSP_AC0p_Quantitative.lean` | published envelope contract | staged Prop / potential wrapper risk | packages published lower bound |
| `not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract` | `AC0pCoinAsymptotic.lean` | published AC0[p] contract + reduction → `¬ InAC0p` | conditional theorem | no final pnp3 hard payload |
| `FormulaCircuitPublishedLowerBoundContract` | `FormulaCircuitPublishedLowerBound.lean` | direct exact formula slice lower-bound field | staged Prop / wrapper risk | packages lower-bound theorem |
| `formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2Contract` | `MCSP_Formula_Final.lean` | theorem-2 contract → exact formula `SizeLowerBound` | conditional theorem | depends on theorem-2 contract |
| `CKLMFormulaCircuitLocalPRGSourceContract` | `MCSP_Formula_Theorem2Quantitative.lean` | local-PRG source contract for CKLM wrapper | staged Prop / honest staging | no final payload |
| `not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope` | `FormulaCircuitAsymptotic.lean` | current CKLM envelope cannot beat every polynomial witness | refuted-route guardrail theorem | none |
| `no_PpolyFormula_of_formulaCircuitPublishedLowerBoundContract_and_growth` | `FormulaCircuitAsymptotic.lean` | contract + extra growth → `¬ PpolyFormula` | conditional / weak route | depends on `PpolyFormula`, not `PpolyDAG` |
| `VerifiedNPDAGLowerBoundSource` | `BridgeToPpolyDAG.lean` | NP language plus `¬ PpolyDAG` proof | canonical final source interface | field is hard payload |
| `NP_not_subset_PpolyDAG_of_verified_source` | `BridgeToPpolyDAG.lean` | source → `NP_not_subset_PpolyDAG` | canonical conditional bridge | depends on `VerifiedNPDAGLowerBoundSource` |
| `P_ne_NP_of_verified_source` | `BridgeToPpolyDAG.lean` | source → `P_ne_NP` | canonical conditional bridge | depends on `VerifiedNPDAGLowerBoundSource` and pnp3 internal `P⊆PpolyDAG` |

No declaration in the audited directory depends on `ResearchGapWitness` or `SearchMCSPMagnificationContract`. Only `BridgeToPpolyDAG.lean` mentions `VerifiedNPDAGLowerBoundSource` and `NP_not_subset_PpolyDAG`.

## 7. Kernel-checked content

The following are genuinely kernel-checked, conditional on their explicit hypotheses:

1. **Finite probability algebra.** `CoinProblem.lean`, `LocalPRG.lean`, and `CoinMaskingTranslation.lean` prove finite-sum facts such as product-bias nonnegativity/normalization, acceptance probability complement/monotonicity lemmas, masking pushforward equations, and finite averaging/maximum facts.
2. **Truth-table MCSP predicates.** `TruthTableMCSP.lean` defines MCSP predicates against the existing pnp3 tree-circuit class and proves monotonicity in the size threshold.
3. **Local PRG transfer.** `MCSP_LocalPRG_Transfer.lean` proves that if a threshold oracle is small, the PRG image is easy under the oracle threshold, the PRG one-sided fools the small class, and `epsilon < 1 - treeMCSPCountRatio`, then contradiction follows; it also proves the corresponding exact thresholded `SizeLowerBound`.
4. **Published-local-PRG compiler.** `LocalPRGHardnessSpec.lean` proves that a supplied published PRG route contract yields no small implemented threshold oracle and an exact thresholded MCSP `SizeLowerBound`.
5. **AC0[p] coin compiler.** `MCSP_AC0p_Final.lean` proves that a supplied AC0[p] coin lower-bound contract plus a supplied MCSP coin-reduction witness/contract yields no small implemented threshold oracle and an exact thresholded MCSP `SizeLowerBound`.
6. **Quantitative AC0[p] wrappers.** `MCSP_AC0p_Quantitative.lean` proves that the quantitative/envelope contracts specialize to the final AC0[p] lower-bound wrappers.
7. **Asymptotic AC0[p] bridge.** `AC0pCoinAsymptotic.lean`, `AC0pSuperPolynomialBridge.lean`, and `AC0pAsymptoticBridge.lean` prove that suitable lower-bound/growth hypotheses imply `¬ HasPolynomialSizeFamily` or `¬ InAC0p` for the abstract pnp4 AC0[p] model.
8. **Formula route wrappers.** `FormulaCircuitPublishedLowerBound.lean`, `MCSP_Formula_Final.lean`, and `MCSP_Formula_Theorem2Quantitative.lean` prove that formula lower-bound or local-PRG source contracts imply exact formula `SizeLowerBound`/no-small-oracle theorems.
9. **Formula-asymptotic no-go.** `FormulaCircuitAsymptotic.lean` proves that the current CKLM theorem-2 envelope cannot satisfy the polynomial-beating growth condition needed for the `PpolyFormula` asymptotic bridge.
10. **Final pnp3 bridge, conditional on hard source.** `BridgeToPpolyDAG.lean` proves `VerifiedNPDAGLowerBoundSource → NP_not_subset_PpolyDAG` and `VerifiedNPDAGLowerBoundSource → P_ne_NP`; the source itself contains the hard `¬ PpolyDAG` proof as a field.

## 8. Staged / placeholder / Prop-only content

The staged content is mostly honest, but several structures are wrapper risks if future workers treat them as proved literature theorems rather than obligations.

| Declaration | Kind | Assessment |
|---|---|---|
| `AC0pHalfVsFairCoinLowerBoundContract` | structure with lower-bound/exclusion field | Honest staging of published AC0[p] coin lower bound; potential wrapper risk if instantiated without a real proof. |
| `HalfVsFairMCSPCoinReductionContract` / `HalfVsFairMCSPCoinRejectionContract` | structures carrying per-slice reduction data | Honest staging; reduction facts are not automatic. |
| `HalfVsFairBiasedLowComplexityMassFacts`, `AdjacentBiasMCSPThresholdSeparationFacts`, `CoinMaskingTranslationSetup` | structures with probability/masking/separation fields | Honest staging; hard distribution facts must be supplied externally or proved separately. |
| `TruthTableLocalPRG` | generator plus easy-image field | Harmless interface if generator is explicit; easy-image proof can be hard but local. |
| `FoolsBoundedTruthTableClass` / `OneSidedFoolsBoundedTruthTableClass` | Prop definitions | Staged PRG fooling property; central hard theorem if supplied. |
| `LocalPRGHardnessSpec` | structure with epsilon-slack field | Harmless schedule interface; slack is a real arithmetic obligation. |
| `PublishedOneSidedLocalPRGRouteContract` / `PublishedLocalPRGRouteContract` | structures with PRG/fooling fields | Potential wrapper risk: carries the full PRG lower-bound theorem as fields. |
| `FormulaCircuitPublishedLowerBoundContract` | structure with direct `sliceLowerBound` field | Higher wrapper risk than source route; can hide the exact theorem unless provenance is tracked. |
| `CKLMFormulaCircuitLocalPRGSourceContract` | structure compiling source contract to route | Honest staging if source/provenance is audited. |
| `AC0pCoinPublishedExpLowerBoundContract` | structure for published envelope lower bound | Potential wrapper risk; packages published lower-bound theorem. |
| `VerifiedNPDAGLowerBoundSource` | structure with `inNP` and `notInPpolyDAG` fields | Canonical hard-source interface; not a placeholder, but its `notInPpolyDAG` field is exactly the missing mainline payload. |

I did not find `TODO` or literal `placeholder` markers in the audited directory. Staging is represented by explicit structure fields rather than `sorry`/`axiom`.

## 9. Refuted / vacuous / legacy route check

Search patterns used: `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `weak route`, `Legacy`, `_Partial`, `TODO`, and `placeholder`.

Findings:

- No `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `Legacy`, `TODO`, or literal `placeholder` names were found in the audited directory.
- Two hits were for `Model_PartialMCSP` in `TruthTableMCSP.lean`: one import and one comment. This is legacy/partial infrastructure reuse, not a refuted route endpoint.
- `FormulaCircuitAsymptotic.lean` contains kernel-checked no-go theorems for the current CKLM envelope. These are not named `RefutedRoute`, but they function as guardrails: any route requiring `BeatsEveryPpolyBoundAtSomeTableLength (cklmFormulaTheorem2LowerEnvelope c)` is refuted for the encoded envelope.
- The formula asymptotic bridge to `¬ PpolyFormula` is a weak side track relative to P-vs-NP mainline because it targets formula circuits, not `PpolyDAG`.

## 10. Hidden payload / Rule 16 check

Search patterns used: `class`, `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `Classical.choose`, and `noncomputable def`.

Summary interpretation:

- No `opaque`, `default_instance`, `attribute [instance]`, or suspicious `Fact` payload channel was found in the audited directory.
- `class` occurrences are overwhelmingly comments or the `CircuitFamilyClass` naming convention, not Lean typeclass declarations.
- `instance` occurrences are mostly ordinary names such as `CoinDistinguisherFamily.instance` and `HalfVsFairTruthTableCoinHardness.instance`, not typeclass instances.
- `noncomputable def` occurrences define finite sums, finite acceptance probabilities, exact languages, or noncomputable adapters. They are mostly harmless infrastructure, but they should not be confused with constructive algorithms.
- `Classical.choose` occurs in `CoinMaskingTranslation.lean` inside `bestMaskForCircuit`/proofs via a finite maximum over masks. Classification: **harmless infrastructure / finite maximization**, not a hidden final witness.
- `VerifiedNPDAGLowerBoundSource` is not hidden: it openly exposes the hard payload field `notInPpolyDAG`. Classification: **canonical hard-source interface**, forbidden to instantiate with wrappers or vacuous assumptions.

## 11. Barrier relevance

| Barrier / theme | Status in audited area |
|---|---|
| Natural proofs | Nothing substantive; no natural-proofs theorem/interface found. |
| Relativization | Nothing. |
| Algebrization | Nothing. |
| Locality | Typed interface/staged Prop via local PRG structures and fooling properties; not a barrier theorem. |
| Hardwiring | Indirectly relevant in asymptotic bridges to polynomial-size nonuniform families/formulas; no explicit anti-hardwiring theorem beyond exact lower-bound predicates. |
| Support-cardinality-only | Relevant in `treeMCSPCountRatio` / Shannon-counting transfer; actual finite theorem in local PRG transfer. |
| Syntax-only filters | `treeCircuitClass` and `formulaCircuitFamilyClass` are syntax/model adapters; no provenance filter. |
| Normalization filters | Nothing. |
| Search-to-decision | Nothing for `SearchMCSPMagnificationContract`; exact threshold oracles are decision predicates only. |
| MCSP / magnification | Actual MCSP finite-slice infrastructure; no `SearchMCSPMagnificationContract` and no compression-magnification bridge to `VerifiedNPDAGLowerBoundSource`. |
| AC0[p] lower bounds | Typed interfaces and conditional theorem wrappers; published theorem staged as contracts. |
| Formula lower bounds | Typed interfaces and conditional theorem wrappers; formula-asymptotic route has a no-go for current CKLM envelope. |

## 12. Reuse map

Safe to reuse:

- `CircuitFamilyClass`, `SizeLowerBound`, and `ClosedUnderInputMasking` as local pnp4 infrastructure.
- `TruthTable`, `treeMCSPPredicate`, `exactTreeMCSPThresholdDecision`, `exactTreeMCSPThresholdLanguage`, and `exactTreeMCSPThresholdLowerBound` for finite truth-table MCSP slice work.
- `CoinProblemInstance`, `SolvesCoinProblem`, and `BoundedClassSolvesCoinProblem` for finite coin-problem reductions.
- `CoinMaskingTranslationFacts` and the masking algebra when paired with explicit distribution facts.
- `smallImplementedThresholdOracle_contradiction_of_localPRGTransfer` and `sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer` for local PRG → MCSP finite-slice transfer.
- `MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction` for conditional AC0[p] finite-slice consequences.
- `formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2Contract` for conditional formula finite-slice consequences.
- `NP_not_subset_PpolyDAG_of_verified_source` and `P_ne_NP_of_verified_source` only after an honest `VerifiedNPDAGLowerBoundSource` is supplied.

Avoid or quarantine:

- Do not treat `FormulaCircuitPublishedLowerBoundContract.sliceLowerBound` as proof unless provenance is audited.
- Do not use `no_PpolyFormula_*_and_growth` routes as P-vs-NP progress; they are formula side tracks and require a growth condition refuted for the current CKLM envelope.
- Do not instantiate `VerifiedNPDAGLowerBoundSource` from restricted AC0[p]/formula/local-PRG lower bounds without a real `PpolyDAG` bridge.
- Do not promote exact thresholded MCSP slice lower bounds to `NP_not_subset_PpolyDAG`; the missing global NP-language and DAG lower-bound bridge is the hard part.

## 13. Gap map

### A. Engineering gaps

1. The directory lacks a consolidated README or machine-readable dependency graph describing the AC0[p]/local-PRG/formula pipeline.
2. Contract wrappers could benefit from explicit naming/provenance comments distinguishing direct theorem-oracle contracts from source-level contracts.
3. Surface tests/audit tests should ensure `BridgeToPpolyDAG` remains the only route in this directory mentioning `NP_not_subset_PpolyDAG`/`VerifiedNPDAGLowerBoundSource`.
4. The import of `Models.Model_PartialMCSP` is safe but should be documented as model reuse, not a partial/refuted route.
5. Direct lower-bound shortcut contracts could be tagged in docs as higher-risk wrapper surfaces.

### B. Formalization gaps

1. No concrete AC0[p] syntax/model instantiates `AC0pFamilyModel` with fully verified closure and published coin lower bounds in this directory.
2. No concrete proof of `HalfVsFairMCSPCoinReductionContract` from raw literature is supplied without staged distribution/masking facts.
3. No concrete local-PRG family with a proved fooling theorem is supplied for the published route contracts.
4. Formula route contracts do not by themselves prove global pnp3 `PpolyFormula` separation unless the extra growth condition is supplied.
5. No adapter turns exact truth-table MCSP slice lower bounds into `VerifiedNPDAGLowerBoundSource`.

### C. Mathematical gaps

1. The mainline gap remains an NP-language lower bound against `PpolyDAG` or a verified compression/magnification route to it.
2. Restricted AC0[p] and formula lower bounds do not imply `PpolyDAG` lower bounds without an additional bridge that is not present here.
3. The current CKLM formula envelope is formally too weak to beat every pnp3 polynomial formula bound; this is a mathematical obstruction for that asymptotic route as encoded.
4. No search-to-decision MCSP magnification theorem is present in this directory.
5. No barrier-bypass theorem for natural proofs/relativization/algebrization is present.

### D. Governance gaps

1. Future PR descriptions may overstate the AC0[p]/formula side tracks as P-vs-NP mainline progress unless the restricted-lower-bound caveat is repeated.
2. `FormulaCircuitPublishedLowerBoundContract` is easy to misuse as a theorem oracle; provenance requirements should be explicit in task prompts.
3. The CKLM no-go result should be referenced in dispatch prompts to prevent duplicate attempts to use the refuted growth condition.
4. `BridgeToPpolyDAG.lean` should remain read-only unless a task explicitly targets the trust-adjacent bridge and includes tests/audit updates.

## 14. End-to-end theorem chain

### AC0[p] finite-slice chain

1. `AC0pHalfVsFairCoinLowerBoundContract model hardness` supplies, for each prime modulus/depth/slice, that no bounded class solver can solve the half-vs-fair coin instance below `sizeBound depth n`.
2. `HalfVsFairMCSPCoinReductionContract hardness` supplies, for each `n`, a thresholded MCSP oracle/reduction witness solving the half-vs-fair coin problem.
3. `MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction` proves a `SizeLowerBound` for `halfVsFairMCSPCoinLanguage reduction n` against `(model.classOf p depth)` with lower bound `halfVsFairMCSPCoinLowerBound reduction n (lowerBound.sizeBound depth n)`.
4. `MCSP_AC0p_Quantitative.lean` specializes the same chain to quantitative/published-envelope contracts.
5. `AC0pCoinAsymptotic.lean` packages the per-slice language into `halfVsFairMCSPCoinAsymptoticLanguage` and proves `¬ InAC0p model p L` from a published envelope contract plus reduction.

Final delivered theorem: conditional `SizeLowerBound` / `¬ InAC0p` for an abstract pnp4 AC0[p] family model. It does **not** bridge to pnp3 `ResearchGapWitness` or `VerifiedNPDAGLowerBoundSource`.

### Formula finite-slice/asymptotic chain

1. `PublishedLocalPRGRouteContract` or `PublishedOneSidedLocalPRGRouteContract` supplies a PRG family, easy-image bound, and fooling theorem.
2. `LocalPRGHardnessSpec.lean` compiles that route into exact thresholded MCSP `SizeLowerBound` statements.
3. `FormulaCircuitTargetModel.lean` specializes the target model to pnp3 formula circuits.
4. `FormulaCircuitPublishedLowerBound.lean` can also skip PRG internals by accepting `FormulaCircuitPublishedLowerBoundContract.sliceLowerBound` directly.
5. `MCSP_Formula_Final.lean` and `MCSP_Formula_Theorem2Quantitative.lean` provide CKLM theorem-facing wrappers.
6. `FormulaCircuitAsymptotic.lean` can derive `¬ PpolyFormula` only if a separate growth condition beats every pnp3 polynomial formula bound; the current CKLM envelope is proved not to satisfy that condition.

Final delivered theorem: conditional finite-slice formula `SizeLowerBound`, and conditional/mostly diagnostic `¬ PpolyFormula` bridge. It does **not** bridge to `NP_not_subset_PpolyDAG`.

### Bridge to pnp3 final target

`BridgeToPpolyDAG.lean` is separate: it starts from `VerifiedNPDAGLowerBoundSource`, not from the AC0[p] or formula final theorems. It proves:

```lean
VerifiedNPDAGLowerBoundSource → NP_not_subset_PpolyDAG
VerifiedNPDAGLowerBoundSource → P_ne_NP
```

There is no theorem of the form:

```lean
MCSP_lower_bound_from_AC0p... → VerifiedNPDAGLowerBoundSource
formulaCircuit_MCSP_lower_bound... → VerifiedNPDAGLowerBoundSource
```

## 15. Quantitative vs asymptotic

- `*_Final` files (`MCSP_AC0p_Final.lean`, `MCSP_Formula_Final.lean`) expose exact finite-slice theorem surfaces: no small implemented threshold oracle and `SizeLowerBound` for a fixed truth-table slice.
- `*_Quantitative` files (`MCSP_AC0p_Quantitative.lean`, `MCSP_Formula_Theorem2Quantitative.lean`) introduce named envelope functions, eventual dominance predicates, and contracts matching published quantitative schedules, then compile them back into the same finite-slice theorem surfaces.
- `AC0pCoinAsymptotic.lean` turns quantitative AC0[p] slice lower bounds plus growth into `¬ HasPolynomialSizeFamily`/`¬ InAC0p` for the abstract pnp4 model.
- `FormulaCircuitAsymptotic.lean` tries the analogous pnp3 formula-family bridge, but also proves the current CKLM envelope fails the needed polynomial-beating growth condition.

## 16. `BridgeToPpolyDAG.lean` detailed audit

`BridgeToPpolyDAG.lean` is short and honest. `VerifiedNPDAGLowerBoundSource` contains exactly three fields: a pnp3 language `L`, a proof `NP L`, and a proof `¬ PpolyDAG L`. `NP_not_subset_PpolyDAG_of_verified_source` constructs the existential pnp3 target directly as `⟨src.L, src.inNP, src.notInPpolyDAG⟩`. `P_ne_NP_of_verified_source` then calls the pnp3 theorem `P_ne_NP_of_nonuniform_dag_separation` with that separation and `proved_P_subset_PpolyDAG_internal`.

This file is a bridge **from** an already verified NP-vs-DAG source; it is not a bridge **from** AC0[p], formula, or local-PRG MCSP lower bounds to such a source. Therefore it is safe to reuse as the canonical endpoint adapter, but it must not be cited as completing the missing restricted-to-DAG bridge.

## 17. Recommended Phase 1+ tasks

### Task 1 — Add a markdown pipeline map for AlgorithmsToLowerBounds

- **Files to touch:** `pnp4/Pnp4/AlgorithmsToLowerBounds/README.md` or `seed_packs/.../docs/A07_pipeline_map.md` if source docs are preferred.
- **Allowed scope:** markdown-only diagram and contract/provenance notes.
- **Forbidden scope:** Lean code edits; endpoint changes; claims of P-vs-NP progress.
- **Expected output:** maintained pipeline map distinguishing finite-slice, asymptotic, and final pnp3 bridge layers.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** optional cross-check with pnp4 frontier audit.
- **Risk level:** low.
- **Type:** markdown-only.

### Task 2 — Add guardrail tests for final-payload mentions in this directory

- **Files to touch:** `scripts/check.sh` or a new audit script if operator permits; possibly `pnp4/Pnp4/Tests/AxiomsAudit.lean` only for theorem surfaces.
- **Allowed scope:** fail if `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, `SourceTheorem`, or `gap_from` appears outside approved bridge files.
- **Forbidden scope:** no theorem implementation; no trust-root edits; no endpoint construction.
- **Expected output:** automated guardrail preventing accidental final-payload promotion from restricted lower-bound modules.
- **Estimated time:** 0.5-1 day.
- **Dependency on other audits:** coordinate with governance/check-script audit.
- **Risk level:** medium because check policy changes can be noisy.
- **Type:** Lean/script infrastructure.

### Task 3 — Provenance labels for direct theorem-oracle contracts

- **Files to touch:** markdown docs or doc-comments in `FormulaCircuitPublishedLowerBound.lean`, `MCSP_AC0p_Quantitative.lean`, and `MCSPCoinReductionContract.lean`.
- **Allowed scope:** documentation/comments only, labeling contracts as source-level vs direct theorem-oracle wrappers.
- **Forbidden scope:** no field changes; no proof changes; no contract weakening/strengthening.
- **Expected output:** clear warning that `sliceLowerBound` and published-envelope fields are obligations, not proved literature imports.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** none.
- **Risk level:** low.
- **Type:** markdown/comment-only.

### Task 4 — Surface-test inventory for public final wrappers

- **Files to touch:** `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`, `pnp4/Pnp4/Tests/AxiomsAudit.lean`.
- **Allowed scope:** add `check_` wrappers / `#print axioms` for already-existing public theorem surfaces if missing.
- **Forbidden scope:** no theorem changes; no new lower-bound claims.
- **Expected output:** test coverage verifies accessibility and axiom hygiene of `MCSP_lower_bound_from_*`, `noSmallImplementedThresholdOracle_*`, and bridge theorems.
- **Estimated time:** 1 day.
- **Dependency on other audits:** should check current test audit to avoid duplication.
- **Risk level:** medium due to potential broad build output.
- **Type:** Lean tests only.

### Task 5 — Quarantine/rename decision for CKLM asymptotic no-go route

- **Files to touch:** operator decision first; possibly markdown docs or theorem names in `FormulaCircuitAsymptotic.lean` if approved.
- **Allowed scope:** clarify names/docs around `not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope` and downstream growth-dependent routes.
- **Forbidden scope:** no attempt to bypass no-go by changing definitions; no trust-root edits; no new final endpoint.
- **Expected output:** dispatch note or docs preventing future workers from reusing the refuted growth condition.
- **Estimated time:** 0.5 day for docs; more if renaming tests is approved.
- **Dependency on other audits:** cross-check with NoGoLog/governance audit.
- **Risk level:** low for docs, medium for renames.
- **Type:** operator decision / markdown or Lean rename-only.

### Task 6 — Audit concrete instantiation status for formula/AC0[p] models

- **Files to touch:** markdown audit report only unless a later implementation is explicitly authorized.
- **Allowed scope:** search outside this directory for existing instantiations of `AC0pFamilyModel`, `FormulaCircuitPublishedLowerBoundContract`, `PublishedLocalPRGRouteContract`, and `VerifiedNPDAGLowerBoundSource`.
- **Forbidden scope:** no implementation; no source edits.
- **Expected output:** de-duplication map showing whether any contracts are already concretely inhabited elsewhere.
- **Estimated time:** 1 day.
- **Dependency on other audits:** A07 plus audits of pnp4 frontier/tests.
- **Risk level:** low.
- **Type:** markdown-only.

## 18. Stop / hold recommendations

- **Hold or downgrade** any planned task claiming the formula CKLM theorem-2 envelope yields `¬ PpolyFormula` through `BeatsEveryPpolyBoundAtSomeTableLength`; the repository currently proves that growth condition false for the encoded envelope.
- **Hold** any task that attempts to construct `VerifiedNPDAGLowerBoundSource` from AC0[p] or formula lower bounds without first specifying a real `PpolyDAG` bridge.
- **Downgrade** AC0[p], formula, local-PRG, and coin-problem tasks to restricted-lower-bound side-track or infrastructure unless they explicitly reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.
- **Do not touch** `BridgeToPpolyDAG.lean` in routine side-track work; it is the critical endpoint adapter and should stay minimal.

## 19. Honest caveats

- I did not rederive every arithmetic/probability proof in `MCSPCoinReductionContract.lean`, `CoinMaskingTranslation.lean`, or `MCSP_LocalPRG_Transfer.lean`; I audited signatures, proof dependencies, and main theorem shapes.
- I did not reconstruct the full import graph outside `pnp4/Pnp4/AlgorithmsToLowerBounds/`.
- I did not inspect every possible instantiation of the contract structures elsewhere in the repository.
- I verified command-level build/check status for the current repo state, but did not run individual `#print axioms` commands for every theorem listed above.
- This audit should be cross-checked with the NoGoLog/governance audits before renaming or quarantining CKLM asymptotic surfaces.

## 20. Commands run

- `find .. -name AGENTS.md -print` → found repository `AGENTS.md` only.
- `git status --short --branch && git rev-parse HEAD` → starting commit `d27b069127f63a3f24ab30d1a91c86c84f8b79c7`, clean branch before creating audit branch.
- `find pnp4/Pnp4/AlgorithmsToLowerBounds -maxdepth 1 -type f -name '*.lean' ... | wc -l` → 24 Lean files found.
- `wc -l $(cat /tmp/a07_files.txt)` → 6687 total lines across the 24 files.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" pnp4/Pnp4/AlgorithmsToLowerBounds` → 6 hits, all in `BridgeToPpolyDAG.lean`.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|weak route|Legacy|_Partial|TODO|placeholder" pnp4/Pnp4/AlgorithmsToLowerBounds` → 2 hits, both `Model_PartialMCSP` in `TruthTableMCSP.lean`.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" pnp4/Pnp4/AlgorithmsToLowerBounds` → 187 textual hits; interpreted above, no hidden final payload found.
- `rg -n "\baxiom\b|\bsorry\b|\badmit\b|native_decide" -g'*.lean' pnp4/Pnp4/AlgorithmsToLowerBounds` → 0 hits.
- `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` → no output, exit status 1 as expected for no matches.
- `./scripts/check.sh` → passed all checks.

## 21. Scope violations

None. This audit created exactly one markdown report and did not edit Lean/source/spec/output/JSONL files.
