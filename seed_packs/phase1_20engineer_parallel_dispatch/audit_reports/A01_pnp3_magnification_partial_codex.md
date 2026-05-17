# A01 audit: `pnp3/Magnification/*_Partial.lean`
Task: A01  
Engineer handle: codex  
Scope: markdown-only Phase 0 audit  
Branch: `khanukov/phase1-A01-codex`

## 1. Executive verdict
**Verdict: PARTIAL_BUT_USEFUL.**

The six `_Partial.lean` files are kernel-checked infrastructure for a partial-MCSP / formula-locality side track, but they are not a closed mainline route to `P != NP` and they do not construct `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPWeakLowerBound`, or `NP_not_subset_PpolyDAG`.  The most mature content is a typed chain from formula witnesses through locality/provider interfaces to `NP_not_subset_PpolyFormula` or `NP_not_subset_PpolyReal`, plus many adapter lemmas converting one staged provider contract into another.  Much of the area is honest staging: many `Prop` contracts package missing multi-switching, certificate, globalizing, and semantic-link obligations instead of proving them unconditionally.  The area is useful for future reuse as an AC0/formula/locality infrastructure layer, but it should be reported as side-track/infrastructure unless a later adapter bridges it to pnp4's `VerifiedNPDAGLowerBoundSource` or `PpolyDAG` target.

## 2. Executive summary
**Complete for partial-MCSP variant? Partial.**  There is a kernel-checked partial-MCSP pipeline for several formula/locality statements, and `LocalityProvider_Partial.lean` contains a large library of provider adapters.  However, the route is not fully closed in the governance sense because important endpoint statements still take provider/certificate/support-bound/semantic-link assumptions, and several default-provider flags are themselves `Prop` assumptions.  **Usable pnp4 integration path? Needs work.**  The existing pnp3 theorems can be imported and wrapped by pnp4 adapter modules, but their endpoints are `NP_not_subset_PpolyFormula` / `NP_not_subset_PpolyReal`, not pnp4's mainline `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound` frontier.

Audit completeness: roughly 85% of LOC carefully read/structurally audited.  I fully read all five smaller files and structurally read the large 3,677-line provider file by declarations, comments, provider sections, risk searches, and representative proof bodies; I did not line-by-line reconstruct every proof in the large provider file.

## 3. Files audited
| File | Approximate role | Read mode | Notes |
| --- | --- | --- | --- |
| `RESEARCH_CONSTITUTION.md` | governance rules and target semantics | skimmed fully enough for rules | Required reading; used to classify mainline vs side-track claims. |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | dispatch/check requirements | skimmed structurally | Required reading; older E-task wording superseded by prompt. |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | worker rules | skimmed structurally | Required reading; prompt override used for A01 naming. |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A01_audit_pnp3_magnification_partial.md` | exact A01 audit spec | read fully | Defines required report path and sections. |
| `pnp3/Magnification/Facts_Magnification_Partial.lean` | OPS-style partial triggers | read fully | 235 LOC. |
| `pnp3/Magnification/PipelineStatements_Partial.lean` | partial pipeline statement surfaces | read fully | 286 LOC. |
| `pnp3/Magnification/LocalityProvider_Partial.lean` | large locality-provider adapter layer | structurally read plus targeted proof/risk inspection | 3,677 LOC; too large to rederive every proof body in this audit wave. |
| `pnp3/Magnification/LocalityInterfaces_Partial.lean` | small general-circuit interface definitions | read fully | 57 LOC. |
| `pnp3/Magnification/LocalityLift_Partial.lean` | façade over `ThirdPartyFacts.PartialLocalityLift` | read fully | 100 LOC. |
| `pnp3/Magnification/Bridge_to_Magnification_Partial.lean` | endpoint bridge to formula/real separations | read fully | 119 LOC. |
| `pnp3/Complexity/Interfaces.lean` | trust-root separation targets | skimmed relevant definitions/theorems | Used to identify formula/real/DAG endpoint strength. |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | trust-root gap witness route | searched/read relevant snippets | Used to check `ResearchGapWitness` relationship. |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` | pnp4 DAG bridge | searched | Used for integration contrast. |
| `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` | pnp4 MCSP frontier | searched | Used for integration contrast. |
| `pnp4/Pnp4/Frontier/CompressionMagnification.lean` | pnp4 mainline compression route | searched | Used for integration contrast. |
| `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean` | bridge requirement surface | searched | Used for integration contrast. |
| `outputs/nogolog.jsonl` | historical no-go registry | not read in this pass | Optional; not needed to identify `_Partial` local staging. |
| `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` | strategic retrospective | not read in this pass | Optional; omitted for time because local Lean files were sufficient for A01. |

## 4. File-by-file audit
### 4.1 `pnp3/Magnification/LocalityInterfaces_Partial.lean`
**Role.**  Defines a small general-circuit solver interface for partial MCSP, separate from formula-specific solvers.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `GeneralCircuitParametersPartial` | structure with `size`, `depth` | canonical infrastructure | none |
| `SmallGeneralCircuitParamsPartial` | structure pairing partial params with general circuit params | canonical infrastructure | none |
| `SmallGeneralCircuitSolver_Partial` | structure with params, semantic function, and promise-correctness proof | canonical infrastructure | uses `GapPartialMCSPParams`, `GapPartialMCSPPromise` |
| `SmallGeneralCircuitSolver_Partial.correct_decide` | if `GapPartialMCSPPromise p x`, solver decision equals membership in `gapPartialMCSP_Language p` | canonical theorem/projection wrapper | none beyond solver fields |

**Kernel-checked content.**  The lemma `SmallGeneralCircuitSolver_Partial.correct_decide` is a direct projection from the solver structure's `correct` field and is kernel-checked.  It proves promise-correct semantic behavior for any `SmallGeneralCircuitSolver_Partial p`.

**Staged/Prop-only content.**  The solver structure contains a proof field `correct`, which is an honest interface obligation, not a proof that such solvers exist.  This is harmless infrastructure.

**Classical / axioms / sorry.**  No `Classical.choose`, `axiom`, `opaque`, `sorry`, or `admit` found in this file.

**Trust-root dependencies.**  Imports `Complexity.Interfaces` and uses the trust-root language semantics indirectly through `Models.gapPartialMCSP_Language` and `ComplexityInterfaces.Bitstring` aliases.

### 4.2 `pnp3/Magnification/LocalityLift_Partial.lean`
**Role.**  Thin façade around `ThirdPartyFacts.PartialLocalityLift`, exposing locality lift lemmas in the `Pnp3.Magnification` namespace.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `locality_lift_partial` | stable restriction + shrinkage provider ⇒ small local solver with polylog bounds | conditional adapter | depends on third-party `ShrinkageWitness.Provider` |
| `locality_lift_partial_of_certificate` | shrinkage certificate + half-cardinality bound ⇒ same locality output | conditional adapter | typeclass certificate provider |
| `locality_lift_partial_of_certificate_auto` | certificate provider + `HalfTableCertificateBound` ⇒ same locality output | conditional adapter | typeclass provider / half-bound |
| `no_general_solver_of_no_local_partial` | no local solver + stable restrictions/providers for all general solvers ⇒ no general solver | conditional adapter | universal stability/provider assumptions |

**Kernel-checked content.**  All four definitions are kernel-checked wrappers delegating to `ThirdPartyFacts.PartialLocalityLift`.  They prove no new mathematical locality theorem by themselves; they transport third-party facts into the magnification namespace under explicit assumptions.

**Staged/Prop-only content.**  None declared locally.  The assumptions are explicit parameters/typeclasses, so this is mostly harmless adapter infrastructure.

**Classical / axioms / sorry.**  No `Classical.choose`, `axiom`, `opaque`, `sorry`, or `admit` found locally.

**Trust-root dependencies.**  Uses partial-MCSP model and lower-bound solver interfaces; no `ResearchGapWitness` or `NP_not_subset_PpolyDAG` dependency.

### 4.3 `pnp3/Magnification/PipelineStatements_Partial.lean`
**Role.**  Provides named AC0 / formula lower-bound statements for the partial-MCSP pipeline and proves them from `LowerBounds.LB_Formulas_Core_Partial` cores.

**Top-level structures/defs.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `AC0StatementPartial_semantic` | semantic small AC0 solver + easy-family data ⇒ `False` | staged Prop / conditional statement | `AC0EasyFamilyDataPartial` |
| `AC0StatementPartial` | abbrev of semantic statement | staged Prop | same |
| `AC0StatementPartial_constructive` | constructive solver ⇒ `False` | conditional statement | solver carries easy data |
| `AC0StatementPartial_closed` | syntactic small solver ⇒ `False` | suspicious/needs context but kernel-checked from core | syntactic solver type |
| `AC0StatementPartial_providerClosed` | solver + `StepCClosureDataPartialProvider solver` ⇒ `False` | staged provider Prop | provider typeclass-like payload |
| `AC0StatementPartial_constructive_providerClosed` | constructive solver ⇒ `False` | conditional/kernel-checked from core | constructive solver package |
| `AC0StatementPartial_fully_closed` | closure package + solver ⇒ `False` | staged Prop | `StepCClosureDataPartial` |
| `AC0BoundedStatementPartial_semantic` | size-bound + easy data ⇒ `False` | conditional statement | explicit bound/easy data |
| `AC0BoundedStatementPartial_constructive` | constructive solver + size-bound ⇒ `False` | conditional statement | constructive solver |
| `FormulaLowerBoundHypothesisPartial` | `0 < δ ∧ AC0BoundedStatementPartial_semantic p δ` | staged Prop wrapper | AC0 statement |
| `FormulaLowerBoundHypothesisPartial_semantic` | abbrev of formula hypothesis | staged Prop wrapper | same |

**Kernel-checked theorem content.**

The file contains 15 lemmas.  Their pattern is reliable: they prove the named statement surfaces by invoking `LB_Formulas_core_partial_*` facts.  Examples:

- `ac0_statement_from_pipeline_partial_semantic` proves `AC0StatementPartial_semantic p` by applying `LB_Formulas_core_partial_of_easyFamilyData` to each solver/easy-data pair.
- `ac0_statement_from_pipeline_partial_constructive` proves `AC0StatementPartial_constructive p` by applying `LB_Formulas_core_partial_constructive`.
- `ac0_statement_from_pipeline_partial_closed`, `_providerClosed`, `_internalized`, and related `_fully_closed` lemmas produce contradictions for several solver packages or closure packages.
- `ac0_bounded_statement_semantic_of_constructive` converts a constructive bounded statement to the semantic bounded statement by packaging `solver` and `easyData` into a `ConstructiveSmallAC0Solver_Partial`.
- `formula_hypothesis_from_pipeline_partial_semantic` proves `FormulaLowerBoundHypothesisPartial_semantic p δ` from only `0 < δ`, because it pairs `hδ` with the semantic bounded statement supplied by the pipeline.

These are kernel-checked, but their strength depends on the imported lower-bound core definitions.  They do not prove `NP_not_subset_PpolyDAG`.

**Staged/Prop-only content.**  Eleven declaration surfaces are `Prop`/abbrev statement packagers.  This is mostly honest staging, but the names `closed` / `fully_closed` should not be over-interpreted as final P-vs-NP closure; they close specific Step-C solver contradictions, not the main target.

**Classical / axioms / sorry.**  No `Classical.choose`, `axiom`, `opaque`, `sorry`, or `admit` found locally.

**Trust-root dependencies.**  No direct `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, or pnp4 source dependency.  Uses partial-MCSP model, AC0 solver structures, and real exponent size bounds.

### 4.4 `pnp3/Magnification/Facts_Magnification_Partial.lean`
**Role.**  OPS-style triggers that turn lower-bound/locality hypotheses into nonuniform formula/real separations for `gapPartialMCSP_Language p`.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `GeneralLowerBoundHypothesisPartial` | `0 < ε ∧ statement` | staged Prop wrapper | input statement |
| `RestrictionLocalityPartial` | existence of polylog test set/local solver with bounds for formula witnesses | staged Prop | `PpolyFormula`, local solver |
| `StructuredLocalityProviderPartial` | ∀ partial params, formula witness ⇒ restriction locality | staged Prop/provider | `PpolyFormula` |
| `StructuredLocalityProviderPartial_semantic` | ∀ params, formula witness ⇒ semantic AC0 easy data for general solver | staged Prop/provider | `PpolyFormula`, `AC0EasyFamilyDataPartial` |
| `OPS_trigger_general_contra_structured_with_provider_partial` | provider + NP-strict + lower-bound statement + `PpolyFormula L` ⇒ contradiction | conditional theorem | provider + NP_strict |
| `OPS_trigger_formulas_contra_structured_with_provider_partial` | formula lower-bound hypothesis + provider + formula witness ⇒ contradiction | conditional theorem | formula hypothesis |
| `OPS_trigger_formulas_partial_of_provider` | provider + NP-strict + PpolyReal→PpolyFormula embed + formula hypothesis ⇒ `NP_not_subset_PpolyReal` | conditional theorem | embed assumption |
| `OPS_trigger_formulas_partial_of_provider_global_embed` | global real→formula embed variant ⇒ `NP_not_subset_PpolyReal` | conditional theorem | global embed |
| `OPS_trigger_formulas_partial_of_provider_formula_separation` | provider + NP-strict + formula hypothesis ⇒ `NP_not_subset_PpolyFormula` | conditional theorem | no DAG source |
| `OPS_trigger_formulas_partial_of_provider_formula_separation_strict` | strict parameterized variant | conditional theorem | explicit formula witness contradiction |
| semantic variants | semantic provider variants for formula/real endpoints | conditional theorem | semantic provider/easy data |

**Kernel-checked content.**  The file proves conditional contradictions: assuming a structured locality provider and a formula lower-bound hypothesis, a nonuniform formula witness for the partial-MCSP language contradicts `NP_strict`.  From that it constructs `NP_not_subset_PpolyFormula` and, with a real-to-formula embedding, `NP_not_subset_PpolyReal`.

**Staged/Prop-only content.**  `RestrictionLocalityPartial`, `StructuredLocalityProviderPartial`, and `StructuredLocalityProviderPartial_semantic` are provider assumptions.  They are honest staging if treated as obligations; they become wrapper risk if advertised as already inhabited without citing a concrete provider theorem.

**Classical / axioms / sorry.**  No `Classical.choose`, `axiom`, `opaque`, `sorry`, or `admit` found locally.

**Trust-root dependencies.**  Uses `ComplexityInterfaces.NP_strict`, `PpolyFormula`, `PpolyReal`, `NP_not_subset_PpolyFormula`, and `NP_not_subset_PpolyReal`.  It does not mention `NP_not_subset_PpolyDAG`, `ResearchGapWitness`, or pnp4 verified sources.

### 4.5 `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`
**Role.**  Small endpoint module exposing preferred partial-MCSP formula/real separation routes.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `NP_not_subset_PpolyFormula_from_partial_formulas` | provider + formula lower-bound hypothesis + NP-strict ⇒ `NP_not_subset_PpolyFormula` | conditional side-track endpoint | `StructuredLocalityProviderPartial`, `FormulaLowerBoundHypothesisPartial`, `NP_strict` |
| `NP_not_subset_PpolyReal_from_partial_formulas` | same but real endpoint via trivial realization bridge | conditional side-track endpoint | provider + formula hypothesis + `NP_strict` |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic` | semantic provider version | conditional side-track endpoint | semantic provider |
| `NP_not_subset_PpolyReal_from_partial_formulas_semantic` | semantic real version | conditional side-track endpoint | semantic provider |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto` | semantic provider + `0 < δ` + NP-strict ⇒ formula separation | conditional theorem | provider + `NP_strict`; auto builds formula hypothesis |
| `NP_not_subset_PpolyReal_from_partial_formulas_semantic_auto` | semantic provider + `0 < δ` + NP-strict ⇒ real separation | conditional theorem | provider + `NP_strict` |

**Kernel-checked content.**  These theorems compose earlier facts.  The `_semantic_auto` theorems are notable because they use `formula_hypothesis_from_pipeline_partial_semantic` to remove the explicit formula lower-bound hypothesis, but they still require `StructuredLocalityProviderPartial_semantic` and `NP_strict (gapPartialMCSP_Language p)`.

**Staged/Prop-only content.**  No new `Prop` definitions; all staging arrives through imported provider and lower-bound hypotheses.

**Classical / axioms / sorry.**  No `Classical.choose`, `axiom`, `opaque`, `sorry`, or `admit` found locally.

**Trust-root dependencies.**  Ends at formula/real separations, not DAG.  No `ResearchGapWitness` or pnp4 source dependency.

### 4.6 `pnp3/Magnification/LocalityProvider_Partial.lean`
**Role.**  Large adapter layer that tries to build `StructuredLocalityProviderPartial` from formula support bounds, restriction certificates, generic extracted local cores, restricted behavior transports, multi-switching contracts, and direct contracts.

**Important top-level declarations by region.**

| Region / declarations | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `generalSolverOfFormula`; `stableWitness_of_formula_supportBound`; `stableWitness_of_formula_sizeBound` | convert formula witnesses/support bounds into general solvers and stable restrictions | canonical infrastructure, conditional lemmas | `PpolyFormula`, formula support/size |
| `ConstructiveLocalityEnginePartial`, `FormulaToGeneralLocalityDataPartial`, `FormulaRestrictionCertificateDataPartial` | structures packaging local-lift and formula-to-general data | staged interfaces | provider fields |
| `FormulaSupportRestrictionBoundsPartial` | ∀ formula witness, formula support yields half-table restriction bound and stability | weak/legacy-risk staged Prop | arbitrary `PpolyFormula` witness |
| `FormulaSupportBoundsPartial_fromPipeline` and `_fixedParams` | provenance-restricted support-bounds contracts with AC0 family/multiswitching inputs | safer staged Prop | explicit AC0 provenance + formula witness |
| `_of_old` bridge theorems | old all-formula support bounds imply new provenance-restricted forms | legacy compatibility | old support-bounds predicate |
| `StructuredLocalityProviderPartial_fromPipeline` and `_of_old` | pipeline-aware provider contract and old-to-new bridge | staged provider | support/certificate data |
| `FormulaRestrictionCertificateDataPartial_fromPipeline` and `_of_old` | certificate data with explicit AC0 provenance; old bridge uses `Classical.choose` | staged provider; old bridge is legacy compatibility | formula witness + AC0 provenance |
| `ExtractedLocalCorePartial`, `GenericExtractedLocalCorePartial`, `WeakGenericExtractedLocalCorePartial` and providers | core extraction data and generic/weak variants | staged interfaces | semantic switching/certification assumptions |
| `RestrictedLocalBehaviorSolver_Partial`, `GenericRestrictedBehaviorCertificatePartial`, `WeakGenericRestrictedBehaviorCertificatePartial` and transports | restricted solver behavior plus preservation/globalization interfaces | staged interfaces; some theorems canonical adapters | promise preservation assumptions |
| `PromisePreservingWeakGenericExtractedLocalCorePartial` and provider lemmas | weak core plus promise-preservation wrapper | safer adapter than weak-only | explicit preservation proof |
| `FormulaSemanticLinkPartial`, `FormulaSupportCoreSteps`, `FormulaSupportCoreBounds` | semantic link/support-core intermediate packages | staged/conditional | formula witness + multi-switching support facts |
| `multiswitching_contract_*`, `formula_support_bounds_*`, `extracted_local_core_provider_*` | convert semantic provider/support bounds/multiswitching contracts to provider packages | conditional adapter theorems | multi-switching contract or support bounds |
| `FormulaCertificateProviderPartial`, `FormulaCertificateProviderPartial_fromPipeline` | suspicious-provider audit-marked provider structures | suspicious / needs review | certificate provider fields with formula witnesses |
| `FormulaHalfSizeBoundPartial`, default flags, default provider theorems | default assumptions and conversions to structured locality provider | hidden-payload risk if used as final source | default `Prop` assumptions |
| `DirectStructuredLocalityProviderContract` and `structuredLocalityProviderPartial_of_contract` | direct contract to provider | harmless interface if explicit | direct contract witness |

**Kernel-checked content.**  The file has 87 theorem/lemma declarations and many definitions.  The kernel-checked content is mostly adapter-style: if a support-bound/certificate/generic-core/multiswitching contract is supplied, then the file constructs a `StructuredLocalityProviderPartial` or a related provider.  It also proves concrete local facts such as stability of formula witnesses under support restrictions and membership preservation for generated restrictions.

**Staged/Prop-only content.**  This file is the main staging area.  Searches found 57 `: Prop`/`where`-style obligation surfaces in the file.  The most important staged obligations are `FormulaSupportRestrictionBoundsPartial`, `FormulaSupportBoundsPartial_fromPipeline`, `StructuredLocalityProviderPartial_fromPipeline`, `FormulaExtractedLocalCoreProviderPartial`, `FormulaGenericExtractedLocalCoreProviderPartial`, weak/generic restricted behavior providers, decision-preservation/globalization predicates, semantic-link predicates, and default-provider flags.  Many are honest interfaces; the default flags and old all-formula support-bounds route are higher risk.

**Classical / axioms / sorry.**  `Classical.choose` appears 42 times, all in `LocalityProvider_Partial.lean`.  The uses I inspected extract witnesses from `PpolyFormula` or staged existential provider data; that is standard for converting a formula witness into a concrete family/circuit, but it is also the place where arbitrary-witness hardwiring risk must be controlled.  No `axiom`, `opaque`, `sorry`, or `admit` found in the six audited files.

**Trust-root dependencies.**  Heavy use of `ComplexityInterfaces.PpolyFormula`, `InPpolyFormula`, formula circuit support/size/eval, and `gapPartialMCSP_Language`.  No direct `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract` mentions in this file.

## 5. Cross-file dependency graph
Text graph from imports:

```text
LocalityInterfaces_Partial
  imports Mathlib, Complexity.Promise, Complexity.Interfaces, Core.BooleanBasics, Models.Model_PartialMCSP

LocalityLift_Partial
  imports LocalityInterfaces_Partial, ThirdPartyFacts.PartialLocalityLift,
          LowerBounds.AntiChecker_Partial, Models.Model_PartialMCSP

PipelineStatements_Partial
  imports LowerBounds.LB_Formulas_Core_Partial, Models.Model_PartialMCSP,
          Mathlib.Analysis.SpecialFunctions.Pow.Real

Facts_Magnification_Partial
  imports PipelineStatements_Partial, Models.Model_PartialMCSP,
          LowerBounds.AntiChecker_Partial, Complexity.Interfaces

LocalityProvider_Partial
  imports Facts_Magnification_Partial, LocalityLift_Partial,
          Magnification.AC0LocalityBridge, LowerBounds.LB_Formulas_Core_Partial,
          ThirdPartyFacts.PartialLocalityLift

Bridge_to_Magnification_Partial
  imports PipelineStatements_Partial, Facts_Magnification_Partial,
          Complexity.Interfaces, Models.Model_PartialMCSP, ThirdPartyFacts.PpolyFormula
```

No import cycles were visible among the six files.  The hidden dependency shape is not cyclic but layered: `LocalityProvider_Partial` depends on both `Facts` and `LocalityLift`, while `Bridge_to_Magnification_Partial` imports only the statement/trigger layers and does not import `LocalityProvider_Partial`.  That means bridge users must explicitly provide a `StructuredLocalityProviderPartial` or import a provider-construction module separately.

## 6. Coverage matrix: partial-MCSP vs full-MCSP vs AC0[p]
| Variant | Covered in audited files | Gap |
| --- | --- | --- |
| Partial-MCSP | Main subject.  The files define partial solver interfaces, locality-lift wrappers, formula lower-bound statements, provider contracts, and formula/real separation bridges for `gapPartialMCSP_Language p`. | Still needs honest provider/certificate/multiswitching witnesses and `NP_strict` hypotheses for endpoint theorems. |
| Full MCSP | Not directly covered.  The audited files use `GapPartialMCSPParams`, `partialInputLen`, `Partial.tableLen`, and partial promise predicates throughout. | Requires separate adapter or theorem connecting partial-MCSP route to full MCSP/search-MCSP if desired. |
| AC0 / formula | Covered as formula/AC0 side-track.  Uses `SmallAC0Solver_Partial`, `AC0EasyFamilyDataPartial`, formula witnesses, and multi-switching contracts. | Does not bridge to `PpolyDAG` or `VerifiedNPDAGLowerBoundSource`. |
| AC0[p] | Not substantively covered.  The route is formula/AC0-flavored, not a pnp4 AC0[p] mainline bridge. | Any AC0[p] use would need separate definitions and an explicit DAG/source bridge. |

## 7. pnp4 integration analysis
**Usable from pnp4 today.**  In principle, pnp4 can import pnp3 modules and use the endpoint theorems in `Bridge_to_Magnification_Partial.lean`, especially the semantic-auto variants.  These provide conditional `NP_not_subset_PpolyFormula` or `NP_not_subset_PpolyReal` endpoints under provider and `NP_strict` assumptions.

**Needs adapter modules.**  A pnp4 adapter would be needed to restate partial-MCSP params and provider hypotheses in pnp4-native terms, and to connect any pnp4 literature theorem to `StructuredLocalityProviderPartial_semantic` or a more explicit support/certificate provider.  A separate adapter would be required if the operator wants these results to appear in pnp4 test/audit surfaces.

**Requires operator decision.**  The main decision is whether this area should remain a pnp3 side-track or be surfaced in pnp4 as restricted lower-bound infrastructure.  It should not be integrated as mainline `P != NP` progress unless a concrete bridge to `VerifiedNPDAGLowerBoundSource` / `PpolyDAG` is specified.

## 8. Top-level theorem / structure inventory
Important declarations are summarized here rather than exhaustively listing all 108 theorem/lemma definitions.

| Name | File | Type/signature summary | Classification | Depends on hard payload? |
| --- | --- | --- | --- | --- |
| `SmallGeneralCircuitSolver_Partial` | `LocalityInterfaces_Partial.lean` | general solver with promise correctness | canonical | no |
| `locality_lift_partial*` | `LocalityLift_Partial.lean` | third-party locality lift wrappers | conditional adapter | no |
| `AC0StatementPartial_*` | `PipelineStatements_Partial.lean` | AC0/solver contradiction statements | staged Prop / conditional | no |
| `formula_hypothesis_from_pipeline_partial_semantic` | `PipelineStatements_Partial.lean` | `0 < δ` ⇒ formula lower-bound hypothesis | conditional/kernel-checked from core | no |
| `StructuredLocalityProviderPartial` | `Facts_Magnification_Partial.lean` | formula witness ⇒ restriction locality | staged Prop/provider | no |
| `StructuredLocalityProviderPartial_semantic` | `Facts_Magnification_Partial.lean` | formula witness ⇒ semantic easy data | staged Prop/provider | no |
| `OPS_trigger_formulas_partial_of_provider_formula_separation` | `Facts_Magnification_Partial.lean` | provider + lower-bound + NP-strict ⇒ `NP_not_subset_PpolyFormula` | conditional side-track endpoint | no DAG/source payload |
| `OPS_trigger_formulas_partial_of_provider_semantic` | `Facts_Magnification_Partial.lean` | semantic provider route to `NP_not_subset_PpolyReal` | conditional side-track endpoint | no DAG/source payload |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto` | `Bridge_to_Magnification_Partial.lean` | semantic provider + `0 < δ` + NP-strict ⇒ formula separation | conditional side-track endpoint | no DAG/source payload |
| `FormulaSupportRestrictionBoundsPartial` | `LocalityProvider_Partial.lean` | all formula witnesses satisfy support restriction bound | weak/legacy-risk staged Prop | no, but hardwiring risk |
| `FormulaSupportBoundsPartial_fromPipeline` | `LocalityProvider_Partial.lean` | provenance-restricted support bounds with AC0 inputs | safer staged Prop | no |
| `FormulaCertificateProviderPartial*` | `LocalityProvider_Partial.lean` | certificate provider structures | suspicious/audit-marked | no, but provider risk |
| `defaultStructuredLocalityProviderPartial` | `LocalityProvider_Partial.lean` | default flag ⇒ structured provider | hidden-payload risk if final-used | no, but default assumption |

No audited declaration depends on `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract` according to targeted search.

## 9. Kernel-checked content
The audited area is buildable and contains kernel-checked Lean.  What is actually proven is mostly conditional:

1. Formula-circuit support facts are used to show stable behavior under restrictions when a formula witness and support bound are supplied.
2. Partial locality-lift wrappers are checked as direct calls to `ThirdPartyFacts.PartialLocalityLift`.
3. AC0 partial pipeline statements are checked by invoking `LB_Formulas_core_partial_*` lemmas.
4. OPS trigger theorems are checked: provider + formula lower-bound + `NP_strict` contradict nonuniform formula/real witnesses for the partial-MCSP language.
5. Endpoint bridge theorems are checked: provider + `NP_strict` + lower-bound/positivity assumptions imply `NP_not_subset_PpolyFormula` or `NP_not_subset_PpolyReal`.
6. Many provider adapters are checked: one staged contract implies another, eventually yielding `StructuredLocalityProviderPartial`.

Not kernel-proven here: a closed provider without assumptions strong enough for mainline, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPWeakLowerBound`, `ResearchGapWitness`, or `P_ne_NP`.

## 10. Staged / placeholder / Prop-only content
The area contains extensive `Prop` staging.  Major categories:

- **Honest staging:** `AC0StatementPartial_*`, `FormulaLowerBoundHypothesisPartial`, `StructuredLocalityProviderPartial`, `StructuredLocalityProviderPartial_semantic`, generic local-core providers, restricted-behavior transports, globalize predicates, semantic-link predicates.
- **Potential wrapper risk:** `FormulaCertificateProviderPartial`, `FormulaCertificateProviderPartial_fromPipeline`, `DirectStructuredLocalityProviderContract`, and default-provider flags.  These are fine as interfaces, but dangerous if a downstream theorem silently assumes them as if constructed.
- **Possible hidden hard theorem:** `defaultStructuredLocalityProviderPartial` and `defaultFormulaCertificateProviderPartial` are especially risky names because they can make a provider look globally available while still requiring a default `Prop` payload.
- **Harmless interface:** `SmallGeneralCircuitSolver_Partial`, `ConstructiveLocalityEnginePartial`, and many structure fields that simply carry semantic correctness or certificate data under explicit parameters.

There are comments in `LocalityProvider_Partial.lean` explicitly warning that the older support-bound predicate was too strong / falsifiable by audit probes and that the pipeline-aware replacement requires AC0 provenance.  Future work should preserve that distinction.

## 11. Refuted / vacuous / legacy route check
Searches for `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `Legacy`, `_Partial`, `TODO`, and `placeholder` found no direct `RefutedRoute`, `Vacuous`, `FinalPayloadProvider`, or `via_ex_falso` occurrences inside the six audited files.  The main findings are:

- Numerous `supportBounds` / support-bounds names in `LocalityProvider_Partial.lean`.
- Comments in `LocalityProvider_Partial.lean` describe an older support-bounds predicate as previously falsifiable or ex-falso-adjacent and introduce provenance-restricted replacements.
- `PipelineStatements_Partial.lean` explicitly says one constructive closed statement avoids a legacy all-functions bridge.
- `FormulaCertificateProviderPartial` and the pipeline variant carry `@audit-class: suspicious-provider` comments.
- Several `weak` provider/core names exist.  These are isolated as explicit weaker interfaces and, in later adapters, are strengthened with promise-preservation/globalization assumptions.

Conclusion: no obvious refuted endpoint is exported in these six files, but legacy compatibility bridges from the old support-bounds predicate should remain quarantined and should not be used to claim progress.

## 12. Hidden payload / Rule 16 check
Search targets included `class`, `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `noncomputable def`, and `Classical.choose`.

| Occurrence category | Finding | Classification |
| --- | --- | --- |
| `class` / `instance` / `attribute [instance]` | No local typeclass instances declaring hard payloads were found in the six files.  Some imported provider assumptions are passed as bracketed typeclass parameters in lift wrappers. | harmless if explicit; watch imported providers |
| `opaque` | None found. | clean |
| `Fact` | No local suspicious `Fact` payloads found in audited files. | clean |
| `noncomputable def` | Many in `LocalityProvider_Partial.lean`, mostly extracting data from formula witnesses or staged provider existentials. | standard extraction or adapter construction, but provider/default names need review |
| `Classical.choose` | 42 occurrences, all in `LocalityProvider_Partial.lean`. | mostly standard witness extraction; hidden-payload risk if applied to arbitrary `PpolyFormula` routes without provenance filters |
| default/provider names | `hasDefault...`, `default...`, `...Provider...` declarations present. | hidden-payload risk if used by candidate endpoints |

I did not find a forbidden hidden construction of `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, or `NP_not_subset_PpolyDAG` in the audited scope.

## 13. Barrier relevance
| Barrier / theme | Audited content status | Notes |
| --- | --- | --- |
| Natural proofs | nothing direct | No natural-proofs theorem in audited files. |
| Relativization | nothing direct | No relativization theorem. |
| Algebrization | nothing direct | No algebrization theorem. |
| Locality | actual typed interfaces and conditional theorems | Main content of `LocalityLift`/`LocalityProvider`. |
| Hardwiring | staged comments and risk surfaces | Old all-formula support-bounds route is hardwiring-risky; pipeline-aware contracts add provenance. |
| Support-cardinality-only | actual staged predicates and adapter theorems | `FormulaSupportRestrictionBoundsPartial` and successors. |
| Syntax-only filters | typed interface / partial | Formula support and syntax are used; no standalone barrier theorem. |
| Normalization filters | little/no direct content | Not a focus of audited files. |
| Search-to-decision | nothing direct | No search-MCSP decision bridge. |
| MCSP / magnification | actual typed interface, staged Prop, and conditional theorems | Partial-MCSP magnification infrastructure only. |

## 14. Reuse map
**Safe to reuse.**

- `SmallGeneralCircuitSolver_Partial` and its correctness projection.
- `locality_lift_partial*` wrappers, provided users keep their assumptions explicit.
- `AC0StatementPartial_*` statement surfaces as names for partial-MCSP Step-C obligations.
- `formula_hypothesis_from_pipeline_partial_semantic` as a checked way to obtain the semantic formula lower-bound hypothesis from the imported core.
- `OPS_trigger_*_formula_separation*` theorems for conditional formula/real separation routes.
- `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto` and real analogue as clear side-track endpoints.
- Pipeline-aware support/certificate interfaces that take explicit AC0 provenance.

**Avoid or treat as audit-only unless operator approves.**

- Old `FormulaSupportRestrictionBoundsPartial` all-formula support-bounds route.
- `_of_old` compatibility bridges if the goal is avoiding known hardwiring/falsifiability issues.
- Default-provider flags and `default...` theorems as candidate dependencies.
- `FormulaCertificateProviderPartial` surfaces marked `@audit-class: suspicious-provider` until their provider audit is complete.
- Any claim that formula/real separation in this area is mainline P-vs-NP progress without an explicit DAG/source bridge.

## 15. Gap map
### A. Engineering gap
- pnp4 has no obvious adapter module exposing these partial-MCSP side-track endpoints in pnp4-native test/audit surfaces.
- The provider file is large and mixes legacy compatibility, current interfaces, and default-provider conveniences; splitting documentation or adding a markdown map would reduce duplicate engineering.
- Existing search surfaces do not appear to label the safe pipeline-aware route versus old support-bounds route strongly enough for future workers.

### B. Formalization gap
- Concrete construction of `StructuredLocalityProviderPartial_semantic` remains an obligation unless supplied by the provider layer under explicit assumptions.
- Pipeline-aware certificate/provider structures need audited, provenance-safe constructors from literature-level multi-switching theorems.
- The link from partial-MCSP formula/locality statements to any full-MCSP or search-MCSP theorem is not present in this audited scope.

### C. Mathematical gap
- No theorem here proves `NP_not_subset_PpolyDAG`.
- No theorem here constructs `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.
- Bridging formula/real lower bounds for partial-MCSP to a DAG lower bound against an NP language remains a main mathematical gap.
- Search-to-decision or MCSP compression-magnification bridge is absent.

### D. Governance gap
- Legacy support-bounds compatibility names could be accidentally reused by future workers unless explicitly marked as avoid/legacy in dispatcher tasks.
- `default...` provider names create a false-comfort risk; future candidate tasks should forbid depending on them unless the default payload is explicitly audited.
- The six files themselves do not create a NoGoLog entry; cross-check with the NoGoLog audit may be useful for the old support-bounds route.

## 16. Recommended Phase 1+ tasks
Recommended Phase 1+ tasks count: 5.

### Task 1: pnp4 partial-MCSP side-track adapter inventory
- **Exact files to touch:** new markdown or Lean adapter under operator-chosen pnp4 infrastructure path; if Lean, likely `pnp4/Pnp4/Frontier/PartialMCSPFormulaSideTrack.lean` plus pnp4 tests.
- **Allowed scope:** restate/import conditional pnp3 endpoints as side-track surfaces only.
- **Forbidden scope:** no `VerifiedNPDAGLowerBoundSource`, no `ResearchGapWitness`, no `P_ne_NP` endpoint.
- **Expected output:** pnp4-visible theorem checks for conditional formula/real endpoints with honest doc comments.
- **Estimated time:** 0.5-1 day.
- **Dependency on other audits:** should wait for pnp4 bridge audit if one exists.
- **Risk level:** low if strictly side-track.
- **Type:** Lean, infrastructure.

### Task 2: Provider-risk markdown quarantine map
- **Exact files to touch:** new markdown under `seed_packs/.../audit_reports/` or operator-approved docs path; do not edit Lean.
- **Allowed scope:** document safe vs legacy provider declarations in `LocalityProvider_Partial.lean`.
- **Forbidden scope:** no code edits, no NoGoLog unless operator requests.
- **Expected output:** table of provider declarations with `safe`, `legacy`, `suspicious-provider`, or `default-assumption` tags.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** useful to cross-check with A09/NoGoLog audit.
- **Risk level:** low.
- **Type:** markdown-only.

### Task 3: Provenance-safe certificate constructor audit
- **Exact files to touch:** no implementation initially; audit `FormulaCertificateProviderPartial_fromPipeline`, `FormulaRestrictionCertificateDataPartial_fromPipeline`, and imported `ThirdPartyFacts.PartialLocalityLift`.
- **Allowed scope:** verify whether pipeline-aware certificate data excludes truth-table hardwiring.
- **Forbidden scope:** no construction of provider payload unless follow-up authorized.
- **Expected output:** audit report or proof obligation list for provider constructors.
- **Estimated time:** 1-2 days.
- **Dependency on other audits:** depends on NoGoLog/provider audit.
- **Risk level:** medium.
- **Type:** markdown-only first; possible later Lean.

### Task 4: Full-MCSP/search-MCSP relationship assessment
- **Exact files to touch:** markdown report first; maybe future pnp4 frontier files only after operator decision.
- **Allowed scope:** compare partial-MCSP endpoints to full MCSP/search-MCSP frontier requirements.
- **Forbidden scope:** no bridge theorem claiming DAG/source lower bound without actual proof.
- **Expected output:** decision memo stating whether a formal adapter is engineering, formalization, or open math.
- **Estimated time:** 1 day.
- **Dependency on other audits:** pnp4 SearchMCSP audit.
- **Risk level:** high mathematically.
- **Type:** operator decision / markdown-only.

### Task 5: Lean surface tests for existing pnp3 partial endpoints, if operator wants reuse
- **Exact files to touch:** pnp3 or pnp4 test files selected by operator; no source theorem changes.
- **Allowed scope:** `#check`/wrapper tests for existing endpoint theorem names.
- **Forbidden scope:** no new mathematical theorem, no source changes.
- **Expected output:** tests preventing accidental rename/regression of conditional side-track endpoints.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** none.
- **Risk level:** low.
- **Type:** Lean test-only.

## 17. Stop / hold recommendations
- Hold any task that tries to use `NP_not_subset_PpolyFormula_from_partial_formulas*` as evidence for `P_ne_NP` without a DAG/source bridge.
- Downgrade any planned task based on `FormulaSupportRestrictionBoundsPartial` old all-formula support bounds to audit-only unless it explicitly addresses hardwiring/provenance.
- Rename future dispatch involving these files as **partial-MCSP formula/locality side-track**, not mainline P-vs-NP.
- Do not touch trust-root files or endpoint definitions to make this route fit mainline; the gap is mathematical/bridge-level, not a naming problem.

## 18. Commands run and summarized results
- `./scripts/check.sh` — failed at step 12.e coordinator HTTP service e2e with `ConnectionResetError`; earlier Lean build and governance scans completed successfully before the coordinator test reset.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" pnp3/Magnification/*_Partial.lean` — no output in audited files.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" pnp3/Magnification/*_Partial.lean` — many `_Partial` and support/weak/legacy-comment hits; no direct `RefutedRoute`, `Vacuous`, `FinalPayloadProvider`, or `via_ex_falso` hits in the six files.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" pnp3/Magnification/*_Partial.lean` — 42 `Classical.choose` hits and many `noncomputable def` hits in `LocalityProvider_Partial.lean`; no local `opaque` hits.
- `rg -n "\bsorry\b|\badmit\b|\baxiom\b|\bopaque\b" pnp3/Magnification/*_Partial.lean` — no output.
- `wc -l pnp3/Magnification/*_Partial.lean` — confirmed 4,474 LOC total.
- Declaration inventory script over `pnp3/Magnification/*_Partial.lean` — found 108 theorem/lemma declarations, 89 def/structure/abbrev declarations, concentrated in `LocalityProvider_Partial.lean`.

## 19. Honest caveats
- I did not reconstruct every proof body in `LocalityProvider_Partial.lean`; I audited it by declaration inventory, comments, targeted proof inspection, and risk searches.
- I did not inspect every imported theorem in `LowerBounds.LB_Formulas_Core_Partial` or `ThirdPartyFacts.PartialLocalityLift`; this audit classifies the current six-file surface, not the full transitive mathematical adequacy of imports.
- I did not read `outputs/nogolog.jsonl`; conclusions about old support-bounds falsifiability come from comments and local route shape, not the global NoGoLog.
- I verified no direct hard-payload names appear in the six audited files, but I did not compute the full dependency closure for every theorem.
- I treated `Classical.choose` over `PpolyFormula` as standard extraction where locally apparent, but a full hardwiring audit would need to inspect downstream candidate use.

## 20. Final structured output template
Task: A01  
Engineer handle: codex  
Branch: khanukov/phase1-A01-codex  
Commit before: d27b069127f63a3f24ab30d1a91c86c84f8b79c7  
Commit after: TBD after commit

Files added/modified:
- `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A01_pnp3_magnification_partial_codex.md`

Outcome: AUDIT_LANDED

Executive verdict: PARTIAL_BUT_USEFUL

Files audited:
- 16 files inspected or searched; 6 target Lean files audited directly.

Key findings:
1. The audited route is conditional partial-MCSP formula/locality infrastructure, not mainline P-vs-NP progress.
2. Kernel-checked endpoints reach `NP_not_subset_PpolyFormula` / `NP_not_subset_PpolyReal` under provider and `NP_strict` assumptions, not `NP_not_subset_PpolyDAG`.
3. `LocalityProvider_Partial.lean` is the primary staging/risk area, especially old support-bounds and default-provider surfaces.

Kernel-checked content found:
- Conditional solver contradictions, locality adapters, OPS triggers, formula/real separation bridges, and provider-adapter theorems.

Staged / placeholder content found:
- Extensive provider/support/certificate/globalization `Prop` contracts; no Lean `sorry`/`admit` placeholders in audited files.

Refuted / vacuous / legacy route findings:
- No direct refuted/vacuous endpoint names in six files; legacy old support-bounds compatibility and suspicious-provider comments are present.

Hidden payload / Rule 16 findings:
- No hard-payload constructions found.  42 `Classical.choose` uses and multiple default-provider names in `LocalityProvider_Partial.lean` require cautious downstream use.

Recommended Phase 1+ tasks:
- 5
- pnp4 side-track adapter inventory; provider-risk quarantine map; provenance-safe certificate constructor audit; full/search MCSP relationship assessment; optional surface tests.

Hold / cancel recommendations:
- Hold/downgrade any task using these formula/real endpoints as mainline `P != NP` evidence without a DAG/source bridge.

Commands run:
- `./scripts/check.sh` → WARNING: failed at step 12.e due to coordinator HTTP service `ConnectionResetError`; Lean build and earlier guards passed before that environment/service failure.
- `rg ...hard payload...` → no output in audited files.
- `rg ...legacy/risk...` → support/weak/legacy-comment hits, no direct refuted endpoint hits.
- `rg ...Rule 16...` → 42 `Classical.choose` hits, all in `LocalityProvider_Partial.lean`; no local `opaque`.
- `rg ...sorry/admit/axiom/opaque...` → no output.

Scope violations:
- none

Honest caveats:
- Large provider file structurally audited, not line-by-line proof rederived.
- Imported lower-bound and third-party files not fully audited.
- NoGoLog not cross-checked in this pass.
