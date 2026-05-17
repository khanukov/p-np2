# A01 audit: `pnp3/Magnification/*_Partial.lean`

Task: A01  
Engineer handle: codex  
Scope: Phase 0 markdown-only audit of the six partial-MCSP magnification files under `pnp3/Magnification/`.

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL.**

The audited area contains kernel-checked partial-MCSP interfaces, Step-C statements, OPS trigger wiring, locality-lift facades, and many adapter theorems that compose explicit hypotheses into `StructuredLocalityProviderPartial` and `NP_not_subset_PpolyFormula` / `NP_not_subset_PpolyReal` consequences. It is **not complete for the partial-MCSP variant** as an unconditional route: the important locality/provider payloads are mostly `Prop` contracts, `Nonempty` packages, or noncomputable extractions from explicit assumptions. The files themselves contain no direct `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract` dependency, so this is a restricted formula/locality side track, not a pnp4 mainline P-vs-NP endpoint. The repository comments explicitly mark at least one older support-bound route as logically vacuous and under migration, so future work should avoid treating old support-bound defaults as progress. A pnp4 integration path exists only as an adapter/governance path for side-track artifacts; it does not currently bridge to `VerifiedNPDAGLowerBoundSource` or `PpolyDAG`.

## 2. Executive summary

These six files are **partially complete** for a partial-MCSP/formula-track magnification API: they define the partial solver interface, prove Step-C contradictions from existing lower-bound cores, delegate locality lifting to `ThirdPartyFacts.PartialLocalityLift`, and expose conditional bridge theorems from a structured locality provider plus NP-strictness to nonuniform formula/real separations. They are **not complete** as a mathematical proof of an unconditional partial-MCSP lower-bound route because the provider/locality/support assumptions are staged and often explicitly packaged as `Prop` obligations. The current pnp4 integration path is **needs work / operator decision**: the files are listed in `lakefile.lean`, but pnp4 does not appear to import the audited bridge endpoints directly, and no audited declaration produces `VerifiedNPDAGLowerBoundSource`, `SearchMCSPWeakLowerBound`, or `NP_not_subset_PpolyDAG`.

## 3. Files audited

| File | Approximate role | Inspection level | Reason if not fully read |
| --- | --- | --- | --- |
| `RESEARCH_CONSTITUTION.md` | Repo governance / route policy | Read fully | Required reading. |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | Dispatch governance | Read fully | Required reading. |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | Worker constraints | Read fully | Required reading; naming override came from the user prompt. |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A01_audit_pnp3_magnification_partial.md` | A01 task file | Read fully | Defines exact six-file scope and report requirements. |
| `pnp3/Magnification/Facts_Magnification_Partial.lean` | OPS trigger and formula/real separation bridge from structured locality | Read fully | Small file. |
| `pnp3/Magnification/PipelineStatements_Partial.lean` | Partial-MCSP Step-C statement API and pipeline lemmas | Read fully | Small file. |
| `pnp3/Magnification/LocalityProvider_Partial.lean` | Main partial locality provider/adapter layer | Skimmed structurally plus targeted reads around all major sections and suspicious comments | 3,677 LOC; I used declaration inventory, targeted chunk reading, and exact searches for hard payload, legacy, hidden-provider, and forbidden terms. |
| `pnp3/Magnification/LocalityInterfaces_Partial.lean` | Partial general circuit parameter and solver interface | Read fully | Small file. |
| `pnp3/Magnification/LocalityLift_Partial.lean` | Thin facade over `ThirdPartyFacts.PartialLocalityLift` | Read fully | Small file. |
| `pnp3/Magnification/Bridge_to_Magnification_Partial.lean` | Top-level formula/real bridge entrypoints | Read fully | Small file. |
| `pnp3/Complexity/Interfaces.lean` | Trust-root complexity interfaces | Searched/skimmed only | Optional, trust-root read-only; audited files depend on `Language`, `PpolyFormula`, `PpolyReal`, `NP_strict`, and separation wrappers. |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | Optional trust-root / gap witness context | Searched/skimmed only | Used only to confirm no direct audited-scope construction path. |
| `outputs/nogolog.jsonl` | Optional no-go context | Not edited; not line-by-line audited | A01 scope was the six Lean files; no JSONL edits allowed. |
| `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` | Optional strategic report | Not deeply audited | Not needed to classify the six files. |

## 4. File-by-file audit

### 4.1 `pnp3/Magnification/LocalityInterfaces_Partial.lean`

**Role.** Defines the minimal partial-MCSP general-circuit solver interface.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard-payload dependency |
| --- | --- | --- | --- |
| `GeneralCircuitParametersPartial` | Structure with `n`, `size`, `depth`. | canonical interface | None. |
| `SmallGeneralCircuitParamsPartial` | Structure tying general parameters to `Models.partialInputLen p`. | canonical interface | None. |
| `SmallGeneralCircuitSolver_Partial` | Structure with params, semantic decider, witness, and `SolvesPromise (GapPartialMCSPPromise p)`. | canonical interface | None. |
| `SmallGeneralCircuitSolver_Partial.decide` | Evaluator induced by semantic witness. | canonical helper | None. |
| `SmallGeneralCircuitSolver_Partial.correct_decide` | Kernel lemma rewriting stored `correct` through `.decide`. | canonical helper theorem | None. |

**Kernel-checked content.** The file proves only the convenience lemma that the stored `correct` field implies `SolvesPromise ... solver.decide` by simplification. It does not prove any lower bound.

**Staged / Prop-only content.** The core solver is a structure with a `correct` field; this is an honest interface, not a proof of solver existence.

**Classical / forbidden terms.** No `Classical.choose`, `noncomputable def`, `axiom`, `sorry`, `admit`, or `opaque` found in this file.

**Trust-root dependencies.** Uses `Complexity.Promise.SolvesPromise`, `ComplexityInterfaces.SemanticDecider`, `Models.GapPartialMCSPParams`, `Models.partialInputLen`, and `Models.GapPartialMCSPPromise`.

### 4.2 `pnp3/Magnification/LocalityLift_Partial.lean`

**Role.** Thin facade delegating partial locality lift statements to `ThirdPartyFacts.PartialLocalityLift`.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard-payload dependency |
| --- | --- | --- | --- |
| `locality_lift_partial` | From a general solver, stable half-table restriction, and shrinkage provider, returns a polylog test set and `SmallLocalCircuitSolver_Partial` with numeric bounds. | conditional adapter theorem/def | Requires external stable witness and shrinkage provider. |
| `locality_lift_partial_of_certificate` | Certificate-provider variant with explicit half-table cardinality proof. | conditional adapter | Requires typeclass certificate provider and half-cardinality proof. |
| `locality_lift_partial_of_certificate_auto` | Certificate-provider variant with `HalfTableCertificateBound` typeclass. | conditional adapter | Requires typeclass certificate and half-bound instances. |
| `no_general_solver_of_no_local_partial` | Converts no-local-solver hypothesis plus lift data into no-general-solver conclusion. | conditional adapter | Requires no-local theorem and provider/stability inputs. |

**Kernel-checked content.** The file kernel-checks the shape-preserving delegation to `ThirdPartyFacts.locality_lift_partial*` and a conditional no-general-solver wrapper. It does not construct the shrinkage/stability payload on its own.

**Staged / Prop-only content.** No local Prop package definitions; the staging is in the imported provider/certificate hypotheses.

**Classical / forbidden terms.** No `Classical.choose`, `noncomputable def`, `axiom`, `sorry`, `admit`, or `opaque` found here. The typeclass provider arguments are harmless only as explicit hypotheses; they would be risky if registered globally or made default instances.

**Trust-root dependencies.** Uses `SmallGeneralCircuitSolver_Partial`, `LowerBounds.SmallLocalCircuitSolver_Partial`, `Facts.LocalityLift.Restriction`, and `ThirdPartyFacts.PartialLocalityLift` conversion helpers.

### 4.3 `pnp3/Magnification/PipelineStatements_Partial.lean`

**Role.** Defines partial Step-C formula/AC0 statements and proves them from the partial formula lower-bound core.

**Top-level declarations.**

| Declaration group | Signature summary | Classification | Hard-payload dependency |
| --- | --- | --- | --- |
| `AC0StatementPartial_semantic`, `AC0StatementPartial`, `AC0StatementPartial_constructive`, `AC0StatementPartial_closed`, `AC0StatementPartial_providerClosed`, `AC0StatementPartial_constructive_providerClosed`, `AC0StatementPartial_fully_closed` | Variants of “no small AC0 solver” over semantic, constructive, syntactic, provider-closed, and fully closed packages. | staged Prop statements plus some canonical aliases | Depend on solver/easy-data packages, not on pnp4 hard payload. |
| `AC0BoundedStatementPartial_semantic`, `AC0BoundedStatementPartial_constructive` | Bounded versions with real-size exponent hypothesis. | staged Prop statements | Requires solver and bound hypothesis. |
| `FormulaLowerBoundHypothesisPartial`, `FormulaLowerBoundHypothesisPartial_semantic` | Positive δ plus bounded semantic Step-C statement. | staged Prop contract | No `ResearchGapWitness`; includes hard math as Prop. |
| `ac0_statement_from_pipeline_partial_*` lemmas | Derive Step-C statements from `LB_Formulas_Core_Partial` APIs. | conditional/canonical within AC0 side track | Depends on imported lower-bound core. |
| `formula_hypothesis_from_pipeline_partial_semantic` | Builds semantic formula hypothesis from δ > 0 and constructive bounded Step-C. | conditional theorem within side track | No pnp4 hard payload. |

**Kernel-checked content.** Kernel-checked lemmas show that the existing `LB_Formulas_Core_Partial` contradictions imply the various Step-C statement forms. The strongest-looking closed statements are still statements about absence of AC0/constructive solver packages, not an NP-language lower bound against `PpolyDAG`.

**Staged / Prop-only content.** The file has 11 `Prop :=` statement forms. These are mostly honest staging interfaces for the formula side track. They are wrapper risks only if downstream code treats `FormulaLowerBoundHypothesisPartial` as an already-proven mainline lower bound rather than a side-track hypothesis assembled from AC0 solver contradictions.

**Classical / forbidden terms.** No `Classical.choose`, `noncomputable def`, `axiom`, `sorry`, `admit`, or `opaque` found here.

**Trust-root dependencies.** Uses `Models.GapPartialMCSPParams`, `Models.partialInputLen`, `LowerBounds.SmallAC0Solver_Partial`, `AC0EasyFamilyDataPartial`, `ConstructiveSmallAC0Solver_Partial`, `SmallAC0Solver_Partial_Syntactic`, `StepCClosureDataPartial`, `StepCClosureDataPartialProvider`, `StepCSyntacticLiftDataPartial`, and `Real.rpow`.

### 4.4 `pnp3/Magnification/Facts_Magnification_Partial.lean`

**Role.** Defines structured locality-provider contracts and OPS-style triggers from those contracts to formula/real separations.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard-payload dependency |
| --- | --- | --- | --- |
| `GeneralLowerBoundHypothesisPartial` | `0 < ε ∧ statement`. | staged Prop wrapper | No hard payload; simple conjunction. |
| `RestrictionLocalityPartial` | Exists polylog test set and `SmallLocalCircuitSolver_Partial`. | staged existential Prop | Local solver existence is payload. |
| `StructuredLocalityProviderPartial` | For all `p,δ`, formula lower-bound hypothesis plus `PpolyFormula gapPartialMCSP` gives `RestrictionLocalityPartial p`. | staged provider contract | No pnp4 hard payload, but locality provider is major payload. |
| `StructuredLocalityProviderPartial_semantic` | Semantic alias/counterpart of the provider contract. | staged provider contract | Same as above. |
| `OPS_trigger_general_contra_structured_with_provider_partial` | From provider, NP-strict target, and formula hypothesis, contradicts universal `NP_strict -> PpolyFormula`. | conditional theorem | Requires provider, NP-strictness, and formula hypothesis. |
| `OPS_trigger_formulas_partial_of_provider` | From provider, NP-strictness, `PpolyReal -> PpolyFormula` embedding, and formula hypothesis, proves `NP_not_subset_PpolyReal`. | conditional theorem | Requires provider and embedding. |
| `OPS_trigger_formulas_partial_of_provider_formula_separation*` | Provider-based formula separation variants. | conditional theorem | Requires provider, NP-strictness, formula hypothesis. |
| Semantic trigger variants | Same shape with `_semantic` provider/hypothesis. | conditional theorem | Same. |

**Kernel-checked content.** The proofs are valid eliminations: assume all NP-strict languages have formula/real circuits, specialize to `gapPartialMCSP_Language p`, use `hProvider` to produce a local solver, then contradict `noSmallLocalCircuitSolver_partial_v2`. This is a kernel-checked conditional implication, not a construction of `hProvider`.

**Staged / Prop-only content.** Four `Prop` definitions. `StructuredLocalityProviderPartial` is the major wrapper risk: it packages the hard locality extraction as a single hypothesis.

**Classical / forbidden terms.** No `Classical.choose`, `noncomputable def`, `axiom`, `sorry`, `admit`, or `opaque` found here.

**Trust-root dependencies.** Uses `ComplexityInterfaces.Language`, `NP_strict`, `PpolyFormula`, `PpolyReal`, `NP_not_subset_PpolyFormula`, `NP_not_subset_PpolyReal`, and conversion lemmas from `Complexity.Interfaces`.

### 4.5 `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`

**Role.** Top-level bridge entrypoints from partial formula hypotheses and structured locality provider contracts to nonuniform formula/real separations.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard-payload dependency |
| --- | --- | --- | --- |
| `NP_not_subset_PpolyFormula_from_partial_formulas` | Provider + formula hypothesis + NP-strict target implies `NP_not_subset_PpolyFormula`. | conditional side-track bridge | Requires provider and NP-strict target. |
| `NP_not_subset_PpolyReal_from_partial_formulas` | Same for `PpolyReal`, using trivial realization bridge. | conditional side-track bridge | Requires provider and NP-strict target. |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic` | Semantic provider/hypothesis formula separation. | conditional side-track bridge | Requires semantic provider and NP-strict target. |
| `NP_not_subset_PpolyReal_from_partial_formulas_semantic` | Semantic provider/hypothesis real separation. | conditional side-track bridge | Requires semantic provider and NP-strict target. |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto` | Auto-builds formula hypothesis from δ > 0, but still requires provider and NP-strict target. | conditional side-track bridge | Provider and NP-strict remain. |
| `NP_not_subset_PpolyReal_from_partial_formulas_semantic_auto` | Auto semantic real variant. | conditional side-track bridge | Provider and NP-strict remain. |

**Kernel-checked content.** These are thin wrappers over `Facts_Magnification_Partial` triggers. The “auto” variants remove only the explicit formula-hypothesis argument by invoking `formula_hypothesis_from_pipeline_partial_semantic`; they do **not** remove the `StructuredLocalityProviderPartial_semantic` or `NP_strict` assumptions.

**Staged / Prop-only content.** No new Prop definitions, but all theorems consume staged provider hypotheses.

**Classical / forbidden terms.** No `Classical.choose`, `noncomputable def`, `axiom`, `sorry`, `admit`, or `opaque` found here.

**Trust-root dependencies.** Uses `Complexity.Interfaces` separation names and `ThirdPartyFacts.PpolyFormula` realization bridge.

### 4.6 `pnp3/Magnification/LocalityProvider_Partial.lean`

**Role.** Large adapter layer that builds structured locality providers from formula witnesses, support bounds, pipeline-restricted bounds, multi-switching contracts, extracted local cores, restricted-behavior transports, certificates, and default availability flags.

**Top-level declaration inventory summary.**

This file has 161 declaration hits in the structural inventory: 24 `noncomputable def`, 21 structures, 104 theorems, 2 lemmas, and many `def`-level Prop contracts. Important declaration families include:

| Declaration family | Signature summary | Classification | Hard-payload dependency |
| --- | --- | --- | --- |
| `generalSolverOfFormula`, `stableWitness_of_formula_supportBound`, `stableWitness_of_formula_sizeBound` | Extract a semantic general solver from `PpolyFormula`, then get stable restriction from support/size bounds. | conditional / standard extraction | Uses `Classical.choose hFormula`; no pnp4 hard payload. |
| `ConstructiveLocalityEnginePartial`, `FormulaToGeneralLocalityDataPartial`, `FormulaRestrictionCertificateDataPartial` | Structures packaging solver extraction, stability, shrinkage providers, and certificate data. | staged structures | Payload fields are hard locality/support assumptions. |
| `FormulaSupportRestrictionBoundsPartial` | Universal support restriction bounds for every formula witness. | legacy / refuted-vacuous risk | Comment says old callers are logically vacuous; no hard pnp4 payload. |
| `FormulaSupportBoundsPartial_fromPipeline`, `FormulaSupportBoundsPartial_fromPipeline_fixedParams` | Provenance-restricted support-bound replacements requiring AC0 provenance and semantic link. | staged Prop / safer replacement | Still a Prop contract. |
| `_of_old` migration theorems | Old universal support-bounds imply newer pipeline-restricted contracts. | legacy compatibility | Should not be used as progress because old premise is problematic. |
| `StructuredLocalityProviderPartial_fromPipeline` and `structuredLocalityProviderPartial_fromPipeline_*` | Pipeline-restricted provider statements and adapters. | staged/conditional | Requires support/certificate packages. |
| `ExtractedLocalCorePartial`, `GenericExtractedLocalCorePartial`, `WeakGenericExtractedLocalCorePartial`, provider Props | Packages restrictions/cores and generic/weak core providers. | staged structures / Prop providers | Core existence is payload. |
| `SemanticSwitchingRestrictionCoreExtractionPartial` and related theorems | Converts semantic switching certificates into weak/generic cores. | conditional adapter | Requires semantic provider/extraction assumptions. |
| `RestrictedLocalBehaviorSolver_Partial` and behavior transport/globalization Props | Model restricted behavior and transport it into local solver packages. | conditional infrastructure | Transport/globalization are payload contracts. |
| `PromisePreservingWeakGenericExtractedLocalCorePartial` and provider theorems | Adds promise-preservation to weak cores. | staged but useful | Preservation proof is payload. |
| `FormulaSupportCoreSteps`, `FormulaSupportCoreBounds`, support-core/multiswitching theorems | Internal adapter chain from multi-switching/support core data to support bounds and semantic links. | conditional adapter | Requires `AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract`. |
| `FormulaCertificateProviderPartial`, `FormulaCertificateProviderPartial_fromPipeline` | Certificate-provider structures; comments mark suspicious-provider audit class. | suspicious-provider wrapper risk | Noncomputably chooses formula/certificate data. |
| Default flags such as `hasDefaultFormulaRestrictionCertificateDataPartial`, `hasDefaultFormulaSupportRestrictionBoundsPartial`, `hasDefaultStructuredLocalityProviderPartial`, `defaultStructuredLocalityProviderPartial` | `Nonempty` flags and extraction of default providers. | staged / hidden-payload risk if misused | No global instance found, but default naming deserves quarantine. |

**Kernel-checked content.** There are many real kernel-checked adapter theorems: support-cardinality implies stable restriction; size bound implies support bound; generic cores imply weak/promise-preserving cores; behavior transports assemble provider structures; support bounds produce formula restriction certificates; certificate providers produce constructive engines; constructive engines produce `StructuredLocalityProviderPartial`; multi-switching contracts can be threaded through several adapters to structured locality providers. The common pattern is “given this explicit support/core/certificate/transport contract, build the next package.” The file does not prove the missing global/pipeline support bounds unconditionally.

**Staged / Prop-only content.** At least 27 `Prop :=` definitions occur in this file. Most are honest staging, but several are wrapper risks because a single assumption can hide the actual hard theorem: `FormulaSupportRestrictionBoundsPartial`, `FormulaSupportBoundsPartial_fromPipeline`, `FormulaExtractedLocalCoreProviderPartial`, `FormulaGenericExtractedLocalCoreProviderPartial`, `FormulaWeakGenericExtractedLocalCoreProviderPartial`, `FormulaGenericRestrictedBehaviorProviderPartial`, `GenericRestrictedLocalBehaviorTransportPartial`, `GlobalizeRestrictedLocalBehaviorPartial`, `FormulaPromisePreservingWeakGenericExtractedLocalCoreProviderPartial`, `FormulaGenericRestrictedLocalCertificateProviderPartial`, `GenericRestrictedLocalCertificateTransportPartial`, `FormulaHalfSizeBoundPartial`, and the `hasDefault*` Nonempty flags.

**Classical / hidden-payload terms.** The file contains 42 textual `Classical.choose` occurrences and 24 `noncomputable def` declarations. Most are standard extraction from an explicit `PpolyFormula` or `Nonempty`/provider hypothesis; they are not automatically dangerous because no `instance`, `default_instance`, or `[instance]` declaration was found in the audited six-file scope. However, `FormulaCertificateProviderPartial`, `FormulaCertificateProviderPartial_fromPipeline`, `defaultFormulaCertificateProviderPartial`, and `defaultStructuredLocalityProviderPartial` are hidden-payload risks if future code treats them as ambient/default facts rather than explicit assumptions.

**Forbidden terms.** No `axiom`, `sorry`, `admit`, `opaque`, or `native_decide` found by the required search in the six audited files.

**Trust-root dependencies.** Heavily uses `ComplexityInterfaces.PpolyFormula`, `InPpolyFormula`, `FormulaCircuit`, `SemanticDecider`, `Models.GapPartialMCSPParams`, `Models.partialInputLen`, `Models.GapPartialMCSPPromise`, `LowerBounds.SmallLocalCircuitSolver_Partial`, `ThirdPartyFacts.PartialLocalityLift`, and `AC0LocalityBridge` contracts.

## 5. Cross-file dependency graph

```text
LocalityInterfaces_Partial
  imports Mathlib.Data.Finset.Basic, Complexity.Promise, Complexity.Interfaces,
          Core.BooleanBasics, Models.Model_PartialMCSP

LocalityLift_Partial
  imports LocalityInterfaces_Partial,
          LowerBounds.AntiChecker_Partial, Models.Model_PartialMCSP,
          ThirdPartyFacts.PartialLocalityLift

PipelineStatements_Partial
  imports LowerBounds.LB_Formulas_Core_Partial,
          Models.Model_PartialMCSP, Mathlib Real pow

Facts_Magnification_Partial
  imports PipelineStatements_Partial,
          Models.Model_PartialMCSP, LowerBounds.AntiChecker_Partial,
          Complexity.Interfaces

Bridge_to_Magnification_Partial
  imports PipelineStatements_Partial and Facts_Magnification_Partial,
          plus Complexity.Interfaces, Models.Model_PartialMCSP,
          ThirdPartyFacts.PpolyFormula

LocalityProvider_Partial
  imports Facts_Magnification_Partial and LocalityLift_Partial,
          plus Magnification.AC0LocalityBridge,
          LowerBounds.LB_Formulas_Core_Partial,
          ThirdPartyFacts.PartialLocalityLift
```

No import cycle was observed among the six files. `Facts_Magnification_Partial` depends on `PipelineStatements_Partial`; `Bridge_to_Magnification_Partial` depends on `Facts` and `Pipeline`; `LocalityProvider_Partial` depends on `Facts` and `LocalityLift`; `LocalityLift` depends on `LocalityInterfaces`. Hidden dependencies are mainly through imported `LowerBounds.*`, `ThirdPartyFacts.*`, and `AC0LocalityBridge`, not through cyclic `_Partial` siblings.

## 6. Top-level theorem / structure inventory

Important audited declarations and classifications are summarized below. For the full large-file inventory, I used `rg` and structural reads rather than copying all 161 `LocalityProvider_Partial` declarations into this report.

| Name | File | Type/signature summary | Classification | Hard payload dependency |
| --- | --- | --- | --- | --- |
| `SmallGeneralCircuitSolver_Partial` | `LocalityInterfaces_Partial.lean` | Solver with semantic decider and `SolvesPromise`. | canonical | None; structure field contains correctness proof. |
| `locality_lift_partial` | `LocalityLift_Partial.lean` | Stable restriction + shrinkage provider -> local solver and bounds. | conditional adapter | Shrinkage/stability payload. |
| `FormulaLowerBoundHypothesisPartial` | `PipelineStatements_Partial.lean` | `0 < δ ∧ AC0BoundedStatementPartial_semantic p δ`. | staged Prop | AC0 lower-bound side-track payload. |
| `formula_hypothesis_from_pipeline_partial_semantic` | `PipelineStatements_Partial.lean` | δ>0 -> semantic formula lower-bound hypothesis. | conditional/canonical side-track | Imported partial formula core. |
| `StructuredLocalityProviderPartial` | `Facts_Magnification_Partial.lean` | Formula hypothesis + PpolyFormula -> locality witness. | staged Prop / wrapper risk | Main locality payload. |
| `OPS_trigger_formulas_partial_of_provider_formula_separation` | `Facts_Magnification_Partial.lean` | Provider + NP-strict + formula hypothesis -> `NP_not_subset_PpolyFormula`. | conditional | Provider and NP-strict. |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto` | `Bridge_to_Magnification_Partial.lean` | Semantic provider + δ>0 + NP-strict -> `NP_not_subset_PpolyFormula`. | conditional side-track bridge | Provider and NP-strict. |
| `generalSolverOfFormula` | `LocalityProvider_Partial.lean` | Extract semantic general solver from PpolyFormula witness. | standard extraction | `PpolyFormula` witness; uses `Classical.choose`. |
| `FormulaSupportRestrictionBoundsPartial` | `LocalityProvider_Partial.lean` | Universal support-bounds over all formula witnesses. | legacy / refuted-vacuous risk | Hard support-bound payload; comments say old route vacuous. |
| `FormulaSupportBoundsPartial_fromPipeline` | `LocalityProvider_Partial.lean` | Provenance-restricted support-bounds with AC0 semantic link. | staged Prop | Hard support-bound payload, safer than old universal form. |
| `FormulaCertificateProviderPartial` | `LocalityProvider_Partial.lean` | Provider package converting each formula to certificate data. | suspicious / needs review | Hidden-payload risk if defaulted. |
| `defaultStructuredLocalityProviderPartial` | `LocalityProvider_Partial.lean` | From `Nonempty ConstructiveLocalityEnginePartial` to provider. | suspicious / staged | Hidden provider extracted from `Nonempty`; explicit hypothesis required. |

## 7. Kernel-checked content

The audited area kernel-checks the following kinds of content:

1. **Interface rewrites.** `SmallGeneralCircuitSolver_Partial.correct_decide` proves the stored `SolvesPromise` field applies to the `.decide` function.
2. **Third-party lift facades.** `locality_lift_partial*` return local solvers with cardinality/size/depth bounds when supplied with stable restrictions, shrinkage providers, and certificates.
3. **Step-C derivations.** `PipelineStatements_Partial` proves semantic/constructive/closed/provider-closed AC0 Step-C statements from imported `LB_Formulas_Core_Partial` contradictions.
4. **Formula-hypothesis packaging.** `formula_hypothesis_from_pipeline_partial_semantic` packages δ positivity and bounded semantic Step-C into `FormulaLowerBoundHypothesisPartial_semantic`.
5. **OPS contradiction wiring.** `Facts_Magnification_Partial` proves that a structured locality provider plus formula lower-bound hypothesis and NP-strictness contradicts universal `NP_strict -> PpolyFormula`; formula/real separation wrappers follow through `ComplexityInterfaces` conversion lemmas.
6. **Top-level partial bridge wrappers.** `Bridge_to_Magnification_Partial` exposes conditional formula/real separation theorems; auto variants remove only the formula-hypothesis argument, not the provider/NP-strict assumptions.
7. **Locality provider adapters.** `LocalityProvider_Partial` proves many adapter theorems from support/core/certificate/transport assumptions to structured locality providers.

None of these kernel-checked items constructs `VerifiedNPDAGLowerBoundSource`, `SearchMCSPWeakLowerBound`, `NP_not_subset_PpolyDAG`, or `ResearchGapWitness`.

## 8. Staged / placeholder / Prop-only content

The required search found no literal `placeholder` in active code comments except task/doc wording outside the scoped files, but the audited files contain substantial staged Prop content:

- `PipelineStatements_Partial.lean`: 11 Prop-level statement forms for AC0/Step-C and formula hypotheses. These are honest staging interfaces.
- `Facts_Magnification_Partial.lean`: `RestrictionLocalityPartial` and `StructuredLocalityProviderPartial(_semantic)` are major provider contracts. They are honest staging but wrapper risks.
- `LocalityProvider_Partial.lean`: 27 Prop definitions, including support bounds, provider availability, transport, globalization, semantic link, and default flags. These are mostly honest staging/adapter interfaces, but `FormulaSupportRestrictionBoundsPartial` and the `hasDefault*` flags require governance caution.
- `LocalityLift_Partial.lean` and `LocalityInterfaces_Partial.lean`: no local Prop-only lower-bound packages beyond structure fields and explicit hypotheses.
- `Bridge_to_Magnification_Partial.lean`: no new Prop definitions, but all theorem endpoints consume staged providers.

Potential wrapper risks: `StructuredLocalityProviderPartial`, `FormulaSupportRestrictionBoundsPartial`, `FormulaSupportBoundsPartial_fromPipeline`, `FormulaCertificateProviderPartial`, `FormulaCertificateProviderPartial_fromPipeline`, `hasDefaultStructuredLocalityProviderPartial`, and `defaultStructuredLocalityProviderPartial`.

## 9. Refuted / vacuous / legacy route check

Search summary for `RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder` over the six files:

- No `RefutedRoute`, `Vacuous`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, or `TODO` hits in the scoped files.
- Many `_Partial` hits are expected by file names and declaration names.
- `supportBounds` / `support bounds` hits are concentrated in `LocalityProvider_Partial.lean`.
- The file comment near `FormulaSupportRestrictionBoundsPartial` explicitly states historical final-line callers remain type-correct but logically vacuous, and prescribes migration to a pipeline-restricted contract.
- `MagnificationAssumptions` is mentioned only in a comment as downstream follow-up threading, not implemented in the audited scope.
- `Legacy` appears in comments/import names around final-result migration references, not as an active theorem named `Legacy` in these files.

Conclusion: the dangerous/vacuous route is not hidden; it is commented and partially quarantined by newer `_fromPipeline` predicates. However, compatibility theorems from the old predicate still exist, so future workers should not promote old support-bound defaults.

## 10. Hidden payload / Rule 16 check

Required search summary for `class|instance|default_instance|attribute [instance]|Fact|opaque|Classical.choose|noncomputable def`:

- `LocalityProvider_Partial.lean`: 68 matching lines; 42 textual `Classical.choose` occurrences and 24 `noncomputable def` declarations by local count.
- The other five audited files: no matches for `Classical.choose` or `noncomputable def` by the required search.
- No `class`, top-level `instance`, `default_instance`, `attribute [instance]`, or `opaque` declaration was found in the six-file scope by the required regex. Some theorem signatures require typeclass-style bracketed providers imported from `ThirdPartyFacts`, but they are explicit hypotheses in the theorem statements.

Interpretation:

| Occurrence family | Classification | Reason |
| --- | --- | --- |
| `Classical.choose hFormula` in `generalSolverOfFormula` and support-bound extraction | standard exponent/formula extraction | Extracts an `InPpolyFormula` witness from explicit `PpolyFormula`; acceptable if not hidden as default. |
| `Classical.choose` inside provider/certificate conversion functions | hidden-payload risk | Converts `Nonempty`/provider data into concrete packages; safe only with explicit assumptions. |
| `noncomputable def factsAssignmentOfSubcube`, `factsRestrictionOfSubcube`, `restrictedBehaviorSem`, `restrictedBehaviorWitness` | harmless infrastructure / semantic construction | Defines semantic objects from explicit restrictions. |
| `noncomputable def defaultFormulaRestrictionCertificateDataPartial`, `defaultFormulaCertificateProviderPartial`, `directStructuredLocalityProviderContract_*`, `defaultStructuredLocalityProviderPartial` | suspicious / hidden-payload risk if used as candidate defaults | Names and `Nonempty` extraction can hide hard locality provider assumptions unless kept explicit and audited. |
| Imported provider typeclasses in `locality_lift_partial_of_certificate*` | forbidden if registered globally for candidate without proof | In audited file they are explicit parameters; no global instance found. |

## 11. Barrier relevance

| Barrier / theme | Audited area content | Classification |
| --- | --- | --- |
| Natural proofs | No explicit natural-proofs barrier theorem in the six files. | nothing |
| Relativization | No explicit relativization theorem. | nothing |
| Algebrization | No explicit algebrization theorem. | nothing |
| Locality | Central theme: locality lift, restrictions, local solvers, structured locality providers. | typed interfaces + conditional adapter theorems + staged Prop |
| Hardwiring | Explicitly relevant in comments warning that arbitrary formula witnesses include truth-table hardwiring and make old support bounds vacuous. | markdown-only comment plus governance signal |
| Support-cardinality-only | Central in `FormulaSupportRestrictionBoundsPartial`, support/core bounds, and stable restriction theorems. | actual conditional theorems + staged Prop; old universal route is weak/refuted-vacuous risk |
| Syntax-only filters | AC0 syntactic/constructive solver packages appear in pipeline statements. | typed interface / conditional theorem |
| Normalization filters | Not directly formalized in scoped files. | nothing |
| Search-to-decision | No mainline search-to-decision bridge. | nothing |
| MCSP / magnification | Central but for partial-MCSP formula/locality track. | typed interfaces + conditional side-track bridges; no mainline pnp4 source obligation |

## 12. Coverage matrix: partial-MCSP vs full-MCSP vs AC⁰[p]

| Variant | Covered in audited files | Kernel-checked? | Gaps |
| --- | --- | --- | --- |
| Partial-MCSP (`*_Partial`) | Yes. Solver interfaces, Step-C partial statements, locality-lift facade, structured provider contracts, provider adapters, formula/real bridge wrappers. | Conditional pieces kernel-check. | No unconditional structured locality provider; old support-bounds route is problematic; no `PpolyDAG` / pnp4 mainline bridge. |
| Full MCSP | Not the focus. Some imports and analogies exist outside scope, but audited declarations are partial-specific. | Not audited here. | Need separate audit of non-partial magnification files before reuse. |
| AC⁰[p] | Not directly. The audited files discuss/formalize AC0/formula-track Step-C statements, not a prime-modular AC⁰[p] lower-bound endpoint. | AC0 side-track statements kernel-check via imported partial formula core. | No explicit AC⁰[p] bridge to `PpolyDAG` or `VerifiedNPDAGLowerBoundSource`. |

## 13. pnp4 integration analysis

- The audited pnp3 modules are listed in `lakefile.lean`, so they are build-visible.
- I found no direct pnp4 import/use of `Bridge_to_Magnification_Partial`, `StructuredLocalityProviderPartial`, or the `NP_not_subset_PpolyFormula_from_partial_formulas*` endpoints in pnp4 source by targeted search.
- Existing pnp4 code uses many pnp3 `ComplexityInterfaces` and `Models.Partial.tableLen` definitions, but that does not equal integration of the audited partial-magnification bridge.
- Usable from pnp4 as-is: definitions/theorems can be imported by module name if an adapter wants a pnp3 formula-track side-track theorem.
- Needs adapter modules: any pnp4 use should wrap these as restricted lower-bound side-track artifacts and explicitly state that they do not produce `VerifiedNPDAGLowerBoundSource` or `NP_not_subset_PpolyDAG`.
- Requires operator decision: whether to preserve old `FormulaSupportRestrictionBoundsPartial` compatibility APIs, quarantine them further, or migrate consumers to `_fromPipeline` only.

## 14. Reuse map

### Safe to reuse

- `SmallGeneralCircuitSolver_Partial` and `.decide` / `.correct_decide` as the canonical partial general-solver interface.
- `locality_lift_partial*` only as conditional facades with explicit stable/shrinkage/certificate inputs.
- `PipelineStatements_Partial` Step-C lemmas as AC0/formula side-track statements.
- `FormulaLowerBoundHypothesisPartial_semantic` and `formula_hypothesis_from_pipeline_partial_semantic` as staged side-track hypotheses, not as pnp4 mainline lower-bound sources.
- `OPS_trigger_*_semantic` and `Bridge_to_Magnification_Partial` endpoints as conditional bridge wrappers when provider and NP-strict assumptions are explicit.
- `_fromPipeline` predicates as safer replacements for old universal support-bounds, subject to explicit provenance.

### Avoid / do not touch without operator decision

- Do not use `FormulaSupportRestrictionBoundsPartial` as an active progress premise; comments identify it as vulnerable/vacuous via arbitrary formula hardwiring.
- Do not promote `hasDefault*` flags or `defaultStructuredLocalityProviderPartial` into ambient facts or instances.
- Do not treat `StructuredLocalityProviderPartial` as proven unless a concrete provider is supplied from audited premises.
- Do not present any formula/locality/AC0 side-track separation as progress toward `P != NP` unless a `PpolyDAG` / `VerifiedNPDAGLowerBoundSource` bridge is supplied.
- Do not edit trust-root files as part of any follow-up from this audit unless separately authorized.

## 15. Gap map

### A. Engineering gaps

1. No small pnp4 adapter/quarantine module documents these partial-magnification endpoints as side-track-only.
2. pnp4 does not appear to expose/import the audited bridge endpoints directly; if needed, an adapter should be explicit and audited.
3. Large `LocalityProvider_Partial.lean` mixes active, migration, default, and old compatibility APIs; future readers can easily misuse names.

### B. Formalization gaps

1. `StructuredLocalityProviderPartial` remains a Prop-level provider contract.
2. `_fromPipeline` support-bound predicates still require concrete AC0 provenance and semantic links.
3. Certificate and restricted-behavior provider Props package nontrivial existence/transport obligations.
4. Default `Nonempty` flags extract providers but do not prove their contents unconditionally.

### C. Mathematical gaps

1. No construction of `NP_not_subset_PpolyDAG`.
2. No construction of `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.
3. No search-to-decision MCSP lower-bound route.
4. No barrier-bypass theorem for hardwiring/support-cardinality pitfalls; the file documents one old route as vacuous.

### D. Governance gaps

1. Legacy universal support-bound APIs remain available and have compatibility theorems.
2. `default*` names can be misread as canonical facts rather than extraction from explicit `Nonempty` hypotheses.
3. The partial-magnification area needs a clearer active-vs-legacy surface list for Phase 1 workers.

## 16. Recommended Phase 1+ tasks

### Task 1 — Markdown quarantine note for old partial support bounds

- **Exact files to touch:** `pnp3/Docs/PhaseI_Verifier_Design.md` or a new markdown-only audit/governance note chosen by the operator.
- **Allowed scope:** Document that `FormulaSupportRestrictionBoundsPartial` is legacy/vacuous-risk and that `_fromPipeline` predicates are the safer staged surface.
- **Forbidden scope:** No Lean edits; no theorem changes; no endpoint promotion.
- **Expected output:** A concise operator-facing note linking old and new names.
- **Estimated time:** 1-2 hours.
- **Dependency on other audits:** Cross-check with A09/NoGoLog if available.
- **Risk level:** Low.
- **Type:** markdown-only / operator decision.

### Task 2 — Lean audit-only test that old partial support-bound route is not imported by pnp4 mainline

- **Exact files to touch:** A new or existing pnp4 audit/test file selected by operator, likely under `pnp4/Pnp4/Tests/`.
- **Allowed scope:** Add negative/audit surface checks for names that must remain side-track or absent from mainline exports.
- **Forbidden scope:** No construction of `StructuredLocalityProviderPartial`; no `ResearchGapWitness`; no `VerifiedNPDAGLowerBoundSource`; no P-vs-NP endpoint changes.
- **Expected output:** Kernel-checked guardrail preventing accidental mainline promotion of old support-bound/default provider names.
- **Estimated time:** 0.5-1 day.
- **Dependency on other audits:** Should wait for operator decision on naming quarantine and any A07/A09 findings.
- **Risk level:** Medium because test design can be brittle.
- **Type:** Lean audit/test only.

### Task 3 — pnp4 side-track adapter inventory, not theorem promotion

- **Exact files to touch:** New markdown report or a pnp4 documentation file; if Lean is authorized, a deliberately named side-track adapter module under `pnp4/Pnp4/AlgorithmsToLowerBounds/`.
- **Allowed scope:** Inventory which partial formula/real bridge theorems can be imported, and wrap them with comments classifying them as restricted side-track.
- **Forbidden scope:** No `PpolyDAG` bridge, no `VerifiedNPDAGLowerBoundSource`, no `NP_not_subset_PpolyDAG`, no `P_ne_NP` claim.
- **Expected output:** Clear map from pnp3 partial endpoints to pnp4 side-track terminology.
- **Estimated time:** 0.5-1 day for markdown; 1-2 days if Lean adapter is requested.
- **Dependency on other audits:** Depends on pnp4 bridge/source-obligation audits.
- **Risk level:** Medium.
- **Type:** operator decision; markdown-first preferred.

### Task 4 — LocalityProvider active-surface split proposal

- **Exact files to touch:** Markdown design note first; Lean split only after operator approval.
- **Allowed scope:** Propose moving legacy/default/provider wrappers into clearly named sections or modules without changing theorem content.
- **Forbidden scope:** No implementation in this audit; no weakening/deleting guardrails; no route promotion.
- **Expected output:** A migration checklist identifying active, compatibility, and legacy/vacuous-risk declarations.
- **Estimated time:** 0.5 day for design; 2-4 days if later implemented in Lean.
- **Dependency on other audits:** Should wait for full final-result and singleton-density audits.
- **Risk level:** Medium-high because `LocalityProvider_Partial.lean` has many downstream consumers.
- **Type:** markdown-only initially; possible Lean refactor later.

## 17. Stop / hold recommendations

- Hold any task that uses `FormulaSupportRestrictionBoundsPartial` or `hasDefaultFormulaSupportRestrictionBoundsPartial` as a progress premise without explicitly acknowledging the vacuous/hardwiring issue.
- Downgrade any planned pnp4 integration of these files from “mainline P-vs-NP progress” to “restricted lower-bound side-track infrastructure” unless it adds an explicit `PpolyDAG` / `VerifiedNPDAGLowerBoundSource` bridge.
- Rename or quarantine “default” provider tasks if the plan is to create ambient providers; all provider extraction should remain explicit.
- Do not dispatch Phase 2/3/4/5 implementation from this audit until the operator decides whether old support-bound compatibility should remain exposed.

## 18. Honest caveats

- I did not reconstruct every proof term in all 3,677 LOC of `LocalityProvider_Partial.lean`; I audited it by declarations, searches, and targeted section reads.
- I did not audit all imported `LowerBounds.*`, `ThirdPartyFacts.*`, or `AC0LocalityBridge` theorem bodies.
- I verified signatures and route shape, not the mathematical adequacy of the imported partial formula lower-bound core.
- I did not perform a complete import-graph analysis beyond the six scoped files and targeted pnp4 searches.
- I did not modify Lean code or add NoGoLog entries.

## 19. Commands run

- `find .. -name AGENTS.md -print` — found repository `AGENTS.md` only.
- `git status --short --branch` — checked initial branch/status.
- `sed -n ...` over required reading and all six audited files — read required docs and scoped files/chunks.
- `rg -n "^(def|abbrev|theorem|lemma|structure|class|instance|opaque|axiom|noncomputable def|inductive)\b|^\s*\[.*instance|^attribute \[instance\]" pnp3/Magnification/*_Partial.lean` — declaration inventory.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" <six-file-scope>` — 0 matches.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" <six-file-scope>` — expected `_Partial` hits plus support-bound/migration comments; no active `RefutedRoute`, `Vacuous`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, or `TODO` hits.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" <six-file-scope>` — 68 hits, all in `LocalityProvider_Partial.lean` by file-count summary.
- `rg -c "\baxiom\b|\bsorry\b|\badmit\b|\bopaque\b|native_decide" <six-file-scope>` — 0 matches.
- `rg -n "Bridge_to_Magnification_Partial|StructuredLocalityProviderPartial|NP_not_subset_PpolyFormula_from_partial" pnp4` — no direct pnp4 use found by targeted search.
- `./scripts/check.sh` — passed: full Lean build, hygiene scans, governance checks, smoke probes, JSONL validation, candidate verifier smoke, axiom-surface dumps, barrier audit module, and unconditional witness gate all completed with `All checks passed`.

## 20. Audit completeness

Estimated careful-read coverage: about **78% of LOC carefully read**, with complete reading of the five small scoped files and structural/targeted reading of the large `LocalityProvider_Partial.lean`. The declarations and required searches covered 100% of the six scoped files textually.

Recommended Phase 1+ tasks count: **4**.
