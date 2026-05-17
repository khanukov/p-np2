# A01 audit: `pnp3/Magnification/*_Partial.lean`

Task: A01  
Engineer handle: codex  
Branch: `khanukov/phase1-A01-codex`  
Audit date: 2026-05-17  
Scope classification: Infrastructure / audit-only. No Lean code was edited.

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL.**

The six audited `_Partial.lean` files contain a kernel-checked partial-MCSP formula/locality pipeline, but the reusable part is conditional: it converts explicit Step-C / locality-provider / certificate packages into `NP_not_subset_PpolyFormula` or `NP_not_subset_PpolyReal`, not into the pnp4 mainline `VerifiedNPDAGLowerBoundSource` or `NP_not_subset_PpolyDAG`. The strongest files are not merely stubs: `PipelineStatements_Partial.lean`, `Facts_Magnification_Partial.lean`, `LocalityLift_Partial.lean`, and parts of `LocalityProvider_Partial.lean` contain Lean proofs wiring lower-bound core contradictions to locality and separation conclusions. However, much of `LocalityProvider_Partial.lean` is staged as structures/Prop provider interfaces; several routes are explicitly support-bound based and documented as known inconsistent/refuted or vacuous if reused without provenance restrictions. pnp4 integration is therefore possible only as a restricted formula/AC0/partial-MCSP side track or as an adapter around explicit conditional contracts; it is not mainline P-vs-NP progress without a separate `PpolyDAG`/`VerifiedNPDAGLowerBoundSource` bridge.

## 2. Executive summary

These files are **partial but not complete** for the partial-MCSP variant. They do define a coherent partial-MCSP formula/locality surface: partial AC0 Step-C statements, locality-lift façade functions, structured locality providers, and conditional bridges to `NP_not_subset_PpolyFormula` / `NP_not_subset_PpolyReal`. They are not a completed unconditional partial-MCSP lower-bound route because the high-level outputs still require a structured locality provider, an NP-strict witness for `gapPartialMCSP_Language p`, and usually a formula lower-bound hypothesis or auto-produced Step-C hypothesis; support-bound routes must be treated as refuted/vacuous unless provenance-restricted. A usable pnp4 integration path **needs work**: pnp4 can import the compiled pnp3 modules, but any adapter must label this as a restricted formula/partial-MCSP side track and must not promote it to `VerifiedNPDAGLowerBoundSource` or `P_ne_NP`.

## 3. Files audited

| File | Approximate role | Read mode | Notes |
| --- | --- | --- | --- |
| `RESEARCH_CONSTITUTION.md` | Governance/trust-root rules | Skimmed structurally | Read required target/rule sections; not audited as code. |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | Phase/worker instructions | Skimmed structurally | Older E-task naming ignored per user override. |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | Shared worker constraints | Skimmed structurally | Used for no-edit/no-push/report expectations; naming overridden by prompt. |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A01_audit_pnp3_magnification_partial.md` | Exact A01 task | Read fully | Defines the six-file audit and report requirements. |
| `pnp3/Magnification/Facts_Magnification_Partial.lean` | OPS-style partial formula triggers | Read fully | 235 LOC. |
| `pnp3/Magnification/PipelineStatements_Partial.lean` | Partial Step-C / AC0 statement API | Read fully | 286 LOC. |
| `pnp3/Magnification/LocalityProvider_Partial.lean` | Large provider/certificate/locality wiring layer | Read structurally with detailed inspection of declaration blocks and risky sections | 3,677 LOC; audited by imports, declaration inventory, keyword searches, and targeted reading of support-bound/provider/default sections. |
| `pnp3/Magnification/LocalityInterfaces_Partial.lean` | Partial general-solver interfaces | Read fully | 57 LOC. |
| `pnp3/Magnification/LocalityLift_Partial.lean` | Façade over third-party partial locality lift | Read fully | 100 LOC. |
| `pnp3/Magnification/Bridge_to_Magnification_Partial.lean` | Partial formula/real separation endpoints | Read fully | 119 LOC. |
| `pnp3/Complexity/Interfaces.lean` | Trust-root complexity interfaces | Searched + skimmed key definitions | Used to interpret `PpolyFormula`, `PpolyReal`, `NP_strict`, `NP_not_subset_*`, `P_ne_NP`. |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | Trust-root research-gap packaging | Searched + skimmed | Used only to confirm audited files do not construct `ResearchGapWitness`. |
| `outputs/nogolog.jsonl` | NoGo ledger | Searched/skipped after line count | Only 9 lines; consulted as optional context, not edited. |

Audit completeness estimate: about **85% of LOC carefully read or structurally audited**. The only file not read proof-by-proof was `LocalityProvider_Partial.lean`; it was audited by full declaration inventory plus targeted reads of each architectural/risk block.

## 4. File-by-file audit

### 4.1 `pnp3/Magnification/LocalityInterfaces_Partial.lean`

**Imports / dependencies.** Imports `Mathlib.Data.Finset.Basic`, `Complexity.Promise`, `Complexity.Interfaces`, `Core.BooleanBasics`, and `Models.Model_PartialMCSP`.

**Top-level structures and theorems.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `GeneralCircuitParametersPartial` | numeric `n`, `size`, `depth` | canonical interface | none |
| `SmallGeneralCircuitParamsPartial` | wraps general params plus `same_n = partialInputLen p` | canonical interface | none |
| `SmallGeneralCircuitSolver_Partial` | semantic decider/witness satisfying `SolvesPromise (GapPartialMCSPPromise p)` | canonical interface | no `ResearchGapWitness`; uses trust-root semantic decider/promise notions |
| `SmallGeneralCircuitSolver_Partial.decide` | evaluator from solver witness | canonical helper | none |
| `SmallGeneralCircuitSolver_Partial.correct_decide` | proves `solver.decide` solves the partial promise | canonical helper | none |

**Kernel-checked content.** The file proves only a convenience lemma: the packaged `correct` field for a `SmallGeneralCircuitSolver_Partial` is definitionally the correctness of `solver.decide`. This is honest interface plumbing.

**Staged/Prop-only content.** No Prop-only lower-bound package here beyond the `correct` field in the solver structure.

**Classical.choose / noncomputable / axiom / sorry.** Zero `Classical.choose`; zero `noncomputable def`; zero `axiom`, `opaque`, `sorry`, `admit`.

**Trust-root dependencies.** Uses `ComplexityInterfaces.SemanticDecider` and `Complexity.Promise.SolvesPromise`; no `NP_not_subset_PpolyDAG`, `P_ne_NP`, or `ResearchGapWitness`.

### 4.2 `pnp3/Magnification/LocalityLift_Partial.lean`

**Imports / dependencies.** Imports `LowerBounds.AntiChecker_Partial`, `Models.Model_PartialMCSP`, `Magnification.LocalityInterfaces_Partial`, and `ThirdPartyFacts.PartialLocalityLift`.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `locality_lift_partial` | from a `SmallGeneralCircuitSolver_Partial`, a stable restriction witness, and a `ShrinkageWitness.Provider`, returns `∃ T loc`, with polylog/cardinality/size/depth bounds | conditional adapter theorem/def | relies on provider and stable restriction payload, not DAG/source objects |
| `locality_lift_partial_of_certificate` | same output from a `ShrinkageCertificate.Provider` instance plus half-table bound | conditional adapter | typeclass provider is explicit local hypothesis |
| `locality_lift_partial_of_certificate_auto` | same output from certificate provider plus `HalfTableCertificateBound` instance | conditional adapter with typeclass inputs | possible hidden-payload risk if used implicitly in candidates; harmless in this audited module |
| `no_general_solver_of_no_local_partial` | no local solvers + lift hypotheses imply no general solver | conditional contrapositive helper | no research-gap dependency |

**Kernel-checked content.** This file is a thin façade: the three lift functions are kernel-checked aliases/applications of `ThirdPartyFacts.locality_lift_partial*`, and `no_general_solver_of_no_local_partial` proves that if every local solver is false, then any general solver satisfying the lift hypotheses is false.

**Staged/Prop-only content.** None introduced, except the provider/certificate hypotheses consumed from `ThirdPartyFacts`.

**Classical.choose / noncomputable / axiom / sorry.** Zero `Classical.choose`; zero `noncomputable def`; zero `axiom`, `opaque`, `sorry`, `admit`.

**Trust-root dependencies.** None beyond partial-MCSP models and local solver interfaces.

### 4.3 `pnp3/Magnification/PipelineStatements_Partial.lean`

**Imports / dependencies.** Imports `LowerBounds.LB_Formulas_Core_Partial`, `Models.Model_PartialMCSP`, and real-power Mathlib support.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `AC0StatementPartial_semantic` | every `SmallAC0Solver_Partial p` with `AC0EasyFamilyDataPartial` gives `False` | canonical partial Step-C Prop | depends on Step-C/easy-family payload, not DAG/source |
| `AC0StatementPartial` | abbrev for semantic statement | canonical alias | same |
| `AC0StatementPartial_constructive` | every constructive small AC0 solver gives `False` | canonical partial Step-C Prop | constructive solver package |
| `AC0StatementPartial_closed` | every syntactic small AC0 solver gives `False` | canonical closed Prop | syntactic solver package |
| `AC0StatementPartial_providerClosed` | solver plus `StepCClosureDataPartialProvider` gives `False` | staged Prop/interface | provider payload |
| `AC0StatementPartial_constructive_providerClosed` | constructive solver gives false using provider-closed closure | staged/canonical interface | provider payload internalized in solver |
| `AC0StatementPartial_fully_closed` | closure package plus solver gives `False` | staged Prop/interface | `StepCClosureDataPartial` hard payload |
| `AC0BoundedStatementPartial_semantic` | bounded-size semantic AC0 solver contradiction | canonical conditional Prop | size bound plus easy-family payload |
| `AC0BoundedStatementPartial_constructive` | bounded constructive AC0 solver contradiction | canonical conditional Prop | size bound |
| `FormulaLowerBoundHypothesisPartial` | `(0 : Rat) < δ ∧ AC0BoundedStatementPartial_semantic p δ` | staged hypothesis package | Step-C contradiction field |
| `FormulaLowerBoundHypothesisPartial_semantic` | abbrev of the formula hypothesis | alias | same |
| `ac0_statement_from_pipeline_partial_*` lemmas | derive the above Step-C statements from `LB_Formulas_Core_Partial` theorems | kernel-checked adapter lemmas | no `ResearchGapWitness`; depends on imported Step-C core theorems |
| `formula_hypothesis_from_pipeline_partial_semantic` | derives `(0<δ ∧ bounded semantic Step-C)` from `hδ` and core theorem | kernel-checked adapter | no DAG/source |

**Kernel-checked content.** The file proves that the imported lower-bound core (`LB_Formulas_core_partial_*`, `gapPartialMCSP_no_semantic_AC0_solver`, etc.) inhabits the local Step-C statement interfaces. In particular, `formula_hypothesis_from_pipeline_partial_semantic` creates a semantic formula lower-bound hypothesis from a positive `δ`, and `ac0_statement_from_pipeline_partial_fully_closed` turns a `StepCClosureDataPartial p` closure package into `∀ solver, False`.

**Staged/Prop-only content.** The main definitions are honest staging of Step-C obligations. The potentially hard payloads are the closure/provider/easy-family packages; the file does not manufacture them from nothing.

**Classical.choose / noncomputable / axiom / sorry.** Zero `Classical.choose`; zero `noncomputable def`; zero `axiom`, `opaque`, `sorry`, `admit`.

**Trust-root dependencies.** No `NP_not_subset_PpolyDAG`, `P_ne_NP`, or `ResearchGapWitness`; all conclusions are AC0/partial Step-C contradictions.

### 4.4 `pnp3/Magnification/Facts_Magnification_Partial.lean`

**Imports / dependencies.** Imports the partial model, local anti-checker, partial pipeline statements, and complexity interfaces.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `GeneralLowerBoundHypothesisPartial` | `(0 : Rat) < ε ∧ statement` | harmless staged wrapper | arbitrary `statement : Prop` |
| `RestrictionLocalityPartial` | existence of polylog test set `T` and `SmallLocalCircuitSolver_Partial p` | staged Prop / locality payload | local solver payload |
| `StructuredLocalityProviderPartial` | formula hypothesis + `PpolyFormula gapPartialMCSP` -> `RestrictionLocalityPartial p` | staged provider interface | provider is hard residual obligation |
| `StructuredLocalityProviderPartial_semantic` | semantic counterpart of provider | staged provider interface | same |
| `OPS_trigger_general_contra_structured_with_provider_partial` | provider + `NP_strict gapPartialMCSP` + formula hypothesis refutes universal `NP_strict -> PpolyFormula` | conditional theorem | provider, NP-strict witness, formula hypothesis |
| `OPS_trigger_formulas_contra_structured_with_provider_partial` | formula-track contra theorem | conditional theorem | same |
| `OPS_trigger_formulas_partial_of_provider` | provider + `NP_strict` + `PpolyReal -> PpolyFormula` embed + formula hyp -> `NP_not_subset_PpolyReal` | conditional theorem | no DAG/source; uses formula/real separation target |
| `OPS_trigger_formulas_partial_of_provider_global_embed` | global embed variant | conditional theorem | same |
| `OPS_trigger_formulas_partial_of_provider_formula_separation` | provider + `NP_strict` + formula hyp -> `NP_not_subset_PpolyFormula` | conditional theorem | no DAG/source |
| `OPS_trigger_formulas_partial_of_provider_formula_separation_strict` | strict-track formula separation | conditional theorem | no DAG/source |
| semantic variants | same conclusions using semantic provider/hypothesis | conditional theorems | no DAG/source |

**Kernel-checked content.** Given a structured locality provider, a strict NP witness for `gapPartialMCSP_Language p`, and a formula lower-bound hypothesis, the file proves separation against `PpolyFormula` or `PpolyReal`. The contradiction is obtained by assuming all strict-NP languages have formula/real nonuniform families, extracting a `PpolyFormula` witness for the partial MCSP language, applying the provider to get a local solver, and contradicting `noSmallLocalCircuitSolver_partial_v2`.

**Staged/Prop-only content.** `RestrictionLocalityPartial` and both structured providers are Prop-only packages. This is honest staging if treated as the residual locality/magnification obligation; it becomes wrapper risk if downstream code treats `StructuredLocalityProviderPartial` as already established.

**Classical.choose / noncomputable / axiom / sorry.** Zero `Classical.choose`; zero `noncomputable def`; zero `axiom`, `opaque`, `sorry`, `admit`.

**Trust-root dependencies.** Uses `PpolyFormula`, `PpolyReal`, `NP_strict`, `NP_not_subset_PpolyFormula`, and `NP_not_subset_PpolyReal`. No `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, `ResearchGapWitness`, `SourceTheorem`, or `gap_from` occur in this file.

### 4.5 `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`

**Imports / dependencies.** Imports partial pipeline/facts, complexity interfaces, partial model, and `ThirdPartyFacts.PpolyFormula`.

**Top-level declarations.**

| Declaration | Signature summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `NP_not_subset_PpolyFormula_from_partial_formulas` | provider + formula hyp + `NP_strict gapPartialMCSP` -> `NP_not_subset_PpolyFormula` | conditional endpoint | no DAG/source; provider+hyp+NP strict |
| `NP_not_subset_PpolyReal_from_partial_formulas` | same for `PpolyReal`, using trivial realization bridge | conditional endpoint | no DAG/source |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic` | semantic provider/hyp variant | conditional endpoint | no DAG/source |
| `NP_not_subset_PpolyReal_from_partial_formulas_semantic` | semantic provider/hyp variant | conditional endpoint | no DAG/source |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto` | semantic provider + positive δ + NP-strict -> formula separation | conditional endpoint | still requires provider and NP-strict |
| `NP_not_subset_PpolyReal_from_partial_formulas_semantic_auto` | semantic provider + positive δ + NP-strict -> real separation | conditional endpoint | still requires provider and NP-strict |

**Kernel-checked content.** The bridge exports clean conditional endpoints from the facts layer. The “auto” variants use `formula_hypothesis_from_pipeline_partial_semantic` to discharge the formula lower-bound hypothesis from `0 < δ`; they do not discharge the structured locality provider or `NP_strict (gapPartialMCSP_Language p)`.

**Staged/Prop-only content.** No new provider Prop is defined here; the file consumes staged providers from `Facts_Magnification_Partial.lean`.

**Classical.choose / noncomputable / axiom / sorry.** Zero `Classical.choose`; zero `noncomputable def`; zero `axiom`, `opaque`, `sorry`, `admit`.

**Trust-root dependencies.** Uses `NP_not_subset_PpolyFormula`, `NP_not_subset_PpolyReal`, `NP_strict`, `PpolyFormula`, `PpolyReal`; no DAG/source/research-gap dependency.

### 4.6 `pnp3/Magnification/LocalityProvider_Partial.lean`

**Imports / dependencies.** Imports `Facts_Magnification_Partial`, `LocalityLift_Partial`, `AC0LocalityBridge`, `LB_Formulas_Core_Partial`, and `ThirdPartyFacts.PartialLocalityLift`.

**Major declaration groups.**

| Group / declarations | Summary | Classification | Hard dependency |
| --- | --- | --- | --- |
| `generalSolverOfFormula`, `stableWitness_of_formula_supportBound`, `stableWitness_of_formula_sizeBound` | extract a partial general solver from a `PpolyFormula` witness and prove stable restrictions from support/size bounds | conditional/kernel-checked extraction | uses `Classical.choose hFormula` to unpack formula witness |
| `ConstructiveLocalityEnginePartial`, `FormulaToGeneralLocalityDataPartial`, `FormulaRestrictionCertificateDataPartial` | packages provider/stability/restriction obligations | staged Prop/structure fields | locality provider payload |
| `FormulaSupportRestrictionBoundsPartial` | universal support-bound assumption over every formula witness | **refuted/vacuous risk** | documented as known inconsistent |
| `FormulaSupportBoundsPartial_fromPipeline`, `_fixedParams` | provenance-restricted replacement contracts | staged Prop / more honest interface | AC0 provenance/semantic-link payload |
| `StructuredLocalityProviderPartial_fromPipeline` and `_of_old` | pipeline provider interface and legacy adapter from old provider | staged + legacy adapter | old provider route can inherit legacy risk |
| `FormulaRestrictionCertificateDataPartial_fromPipeline` and `_of_old` | certificate data with pipeline provenance | staged interface + legacy adapter | provider payload |
| `ExtractedLocalCorePartial`, `GenericExtractedLocalCorePartial`, `WeakGenericExtractedLocalCorePartial`, provider defs | local-core extraction interfaces | staged Prop/structure | local-core/provenance obligations |
| `RestrictedLocalBehaviorSolver_Partial`, `GenericRestrictedBehaviorCertificatePartial`, weak/generic/globalize/preservation defs | restricted-behavior interfaces and transports | staged interface with several kernel-checked transports | promise-preservation/globalization payload |
| Multiswitching/core-step theorems (`formula_support_bounds_from_multiswitching`, `extracted_local_core_provider_of_multiswitching_contract`, etc.) | adapters from `AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract` to support/core/provider packages | conditional theorems | hard AC0/multiswitching contract; some paths pass through support-bound assumptions |
| `FormulaCertificateProviderPartial`, `FormulaCertificateProviderPartial_fromPipeline` | package certificate production functions | staged provider structures | certificate payload; audit-class suspicious comments present |
| Default flags (`hasDefault*`, `default*`) | `Nonempty` wrappers and `Classical.choice` extraction of default packages | wrapper risk if used as hidden payload | no instances, but noncomputable default extraction requires explicit `Nonempty` proof |
| `structuredLocalityProviderPartial_*` | many constructors from engine/cert/support/multiswitching/core packages to `StructuredLocalityProviderPartial` | conditional theorems | provider/certificate/support contracts; no DAG/source |

**Kernel-checked content.** This file proves many adapters among the staged locality/certificate interfaces. Important examples:

- `generalSolverOfFormula` constructs a `SmallGeneralCircuitSolver_Partial p` from a `PpolyFormula (gapPartialMCSP_Language p)` by extracting the formula witness and proving it solves the partial promise.
- `stableWitness_of_formula_supportBound` and `stableWitness_of_formula_sizeBound` turn explicit support/size bounds into stable-restriction witnesses.
- `formulaRestrictionCertificateData_of_supportBounds` and related constructors turn numeric support-bound packages into certificate data; these are kernel-checked but may be ex-falso if the support-bound package is inconsistent.
- `structuredLocalityProviderPartial_of_engine`, `structuredLocalityProviderPartial_of_formulaCertificate`, `structuredLocalityProviderPartial_of_restrictionData`, and many later variants build `StructuredLocalityProviderPartial` from explicit engines/certificates/local-core providers.
- `defaultStructuredLocalityProviderPartial` extracts a structured provider from an explicit `Nonempty ConstructiveLocalityEnginePartial` flag.

**Staged/Prop-only content.** This is the most staged file in scope. The core mathematical obligations are mostly structure fields or Prop-valued provider definitions: stable restrictions, shrinkage providers, support bounds, AC0 provenance, semantic links, local-core extraction, restricted behavior, promise preservation, globalization, and default `Nonempty` flags. The staging is useful as API design, but it is not by itself proof of a genuine lower bound.

**Classical.choose / noncomputable / axiom / sorry.** `Classical.choose` occurs 42 times in the audited scope, all in this file. There are 24 `noncomputable def` declarations in the audited scope, all in this file. No `axiom`, `opaque`, `sorry`, or `admit` was found in any of the six audited files.

**Trust-root dependencies.** Uses `PpolyFormula`, formula circuit size/support/eval, `NP_not_subset_*` indirectly through imported facts, and partial promise semantics. It does not mention `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPMagnificationContract`, `SourceTheorem`, or `gap_from`.

## 5. Cross-file dependency graph

```text
LocalityInterfaces_Partial
  imports Complexity.Promise, Complexity.Interfaces, Core.BooleanBasics,
          Models.Model_PartialMCSP

LocalityLift_Partial
  imports LocalityInterfaces_Partial,
          LowerBounds.AntiChecker_Partial,
          Models.Model_PartialMCSP,
          ThirdPartyFacts.PartialLocalityLift

PipelineStatements_Partial
  imports LowerBounds.LB_Formulas_Core_Partial,
          Models.Model_PartialMCSP,
          Mathlib.Analysis.SpecialFunctions.Pow.Real

Facts_Magnification_Partial
  imports PipelineStatements_Partial,
          Models.Model_PartialMCSP,
          LowerBounds.AntiChecker_Partial,
          Complexity.Interfaces

Bridge_to_Magnification_Partial
  imports PipelineStatements_Partial,
          Facts_Magnification_Partial,
          Complexity.Interfaces,
          Models.Model_PartialMCSP,
          ThirdPartyFacts.PpolyFormula

LocalityProvider_Partial
  imports Facts_Magnification_Partial,
          LocalityLift_Partial,
          Magnification.AC0LocalityBridge,
          LowerBounds.LB_Formulas_Core_Partial,
          ThirdPartyFacts.PartialLocalityLift
```

No import cycle among the six audited files was found from the import declarations. The sibling dependency shape is a DAG: `LocalityInterfaces` feeds `LocalityLift`; `PipelineStatements` feeds `Facts`; `Facts` feeds both `Bridge` and `LocalityProvider`; `LocalityProvider` additionally depends on `LocalityLift`. Hidden dependencies are not import-cycle hidden, but they are payload hidden in the sense that `LocalityProvider_Partial.lean` introduces many Prop/structure fields whose names can make downstream routes look complete unless the required provider inputs are tracked.

## 6. Top-level theorem / structure inventory

The complete declaration scan found:

| File | Structures | Defs/abbrevs, including noncomputable | Lemmas/theorems | Notes |
| --- | ---: | ---: | ---: | --- |
| `LocalityInterfaces_Partial.lean` | 3 | 1 | 1 | Small, canonical interfaces. |
| `LocalityLift_Partial.lean` | 0 | 4 | 0 | Thin façade/adapters. |
| `PipelineStatements_Partial.lean` | 0 | 11 | 15 | AC0/Step-C statement layer. |
| `Facts_Magnification_Partial.lean` | 0 | 4 | 9 | OPS trigger/separation layer. |
| `Bridge_to_Magnification_Partial.lean` | 0 | 0 | 6 | Export endpoints. |
| `LocalityProvider_Partial.lean` | about 16 | about 48 | about 55 | Large staged provider/certificate/local-core layer. |

Important declarations and classification:

| Declaration | File | Type/signature summary | Classification | Depends on hard payload? |
| --- | --- | --- | --- | --- |
| `SmallGeneralCircuitSolver_Partial` | `LocalityInterfaces_Partial.lean` | solver for `GapPartialMCSPPromise p` | canonical | no research-gap/DAG payload |
| `locality_lift_partial` | `LocalityLift_Partial.lean` | stable general solver + shrinkage provider -> local solver/test set | conditional | shrinkage provider, stable restriction |
| `AC0StatementPartial_semantic` | `PipelineStatements_Partial.lean` | no semantic AC0 solver with easy-family data | staged Prop / canonical interface | easy-family payload |
| `FormulaLowerBoundHypothesisPartial` | `PipelineStatements_Partial.lean` | positive δ plus bounded Step-C contradiction | staged Prop | Step-C contradiction |
| `formula_hypothesis_from_pipeline_partial_semantic` | `PipelineStatements_Partial.lean` | positive δ -> formula lower-bound hypothesis | canonical adapter | imported lower-bound core |
| `StructuredLocalityProviderPartial` | `Facts_Magnification_Partial.lean` | formula hyp + formula witness -> restriction locality | staged Prop / hard residual interface | locality provider hard payload |
| `OPS_trigger_formulas_partial_of_provider_formula_separation` | `Facts_Magnification_Partial.lean` | provider + NP-strict + formula hyp -> `NP_not_subset_PpolyFormula` | conditional theorem | provider, NP-strict, formula hyp |
| `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto` | `Bridge_to_Magnification_Partial.lean` | semantic provider + positive δ + NP-strict -> formula separation | conditional endpoint | provider and NP-strict still hard |
| `FormulaSupportRestrictionBoundsPartial` | `LocalityProvider_Partial.lean` | universal support bounds over arbitrary formula witnesses | refuted route / legacy-vacuous risk | hard/inconsistent support payload |
| `FormulaSupportBoundsPartial_fromPipeline` | `LocalityProvider_Partial.lean` | provenance-restricted support bounds with AC0 data | staged Prop / honest replacement | AC0 provenance and semantic-link payload |
| `FormulaCertificateProviderPartial` | `LocalityProvider_Partial.lean` | certificate provider structure | staged provider | certificate hard payload |
| `defaultStructuredLocalityProviderPartial` | `LocalityProvider_Partial.lean` | `Nonempty ConstructiveLocalityEnginePartial` -> provider | wrapper-risk theorem | Nonempty engine payload |

None of the audited declarations depends on `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPMagnificationContract`, `SourceTheorem`, or `gap_from` by textual search.

## 7. Kernel-checked content

The repository currently kernel-checks the following useful facts in this area:

1. **Partial general solver interface correctness.** A `SmallGeneralCircuitSolver_Partial` induces a decision function satisfying the same partial promise correctness field already stored in the solver.
2. **Locality lift façade.** Given explicit stable-restriction and shrinkage-provider/certificate hypotheses, `LocalityLift_Partial.lean` returns an explicit local solver and test set with polylog and size/depth bounds.
3. **Step-C adapters.** `PipelineStatements_Partial.lean` proves that imported lower-bound core theorems imply the partial AC0 statement interfaces, including semantic, constructive, closed, provider-closed, fully-closed, and bounded variants.
4. **Formula-hypothesis auto construction.** A positive `δ` plus the imported partial lower-bound core yields `FormulaLowerBoundHypothesisPartial_semantic p δ`.
5. **OPS trigger.** A structured locality provider, an `NP_strict` witness for the partial MCSP language, and the formula lower-bound hypothesis imply `NP_not_subset_PpolyFormula`; with a realization/embed from real to formula witnesses, they imply `NP_not_subset_PpolyReal`.
6. **Locality-provider adapters.** `LocalityProvider_Partial.lean` proves many implications from explicit engines/certificates/restriction data/support bounds/multiswitching contracts to `StructuredLocalityProviderPartial`.

What is **not** kernel-checked in these six files: a closed `StructuredLocalityProviderPartial`, a closed `NP_strict (gapPartialMCSP_Language p)`, a closed `NP_not_subset_PpolyDAG`, a `ResearchGapWitness`, a pnp4 `VerifiedNPDAGLowerBoundSource`, or a closed `P_ne_NP` result.

## 8. Staged / placeholder / Prop-only content

| Item | Status | Risk assessment |
| --- | --- | --- |
| `AC0StatementPartial_*` | Prop interfaces for AC0 Step-C contradictions | honest staging; some are discharged by imported core theorems |
| `FormulaLowerBoundHypothesisPartial` | Prop package of δ positivity and bounded AC0 contradiction | harmless if tracked as hypothesis; wrapper risk if called “lower bound” without conditions |
| `RestrictionLocalityPartial` | existential local-solver/test-set Prop | honest staging of locality payload |
| `StructuredLocalityProviderPartial` / `_semantic` | high-level provider Prop | hard residual obligation; potential wrapper risk |
| `ConstructiveLocalityEnginePartial` | structure fields for formula-to-general extraction, stability, shrinkage provider | staged provider; useful but not proof by itself |
| `FormulaRestrictionCertificateDataPartial` | structure field returning restriction/certificate data for each formula witness | staged provider; hard payload |
| `FormulaSupportRestrictionBoundsPartial` | universal support-bound Prop | refuted/vacuous route risk; should not be used for progress |
| `FormulaSupportBoundsPartial_fromPipeline` / `_fixedParams` | provenance-aware support-bound replacement | honest staging, but still hard formalization/mathematical payload |
| `Generic*`, `Weak*`, `PromisePreserving*`, `Globalize*` provider defs | local-core/restricted-behavior transport interfaces | honest staging with many hard fields; weak variants need careful naming |
| `hasDefault*` flags | `Nonempty` wrappers around provider structures | wrapper risk if used to hide payload; no instance-based auto-discharge found |

## 9. Refuted / vacuous / legacy route check

Search terms covered: `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `Legacy`, `_Partial`, `TODO`, and `placeholder`.

Findings:

- No `RefutedRoute`, `Vacuous`, `FinalPayloadProvider`, `via_ex_falso`, or `weakRoute` declarations were found inside the six audited files.
- `LocalityProvider_Partial.lean` contains an explicit warning that `FormulaSupportRestrictionBoundsPartial` is known inconsistent in the current formalization and that every theorem depending on it is ex-falso and should not be interpreted as progress.
- The same file contains several support-bound/default-support-bound routes. These are type-correct adapter paths, but anything that depends specifically on the old universal `FormulaSupportRestrictionBoundsPartial` should be classified as refuted/legacy/audit-only unless it is replaced by a provenance-restricted pipeline contract.
- `MagnificationAssumptions` occurs only in comments in this audited scope, as a downstream follow-up mention; it is not defined or used here.
- `_Partial` is pervasive because this is the partial-MCSP API, not by itself a legacy marker.
- No TODO-driven unimplemented Lean proof hole was found.

Isolation assessment: the refuted/vacuous risk is mostly isolated by comments and naming around support-bound routes, but the old support-bound theorem constructors remain callable. Future work should avoid using them in any new endpoint.

## 10. Hidden payload / Rule 16 check

Search terms covered: `class`, `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `Classical.choose`, and `noncomputable def`.

| Occurrence type | Count in audited six files | Interpretation |
| --- | ---: | --- |
| `class` | 2 textual comment/identifier occurrences | harmless; no Lean `class` declarations found in audited files |
| `instance` | 0 for the exact word outside implicit square-bracket provider arguments in declarations; no declarations | no global instance payload introduced |
| `default_instance` | 0 | no risk |
| `attribute [instance]` | 0 | no risk |
| `Fact` | 0 exact word | no `Fact` payload channel found |
| `opaque` | 0 | no risk |
| `Classical.choose` | 42 | standard existential extraction from `PpolyFormula`/`Nonempty`/data proofs, but high-risk if a downstream candidate hides the chosen payload behind defaults |
| `noncomputable def` | 24 | mostly extraction/default provider builders in `LocalityProvider_Partial.lean`; acceptable as explicit conditional adapters, not acceptable as candidate hidden payload |

Classification:

- `generalSolverOfFormula` and related formula witness extraction: **standard exponent/witness extraction** from the trust-root `PpolyFormula` existential.
- `defaultFormulaRestrictionCertificateDataPartial`, `defaultFormulaCertificateProviderPartial`, `defaultStructuredLocalityProviderPartial` path: **wrapper risk** because `Nonempty` flags and `Classical.choice` can make a hard provider appear “default”; still not a Rule-16 violation in this module because no global instance/default instance is declared.
- Certificate/provider constructors with `Provider`, `Payload`, `Witness`, `Source`, or `Default`-like names: **hidden-payload risk if imported into a candidate as assumptions without provenance**. They should remain explicit hypotheses and must not be made typeclass instances or candidate endpoints.

## 11. Barrier relevance

| Barrier / topic | Present in audited area? | Form present | Assessment |
| --- | --- | --- | --- |
| Natural proofs | Not directly | nothing | No natural-proofs theorem in these six files. |
| Relativization | Not directly | nothing | No relativization theorem/interface. |
| Algebrization | Not directly | nothing | No algebrization theorem/interface. |
| Locality | Yes | actual adapter theorems + staged providers | Central to `LocalityLift_Partial` and `LocalityProvider_Partial`; actual theorems are conditional on provider/certificate data. |
| Hardwiring | Yes, in comments/audit warning | markdown/doc comments inside Lean | The support-bound route is warned as broken by truth-table hardwiring. |
| Support-cardinality-only | Yes | staged Prop + warning + support-bound adapters | Old support-bound route is dangerous/refuted; provenance-restricted replacement is staged. |
| Syntax-only filters | Indirect | staged provider/provenance interfaces | No robust syntax-filter theorem in audited files. |
| Normalization filters | Not directly | nothing | No normalization-filter theorem. |
| Search-to-decision | Not directly | nothing | No search-to-decision bridge or MCSP search contract. |
| MCSP / magnification | Yes | actual partial-MCSP formula/locality theorems + staged provider contracts | Restricted partial-MCSP formula track only; no mainline pnp4 DAG bridge. |

## 12. Coverage matrix: partial-MCSP vs full-MCSP vs AC⁰[p]

| Variant | Covered in audited files | Not covered / gaps |
| --- | --- | --- |
| Partial-MCSP | Strongest coverage. Includes `GapPartialMCSPParams`, `gapPartialMCSP_Language`, partial AC0 solver statements, partial local/general solvers, locality lift façade, and formula/real separation endpoints conditional on providers. | No closed structured locality provider; no closed NP-strict witness for the partial MCSP language; old support-bound route is refuted/vacuous without provenance. |
| Full MCSP | Not directly covered. These files are named and typed for `GapPartialMCSPParams` and partial promises. | Needs separate adapter from partial to full MCSP or pnp4-native search/decision target. No such adapter in this six-file scope. |
| AC⁰[p] | Not directly covered as AC0[p]. The files cover AC0/formula/Step-C style partial-MCSP statements and use `SmallAC0Solver_Partial`. | No modulus-`p` AC0[p] lower-bound route or pnp4 `AC0p` bridge in this scope. Treat any AC0[p] integration as separate side-track work. |
| PpolyDAG / pnp4 mainline | Not covered. | No `NP_not_subset_PpolyDAG`, no `VerifiedNPDAGLowerBoundSource`, no `SearchMCSPWeakLowerBound`, no `P_ne_NP`. |

## 13. pnp4 integration analysis

**Usable from pnp4 via existing imports.** The build showed pnp4 and pnp3 compile together, and `./scripts/check.sh` built `Magnification.LocalityInterfaces_Partial`, `Magnification.LocalityLift_Partial`, `Magnification.PipelineStatements_Partial`, `Magnification.Facts_Magnification_Partial`, `Magnification.Bridge_to_Magnification_Partial`, and `Magnification.LocalityProvider_Partial`. Therefore pnp4 can technically import these pnp3 modules if lake module names are available.

**Theorems most suitable for adapter use.**

- `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto`: cleanest conditional formula endpoint; remaining hypotheses are explicit provider, positive δ, and NP-strict partial-MCSP membership.
- `NP_not_subset_PpolyReal_from_partial_formulas_semantic_auto`: same, with real/formula realization handled internally by `ThirdPartyFacts.PpolyFormula`.
- `locality_lift_partial*`: low-level adapters if pnp4 needs a typed partial locality-lift surface.
- `formula_hypothesis_from_pipeline_partial_semantic`: useful to avoid re-proving the Step-C formula hypothesis.

**Needs adapter modules in pnp4.** Any pnp4 use needs a thin adapter that states exactly what pnp4 object it wants: restricted formula-track source, not `VerifiedNPDAGLowerBoundSource`. If the operator wants pnp4-native naming, create a module under a restricted lower-bound area, not under mainline frontier endpoints.

**Requires operator decision before integration.**

- Whether pnp4 should expose pnp3 `NP_not_subset_PpolyFormula`/`PpolyReal` statements at all, because pnp4 mainline policy centers `VerifiedNPDAGLowerBoundSource` and `PpolyDAG`.
- Whether to quarantine or rename support-bound-derived pnp3 adapters before pnp4 imports them.
- Whether the partial-MCSP language should be restated in pnp4-native form or imported as pnp3 `gapPartialMCSP_Language p`.

## 14. Reuse map

**Safe to reuse, with conditions.**

- `SmallGeneralCircuitSolver_Partial`, `.decide`, `.correct_decide`: safe interface plumbing.
- `locality_lift_partial`, `_of_certificate`, `_auto`: safe if all provider/certificate inputs remain explicit and are not turned into global instances.
- `AC0StatementPartial_*` and `FormulaLowerBoundHypothesisPartial_semantic`: safe as staged Step-C interfaces.
- `formula_hypothesis_from_pipeline_partial_semantic`: safe adapter from imported core theorem plus `0 < δ`.
- `OPS_trigger_formulas_partial_of_provider_formula_separation(_semantic)`: safe conditional theorem when hypotheses are explicitly reported.
- `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto`: safe conditional endpoint for restricted formula-track reporting.
- Provenance-restricted contracts such as `FormulaSupportBoundsPartial_fromPipeline`: safe as honest staging, not as completed proof.

**Avoid / do not touch without operator decision.**

- Do not use `FormulaSupportRestrictionBoundsPartial` or downstream `*_of_supportBounds` routes as progress; they are documented as inconsistent/refuted.
- Do not promote `hasDefault*`/`default*` wrappers into instances or implicit assumptions.
- Do not create a pnp4 `VerifiedNPDAGLowerBoundSource` from these formula/real endpoints without a separate DAG bridge.
- Do not alter trust-root files as part of this route.

## 15. Gap map

### A. Engineering gaps

1. A pnp4 restricted-side-track adapter module is absent for these partial-MCSP formula endpoints.
2. Public theorem/audit surfaces for any pnp4 adapter would need explicit tests and AxiomsAudit entries.
3. Support-bound legacy names remain callable; a naming/quarantine pass may be needed to make accidental reuse harder.
4. Import documentation is thin: future workers may not know whether to import `Bridge_to_Magnification_Partial` or `LocalityProvider_Partial`.

### B. Formalization gaps

1. No closed `StructuredLocalityProviderPartial` is proved without hard provider assumptions.
2. No closed `StructuredLocalityProviderPartial_semantic` is proved without provider assumptions.
3. Provenance-restricted support-bound contracts are staged but not independently validated as non-vacuous in this audit.
4. The `NP_strict (gapPartialMCSP_Language p)` premise is not discharged in the six-file scope.
5. Full proof-body audit of every `LocalityProvider_Partial.lean` theorem was not performed.

### C. Mathematical gaps

1. No bridge from formula/real separations to `NP_not_subset_PpolyDAG` is present.
2. No `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound` is reduced.
3. No full-MCSP or search-to-decision magnification theorem is present in this audited scope.
4. The support-bound route is mathematically blocked by hardwiring unless provenance restrictions eliminate the counterexample.

### D. Governance gaps

1. Old support-bound routes are documented as bad but remain in active module namespaces.
2. `default*` names may overstate availability of hard provider packages.
3. pnp4 integration risk: future PRs could mistakenly advertise this restricted formula track as P-vs-NP mainline progress.
4. Cross-check with NoGoLog / support-cardinality barrier audits should be required before any support-bound route is reused.

## 16. Recommended Phase 1+ tasks

Recommended Phase 1+ tasks count: **5**.

1. **Quarantine labels for old support-bound partial routes.** Touch `pnp3/Magnification/LocalityProvider_Partial.lean` and tests/audits only if names are public. Allowed scope: rename/add doc/audit markers for `FormulaSupportRestrictionBoundsPartial`-dependent constructors. Forbidden: meaning changes, new endpoints, trust-root edits. Expected output: clearly legacy/refuted names/comments and passing guards. Estimate: 1-2 days. Dependencies: NoGoLog/support-cardinality audits. Risk: medium. Type: Lean/docs/tests.
2. **pnp4 restricted-side-track adapter for partial formula endpoint.** Touch a new operator-selected pnp4 restricted module, `lakefile.lean`, and pnp4 surface/audit tests if public. Allowed: restate `NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto` with explicit hypotheses. Forbidden: `VerifiedNPDAGLowerBoundSource`, `NP_not_subset_PpolyDAG`, `P_ne_NP`, or mainline progress claim. Expected output: pnp4-native conditional restricted formula theorem. Estimate: 2-3 days. Dependencies: pnp4 frontier/source audit. Risk: medium-high. Type: Lean.
3. **Non-vacuity audit for `FormulaSupportBoundsPartial_fromPipeline`.** Touch only a new audit report or operator-approved audit test module. Allowed: determine whether provenance-restricted support bounds avoid hardwiring refutation. Forbidden: implementation/fixes/new lower-bound endpoint. Expected output: precise non-vacuity/refutation report. Estimate: 3-5 days. Dependencies: support-cardinality and NoGoLog audits. Risk: high. Type: markdown-only or audit Lean, operator decision.
4. **Provider-wrapper hygiene pass for `hasDefault*` names.** Touch `pnp3/Magnification/LocalityProvider_Partial.lean` and tests if public names change. Allowed: make `Nonempty`/`default*` wrappers explicit in names/docstrings. Forbidden: new instances/typeclass automation/provider construction from thin air. Expected output: reduced Rule-16 confusion. Estimate: 1-2 days. Dependencies: none. Risk: medium. Type: Lean/docstring cleanup.
5. **Full proof-body audit of `LocalityProvider_Partial.lean`.** Touch only a new markdown audit report. Allowed: classify every theorem dependency chain, especially lines 1700-3677. Forbidden: Lean edits. Expected output: fine-grained dependency map. Estimate: 1 week. Dependencies: A01 and pre-integration planning. Risk: low repo-risk, high audit time. Type: markdown-only.

## 17. Stop / hold recommendations

- **Hold** any pnp4 mainline task that attempts to turn these partial formula/real endpoints into `VerifiedNPDAGLowerBoundSource`, `NP_not_subset_PpolyDAG`, or `P_ne_NP` without a separate explicit DAG bridge.
- **Downgrade** support-bound-based partial routes to legacy/refuted/audit-only unless they use a provenance-restricted replacement and have a separate non-vacuity audit.
- **Rename or quarantine** any planned task title that says “partial-MCSP proves P vs NP” or “mainline progress” for this scope; the correct classification is restricted side track or infrastructure.
- **Do not touch** trust-root files (`Complexity.Interfaces`, `UnconditionalResearchGap`, pnp4 bridge requirements) for this A01 route without a dedicated foundational/operator decision.

## 18. Commands run

- `find .. -name AGENTS.md -print` — found only repository `AGENTS.md`.
- `git switch -c khanukov/phase1-A01-codex || git switch khanukov/phase1-A01-codex` — created/switched to required audit branch.
- `sed -n ...` on instruction and audited Lean files — used for reading.
- `rg -n "^(def|abbrev|structure|class|theorem|lemma|instance|opaque|axiom|noncomputable def)\b" pnp3/Magnification/*_Partial.lean` — declaration inventory.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" <six-file-scope>` — **0 matches**.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" <six-file-scope>` — **150 textual matches**, mostly `_Partial` names and support-bound/legacy comments.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" <six-file-scope>` — 42 `Classical.choose`, 24 `noncomputable def`, 0 `opaque`, 0 global instance declarations.
- `rg -n "\bsorry\b|\badmit\b|\baxiom\b|\bopaque\b" <six-file-scope>` — **0 matches**.
- `./scripts/check.sh` — **passed** all 17 steps; existing warnings were linter warnings in pre-existing modules.

## 19. Honest caveats

- I did not reconstruct the full import graph beyond explicit imports in the six audited files.
- I did not inspect every proof body in `LocalityProvider_Partial.lean`; I audited it by declaration inventory, keyword searches, and targeted reading of architectural/risk sections.
- I verified signatures and dependency shape, not the mathematical adequacy of the underlying AC0/multiswitching claims imported from other modules.
- I did not audit `ThirdPartyFacts.PartialLocalityLift` or `LowerBounds.LB_Formulas_Core_Partial` in detail; those are important upstream dependencies for the kernel-checked adapters.
- I did not perform a full NoGoLog semantic audit; `outputs/nogolog.jsonl` was only lightly consulted.
- This audit should be cross-checked with audits covering support-cardinality barriers, pnp4 bridge requirements, and NoGoLog entries before any integration task is dispatched.
