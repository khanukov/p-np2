# A03 audit report: pnp3 AC0 bridges

Task: A03  
Engineer handle: gpt55  
Branch: khanukov/phase1-A03-gpt55  
Scope: markdown-only Phase 0 audit of `pnp3/Magnification/AC0*.lean` and `pnp3/Magnification/Asymptotic*Collapse.lean`.

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL.**

The audited AC0/locality bridge area contains real kernel-checked bridge lemmas and typed interfaces, but the AC0-to-`PpolyDAG`/`ResearchGapWitness` pipeline is not complete. The strongest fully canonical endpoint in the audited files is conditional: `AsymptoticDAGCollapse.lean` can produce `NP_not_subset_PpolyDAG` only from an already-supplied asymptotic `PpolyDAG` collapse plus an `NP_strict` hypothesis. The AC0 files mostly package semantic switching, atlas/scenario-budget, small-mismatch, and approximate-family obligations; these are honest interfaces or conditional reductions, not closed lower bounds. The current internal semantic provider is explicitly singleton/per-formula and has audit markers/refutation evidence, so it should not be promoted as mainline progress. Future work should reuse the slice-bridge and scenario-budget adapters, but should not try to close P-vs-NP by wrapping the current AC0 provider surfaces.

## 2. Executive summary: AC0 -> DAG collapse pipeline status

**Pipeline complete? No.** The audited files implement several reusable arrows, but the critical source obligations are still external/staged:

```text
PpolyFormula witness for fixed gapPartialMCSP slice
  -> FormulaSemanticMultiSwitchingProvider / SemanticSwitchingCertificatePartial
  -> SemanticSwitchingBoundedAtlasScenarioPartial or SemanticSwitchingScenarioBudgetPartial
  -> either:
       (a) small-mismatch/testset payload, still only a stronger source obligation; or
       (b) approximate-family package, which gives contradiction against PpolyFormula
  -> formula separation wrappers (NP_not_subset_PpolyFormula only)

Separate DAG track:
Asymptotic PpolyDAG collapse + NP_strict(asymptotic language)
  -> NP_not_subset_PpolyDAG
```

The AC0 route's input requirement is not merely an AC0[p] lower bound. In pnp3 it needs source-side semantic switching data tied to `PpolyFormula` witnesses, plus either a small-mismatch extraction, a large common `ApproxClass` family, or a fixed/asymptotic collapse hypothesis. In pnp4, existing AC0[p] lower-bound bridges deliberately stop at restricted `¬ InAC0p` conclusions; `PvsNPBridgeRequirements.lean` records that an explicit `VerifiedNPDAGLowerBoundSource` bridge is still missing.

## 3. Files audited

| File | Approximate role | Inspection mode | Notes |
| --- | --- | --- | --- |
| `RESEARCH_CONSTITUTION.md` | Governance and target semantics | Read structurally | Used to confirm `ResearchGapWitness`/DAG target and refuted-route rules. |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | Dispatch/common expectations | Read structurally | Some Phase 1 implementation language is overridden by A03 audit prompt. |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | Shared worker instructions | Read structurally | Ignored old E-number naming where it conflicts with A03 prompt. |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A03_audit_pnp3_ac0_bridges.md` | Exact task file | Read fully | Defines the audit file set and required A03 sections. |
| `pnp3/Magnification/AC0LocalityBridge.lean` | AC0 semantic switching/locality bridge and singleton audit route | Read fully enough for declarations and key proof bodies; long constructive middle skimmed structurally | 1,555 LOC; all public declarations and hidden-payload points were inspected. |
| `pnp3/Magnification/AC0AtlasBridge.lean` | AC0 certificate -> atlas/scenario-budget/small-testset adapters | Read fully | Medium file; all declarations inspected. |
| `pnp3/Magnification/AC0ApproxFamilyBridge.lean` | Approx-family direct counting contradiction route | Read fully | Small file; all declarations inspected. |
| `pnp3/Magnification/AsymptoticDAGCollapse.lean` | Asymptotic-to-fixed DAG slice bridge and canonical DAG-separation wrapper | Read fully | Small file; all declarations inspected. |
| `pnp3/Magnification/AsymptoticFormulaCollapse.lean` | Formula fixed/asymptotic collapse wrappers | Read fully | Small file; all declarations inspected. |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pSuperPolynomialBridge.lean` | pnp4 AC0[p] quasi-polynomial lower-bound bridge | Read structurally | Checked that it feeds `¬ InAC0p`, not pnp3 AC0 bridge files. |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pAsymptoticBridge.lean` | pnp4 asymptotic AC0[p] exclusion bridge | Searched/skimmed structurally | Used for cross-track integration check. |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pCoinLowerBound.lean` | pnp4 AC0[p]/coin contract definitions | Searched/skimmed structurally | Used for cross-track integration check. |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pCoinAsymptotic.lean` | pnp4 published coin contract -> asymptotic AC0[p] exclusion | Searched/skimmed structurally | Used for cross-track integration check. |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_AC0p_Final.lean` | pnp4 AC0[p]/coin -> MCSP lower-bound wrappers | Searched/skimmed structurally | Used for cross-track integration check. |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_AC0p_Quantitative.lean` | pnp4 quantitative AC0[p]/coin wrappers | Searched/skimmed structurally | Used for cross-track integration check. |
| `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean` | Restricted AC0[p] vs verified DAG-source boundary | Read fully | Confirms restricted AC0[p] source is not a P-vs-NP source. |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | Trust-root research-gap boundary | Read relevant header and definitions | Confirms support-bounds/AC0 provenance routes are not acceptable final gap closures. |
| `pnp3/Complexity/Interfaces.lean` | Trust-root complexity interfaces | Skimmed structurally | Confirmed canonical formula/DAG classes and target names. |
| `outputs/nogolog.jsonl` | NoGoLog | Searched only | No A03-specific hits for audited route names found by targeted search. |
| `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` | Optional retrospective | Searched only | No A03-specific hits for audited route names found by targeted search. |

## 4. Top-level theorem / structure inventory

### `AC0LocalityBridge.lean`

| Declaration | Signature summary | Classification | Hard-payload dependency check |
| --- | --- | --- | --- |
| `FormulaSupportBoundsFromMultiSwitchingContract` | Structure whose `package` field turns each `PpolyFormula (gapPartialMCSP_Language p)` into AC0 provenance, semantic link, and numeric locality/support bounds. | **staged Prop / suspicious-needs-review** | Uses `Classical.choose hFormula`; no direct `ResearchGapWitness`/`NP_not_subset_PpolyDAG`, but trust-root notes identify support-bounds routes as refuted/unsafe if promoted. |
| `FormulaSemanticMultiSwitchingProvider` | Structure whose `package` field gives AC0 family provenance and semantic link for each extracted formula witness. | **audit-only / refuted-channel** | Marked `@audit-class: refuted-channel`; no direct DAG source. |
| `SemanticSwitchingCertificatePartial` | Explicit certificate containing `ac0`, `F`, AC0 family witness, multiswitching witness, polylog witness, and semantic link. | **staged Prop / interface** | Depends on formula witness and third-party AC0 facts; no `ResearchGapWitness` or `VerifiedNPDAGLowerBoundSource`. |
| `SemanticSwitchingCertificateProviderPartial` | Provider Prop returning `Nonempty (SemanticSwitchingCertificatePartial hFormula)` for all formula witnesses. | **staged Prop** | Provider wrapper; no hard target. |
| `SemanticSwitchingNontrivialFamilyPackagePartial` / `ProviderPartial` | Certificate plus `2 <= cert.F.length`. | **staged Prop / honest frontier** | Isolates a missing non-singleton-family condition; no hard target. |
| `semanticSwitchingNontrivialFamilyProvider_of_certificateProvider_and_length` | Converts certificate provider + chosen certificate length proof into nontrivial-family provider. | **conditional** | Uses `Classical.choice` on provider output; harmless as adapter but does not prove source theorem. |
| `semanticSingletonWitness` and theorems around it | Explicit truth-table-DNF/subcube witness for a singleton semantic route; proves coverage/error/selector facts. | **audit-only / weak route** | Useful for falsifiability/provenance; not a P-vs-NP source. |
| `CurrentSingletonRouteWitnessProp` | Prop saying the singleton route admits a `WorksFor` witness in the atlas dictionary. | **weak route / audit-only** | Built from `Classical.choose hFormula`; no hard target; used to show empty witness admissibility under comparison. |
| `empty_witness_admissible_for_current_singleton_route` | Under numeric comparison, proves `CurrentSingletonRouteWitnessProp` via empty selector. | **refuted/weak route evidence** | Shows singleton route is too weak; should not be promoted. |
| `comparison_hypothesis_of_nat_crossmul` | Converts a natural inequality into the rational comparison used by empty-witness theorem. | **conditional arithmetic helper** | No hard payload. |
| `formulaSemanticMultiSwitchingProvider_internal` | Noncomputable internal provider that constructs AC0 provenance from the formula's truth-table/function as singleton `[f]`. | **audit-only / hidden-payload risk if promoted** | Uses `Classical.choose hFormula`; theorem proves it is singleton. |
| `formulaSemanticMultiSwitchingProvider_internal_singleton_family` | Proves the internal provider exports a singleton family `[f]`. | **audit-only theorem** | Directly blocks treating internal provider as nontrivial source. |
| `semanticSwitchingCertificate_internal` | Noncomputable singleton certificate from internal provider. | **audit-only / weak route** | Uses `Classical.choose hFormula`; not a hard target. |
| `formulaSemanticMultiSwitchingProvider_internal_not_nontrivial_family` | Proves the internal certificate cannot satisfy `2 <= F.length`. | **audit-only theorem** | Negative evidence; safe for audits. |
| `semanticSwitchingCertificate_of_provider` / `Provider_of_provider` | Adapters from semantic provider to certificate provider. | **conditional adapter** | Safe only if provider source is safe; dangerous with internal singleton provider if promoted. |
| `semantic_provider_semantic_link` / `package_semantic_link` | Extract semantic-link existence from provider/package. | **audit helper** | Harmless extraction; no hard target. |

### `AC0AtlasBridge.lean`

| Declaration | Signature summary | Classification | Hard-payload dependency check |
| --- | --- | --- | --- |
| `SemanticSwitchingBoundedAtlasScenarioPartial` | Certificate plus `LowerBounds.BoundedAtlasScenario` and family equality. | **staged Prop / adapter structure** | No direct hard target. |
| `SemanticSwitchingScenarioBudgetPartial` | Certificate plus `LowerBounds.ScenarioBudget`. | **staged Prop / adapter structure** | No direct hard target. |
| `SemanticSwitchingBoundedAtlasScenarioProviderPartial` / `ScenarioBudgetProviderPartial` | Provider Props for those packages. | **staged Prop** | No hard target. |
| `SemanticSwitchingSmallMismatchPackagePartial` | Bounded atlas package plus linked `f`, approximating subcube list `S`, and polylog-small mismatch set. | **staged Prop / honest stronger-source frontier** | No hard target; potentially useful but still an obligation. |
| `SemanticSwitchingSmallMismatchProviderPartial` | Provider Prop for small-mismatch packages. | **staged Prop** | No hard target. |
| `SemanticSwitchingSmallMismatchExtractionPartial` | Global extraction property from every bounded atlas package to a small-mismatch witness. | **staged Prop / potential wrapper risk** | Stronger than provenance-aware package; not proven. |
| `boundedAtlasScenario_of_semanticSwitchingCertificate` | Kernel-checked adapter from certificate to bounded atlas scenario using `scenarioFromAC0_with_polylog`. | **conditional adapter** | Safe given a real certificate; no hard target. |
| `scenarioBudget_of_semanticSwitchingCertificate` | Kernel-checked adapter from certificate to scenario budget. | **conditional adapter** | Safe given a real certificate; no hard target. |
| `semanticSwitchingScenarioBudget_no_large_gap` | Proves a scenario budget cannot by itself yield strict large-family gap. | **audit-only no-go theorem** | Negative isolation; no hard target. |
| `linked_testset_of_semanticSwitchingScenarioBudget` | Extracts linked function and testset bounded by epsilon-density, not polylog. | **conditional weak route** | Useful but insufficient; no hard target. |
| `linked_small_testset_of_boundedAtlasScenario` | If small-mismatch extraction exists, yields linked polylog-small testset. | **conditional adapter** | Depends on staged extraction. |
| `semanticSwitchingSmallMismatchPackage_of_extraction` | Packages global extraction output into provenance-aware small-mismatch package. | **conditional adapter** | Depends on staged extraction. |
| `linked_small_testset_of_semanticSwitchingSmallMismatchPackage` | Small-mismatch package -> polylog-small testset. | **conditional adapter** | Safe if source package is real. |
| Provider-level adapters and internal provider wrappers | Lift certificate/semantic providers to atlas/scenario-budget providers. | **conditional / audit-only when using internal provider** | Internal wrappers inherit singleton provider weakness. |

### `AC0ApproxFamilyBridge.lean`

| Declaration | Signature summary | Classification | Hard-payload dependency check |
| --- | --- | --- | --- |
| `SemanticSwitchingApproxFamilyPackagePartial` | Scenario-budget package plus finite family `Y` in one common `ApproxClass`, with `Y.card` above capacity. | **staged Prop / honest frontier** | No direct `NP_not_subset_PpolyDAG`; source obligation is substantial. |
| `SemanticSwitchingApproxFamilyProviderPartial` | Provider Prop producing a family package for every formula witness. | **staged Prop** | No hard target. |
| `contradiction_of_semanticSwitchingApproxFamilyPackage` | Kernel-checked contradiction via `Counting.incompatibility`. | **conditional theorem** | Real contradiction from package; package itself is hard/staged. |
| `no_ppolyFormula_of_semanticSwitchingApproxFamilyProvider` | Provider + formula witness -> `False`. | **conditional theorem** | Formula-only separation route. |
| `NP_strict_not_subset_PpolyFormula_of_semanticSwitchingApproxFamilyProvider` | Provider + fixed strict-NP slice -> `NP_strict_not_subset_PpolyFormula`. | **conditional theorem** | Formula-only, not DAG. |
| `NP_not_subset_PpolyFormula_of_semanticSwitchingApproxFamilyProvider` | Provider + fixed strict-NP slice -> `NP_not_subset_PpolyFormula`. | **conditional theorem** | Formula lower bound only; no `NP_not_subset_PpolyDAG`. |

### `AsymptoticDAGCollapse.lean`

| Declaration | Signature summary | Classification | Hard-payload dependency check |
| --- | --- | --- | --- |
| `asymptotic_dag_collapse_of_slice_bridge` | Fixed-slice `PpolyDAG` contradiction + explicit asymptotic-to-fixed DAG bridge -> asymptotic `PpolyDAG` contradiction. | **conditional canonical DAG adapter** | Does not depend on `ResearchGapWitness`; consumes a collapse/bridge. |
| `ppolyDAG_fixed_of_asymptotic_slice` | Pointwise slice equality converts asymptotic `PpolyDAG` witness to fixed-slice `PpolyDAG` witness. | **kernel-checked adapter** | Safe reusable theorem; no hard target by itself. |
| `asymptotic_dag_collapse_of_slice_agreement` | Fixed-slice DAG collapse + slice equality -> asymptotic DAG collapse. | **conditional canonical DAG adapter** | Safe but needs fixed-slice collapse. |
| `NP_not_subset_PpolyDAG_of_asymptotic_dag_collapse` | `NP_strict` asymptotic language + asymptotic DAG contradiction -> `NP_not_subset_PpolyDAG`. | **conditional canonical endpoint** | Directly yields hard target only from strong hypotheses; no `ResearchGapWitness` wrapper. |

### `AsymptoticFormulaCollapse.lean`

| Declaration | Signature summary | Classification | Hard-payload dependency check |
| --- | --- | --- | --- |
| `fixed_formula_collapse_of_provider` | Structured locality provider + formula lower-bound hypothesis -> fixed-slice `PpolyFormula` contradiction. | **conditional / suspicious if provider is refuted route** | Depends on `FormulaSupportBoundsPartial`; not a DAG source. |
| `fixed_formula_collapse_of_provider_fromPipeline` | Pipeline provider + semantic AC0 provider + lower-bound hypothesis -> fixed-slice formula contradiction. | **conditional / refuted-route risk** | Depends on `FormulaSemanticMultiSwitchingProvider`; trust-root warns against support-bounds route promotion. |
| `asymptotic_formula_collapse_of_slice_bridge` | Fixed formula collapse + explicit asymptotic-to-fixed bridge -> asymptotic formula collapse. | **conditional formula adapter** | Formula-only. |
| `ppolyFormula_fixed_of_asymptotic_slice` | Pointwise slice equality converts asymptotic formula witness to fixed-slice formula witness. | **kernel-checked adapter** | Safe reusable theorem. |
| `asymptotic_formula_collapse_of_slice_agreement` | Fixed formula collapse + slice equality -> asymptotic formula collapse. | **conditional formula adapter** | Formula-only. |
| `NP_not_subset_PpolyFormula_of_fixed_formula_collapse` | Fixed strict-NP slice + fixed formula collapse -> canonical formula separation. | **conditional formula endpoint** | Not DAG. |
| `NP_not_subset_PpolyFormula_of_asymptotic_formula_collapse` | Asymptotic strict-NP + asymptotic formula collapse -> canonical formula separation. | **conditional formula endpoint** | Not DAG. |

## 5. Kernel-checked content

Kernel-checked content found in the audited area includes:

1. **AC0 certificate to atlas/scenario-budget adapters.** `boundedAtlasScenario_of_semanticSwitchingCertificate` uses `LowerBounds.scenarioFromAC0_with_polylog` to build a `SemanticSwitchingBoundedAtlasScenarioPartial`; `scenarioBudget_of_semanticSwitchingCertificate` builds a `SemanticSwitchingScenarioBudgetPartial` from `LowerBounds.scenarioBudgetFromAC0`.
2. **No-large-gap isolation.** `semanticSwitchingScenarioBudget_no_large_gap` proves that a scenario budget cannot by itself produce a finite family above `LowerBounds.scenarioCapacity`. This is negative evidence against the old large-family gap route.
3. **Weak linked-testset extraction.** `linked_testset_of_semanticSwitchingScenarioBudget` extracts a linked `f` and a testset whose cardinality is bounded by epsilon times the truth-table universe, not by `polylogBudget`. This is weaker than the current small-testset goal.
4. **Small-mismatch adapters.** Given the staged small-mismatch extraction/package, the atlas bridge proves polylog-small testset existence.
5. **Approx-family contradiction.** `contradiction_of_semanticSwitchingApproxFamilyPackage` is a genuine contradiction theorem, but it requires the package to provide a common `ApproxClass` family exceeding `Counting.capacityBound`.
6. **Formula separation wrappers.** The approximate-family provider yields `NP_not_subset_PpolyFormula` when combined with a fixed strict-NP slice; the formula collapse file has fixed/asymptotic formula separation wrappers.
7. **DAG slice bridge.** `ppolyDAG_fixed_of_asymptotic_slice` constructively converts an asymptotic DAG witness into a fixed-slice DAG witness under pointwise slice equality, with a padded polynomial bound.
8. **Conditional DAG endpoint.** `NP_not_subset_PpolyDAG_of_asymptotic_dag_collapse` is the strongest relevant kernel-checked theorem in scope: it gives canonical `NP_not_subset_PpolyDAG` from `NP_strict (gapPartialMCSP_AsymptoticLanguage spec)` and a collapse `PpolyDAG (gapPartialMCSP_AsymptoticLanguage spec) -> False`.
9. **Singleton route audit theorems.** The internal provider is proved singleton, and the current singleton route admits an empty witness under a numeric comparison. These are useful audit results, not source progress.

No theorem in the audited AC0 bridge files constructs `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPMagnificationContract`, or a closed `P_ne_NP` endpoint.

## 6. Staged / placeholder / Prop-only content

| Item | Why it is staged / Prop-only | Risk classification |
| --- | --- | --- |
| `FormulaSupportBoundsFromMultiSwitchingContract` | A structure with a `package` field asking for AC0 provenance plus support/locality bounds for every formula witness. | **Potential wrapper risk** because trust-root comments say support-bounds routes are refuted/unsafe as final gap closures. |
| `FormulaSemanticMultiSwitchingProvider` | A structure field packages AC0 family provenance and semantic link for every formula witness. | **Refuted-channel / hidden-payload risk if promoted**, explicitly audit-marked. |
| `SemanticSwitchingCertificateProviderPartial` | Prop returning `Nonempty` certificate for every formula witness. | **Honest staging** if used only as intermediate interface. |
| `SemanticSwitchingNontrivialFamilyProviderPartial` | Prop requiring nontrivial family certificates. | **Honest staging**; it isolates a known missing non-singleton condition. |
| `SemanticSwitchingBoundedAtlasScenarioProviderPartial` / `ScenarioBudgetProviderPartial` | Props producing atlas/scenario-budget wrappers. | **Harmless interface** if kept adapter-level. |
| `SemanticSwitchingSmallMismatchExtractionPartial` | Global theorem-shaped Prop extracting polylog-small mismatch data from every bounded atlas package. | **Potential wrapper risk**; stronger than provenance-aware source and not proven. |
| `SemanticSwitchingSmallMismatchProviderPartial` | Prop producing small-mismatch packages. | **Honest staging**, provided it is not mistaken for a proof. |
| `SemanticSwitchingApproxFamilyProviderPartial` | Prop producing a large common `ApproxClass` family exceeding counting capacity. | **Honest staging / hard source obligation**. |
| `fixed_formula_collapse_of_provider` hypotheses | Consumes provider/lower-bound hypotheses; does not prove them. | **Conditional interface**; risk depends on provider source. |
| `asymptotic_*_collapse_of_slice_bridge` hypotheses | Consume fixed collapse and bridge/slice equality hypotheses. | **Harmless interface**; explicit inputs make the gap visible. |

## 7. Refuted / vacuous / legacy route check

Search terms checked: `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `default support bounds`, `weak route`, `legacy route`, `via_ex_falso`, `_Partial`, `_Legacy`, `TODO`, `placeholder`.

Findings:

- The audited AC0 files contain many `_Partial` names. In this area `_Partial` is mostly an honest marker that the object is an interface/provider package rather than a closed source theorem.
- `AC0LocalityBridge.lean` explicitly labels `FormulaSemanticMultiSwitchingProvider` as `@audit-class: refuted-channel`, with a note that new uses outside audit/test/docs are blocked by the typeclass-payload quarantine script.
- `AC0AtlasBridge.lean` has no `RefutedRoute` declaration, but it has explicit no-go content: `semanticSwitchingScenarioBudget_no_large_gap` proves the current scenario budget cannot give the strict large-family gap needed downstream.
- The singleton route in `AC0LocalityBridge.lean` is weak/audit-only: the internal provider exports `[f]`, `formulaSemanticMultiSwitchingProvider_internal_not_nontrivial_family` rules out `2 <= F.length`, and `empty_witness_admissible_for_current_singleton_route` shows an empty selector witness can satisfy the current route under a comparison hypothesis.
- `AsymptoticFormulaCollapse.lean` imports `Magnification.Facts_Magnification_Partial` and `Magnification.LocalityProvider_Partial`, so formula-collapse results that consume support/locality providers should be treated as conditional and potentially refuted-route-adjacent unless the provider input is independently safe.
- No `via_ex_falso`, `FinalPayloadProvider`, or `MagnificationAssumptions` occurrence appears inside the audited file set by targeted search.

## 8. Hidden payload / Rule 16 check

Search terms checked: `class`, `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `noncomputable def`, `Provider`, `Payload`, `Witness`, `Source`, `Default`, and `Classical.choose`.

| Occurrence family | Interpretation | Classification |
| --- | --- | --- |
| `Classical.choose hFormula` in formula/provider structures | Extracts the `InPpolyFormula` witness from `PpolyFormula` packaging to name the slice circuit. | **Standard witness extraction / harmless if not a final payload**, but dangerous if used to hide source obligations. |
| `FormulaSemanticMultiSwitchingProvider` | Provider structure itself is audit-marked as refuted-channel. | **Hidden-payload risk / forbidden if used by candidate as source.** |
| Private `noncomputable def` truth-table DNF/subcube machinery | Constructs explicit semantic/truth-table AC0 objects for a chosen function. | **Harmless audit infrastructure**, but produces singleton/per-function provenance. |
| `semanticSingletonWitness` | Public noncomputable selector list from explicit semantic circuit. | **Audit-only infrastructure**. |
| `current_singleton_preSingleton_selector_package` | Chooses a witness from an existence theorem around the singleton route. | **Audit-only / weak-route risk**; do not promote. |
| `formulaSemanticMultiSwitchingProvider_internal` | Noncomputable provider creating singleton AC0 family `[f]` from extracted formula. | **Hidden-payload risk if used outside audits**. |
| `semanticSwitchingCertificate_internal` | Noncomputable singleton certificate from internal provider. | **Audit-only / hidden-payload risk if promoted**. |
| Provider-level adapters in `AC0AtlasBridge.lean` using `Classical.choice` | Choose package from `Nonempty` provider output. | **Harmless adapter pattern** if source provider is safe; inherits risk from unsafe provider. |
| `opaque`, `class`, `instance`, `default_instance`, `attribute [instance]` | No dangerous occurrences found in audited file set by targeted search. | **No issue found in scope**. |

## 9. Barrier relevance

| Barrier / topic | Relevant? | Content type in audited area | Notes |
| --- | --- | --- | --- |
| Natural proofs | Indirectly | Nothing formal in audited files | No explicit natural-proofs theorem. |
| Relativization | No | Nothing | Not touched. |
| Algebrization | No | Nothing | Not touched. |
| Locality | Yes | Typed interface + conditional theorems | `FormulaSupportBoundsFromMultiSwitchingContract` and formula-collapse provider theorems consume locality/support data; trust-root warns this route is refuted if used as final source. |
| Hardwiring | Yes | Audit comments and singleton constructions | Internal provider extracts formula-specific truth-table-like/singleton AC0 provenance. This is exactly the kind of per-witness hardwiring the research-gap notes warn against. |
| Support-cardinality-only | Yes | Typed interfaces and audit/no-go content | Support-bounds route appears in `FormulaSupportBoundsFromMultiSwitchingContract` and formula-collapse imports; should not be promoted. |
| Syntax-only filters | Indirectly | Nothing direct | AC0 family witnesses are syntactic/provenance packages, but no syntax-only filter theorem is closed. |
| Normalization filters | Indirectly | Nothing direct | No standalone normalization filter theorem in audited files. |
| Search-to-decision | No direct content | Nothing in audited files | pnp4 SearchMCSP surfaces are not imported here. |
| MCSP / magnification | Yes | Typed interfaces + conditional theorems | All files are about gap partial MCSP slices/asymptotic languages and magnification-style collapse. |
| AC0[p] | Cross-track only | pnp4 typed interfaces; pnp3 files mostly AC0/multiswitching, not pnp4 `InAC0p` | No explicit import from pnp4 AC0[p] bridges into pnp3 audited files. |

## 10. AC0[p] -> P/poly bridge map

### pnp3 audited bridge map

```text
AC0LocalityBridge.SemanticSwitchingCertificatePartial
  --boundedAtlasScenario_of_semanticSwitchingCertificate-->
AC0AtlasBridge.SemanticSwitchingBoundedAtlasScenarioPartial
  --linked_small_testset_of_boundedAtlasScenario, only with SmallMismatchExtraction-->
polylog-small linked testset

AC0LocalityBridge.SemanticSwitchingCertificatePartial
  --scenarioBudget_of_semanticSwitchingCertificate-->
AC0AtlasBridge.SemanticSwitchingScenarioBudgetPartial
  --linked_testset_of_semanticSwitchingScenarioBudget-->
epsilon-density linked testset (not polylog)
  --semanticSwitchingScenarioBudget_no_large_gap-->
no strict large-family gap from budget alone

AC0AtlasBridge.SemanticSwitchingScenarioBudgetPartial
  + common large Y in Counting.ApproxClass above capacity
  --AC0ApproxFamilyBridge.contradiction_of_semanticSwitchingApproxFamilyPackage-->
False
  --provider wrappers + NP_strict slice-->
NP_not_subset_PpolyFormula
```

### Relation to `ResearchGapWitness`

The pnp3 AC0 audited bridge map does **not** reach `ResearchGapWitness` directly. The formula endpoints reach `NP_not_subset_PpolyFormula`, not `NP_not_subset_PpolyDAG`. The only audited file that reaches `NP_not_subset_PpolyDAG` is `AsymptoticDAGCollapse.lean`, and it requires an independently supplied asymptotic `PpolyDAG` collapse.

### pnp4 AC0[p] cross-track map

```text
pnp4 AC0[p]/coin contracts
  -> AC0pSuperPolynomialBridge / AC0pAsymptoticBridge
  -> ¬ InAC0p model p L
  -> PvsNPBridgeRequirements.AC0pRestrictedLowerBoundSource
  -> requires RestrictedToVerifiedDAGBridge with VerifiedNPDAGLowerBoundSource
  -> P_ne_NP_of_verified_source
```

No explicit import connects `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pSuperPolynomialBridge.lean` (or its coin/asymptotic friends) to the pnp3 audited AC0 bridge files. The pnp4 frontier file is honest: restricted AC0[p] lower bounds carry no `PpolyDAG` lower bound and need a separate `VerifiedNPDAGLowerBoundSource` bridge.

## 11. Asymptotic collapse coverage

### DAG coverage

`AsymptoticDAGCollapse.lean` covers the following input shapes:

1. **Explicit bridge shape:** If a fixed-slice contradiction `PpolyDAG (gapPartialMCSP_Language p) -> False` and an explicit bridge from asymptotic `PpolyDAG` to fixed-slice `PpolyDAG` are supplied, then asymptotic `PpolyDAG` collapses.
2. **Pointwise slice-agreement shape:** If the asymptotic language agrees with the fixed gap language on `partialInputLen p`, then the file constructs the asymptotic-to-fixed `PpolyDAG` bridge. Off-slice it uses a constant-false DAG and pads the polynomial bound.
3. **Canonical separation wrapper:** If the asymptotic language is `NP_strict` and has no `PpolyDAG` witness, the file proves `NP_not_subset_PpolyDAG`.

This is the only audited path to the canonical DAG lower-bound target, but it is conditional on a DAG collapse hypothesis.

### Formula coverage

`AsymptoticFormulaCollapse.lean` covers:

1. **Provider-driven fixed formula collapse:** From structured locality/support provider hypotheses plus a formula lower-bound hypothesis, it derives a fixed-slice `PpolyFormula` contradiction.
2. **Pipeline-provider fixed formula collapse:** From a pipeline provider and `FormulaSemanticMultiSwitchingProvider`, it extracts AC0 provenance and derives fixed-slice formula collapse.
3. **Explicit bridge and slice-agreement asymptotic formula collapse:** It mirrors the DAG slice bridge for `PpolyFormula`, using a constant-false formula off-slice.
4. **Formula separation wrappers:** It converts fixed or asymptotic formula collapse plus `NP_strict` into `NP_not_subset_PpolyFormula`.

Formula coverage is useful but not mainline P-vs-NP progress unless paired with an explicit formula-to-DAG/PpolyDAG bridge that satisfies the research-gap constraints.

## 12. Cross-track integration with pnp4

I found no explicit imports from the audited pnp3 files to pnp4 `AlgorithmsToLowerBounds` modules. The relation is conceptual rather than wired:

- `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pSuperPolynomialBridge.lean` defines `InAC0p` and proves that depthwise quasi-polynomial lower bounds imply `¬ InAC0p`.
- `AC0pAsymptoticBridge.lean`, `AC0pCoinLowerBound.lean`, `AC0pCoinAsymptotic.lean`, `MCSP_AC0p_Final.lean`, and `MCSP_AC0p_Quantitative.lean` normalize AC0[p]/coin lower-bound contracts into restricted exclusions or MCSP lower-bound statements.
- `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean` explicitly quarantines this as an `AC0pRestrictedLowerBoundSource` and requires `RestrictedToVerifiedDAGBridge`/`VerifiedNPDAGLowerBoundSource` before any P-vs-NP endpoint.

Therefore future workers should not claim that pnp4 AC0[p] lower bounds already feed the pnp3 AC0 atlas/locality pipeline or the final DAG target. A bridge would be new mathematical/formal work and must be scoped as such.

## 13. Reuse map

### Safe to reuse

- `AsymptoticDAGCollapse.ppolyDAG_fixed_of_asymptotic_slice` and `asymptotic_dag_collapse_of_slice_agreement` for honest asymptotic-to-fixed DAG conversions.
- `AsymptoticDAGCollapse.NP_not_subset_PpolyDAG_of_asymptotic_dag_collapse` as a canonical wrapper **only after** a real asymptotic DAG collapse is available.
- `AsymptoticFormulaCollapse.ppolyFormula_fixed_of_asymptotic_slice` for formula-only asymptotic/fixed adapters.
- `AC0AtlasBridge.boundedAtlasScenario_of_semanticSwitchingCertificate` and `scenarioBudget_of_semanticSwitchingCertificate` as adapter lemmas from a safe certificate source.
- `AC0AtlasBridge.semanticSwitchingScenarioBudget_no_large_gap` as no-go evidence preventing false large-family progress claims.
- `AC0ApproxFamilyBridge.contradiction_of_semanticSwitchingApproxFamilyPackage` if a future source theorem truly provides a large common `ApproxClass` family.
- `PvsNPBridgeRequirements.RestrictedToVerifiedDAGBridge` as the honest pnp4 boundary for AC0[p] restricted lower bounds.

### Avoid / do not touch or promote

- Do not promote `FormulaSemanticMultiSwitchingProvider` or `formulaSemanticMultiSwitchingProvider_internal` as a candidate source; it is audit-marked and singleton/per-formula.
- Do not use `FormulaSupportBoundsFromMultiSwitchingContract` or related support-bounds provider paths as a final source without a fresh governance/foundational review; trust-root text identifies those routes as refuted/unsafe.
- Do not treat `SemanticSwitchingScenarioBudgetProviderPartial` as enough for contradiction; the no-large-gap theorem says it is not.
- Do not treat formula-only endpoints (`NP_not_subset_PpolyFormula`) as P-vs-NP mainline progress unless paired with a valid PpolyDAG/`VerifiedNPDAGLowerBoundSource` bridge.
- Do not modify trust-root files listed in the prompt as part of a future AC0 bridge cleanup unless the operator dispatches a foundational task.

## 14. Gap map

### A. Engineering gaps

- No explicit import/adaptor connects pnp4 AC0[p] restricted lower-bound surfaces to pnp3 AC0 locality/atlas bridge files.
- Audit/test surfaces could better expose that `SemanticSwitchingScenarioBudgetProviderPartial` is insufficient by itself; the no-large-gap theorem exists but may not be visible in high-level docs.
- Naming around provider-level wrappers could be clearer about `formula` vs `DAG` endpoints to prevent accidental mainline claims.

### B. Formalization gaps

- `SemanticSwitchingSmallMismatchExtractionPartial` is only a Prop/interface; no proof in the audited area constructs the small-mismatch witness.
- `SemanticSwitchingApproxFamilyProviderPartial` is only a Prop/interface; no proof constructs a large family in one common `ApproxClass` above counting capacity.
- `SemanticSwitchingNontrivialFamilyProviderPartial` is only staged; the internal provider is proven not to satisfy its `2 <= F.length` condition.
- Formula-to-DAG bridge needed to convert formula-only separations into `NP_not_subset_PpolyDAG` is absent from the audited files.

### C. Mathematical gaps

- A real asymptotic or fixed-slice `PpolyDAG` collapse for an `NP_strict` language is still needed for `NP_not_subset_PpolyDAG`.
- Restricted AC0[p] lower bounds do not imply `PpolyDAG` lower bounds without an explicit `RestrictedToVerifiedDAGBridge`/`VerifiedNPDAGLowerBoundSource`.
- Large common `ApproxClass` family construction appears to be the genuine hard content of the direct counting route.
- Any use of singleton/per-formula AC0 provenance risks truth-table hardwiring and does not overcome the support/locality audit barrier.

### D. Governance gaps

- The audited pnp3 files themselves are mostly honest, but high-level planning should label the AC0/locality route as side-track or conditional unless it explicitly targets `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.
- Cross-track docs should emphasize that pnp4 AC0[p] milestones are restricted lower-bound sources, not P-vs-NP sources.
- Future dispatch tasks should separate markdown/governance cleanup from Lean implementation to avoid accidental source edits during audit waves.

## 15. Recommended Phase 1+ tasks

### Task 1: Document and test the scenario-budget no-go surface

- **Exact files to touch:** `pnp3/Magnification/AC0AtlasBridge.lean`, `pnp3/Tests` or existing audit/test surface chosen by operator, and possibly a markdown route-status file.
- **Allowed scope:** Add/re-export/check the existing `semanticSwitchingScenarioBudget_no_large_gap` theorem so downstream workers see that scenario budgets alone cannot produce the strict large-family gap.
- **Forbidden scope:** No new lower-bound source theorem, no `ResearchGapWitness`, no `P_ne_NP`, no weakening of scenario definitions.
- **Expected output:** A small Lean test/check or markdown note confirming the no-go theorem is public and route-limiting.
- **Estimated time:** 0.5-1 day.
- **Dependency on other audits:** Cross-check with any audit of `LowerBounds.LB_Formulas` or `AntiChecker_Partial`.
- **Risk level:** Low.
- **Type:** Lean test or markdown-only, depending on operator preference.

### Task 2: Write a restricted AC0[p] cross-track boundary note

- **Exact files to touch:** A markdown file under `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/` or a route-status doc selected by operator; optionally no Lean files.
- **Allowed scope:** Summarize that pnp4 `AC0pRestrictedLowerBoundSource` requires `RestrictedToVerifiedDAGBridge` before final P-vs-NP use.
- **Forbidden scope:** No pnp4 bridge implementation, no `VerifiedNPDAGLowerBoundSource` construction, no promotion of AC0[p] lower bounds to mainline.
- **Expected output:** Clear route diagram preventing duplicate or false-progress tasks.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** Should coordinate with pnp4 frontier/AC0[p] audits if present.
- **Risk level:** Low.
- **Type:** Markdown-only / operator decision.

### Task 3: Operator decision on quarantining `FormulaSemanticMultiSwitchingProvider` uses

- **Exact files to touch:** Operator-chosen governance/check files; possibly only markdown if current quarantine is sufficient.
- **Allowed scope:** Inventory uses of `FormulaSemanticMultiSwitchingProvider` outside audit/test/doc surfaces and decide whether to hold, rename, or add comments.
- **Forbidden scope:** Do not delete provider definitions or rewrite trust-root semantics without foundational dispatch.
- **Expected output:** Decision record: keep as audit-only, rename with stronger warning, or add a guardrail check.
- **Estimated time:** 1 day for decision + small follow-up if needed.
- **Dependency on other audits:** Needs cross-check with A09/NoGoLog and any `LocalityProvider_Partial` audit.
- **Risk level:** Medium because changing guardrails may affect existing modules.
- **Type:** Operator decision, possibly markdown-only.

### Task 4: Formal surface for the genuine DAG source gap

- **Exact files to touch:** Prefer pnp4 frontier or a new markdown task spec; do not touch trust-root files initially.
- **Allowed scope:** State, as a task specification, the exact theorem shape needed to feed `AsymptoticDAGCollapse.NP_not_subset_PpolyDAG_of_asymptotic_dag_collapse` or pnp4 `VerifiedNPDAGLowerBoundSource`.
- **Forbidden scope:** No attempt to prove the DAG lower bound; no candidate source theorem; no `gap_from`.
- **Expected output:** A precise Phase 1+ spec distinguishing engineering wrappers from open mathematical content.
- **Estimated time:** 0.5-1 day.
- **Dependency on other audits:** Coordinate with A01/A02/A09 if those cover final DAG bridge or NoGoLog.
- **Risk level:** Low if markdown-only.
- **Type:** Markdown-only / operator decision.

## 16. Stop / hold recommendations

- **Hold** any task that attempts to derive `P_ne_NP`, `ResearchGapWitness`, or `VerifiedNPDAGLowerBoundSource` directly from `FormulaSemanticMultiSwitchingProvider`, `formulaSemanticMultiSwitchingProvider_internal`, or `FormulaSupportBoundsFromMultiSwitchingContract`.
- **Downgrade** any planned AC0[p] milestone task from “P-vs-NP mainline” to “restricted lower-bound side track” unless it explicitly includes a `PpolyDAG`/`VerifiedNPDAGLowerBoundSource` bridge.
- **Rename or annotate** any task title implying that pnp3 AC0 atlas/scenario-budget packaging alone gives a lower-bound contradiction; the no-large-gap theorem contradicts that reading.
- **Do not cancel** reuse of `AsymptoticDAGCollapse` adapters; they are clean conditional infrastructure for a genuine DAG-collapse input.

## 17. Honest caveats

- I did not reconstruct the full import graph transitively; I used targeted imports/searches and read the audited files plus pnp4 frontier/AC0[p] surfaces relevant to the task.
- I did not inspect every private proof body in the 1,555-line constructive middle of `AC0LocalityBridge.lean`; I inspected all declaration surfaces and key singleton/hidden-payload sections.
- I verified signatures and route shapes, not the mathematical adequacy of third-party AC0 switching facts.
- I did not run `#print axioms` on every audited theorem individually.
- `./scripts/check.sh` was run after creating no Lean changes; its result is recorded in the command summary.
- This audit should be cross-checked with audits of `LocalityProvider_Partial.lean`, `FinalResultMainline.lean`, and NoGoLog/provider-quarantine surfaces.

## 18. Commands run

- `find pnp3/Magnification -maxdepth 1 -name 'AC0*.lean' -print | sort` -> found exactly `AC0ApproxFamilyBridge.lean`, `AC0AtlasBridge.lean`, and `AC0LocalityBridge.lean`.
- `find pnp3/Magnification -maxdepth 1 -name 'Asymptotic*Collapse.lean' -print | sort` -> found exactly `AsymptoticDAGCollapse.lean` and `AsymptoticFormulaCollapse.lean`.
- `wc -l pnp3/Magnification/AC0*.lean pnp3/Magnification/Asymptotic*Collapse.lean` -> audited file set totals 2,476 LOC.
- `rg -n "^(structure|class|def|theorem|lemma|opaque|axiom|noncomputable def)\b" <audit-scope>` -> declaration inventory generated; no `axiom`/`opaque` declarations in audited file set.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" <audit-scope>` -> only `AsymptoticDAGCollapse.lean` mentions/proves `NP_not_subset_PpolyDAG`; no `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPMagnificationContract`, `SourceTheorem`, or `gap_from` in audited file set.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" <audit-scope>` -> `_Partial` appears as interface naming; `AntiChecker_Partial` appears in comments; no `via_ex_falso`/`FinalPayloadProvider` in scope.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" <audit-scope>` -> no class/instance/default-instance/opaque hazards; multiple expected `Classical.choose` and noncomputable singleton/provider helpers in `AC0LocalityBridge.lean`.
- `rg -n "AC0|AC0p|FormulaSemanticMultiSwitchingProvider|CurrentSingleton|AsymptoticDAG|AsymptoticFormula|AC0LocalityBridge|AC0AtlasBridge|AC0ApproxFamily" outputs/nogolog.jsonl seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md pnp3/Magnification/UnconditionalResearchGap.lean pnp3/Complexity/Interfaces.lean` -> relevant hits only in `UnconditionalResearchGap.lean` warning against AC0/support-locality routes; no targeted hits in the optional NoGoLog/retrospective files.
- `rg -n "AC0|AC0p|AC0LocalityBridge|AC0AtlasBridge|AC0ApproxFamilyBridge|AsymptoticDAGCollapse|AsymptoticFormulaCollapse|ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" pnp4/Pnp4/AlgorithmsToLowerBounds pnp4/Pnp4/Frontier pnp3/Magnification -g '*.lean'` -> confirmed pnp4 AC0[p] restricted surfaces and no direct import from audited pnp3 files to pnp4 AC0[p] bridge files.
- `./scripts/check.sh` -> completed successfully after this report was written; no Lean/source changes were made.

## 19. Final structured output

Task: A03  
Engineer handle: gpt55  
Branch: khanukov/phase1-A03-gpt55  
Commit before: d27b069127f63a3f24ab30d1a91c86c84f8b79c7  
Commit after: TO_BE_FILLED_AFTER_COMMIT

Files added/modified:
- `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A03_pnp3_ac0_bridges_gpt55.md`

Outcome:  
AUDIT_LANDED

Executive verdict:  
PARTIAL_BUT_USEFUL

Files audited:
- 20 files inspected or searched; core audited Lean files are `AC0LocalityBridge.lean`, `AC0AtlasBridge.lean`, `AC0ApproxFamilyBridge.lean`, `AsymptoticDAGCollapse.lean`, and `AsymptoticFormulaCollapse.lean`.

Key findings:
1. The pnp3 AC0 bridge files implement real adapters and no-go checks, but not a complete AC0 -> `PpolyDAG` lower-bound pipeline.
2. The current internal semantic provider is singleton/per-formula and explicitly audit/refuted-channel adjacent; it should not be promoted as a source theorem.
3. The only audited canonical DAG endpoint is conditional on an externally supplied asymptotic `PpolyDAG` collapse and `NP_strict` hypothesis.

Kernel-checked content found:
- AC0 certificate-to-atlas/scenario-budget adapters, no-large-gap theorem, weak linked-testset extraction, small-mismatch adapters, approximate-family contradiction, formula-separation wrappers, DAG slice adapters, and conditional `NP_not_subset_PpolyDAG` wrapper.

Staged / placeholder content found:
- Provider/package Props for semantic switching certificates, nontrivial family, small mismatch, approximate family, support-bounds, and formula/asymptotic collapse inputs.

Refuted / vacuous / legacy route findings:
- `FormulaSemanticMultiSwitchingProvider` is audit-marked `refuted-channel`; singleton-route theorems show the internal provider is `[f]` and cannot satisfy nontrivial-family payload; scenario budget alone has a no-large-gap theorem.

Hidden payload / Rule 16 findings:
- No class/instance/opaque hazards in audited files. Main risk is `Classical.choose hFormula` plus noncomputable singleton/provider constructions; harmless as audit infrastructure, dangerous if promoted as candidate payload.

Recommended Phase 1+ tasks:
- 4
- Document/test scenario-budget no-go surface.
- Write restricted AC0[p] cross-track boundary note.
- Operator decision on quarantining `FormulaSemanticMultiSwitchingProvider` uses.
- Formal markdown surface for the genuine DAG source gap.

Hold / cancel recommendations:
- Hold any task deriving final targets from semantic/support-bounds providers.
- Downgrade AC0[p] milestones to restricted lower-bound side track unless paired with explicit DAG-source bridge.
- Do not cancel clean DAG slice-bridge reuse.

Commands run:
- `./scripts/check.sh` -> pass
- Required `rg ...` commands -> summarized above
- `find ...` AC0/asymptotic file cross-check -> pass

Scope violations:
- none

Honest caveats:
- I did not reconstruct the full import graph transitively.
- I did not inspect every private proof body in the long constructive middle of `AC0LocalityBridge.lean`.
- I verified signatures and route shape, not third-party mathematical adequacy.
- I did not run per-theorem `#print axioms`.
