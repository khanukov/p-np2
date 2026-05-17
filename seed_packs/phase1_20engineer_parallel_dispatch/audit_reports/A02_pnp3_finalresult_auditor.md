# A02 Audit Report: `pnp3/Magnification/FinalResult*.lean`

Task: A02  
Area: pnp3 final-result surface  
Engineer handle: auditor  
Branch: `khanukov/phase1-A02-auditor`  
Date: 2026-05-17

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL.**

The FinalResult pipeline is complete only in the narrow, conditional sense that a supplied `NP_not_subset_PpolyDAG` or a supplied `ResearchGapWitness` is kernel-wired to `P_ne_NP` through `P_ne_NP_final_dag_only` and `UnconditionalResearchGap.P_ne_NP_final`. It is **not** complete as an unconditional P-vs-NP proof: all public zero-argument or provider-style final endpoints in this audited area are explicitly quarantined as vacuous/refuted support-bounds routes. The genuinely reusable pieces are mostly adapter theorems: they convert explicit DAG-side route obligations, anti-checker packages, fixed-slice lower-bound routes, or weak-route statements into `NP_not_subset_PpolyDAG`, then into `P_ne_NP`. The dangerous content is well labeled with `RefutedRoute_`/`Vacuous_` names and audit comments, but it remains import-reachable through compatibility modules and therefore should not be used as research progress. The main missing work is not another wrapper; it is a non-vacuous source of `ResearchGapWitness.dagSeparation` / `NP_not_subset_PpolyDAG` or a pnp4 adapter from a future `VerifiedNPDAGLowerBoundSource`.

## 2. Files audited

| File | Approximate role | Read depth | Notes |
| --- | --- | --- | --- |
| `RESEARCH_CONSTITUTION.md` | Governance and route-policy rules for final claims, refuted routes, hidden payloads, and candidate boundaries | Read structurally; target rules inspected | Used to interpret `ResearchGapWitness`, refuted-route quarantine, and hidden-payload risks. |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | Phase dispatch and worker requirements | Read structurally | Older E-task wording was overridden by the A02 prompt where conflicting. |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | Shared worker rules, checks, PR template | Read structurally | Implementation/lakefile parts treated as non-applicable because this is markdown-only. |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A02_audit_pnp3_finalresult.md` | Exact A02 scope and required sections | Read fully | Source of the six-file audit scope. |
| `pnp3/Magnification/FinalResult.lean` | Historical compatibility import path | Read fully | Thin import/re-export of `UnconditionalResearchGap`. |
| `pnp3/Magnification/FinalResultCore.lean` | Compatibility aggregation for refactored final-result layers | Read fully | Imports mainline, audit routes, weak routes, and legacy TM wrappers. |
| `pnp3/Magnification/FinalResultMainline.lean` | Main conditional pipeline and anti-checker/DAG wrappers | Read structurally plus signature search; key proof bodies inspected | Full line-by-line proof reconstruction was not attempted because the goal is endpoint audit, not proof review. |
| `pnp3/Magnification/FinalResultAuditRoutes.lean` | Refuted/vacuous/provider-backed compatibility surfaces | Read structurally plus signature search; provider block read closely | Critical for Rule 16 and vacuous route assessment. |
| `pnp3/Magnification/FinalResultLegacyTM.lean` | Legacy fixed-slice TM wrappers around DAG lower-bound routes | Read fully | Mostly thin wrappers to `LowerBounds` theorems and `P_ne_NP_final_dag_only`. |
| `pnp3/Magnification/FinalResultWeakRoutes.lean` | Weak-route and class-level DAG wrappers | Read structurally plus signature search | Important for safe reusable interfaces, but many wrappers are thin compositions. |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | Public honest research-gap boundary imported by `FinalResult.lean` | Read fully | Not one of the six task files, but necessary to answer `ResearchGapWitness` questions. |
| `pnp3/Complexity/Interfaces.lean` | Trust-root complexity interfaces | Skimmed structurally | Used to confirm target names and that final theorem target is interface-level `P_ne_NP`. |
| `pnp3/Tests/RouteSurfaceAudit.lean` | Test/audit surface for final routes | Searched only | Used to check public route reachability and quarantine expectations. |
| `pnp3/Tests/AxiomsAudit.lean` | Axiom-print audit surface | Searched only | Used to identify which final endpoints are audited by tests. |
| `pnp4/**` Lean files | pnp4 integration/import check | Searched only | Search found no direct pnp4 imports or references to these pnp3 final-result names. |

## 3. Executive summary: completeness modulo `ResearchGapWitness`

The pipeline is complete modulo `ResearchGapWitness` in the following precise sense:

```lean
ResearchGapWitness.dagSeparation : NP_not_subset_PpolyDAG
P_ne_NP_final_dag_only : NP_not_subset_PpolyDAG → P_ne_NP
P_ne_NP_final : ResearchGapWitness → P_ne_NP
```

This is a kernel-checked conditional bridge, not a solved lower bound. The audited FinalResult files provide many additional sufficient routes into `NP_not_subset_PpolyDAG`, including anti-checker eventual routes, fixed-slice route wrappers, legacy TM wrappers, and weak-route class-level wrappers. However, every route that relies on `FormulaSupportRestrictionBoundsPartial`, `FormulaSupportBoundsFromMultiSwitchingContract`, default support-bounds providers, `VacuousFinalPayloadProvider`, or overbroad fixed-params uniform provenance is explicitly treated as refuted/vacuous/audit-only. The `UnconditionalResearchGap.lean` header states the current support-bounds route is not merely unfinished; its core predicates are ex-falso, so the remaining task is a non-vacuous DAG separation source.

## 4. File-by-file findings

### `FinalResult.lean`

- Imports only `Magnification.UnconditionalResearchGap`.
- No declarations beyond namespace/doc comment.
- Role: preserves historical `Magnification.FinalResult` import path while exposing the honest public frontier (`ResearchGapWitness → P_ne_NP`) from `UnconditionalResearchGap`.
- Safe to reuse as an import path; do not add new endpoint logic here unless deliberately changing public surface.

### `FinalResultCore.lean`

- Imports `FinalResultMainline`, `FinalResultAuditRoutes`, `FinalResultWeakRoutes`, and `FinalResultLegacyTM`.
- No theorem declarations; only aggregation documentation.
- Role: compatibility umbrella for refactored final-result surface.
- Risk: importing it brings audit/refuted/vacuous routes into scope as well as safe mainline wrappers.

### `FinalResultMainline.lean`

Important structures / staged packages:

- `AsymptoticFormulaTrackHypothesis`: explicit asymptotic slice data (`spec`, threshold `N0`, parameters `pAt`, agreement `sliceEq`). Classification: **staged interface / canonical plumbing**. Does not itself prove lower bounds.
- `AsymptoticNPPullback hAsym`: packages `NP_strict` for the asymptotic language. Classification: **staged interface**; requires hard NP witness payload.
- `AsymptoticFormulaTrackData`: constructive source package including `gapPartialMCSP_Asymptotic_in_NP_TM`. Classification: **staged interface**, useful and safer than provider classes.
- `SwitchingAssumptions`: contains `FormulaSupportBoundsFromMultiSwitchingContract`. Classification: **refuted route carrier**.
- `SwitchingAssumptions_fromPipeline` and `MagnificationAssumptions_fromPipeline`: pipeline-aware replacements that separate semantic provenance and support-bounds-from-pipeline. Classification: **staged/conditional**, not a final DAG bridge.
- `AntiCheckerAssumptions`: packages only asymptotic + NP pullback. Classification: **safe adapter package** if supplied honestly.
- `MagnificationAssumptions`: contains `SwitchingAssumptions` plus anti-checker; explicitly legacy/audit because of the refuted switching field.

Important theorem families:

- Formula/real endpoint wrappers such as `NP_not_subset_PpolyFormula_final_with_provider`, `_fromPipeline`, and `NP_not_subset_PpolyReal_final_with_provider` are kernel-checked conditional implications from locality-provider/AC0/provenance assumptions to formula/real non-inclusion. Classification: **conditional side-track**, not DAG/P-vs-NP mainline unless bridged to `PpolyDAG`.
- `RefutedRoute_NP_not_subset_PpolyFormula_final*` and `RefutedRoute_NP_not_subset_PpolyReal_final*` are explicitly ex-falso support-bounds wrappers. Classification: **refuted route / audit-only**.
- `P_ne_NP_final_with_provider` proves `P_ne_NP` from explicit `NP_not_subset_PpolyDAG` plus explicit `PsubsetPpolyCompiledRuntimeLinearOutputContracts`. Classification: **canonical conditional endpoint**.
- `P_ne_NP_final_dag_only` proves `P_ne_NP` from `NP_not_subset_PpolyDAG` using internalized `proved_P_subset_PpolyDAG_internal`. Classification: **canonical conditional endpoint**.
- `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute` and `_withAntiChecker` prove DAG non-inclusion from explicit asymptotic anti-checker data plus `AsymptoticIsoStrongRoute`. Classification: **conditional mainline adapter**; hard payload is the route itself.
- `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute` and `_withAntiChecker` reduce a promise-YES route to the iso-strong route, then to DAG non-inclusion. Classification: **conditional mainline adapter**.
- Fixed-slice route definitions (`FixedSlicePromiseYesCertificateRoute`, `FixedSlicePromiseValueLocalityRoute`, `FixedSliceWitnessEasyDensityRoute`, `FixedSliceWitnessUniformLowerRoute`, `FixedSliceTransferQuarterRoute`, `FixedSliceSupportHalfValueSupportedRoute`, `FixedSliceDAGStableRestrictionSlackRoute`, `FixedSliceShrinkageCertificateRoute`, `FixedSliceRestrictionDataRoute`, `FixedSliceSupportNumericRoute`, `FixedSliceSupportNumericComponentRoute`) are mostly Prop aliases for lower-bound obligations. Classification: **staged Prop / possible wrapper risk if advertised as proofs**.
- Fixed-slice conversion theorems (`fixedSlice..._of_fixedSlice...`) and `_withAntiChecker` final wrappers are kernel-checked adapter chains from stronger route obligations to `NP_not_subset_PpolyDAG` / `P_ne_NP`.

### `FinalResultAuditRoutes.lean`

- Contains the quarantined compatibility layer around `MagnificationAssumptions`, support bounds, multiswitching, and provider/default payload channels.
- `fixedSliceCollapse_of_supportBounds` turns refuted `FormulaSupportRestrictionBoundsPartial` into fixed-slice `PpolyDAG → False`; classification: **refuted route consumer**.
- `RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptotic_supportBounds`, `RefutedRoute_NP_not_subset_PpolyDAG_final_with_magnification`, `RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptoticPullback`, `RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData`, `RefutedRoute_NP_not_subset_PpolyDAG_final_of_supportBounds`, and companion `P_ne_NP` theorems are all audit/compatibility endpoints.
- The non-`RefutedRoute_` legacy package-shaped wrappers around anti-checker routes (`NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withMagnification`, etc.) immediately project `hMag.antiChecker`. They can be logically non-vacuous if `hMag` is honestly supplied, but the package includes a refuted switching field, so future work should prefer the `_withAntiChecker` versions.
- `RefutedRoute_NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance` makes a research-level bottleneck visible but intentionally reconstructs the old false support-bounds predicate from an overbroad uniform provenance hypothesis. Classification: **refuted/gap-exposing, do not use as candidate**.
- `VacuousFinalPayloadProvider`, `AsymptoticPayloadProvider`, default flags, and `Vacuous_P_ne_NP_via_*` endpoints are Rule 16-relevant hidden-payload surfaces. They are labeled audit-only and should remain quarantined.

### `FinalResultWeakRoutes.lean`

- Provides thin wrappers from weak/accepted-family/promise-YES/PRG/easy-source/restriction-extraction statements into no-small-DAG conclusions, global `¬ PpolyDAG bridge.L`, or `NP_not_subset_PpolyDAG` given an explicit NP witness on the bridge language.
- It does **not** mention `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract` in the audited file. It works one layer below the final research-gap witness.
- Safe reusable adapters include `noSmallDAG_surface_of_acceptedFamilyStatement`, `noSmallDAG_surface_of_promiseYesSubcubeStatement`, `not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies`, and the `NP_not_subset_PpolyDAG_surface_of_*WeakRoute` wrappers, provided future workers supply the actual weak-route hypotheses honestly.
- Risk: the word “weak route” is accurate; these are sufficient-condition adapters, not source theorems. Do not advertise them as P-vs-NP progress without the missing source theorem and NP bridge.

### `FinalResultLegacyTM.lean`

- Contains fixed-slice TM compatibility wrappers from stronger DAG-side lower-bound obligations to `NP_not_subset_PpolyDAG` and then `P_ne_NP`.
- Safe conditional wrappers: `NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM`, `...certificateProvider_TM`, `...invariantProvider_TM`, `...sourceClosure_TM`, `...blocker_TM`, and payload variants.
- Refuted wrappers: `RefutedRoute_NP_not_subset_PpolyDAG_final_of_supportBounds_TM` and `RefutedRoute_P_ne_NP_final_of_supportBounds_TM` because they consume `FormulaSupportRestrictionBoundsPartial`.
- These are legacy/stronger optional sufficient routes. They do not construct an unconditional fixed-slice witness and should not be the default mainline unless a future task explicitly targets the corresponding DAG-side source obligation.

## 5. Pipeline diagram

```text
A. Honest public frontier

  ResearchGapWitness
    .dagSeparation : NP_not_subset_PpolyDAG
      └─ P_ne_NP_final_dag_only
          └─ P_ne_NP_final / P_ne_NP_of_researchGap : P_ne_NP

B. Direct DAG conditional endpoint

  hNPDag : NP_not_subset_PpolyDAG
    ├─ P_ne_NP_final_dag_only
    └─ P_ne_NP_final_with_provider (if explicit P⊆PpolyDAG contracts supplied)

C. Anti-checker/eventual mainline adapters

  AntiCheckerAssumptions
    + AsymptoticIsoStrongRoute
      └─ NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker
          └─ P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker

  AntiCheckerAssumptions
    + AsymptoticPromiseYesCertificateRoute
      └─ asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute
          └─ same DAG/P≠NP endpoint

D. Fixed-slice route adapters

  AntiCheckerAssumptions + n ≥ N0 + one fixed-slice route
    (collapse / promise-YES / locality / support-half / shrinkage /
     restriction / numeric / transfer / witness-density / source-closure / blocker)
      └─ NP_not_subset_PpolyDAG_final_of_asymptotic_*_withAntiChecker
          └─ P_ne_NP_final_dag_only

E. Weak route adapters

  GapSliceFamily + bridge + NP bridge.L + weak-route source debt
      └─ ¬ PpolyDAG bridge.L
          └─ NP_not_subset_PpolyDAG_surface_of_*WeakRoute

F. Legacy/refuted/audit-only routes

  FormulaSupportRestrictionBoundsPartial
    or FormulaSupportBoundsFromMultiSwitchingContract
    or MagnificationAssumptions.switching.multiswitching
    or VacuousFinalPayloadProvider / default support-bounds Fact
      └─ RefutedRoute_* / Vacuous_*
          └─ NP_not_subset_PpolyDAG or P_ne_NP  (audit-only, ex-falso risk)
```

## 6. Top-level theorem / structure inventory

This inventory groups related declarations rather than listing every thin wrapper individually.

| Declaration(s) | File | Type/signature summary | Classification | Hard payload dependency |
| --- | --- | --- | --- | --- |
| `AsymptoticFormulaTrackHypothesis` | `FinalResultMainline.lean` | Asymptotic spec, threshold, parameter map, slice agreement | staged Prop/interface | Slice agreement and partial-MCSP asymptotic setup; no `ResearchGapWitness`. |
| `AsymptoticNPPullback` | `FinalResultMainline.lean` | `NP_strict (gapPartialMCSP_AsymptoticLanguage hAsym.spec)` | staged interface | Hard NP witness. |
| `AsymptoticFormulaTrackData` | `FinalResultMainline.lean` | Constructive asymptotic source data with TM NP witness | staged interface, safer payload | `gapPartialMCSP_Asymptotic_in_NP_TM`; no DAG lower bound. |
| `SwitchingAssumptions`, `MagnificationAssumptions` | `FinalResultMainline.lean` | Packages `FormulaSupportBoundsFromMultiSwitchingContract` with anti-checker data | refuted route carrier | Refuted support-bounds/multiswitching payload. |
| `SwitchingAssumptions_fromPipeline`, `MagnificationAssumptions_fromPipeline` | `FinalResultMainline.lean` | Separates semantic provider and support-bounds-from-pipeline | conditional / staged | AC0 provenance/support-bound payload; no DAG bridge. |
| `AntiCheckerAssumptions` | `FinalResultMainline.lean` | Packages asymptotic track and NP pullback | canonical adapter package | Asymptotic data + NP witness. |
| `AsymptoticIsoStrongRoute` | `FinalResultMainline.lean` | For any per-slice DAG witnesses, produces eventual isolation envelope data | conditional mainline source obligation | Hard weak-route/isolation payload; no `ResearchGapWitness`. |
| `AsymptoticPromiseYesCertificateRoute` | `FinalResultMainline.lean` | Eventual promise-YES certificate route | conditional mainline source obligation | Hard certificate route. |
| `AsymptoticPromiseYesWeakRouteEventually` | `FinalResultMainline.lean` | Eventual weak route producing promise-YES subcubes | weak/staged route | Hard weak-route payload. |
| `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually` | `FinalResultMainline.lean` | Converts weak route to certificate route | conditional adapter | Uses `Classical.choose` for existential data extraction. |
| `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute` | `FinalResultMainline.lean` | Converts promise-YES route to iso-strong route | conditional adapter | Route hypothesis. |
| `NP_not_subset_PpolyFormula_final_with_provider`, `_fromPipeline` | `FinalResultMainline.lean` | Provider/provenance assumptions imply `NP_not_subset_PpolyFormula` | side-track conditional | Locality provider + NP bridge; no DAG target. |
| `RefutedRoute_NP_not_subset_PpolyFormula_final*`, `RefutedRoute_NP_not_subset_PpolyReal_final*` | `FinalResultMainline.lean` | Support-bounds/multiswitching package implies formula/real non-inclusion | refuted/audit-only | Refuted support-bounds payload. |
| `P_ne_NP_final_with_provider` | `FinalResultMainline.lean` | `NP_not_subset_PpolyDAG` + explicit P⊆PpolyDAG contracts → `P_ne_NP` | canonical conditional | `NP_not_subset_PpolyDAG`. |
| `P_ne_NP_final_dag_only` | `FinalResultMainline.lean` | `NP_not_subset_PpolyDAG → P_ne_NP` | canonical conditional | `NP_not_subset_PpolyDAG`; internal P⊆PpolyDAG theorem. |
| `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute(_withAntiChecker)` | `FinalResultMainline.lean` | Asymptotic route → `NP_not_subset_PpolyDAG` | conditional mainline adapter | `AsymptoticIsoStrongRoute` + NP bridge. |
| `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute(_withAntiChecker)` | `FinalResultMainline.lean` | Promise-YES route → DAG non-inclusion | conditional mainline adapter | Promise-YES route + NP bridge. |
| `FixedSlice*Route` aliases | `FinalResultMainline.lean` | Prop aliases for fixed-slice lower-bound obligations | staged Prop | Hard fixed-slice lower-bound payload. |
| `NP_not_subset_PpolyDAG_final_of_asymptotic_*_withAntiChecker` fixed-slice family | `FinalResultMainline.lean` | Fixed-slice obligation + anti-checker → DAG non-inclusion | conditional adapter | Fixed-slice route hypotheses. |
| `fixedSliceCollapse_of_supportBounds` | `FinalResultAuditRoutes.lean` | Support bounds → fixed-slice `PpolyDAG → False` | refuted route | `FormulaSupportRestrictionBoundsPartial`. |
| `RefutedRoute_NP_not_subset_PpolyDAG_final_*`, `RefutedRoute_P_ne_NP_final_*` | `FinalResultAuditRoutes.lean` | Support-bounds/multiswitching/default packages → DAG/P≠NP endpoints | refuted/audit-only | Refuted support-bounds or overbroad provenance. |
| `VacuousFinalPayloadProvider` | `FinalResultAuditRoutes.lean` | Typeclass provider containing `hMS` and asymptotic data | hidden-payload risk, quarantined | Refuted `FormulaSupportBoundsFromMultiSwitchingContract`. |
| `AsymptoticPayloadProvider` | `FinalResultAuditRoutes.lean` | Typeclass for asymptotic data only | hidden-payload infrastructure | Asymptotic data; dangerous when paired with default support-bounds. |
| `Vacuous_P_ne_NP_via_*` | `FinalResultAuditRoutes.lean` | Zero-visible-argument/provider-backed P≠NP endpoints | vacuous/refuted/audit-only | Typeclass/default support-bounds payload. |
| `NP_not_subset_PpolyDAG_final_of_*_TM`, `P_ne_NP_final_of_*_TM` | `FinalResultLegacyTM.lean` | Fixed-slice TM witness + DAG-side route → DAG/P≠NP | legacy conditional | TM witness + DAG-side route; support-bounds variants refuted. |
| `noSmallDAG_surface_of_*` | `FinalResultWeakRoutes.lean` | Weak source statements → no small DAG solver | weak conditional adapter | Weak-route hypotheses. |
| `not_globalPpolyDAG_surface_of_*` | `FinalResultWeakRoutes.lean` | Canonical/weak debt → `¬ PpolyDAG bridge.L` | weak conditional adapter | Bridge + source debt. |
| `NP_not_subset_PpolyDAG_surface_of_*` | `FinalResultWeakRoutes.lean` | Bridge NP witness + no-global-DAG route → `NP_not_subset_PpolyDAG` | weak conditional adapter | `NP bridge.L` + weak route debt. |
| `ResearchGapWitness`, `NP_not_subset_PpolyDAG_final`, `P_ne_NP_final` | `UnconditionalResearchGap.lean` | Direct DAG separation witness and public final endpoints | canonical public frontier | `ResearchGapWitness.dagSeparation`. |

## 7. Kernel-checked content

The following is actually proven by Lean, subject to the imported definitions and hypotheses:

1. **DAG separation implies P ≠ NP.** `P_ne_NP_final_dag_only` proves `ComplexityInterfaces.P_ne_NP` from `ComplexityInterfaces.NP_not_subset_PpolyDAG`, using the repository's internal theorem `proved_P_subset_PpolyDAG_internal` and `P_ne_NP_of_nonuniform_dag_separation`.
2. **Research-gap witness implies final endpoints.** `UnconditionalResearchGap.NP_not_subset_PpolyDAG_final` returns `gap.dagSeparation`; `UnconditionalResearchGap.P_ne_NP_final` composes that witness with `P_ne_NP_final_dag_only`.
3. **Asymptotic anti-checker route adapters compile.** Given `AntiCheckerAssumptions` plus `AsymptoticIsoStrongRoute` or `AsymptoticPromiseYesCertificateRoute`, Lean derives `NP_not_subset_PpolyDAG` and then `P_ne_NP`.
4. **Fixed-slice route adapters compile.** Given anti-checker data, a threshold slice, and a fixed-slice lower-bound obligation/collapse/producer, Lean derives `NP_not_subset_PpolyDAG` and then `P_ne_NP`.
5. **Weak-route bridge adapters compile.** Given explicit weak-route source debt, bridge data, and an NP witness for the bridge language, Lean derives `¬ PpolyDAG bridge.L` or `NP_not_subset_PpolyDAG`.
6. **Legacy TM adapters compile.** Given `GapPartialMCSP_TMWitness p` plus stronger DAG-side route obligations, Lean derives `NP_not_subset_PpolyDAG` and `P_ne_NP`.
7. **Refuted-route wrappers also compile.** Lean can derive endpoint conclusions from support-bounds or provider assumptions; this is not progress because those assumptions are formally known/refuted elsewhere or explicitly overbroad in this audit surface.

No audited theorem constructs a closed, zero-argument, non-vacuous `P_ne_NP` proof. No audited theorem constructs a `ResearchGapWitness` without an input that is already as hard as `NP_not_subset_PpolyDAG` or a route obligation meant to imply it.

## 8. Staged / placeholder / Prop-only content

| Content | Status | Risk assessment |
| --- | --- | --- |
| `AsymptoticFormulaTrackHypothesis` | Honest staging | Harmless if treated as data; not a proof of lower bounds. |
| `AsymptoticNPPullback` | Honest staging | Requires a real NP witness; no P-vs-NP claim. |
| `AsymptoticFormulaTrackData` | Honest staging | Safer than provider classes because payload is explicit; still not a DAG lower bound. |
| `SwitchingAssumptions_fromPipeline`, `MagnificationAssumptions_fromPipeline` | Staged interface | Possible wrapper risk if advertised as non-ex-falso final progress; still AC0/formula side. |
| `MagnificationAssumptions` | Refuted carrier | Contains refuted `FormulaSupportBoundsFromMultiSwitchingContract`; should not be touched except quarantine/audit. |
| `AsymptoticIsoStrongRoute`, `AsymptoticPromiseYesCertificateRoute`, `AsymptoticPromiseYesWeakRouteEventually` | Prop-level source obligations | Honest staging if named as obligations; hidden hard theorem risk if a candidate merely wraps these. |
| `FixedSlice*Route` aliases | Prop aliases around lower-bound conditions | Wrapper risk: a future task can “prove” endpoints by assuming these exact obligations. Must classify as formalization source obligations, not results. |
| `hasDefaultAsymptoticFormulaTrackData` | Default availability flag | Harmless alone; dangerous when paired with default support-bounds provider to produce vacuous endpoints. |
| `VacuousFinalPayloadProvider` | Provider interface | Hidden payload risk; already quarantined. |
| Commented `researchGapWitness` template in `UnconditionalResearchGap.lean` | Placeholder comment only | Harmless as documentation; no active Lean declaration. |

## 9. ResearchGapWitness usage map

Inside the six audited `FinalResult*.lean` files, `ResearchGapWitness` appears in documentation/import-path comments only; no theorem in those six files takes it directly. The active direct usage is in `pnp3/Magnification/UnconditionalResearchGap.lean`:

- `structure ResearchGapWitness` with field `dagSeparation : ResearchGapTarget` where `ResearchGapTarget := NP_not_subset_PpolyDAG`.
- `P_ne_NP_of_researchGap (gap : ResearchGapWitness) : P_ne_NP`.
- `NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness) : NP_not_subset_PpolyDAG`.
- `P_ne_NP_final (gap : ResearchGapWitness) : P_ne_NP`.

The final-result compatibility path is therefore:

```text
import Magnification.FinalResult
  -> import Magnification.UnconditionalResearchGap
      -> public final theorem takes ResearchGapWitness
```

## 10. Dependency on `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, and related hard payloads

- Direct dependency on `NP_not_subset_PpolyDAG`:
  - `P_ne_NP_final_dag_only` and `P_ne_NP_final_with_provider` consume it.
  - `ResearchGapWitness.dagSeparation` is exactly this target via `ResearchGapTarget`.
  - All `NP_not_subset_PpolyDAG_final_of_*` and `NP_not_subset_PpolyDAG_surface_of_*` wrappers aim to produce it from stronger route hypotheses.
- Direct dependency on `VerifiedNPDAGLowerBoundSource`:
  - None found in the six audited files.
- Direct dependency on `SearchMCSPMagnificationContract`:
  - None found in the six audited files.
- Direct `SourceTheorem` / `gap_from` candidate pattern:
  - None found in the six audited files.
- pnp4 integration implication:
  - The pnp3 final-result layer is ready to consume a DAG separation, but no pnp4-to-pnp3 adapter from `VerifiedNPDAGLowerBoundSource` to `ResearchGapWitness` appears in the audited files, and a repository-wide pnp4 search found no direct references to these pnp3 final-result names.

## 11. Refuted / vacuous / legacy route check

Search terms inspected included `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `Legacy`, `_Partial`, `TODO`, and `placeholder`.

Findings:

- `RefutedRoute_` names are abundant and generally well isolated to `FinalResultMainline.lean` formula/real wrappers, `FinalResultAuditRoutes.lean`, and support-bounds variants in `FinalResultLegacyTM.lean`.
- `Vacuous_` endpoints occur in `FinalResultAuditRoutes.lean` and are typeclass/provider-backed compatibility endpoints. They are explicitly documented as quarantine/audit-only.
- `MagnificationAssumptions` is legacy because it contains `switching.multiswitching : FormulaSupportBoundsFromMultiSwitchingContract`; do not build new work on it. Prefer `AntiCheckerAssumptions` for DAG routes or direct `ResearchGapWitness` for final closure.
- `supportBounds` appears in refuted route names and comments, and in fixed-slice collapse wrappers that consume the refuted predicate.
- `FinalPayloadProvider` appears only as historical wording / renamed quarantine to `VacuousFinalPayloadProvider`; this is good governance.
- `weakRoute` appears in weak-route theorem names. These are not refuted by name but are explicitly weak sufficient-condition adapters.
- `Legacy` appears mainly in comments and `FinalResultLegacyTM.lean`; legacy wrappers are import-stability surfaces.
- No active `TODO` was found in the audited files by the required search pattern.
- The only active placeholder-like item is the commented future completion template in `UnconditionalResearchGap.lean`, outside the six audited files; it is not an active Lean declaration.

## 12. Hidden payload / Rule 16 check

Search terms inspected included `class`, `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `Classical.choose`, and `noncomputable def`.

Classified occurrences:

| Occurrence | Classification | Interpretation |
| --- | --- | --- |
| `noncomputable def eventualCanonicalBridge_of_asymptotic` | harmless infrastructure | Constructs bridge data from explicit asymptotic fields; no hidden final payload. |
| `noncomputable def promiseYesSubcubeCertificateAt_of_eventualPromiseYesWeakRoute` | standard existential extraction | Uses `Classical.choose` to unpack route witnesses from explicit hypothesis. Not a hidden proof of the route. |
| `Classical.choose` in conversion from eventual weak route to certificate route | standard exponent/witness extraction | Acceptable as adapter extraction, but future proofs should not hide source obligations behind this conversion. |
| `Classical.choose hDag` in fixed-slice collapse routes | standard extraction from explicit `PpolyDAG` witness | Harmless for contradiction adapters. |
| `Classical.choose hFormula` in overbroad uniform provenance route | suspicious / forbidden if used by candidate | Occurs in a refuted/gap-exposing theorem reconstructing old false support-bounds; do not use as source. |
| `class VacuousFinalPayloadProvider` | hidden-payload risk, quarantined | Contains refuted multiswitching contract and asymptotic data; explicitly audit-only. |
| `class AsymptoticPayloadProvider` | harmless alone, risky in combination | Only asymptotic data, but participates in default-source vacuous endpoints when paired with default support-bounds facts. |
| `noncomputable def defaultAsymptoticFormulaTrackData` | hidden-default infrastructure | Uses `Classical.choice` from `Nonempty`; harmless alone but dangerous when used in zero-visible-payload endpoints. |
| `noncomputable instance asymptoticPayloadProvider_of_default_asymptoticData` | hidden-payload risk if combined | Typeclass channel for asymptotic data; quarantine concerns are weaker than formula support-bounds but still provider-based. |
| `instance vacuousFinalPayloadProvider_of_default_supportBounds` | hidden-payload risk / refuted channel | Reconstructs refuted formula-side payload through typeclass resolution. Should remain audit-only. |
| `Fact hasDefaultFormulaSupportRestrictionBoundsPartial` in vacuous endpoints | forbidden if used by candidate | Default support-bounds facts are a hidden assumption channel for refuted payload. |
| `opaque`, `default_instance`, `attribute [instance]` | none found in audited scope | No additional risk from those channels. |

## 13. Barrier relevance

| Barrier / theme | Audited-area status | Details |
| --- | --- | --- |
| Natural proofs | Mostly nothing explicit | No direct natural-proofs theorem in these files. Related “source debt” wrappers are too abstract to certify bypass. |
| Relativization | Nothing explicit | No relativization barrier theorem in audited files. |
| Algebrization | Nothing explicit | No algebrization barrier theorem in audited files. |
| Locality | Typed interfaces and staged/conditional theorems | Formula/locality providers and support-bounds routes are central; refuted support-bounds routes are quarantined. |
| Hardwiring | Important audit concern | Refuted support-bounds and overbroad uniform provenance are dangerous because they quantify over arbitrary formula witnesses and can reconstruct truth-table/singleton hardwiring attacks. |
| Support-cardinality-only | Refuted route content | `FormulaSupportRestrictionBoundsPartial` and multiswitching support-bounds routes are explicitly marked ex-falso/refuted. |
| Syntax-only filters | Mostly audit relevance | Formula support and AC0 provenance filters appear as predicates; no new safe syntax-only filter is proven adequate here. |
| Normalization filters | Nothing substantial in audited final files | No direct normalization-filter theorem observed. |
| Search-to-decision | Weak interface only | Weak-route adapters use search/solver-style slice statements but do not solve search-to-decision lower bounds. |
| MCSP / magnification | Typed interfaces and conditional adapters | Partial-MCSP asymptotic data, gap languages, anti-checker routes, and magnification wrappers are central, but final closure still requires DAG separation. |

## 14. Reuse map

Safe to reuse:

- `P_ne_NP_final_dag_only` as the honest final pnp3 bridge from `NP_not_subset_PpolyDAG` to `P_ne_NP`.
- `UnconditionalResearchGap.ResearchGapWitness`, `NP_not_subset_PpolyDAG_final`, and `P_ne_NP_final` as the public final boundary.
- `AntiCheckerAssumptions` as a cleaner package than `MagnificationAssumptions` for anti-checker/DAG route adapters.
- `AsymptoticFormulaTrackData` and its conversions to `AsymptoticFormulaTrackHypothesis` / `AsymptoticNPPullback` when source data is explicit.
- `_withAntiChecker` DAG route wrappers in `FinalResultMainline.lean`.
- `FinalResultWeakRoutes.lean` adapters from explicit weak-route source obligations to `NP_not_subset_PpolyDAG`, with honest labeling as weak sufficient conditions.
- `FinalResultLegacyTM.lean` non-support-bounds TM wrappers when a future task truly has a fixed-slice TM witness plus DAG-side source obligation.
- Existing tests/audits: `pnp3/Tests/RouteSurfaceAudit.lean`, `pnp3/Tests/AxiomsAudit.lean`, and falsifiability probes should be updated if public surfaces change.

Avoid:

- `MagnificationAssumptions` for new work.
- `SwitchingAssumptions` and any route consuming `FormulaSupportBoundsFromMultiSwitchingContract`.
- `FormulaSupportRestrictionBoundsPartial` and all `supportBounds` final wrappers.
- `VacuousFinalPayloadProvider`, `Vacuous_P_ne_NP_via_*`, default support-bounds `Fact` channels, and provider-backed zero-visible-payload endpoints.
- `RefutedRoute_NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance` as a candidate route; it is a diagnostic/gap-exposing theorem showing overbroad provenance is too strong.
- Non-`RefutedRoute_` wrappers in `FinalResultAuditRoutes.lean` that take `MagnificationAssumptions`; use `_withAntiChecker` equivalents instead.

## 15. Gap map

### A. Engineering gaps

1. No pnp4 adapter was found that turns a future pnp4 `VerifiedNPDAGLowerBoundSource` into pnp3 `ResearchGapWitness` or a pnp4-native final bridge.
2. The import surface still makes audit/refuted routes reachable through `FinalResultCore`; this is intentional compatibility, but it increases misuse risk.
3. Some legacy package-shaped wrappers in `FinalResultAuditRoutes.lean` lack `RefutedRoute_` names even though they take `MagnificationAssumptions`; this can confuse search-based governance.
4. The final-result route inventory is not machine-generated; declarations could drift without a dedicated surface report.

### B. Formalization gaps

1. `AsymptoticIsoStrongRoute`, `AsymptoticPromiseYesCertificateRoute`, and fixed-slice route aliases are source obligations, not proven source theorems.
2. Weak-route adapters require explicit bridge languages and NP witnesses; no audited theorem constructs the full source route unconditionally.
3. Pipeline-aware formula/real endpoints are not bridged to `PpolyDAG` in a non-refuted way.
4. There is no active construction of `ResearchGapWitness`.

### C. Mathematical gaps

1. A non-vacuous proof of `NP_not_subset_PpolyDAG` remains the central open gap.
2. A non-refuted MCSP/search magnification theorem producing DAG separation remains absent from this pnp3 final surface.
3. AC0/locality/support-cardinality routes cannot be used unless they avoid truth-table hardwiring and the already-refuted support-bounds predicates.
4. Any fixed-params/provenance route must be narrower than the overbroad uniform provenance shape, or it reconstructs the old false predicate.

### D. Governance gaps

1. Keep audit/refuted routes quarantined and named visibly. Existing quarantine is good, but compatibility imports still expose them.
2. Consider renaming or documenting `RefutedRoute_NP_not_subset_PpolyFormula_final_fromPipeline` / `_PpolyReal_final_fromPipeline`: comments call them non-ex-falso, but the names begin `RefutedRoute_`, which is confusing and should be an operator decision.
3. Public documentation should consistently say that `FinalResult` is complete only modulo `ResearchGapWitness`, not as a P-vs-NP proof.
4. pnp4 integration status should be documented in one place to prevent duplicate adapter work.

## 16. Recommended Phase 1+ tasks

### Task 1: pnp4-to-pnp3 final-boundary adapter design audit

- **Exact files to touch:** markdown only, e.g. `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/Axx_pnp4_pnp3_final_adapter_<handle>.md`.
- **Allowed scope:** Map `VerifiedNPDAGLowerBoundSource`, `SearchMCSPWeakLowerBound`, and pnp3 `ResearchGapWitness` compatibility at the interface level.
- **Forbidden scope:** No Lean edits; no construction of `ResearchGapWitness`; no endpoint promotion.
- **Expected output:** A design decision: whether adapter belongs in pnp3, pnp4, or a new bridge module, and exact theorem statement candidates.
- **Estimated time:** 1-2 days.
- **Dependency on other audits:** Should coordinate with any pnp4 frontier/bridge audits.
- **Risk level:** Medium.
- **Type:** markdown-only / operator decision.

### Task 2: Route-surface quarantine naming cleanup proposal

- **Exact files to touch:** markdown report first; possible later Lean task limited to `pnp3/Magnification/FinalResultAuditRoutes.lean` and tests if approved.
- **Allowed scope:** Identify wrappers taking `MagnificationAssumptions` that lack `RefutedRoute_` or clear audit naming; propose aliases/deprecations.
- **Forbidden scope:** No semantic theorem changes; no removal of compatibility names without operator approval.
- **Expected output:** Rename/alias plan that reduces accidental use of `MagnificationAssumptions` routes.
- **Estimated time:** 0.5-1 day for proposal; 1 day for later Lean cleanup.
- **Dependency on other audits:** A09 NoGoLog/provider quarantine audit would be helpful.
- **Risk level:** Low-to-medium because of import compatibility.
- **Type:** markdown-only first; later Lean if approved.

### Task 3: FinalResult generated declaration inventory/check

- **Exact files to touch:** `scripts/` and/or `pnp3/Tests/RouteSurfaceAudit.lean` only in a later implementation task.
- **Allowed scope:** Add a check that public final-result declarations containing `supportBounds`, `Vacuous`, `FinalPayloadProvider`, or `MagnificationAssumptions` stay quarantined/audit-named.
- **Forbidden scope:** No theorem changes; no source obligation changes.
- **Expected output:** CI guard or test that prevents new hidden final endpoints.
- **Estimated time:** 1-2 days.
- **Dependency on other audits:** Provider audit / Rule 16 audit.
- **Risk level:** Low.
- **Type:** Lean/script infrastructure.

### Task 4: AntiChecker-only route surface documentation

- **Exact files to touch:** markdown docs only, e.g. `pnp3/Docs/` or seed-pack report if approved.
- **Allowed scope:** Document the safe `_withAntiChecker` route family and when to use it instead of `MagnificationAssumptions` wrappers.
- **Forbidden scope:** No new theorems; no claims of P-vs-NP progress.
- **Expected output:** Short route map for future source-theorem workers.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** None.
- **Risk level:** Low.
- **Type:** markdown-only.

### Task 5: Weak-route source-obligation boundary audit

- **Exact files to touch:** markdown report; later tests only if approved.
- **Allowed scope:** Audit the upstream files imported by `FinalResultWeakRoutes.lean` to identify which weak-route hypotheses are merely Prop aliases and which have kernel proofs.
- **Forbidden scope:** No implementation of weak routes; no `ResearchGapWitness` construction.
- **Expected output:** A dependency graph from weak-route statement to `NP_not_subset_PpolyDAG_surface_of_*` endpoints.
- **Estimated time:** 2-4 days.
- **Dependency on other audits:** Could depend on lower-bound/source-closure audits.
- **Risk level:** Medium.
- **Type:** markdown-only.

### Task 6: Fixed-params provenance no-go consolidation

- **Exact files to touch:** markdown report; possible NoGoLog update only if separately authorized.
- **Allowed scope:** Consolidate the reason `FormulaSupportBoundsPartial_fromPipeline_fixedParams + OverbroadUniformFormulaProvenance` reconstructs the false old support-bounds predicate.
- **Forbidden scope:** No NoGoLog edits in this audit wave; no new Lean theorem unless later dispatched.
- **Expected output:** Operator-ready decision on whether planned fixed-params tasks should be cancelled, narrowed, or renamed.
- **Estimated time:** 1-2 days.
- **Dependency on other audits:** A09 NoGoLog audit and formula-support falsifiability audit.
- **Risk level:** Medium.
- **Type:** markdown-only / operator decision.

## 17. Stop / hold recommendations

- **Hold** any task that tries to prove P-vs-NP by providing `FormulaSupportRestrictionBoundsPartial`, `FormulaSupportBoundsFromMultiSwitchingContract`, or default support-bounds facts.
- **Hold or rename** any task described as “complete final result” if it only proves a wrapper to `P_ne_NP_final_dag_only` without a new source of `NP_not_subset_PpolyDAG`.
- **Downgrade** AC0[p], formula, local-PRG, support-cardinality, or locality-only tasks to side-track/infrastructure unless they explicitly bridge to `PpolyDAG` / `ResearchGapWitness` without refuted predicates.
- **Prefer** pnp4 mainline tasks targeting `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound` over additional pnp3 FinalResult wrappers.
- **Do not touch** trust-root files or support-bounds quarantine in a routine Phase 1 engineering task.

## 18. pnp4 integration

A direct search of `pnp4/**/*.lean` for `FinalResult`, `P_ne_NP_final`, `ResearchGapWitness`, and `NP_not_subset_PpolyDAG_final` returned no matches. Therefore, from this audit, pnp4 does not currently import or call the pnp3 FinalResult surface directly. The conceptual integration path is nevertheless clear:

```text
pnp4 future source
  VerifiedNPDAGLowerBoundSource or SearchMCSPWeakLowerBound
    -> pnp4 NP_not_subset_PpolyDAG / equivalent DAG lower-bound endpoint
      -> adapter to pnp3 ComplexityInterfaces.NP_not_subset_PpolyDAG or pnp3 ResearchGapWitness
        -> pnp3 UnconditionalResearchGap.P_ne_NP_final
```

This adapter should not be implemented casually because it crosses trust-root/interface boundaries. It should be a small, audited bridge task with explicit statement and tests.

## 19. What is safe to reuse / what should not be touched

Safe to reuse immediately:

- `P_ne_NP_final_dag_only` for any honest `NP_not_subset_PpolyDAG` proof.
- `ResearchGapWitness` and `P_ne_NP_final` as final public boundary.
- Anti-checker-only route wrappers in `FinalResultMainline.lean`.
- Weak-route wrappers as adapters, not as source theorems.
- Non-support-bounds legacy TM wrappers if their strong DAG-side hypotheses are genuinely produced.

Should not be touched in Phase 1 implementation unless operator explicitly approves:

- `pnp3/Complexity/Interfaces.lean`.
- `pnp3/Magnification/UnconditionalResearchGap.lean` except a future mathematically valid `ResearchGapWitness` PR.
- `VacuousFinalPayloadProvider` and default support-bounds provider plumbing.
- Refuted support-bounds predicates and their compatibility wrappers.
- Public endpoint names `NP_not_subset_PpolyDAG_final` and `P_ne_NP_final` except through the honest research-gap boundary.

## 20. Commands run

- `find .. -name AGENTS.md -print` — confirmed only repository-level `AGENTS.md` was present.
- `git switch -c khanukov/phase1-A02-auditor` — created the required audit branch.
- `wc -l pnp3/Magnification/FinalResult*.lean` — confirmed six-file scope totals 4,091 LOC.
- `rg -n "^(theorem|def|structure|class|abbrev|opaque|axiom|instance|noncomputable def)\b" pnp3/Magnification/FinalResult*.lean` — declaration inventory.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" <six-file-scope>` — 229 matches, mostly DAG endpoints and documentation; no `VerifiedNPDAGLowerBoundSource` / `SearchMCSPMagnificationContract` / `SourceTheorem` / `gap_from` hits in the six files.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" <six-file-scope>` — 191 matches, concentrated in audit/refuted support-bounds/provider route surfaces and comments.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" <six-file-scope>` — 39 matches; no `opaque`, `default_instance`, or `attribute [instance]` found in audited scope.
- `rg -n "FinalResult|P_ne_NP_final|ResearchGapWitness|NP_not_subset_PpolyDAG_final" pnp4 --glob '*.lean'` — no direct pnp4 matches.
- `./scripts/check.sh` — run from repository root; status recorded in final response.

## 21. Scope violations

None. This audit added exactly one markdown report and did not edit Lean, source, JSONL, output, spec, trust-root, endpoint, or NoGoLog files.

## 22. Honest caveats

- I did not reconstruct every proof body in `FinalResultMainline.lean` and `FinalResultWeakRoutes.lean`; I audited signatures, comments, and key adapter bodies relevant to final-route trust.
- I did not inspect every upstream imported lower-bound file, so this report classifies imported route hypotheses by their names/signatures and local documentation, not by full dependency closure.
- I did not run `#print axioms` manually for each theorem; I relied on existing audit surfaces plus `./scripts/check.sh`.
- I did not inspect `outputs/nogolog.jsonl` or the optional strategic retrospective in depth.
- The pnp4 integration conclusion is based on text search for final-route names, not a full import graph reconstruction.
- Some comments in the repository say pipeline-aware formula endpoints are “genuinely derived” while names still start with `RefutedRoute_`; this audit treats that as governance/naming ambiguity, not as a mathematical validation.
