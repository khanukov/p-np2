# Project Status (current)

Updated: 2026-03-16

Authoritative checklist: `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release positioning for current tree: `RELEASE_RC.md`.

## Current verified state

- Active `axiom` declarations in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- `./scripts/check.sh` passes (rechecked on 2026-03-16)
- Current audit/regression tests pass (rechecked on 2026-03-16):
  `AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
  `BridgeLocalityRegression`

## Current frontier (2026-03-16)

- The current singleton `β`-route is no longer an open plumbing problem.
  It has been reduced to a decision layer:
  `CurrentSingletonRouteWitnessProp` plus the nat-crossmul comparison wrapper.
- This route is currently nongeneric: without a family-specific comparison
  theorem controlling `sYES`, the repository neither proves nor refutes a
  chosen selector witness from the current singleton theorem layer.
- Atlas/Rf compatibility is now promoted from scratch to named API:
  `pnp3/Magnification/AC0AtlasBridge.lean` exposes bridges from
  `SemanticSwitchingCertificatePartial` to
  `BoundedAtlasScenario` and `ScenarioBudget`.
- Two false downstream routes are now formally ruled out:
  `ScenarioBudget -> strict large-family gap` and
  `ApproxClass -> small mismatch`.
- The recommended active contradiction route is now the family-level package
  `SemanticSwitchingApproxFamilyPackagePartial` / provider
  `SemanticSwitchingApproxFamilyProviderPartial` in
  `pnp3/Magnification/AC0ApproxFamilyBridge.lean`.
- This route targets the existing counting contradiction
  `Counting.incompatibility` directly, instead of trying to re-enter the old
  `AntiChecker_Partial` large-family-gap endpoint.
- The older provenance-aware singleton package
  `SemanticSwitchingSmallMismatchPackagePartial` remains as a stronger-source
  side branch: it would recover linked polylog-small testsets, but it is no
  longer the primary contradiction route.
- The remaining source-side mathematical question is now:
  can semantic switching produce one large finite family `Y` lying in a common
  `ApproxClass`, with `Y.card` above the counting capacity bound?

## Active final theorem surface

File: `pnp3/Magnification/FinalResult.lean`

- `NP_not_subset_PpolyFormula_final*`
- `NP_not_subset_PpolyReal_final*`
- `P_ne_NP_final*`
- asymptotic NP bridge helpers:
  `AsymptoticNPPullback`

Formula-route progress note (2026-03-15):

- Active formula final wiring now consumes asymptotic NP witness directly:
  `NP_not_subset_PpolyFormula_final_with_provider` is routed through
  `strictAsymptotic` + `asymptotic_formula_collapse`.
- `AsymptoticFormulaTrackHypothesis` now carries explicit `sliceEq`, and
  `asymptotic_formula_collapse` consumes it from the hypothesis package.
- Fixed-slice witnesses remain as auxiliary support (`strictFixed`) for
  helper/localized routes (not as the primary formula-final endpoint input).
- `MagnificationAssumptions.switching` now carries
  `FormulaSupportBoundsFromMultiSwitchingContract` (strengthened A9 boundary),
  and active formula/real finals derive support-bounds and provider internally
  via `formula_support_bounds_from_multiswitching` and
  `structuredLocalityProviderPartial_of_supportBounds`.
- Exact singleton `epsilon`, raw YES-density bounds, and the current singleton
  empty-witness decision layer are now formalized in-repo.
- Source semantic certificates now compose directly with atlas/downstream
  scenario objects through `Magnification.AC0AtlasBridge`.
- The direct family-level `ApproxClass` route is now explicit in
  `Magnification.AC0ApproxFamilyBridge`, with a contradiction theorem that
  reuses the existing counting endpoint.
- The singleton small-mismatch frontier remains formalized as a stronger-source
  side branch, with a thin bridge to linked polylog-small testsets.

## Interpretation

- The repository currently formalizes a constructive, axiom-clean,
  AC0/formula pipeline plus conditional DAG final wrappers.
- Recent work has mainly eliminated false routes and localized the remaining
  mathematical barriers; it has not yet discharged the DAG-side blocker below.
- Final `P ≠ NP` wrappers are conditional.
- The project does not currently contain an unconditional in-repo theorem
  `P ≠ NP`.

## Remaining blockers to unconditional status

Active DAG final wrapper `P_ne_NP_final` requires one external input:

1. `NP_not_subset_PpolyDAG` (`hNPDag`)

Current inclusion-side status:

- No-arg linear output-wire witness is closed:
  `compiledAcceptOutputWireAgreementLinear_internal`.
- No-arg inclusion endpoint is closed:
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- `RuntimeConfigEqStepCompiled` remains open only for legacy bridge routes
  (`runtimeConfig` path with `step = id`), not for the active no-arg linear
  closure.

## Contract hardening updates

- A9 interface hardening is closed:
  `FormulaSupportBoundsFromMultiSwitchingContract` now includes an explicit
  semantic linkage field from AC0-family payload to the extracted strict formula.
- The vacuous empty-family constructor for this contract was removed from
  `Magnification/LocalityProvider_Partial.lean`.
- The active locality bridge now exposes a combined theorem
  `formula_support_bounds_and_semantic_link_from_multiswitching`, so the
  semantic linkage is preserved at the API level (alongside numeric bounds).
- Added split constructor
  `multiswitching_contract_of_semantic_provider_and_support_bounds`:
  full A9 contract is now assembled from
  `FormulaSemanticMultiSwitchingProvider` + `FormulaSupportRestrictionBoundsPartial`.
- Added internal constructive provider
  `AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal` and
  internalized constructor
  `multiswitching_contract_internalized_of_support_bounds`, so semantic
  AC0/multi-switching linkage is now in-repo constructive (no external semantic
  provider input needed for contract assembly).

## Canonical CCDT bridge updates

- A8 closure is now integrated in `ThirdPartyFacts/Facts_Switching.lean`.
- Added constructive leaf-partition machinery for canonical CNF DT/CCDT:
  `LeafPartitionWithin`,
  `canonicalDT_CNF_aux_leaf_of_compatible`,
  `canonicalDT_CNF_aux_leaf_unique_of_compatible`,
  `canonicalCCDT_CNF_aux_leafPartition_free`.
- Removed external `LeafPartition` hypothesis from
  `shrinkage_negDnfFamily_to_dnf_canonicalCCDT`; canonical partition is now
  derived internally from `canonicalCCDT_CNF_aux`.

## Documentation policy

Any file claiming unconditional `P ≠ NP` before these blockers are discharged
is incorrect and must be treated as outdated.
