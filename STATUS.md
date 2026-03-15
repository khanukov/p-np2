# Project Status (current)

Updated: 2026-03-14

Authoritative checklist: `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release positioning for current tree: `RELEASE_RC.md`.

## Current verified state

- Active `axiom` declarations in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- `./scripts/check.sh` passes (rechecked on 2026-03-14)
- Current audit/regression tests pass (rechecked on 2026-03-14):
  `AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
  `BridgeLocalityRegression`

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

## Interpretation

- The repository currently formalizes a constructive, axiom-clean,
  AC0/formula pipeline plus conditional DAG final wrappers.
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
