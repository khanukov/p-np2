# TODO / Roadmap (current)

Updated: 2026-02-26

This roadmap reflects the **actual** current code state.

## Snapshot

- Active `axiom` in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- Active strategic target: AC0-focused separation route
- Active semantic final hooks available:
  - `NP_not_subset_PpolyFormula_from_params_semantic`
  - `NP_not_subset_PpolyFormula_from_params_semantic_of_syntacticEasy`
  - `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic`
  - `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic_of_syntacticEasy`
  - `NP_not_subset_PpolyFormula_final`
- TM-witness bridge available: `strictGapNPFamily_of_tmWitnesses`
- `P != NP` wrappers remain conditional on `hFormulaToPpoly`

## Completed

1. I-1 closed
- Localized `PpolyReal -> PpolyFormula` path internalized via
  `trivialFormulaizer` / `gapPartialMCSP_realization_trivial`.

2. I-3 closed at certificate-contract level
- Certificate route supports automatic half-cardinality export via
  `HalfTableCertificateBound`.
- Main certificate locality-lift path has auto wrapper;
  no manual `hCardHalf` threading in the main route.

3. I-2 closed (constructive wiring, contract-scoped)
- End-to-end route is wired through:
  - `hasDefaultStructuredLocalityProviderPartial_of_multiswitching_contract`
  - `NP_not_subset_PpolyFormula_final_of_multiswitching_contract`
  - `P_ne_NP_final_of_multiswitching_contract`
- Compile-time regression checks are present in
  `pnp3/Tests/BridgeLocalityRegression.lean`.
- Scope note: this is not an unconditional closure, because the route requires
  `AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract`.

## Open blockers

1. I-5 (research-level)
- Close bridge `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`
  or keep `P != NP` explicitly conditional.
- New active subtrack: depth-aware bridge contract
  `NP_not_subset_PpolyFormulaDepth d -> NP_not_subset_Ppoly`
  with explicit lift
  `NP_not_subset_PpolyFormula -> NP_not_subset_PpolyFormulaDepth d`
  to keep the bridge aligned with AC0-style bounded depth.

2. Optional broader bridges (separate layer)
- Any non-AC0 front (e.g., stronger Ppoly-side bridge assumptions) should stay
  explicitly separated from the AC0-closed I-4 core.

3. Step-C semantics migration (new, immediate)
- New semantic API exists (`*_semantic`) with solver-local witnesses.
- Progress done:
  - active bridge entrypoints no longer auto-build Step-C from
    `allFunctionsFamily`; they require explicit lower-bound hypotheses;
  - legacy `allFunctions/default_multiSwitching` public final entrypoints were
    removed from `FinalResult.lean`;
  - semantic provider/bridge/final wrappers added (`*_semantic`) to run
    non-vacuous Step-C assumptions through OPS to formula separation.
- Remaining work:
  - migrate default multi-switching constructors to solver-local semantic
    witnesses end-to-end;
  - connect semantic Step-C to constructive multi-switching providers
    in family-level easy-data form (instead of all-functions form).
  - instantiate `AC0EasyFamilyDataPartial` with a mathematically justified
    `AC0EasyFamily` (not just wrappers), including a proved cardinal lower
    premise actually used by the counting contradiction.

## Execution order

1. Maintain explicit conditional labeling for `P != NP` until I-5 is solved.
2. Keep optional stronger bridges in separate, clearly-labeled modules.
3. Continue semantic Step-C migration to remove legacy compatibility surface.

## Definition of done per open item

### I-4 (closed scope note)

- I-4 is considered closed for explicit AC0/CNF inputs (Path A).
- Reference module: `pnp3/Magnification/AC0LocalityBridge.lean`.
- General `PpolyFormula -> AC0` conversion is intentionally out of scope.

### I-5 DoD

- Either:
  - internal proof of `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`, or
  - project-wide docs/status remain explicitly scoped to formula-track
    separation and conditional `P != NP` wrappers.

## CI requirements

- Keep `./scripts/check.sh` in required CI.
- Keep nightly `UNCONDITIONAL=1 ./scripts/check.sh` as progress metric.
