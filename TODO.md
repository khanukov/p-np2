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

## Open blockers

1. I-2 (primary)
- Internalize default structured locality provider availability from existing
  constructive artifacts (including AC0 Path-A I-4 bridge), without extra
  external provider assumptions.

2. I-5 (research-level)
- Close bridge `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`
  or keep `P != NP` explicitly conditional.
- New active subtrack: depth-aware bridge contract
  `NP_not_subset_PpolyFormulaDepth d -> NP_not_subset_Ppoly`
  with explicit lift
  `NP_not_subset_PpolyFormula -> NP_not_subset_PpolyFormulaDepth d`
  to keep the bridge aligned with AC0-style bounded depth.

3. Optional broader bridges (separate layer)
- Any non-AC0 front (e.g., stronger Ppoly-side bridge assumptions) should stay
  explicitly separated from the AC0-closed I-4 core.

4. Step-C legacy cleanup (status)
- Step-C partial route is now internalized and machine-checked through
  solver-local payloads (`circuit`, `decide_eq`, `easyData`) plus
  `stepCSyntacticLiftDataPartial_default`.
- Legacy hypothesis-bridge wrappers (`..._of_hypotheses`,
  all-functions-based helper wrappers) were removed from active
  `AntiChecker_Partial` / core / pipeline APIs.
- Remaining Step-C work is optional refactoring/documentation hygiene,
  not proof-blocking for the internalized constructive route.

## Execution order

1. Wire existing constructive artifacts into default provider path (I-2).
2. Maintain explicit conditional labeling for `P != NP` until I-5 is solved.
3. Keep optional stronger bridges in separate, clearly-labeled modules.

## Definition of done per open item

### I-4 (closed scope note)

- I-4 is considered closed for explicit AC0/CNF inputs (Path A).
- Reference module: `pnp3/Magnification/AC0LocalityBridge.lean`.
- General `PpolyFormula -> AC0` conversion is intentionally out of scope.

### I-2 DoD

- `hasDefaultStructuredLocalityProviderPartial` obtained from internal
  certificate providers in the default route.

### I-5 DoD

- Either:
  - internal proof of `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`, or
  - project-wide docs/status remain explicitly scoped to formula-track
    separation and conditional `P != NP` wrappers.

## CI requirements

- Keep `./scripts/check.sh` in required CI.
- Keep nightly `UNCONDITIONAL=1 ./scripts/check.sh` as progress metric.
