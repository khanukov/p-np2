# TODO / Roadmap (current)

Updated: 2026-02-22

This roadmap reflects the **actual** current code state.

## Snapshot

- Active `axiom` in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- Active final target: conditional `NP_not_subset_PpolyFormula`
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

1. I-4 (primary)
- Build real multi-switching/shrinkage instances for target solver families.
- Deliver concrete provider-grade artifacts consumed by:
  - `AC0MultiSwitchingWitnessProvider` paths,
  - `FormulaCertificateProviderPartial` paths.

2. I-2 (depends on I-4)
- Internalize default structured locality provider availability from real
  certificate providers, not from external assumptions.

3. I-5 (research-level)
- Close bridge `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`
  or keep `P != NP` explicitly conditional.

## Execution order

1. Finish I-4 artifacts for concrete families and parameters.
2. Wire those artifacts into default constructive provider path (I-2).
3. Maintain explicit conditional labeling for `P != NP` until I-5 is solved.

## Definition of done per open item

### I-4 DoD

- At least one nontrivial target-family instance is internalized and consumed by
  provider-level theorems (not only interface wrappers).
- End-to-end constructive formula-track theorem compiles from these instances
  without introducing new external assumptions.

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
