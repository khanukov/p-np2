# Handoff: Structured Locality Provider (updated)

This document supersedes the older handoff that targeted
`LanguageLocalityPartial` (global junta form). The active pipeline now uses a
restriction-style provider witness.

## Current provider target

File: `pnp3/Magnification/Facts_Magnification_Partial.lean`

`StructuredLocalityProviderPartial` now requires:

- input: `PpolyFormula (gapPartialMCSP_Language p)`
- output: `RestrictionLocalityPartial p`

where `RestrictionLocalityPartial p` packages:

- a test set `T`,
- a local solver `SmallLocalCircuitSolver_Partial p`,
- polylog bounds on `T.card` and locality parameter `ℓ`.

The partial locality bridge now also exposes certificate-driven plumbing:

- `stableRestriction_of_certificate`
- `locality_lift_partial_of_certificate`

with explicit hypothesis `hCardHalf` for the certificate restriction.

## Why this changed

The old target (`LanguageLocalityPartial`) encoded a global junta property for
the whole language and is not the active proof surface anymore. The current
pipeline consumes local solver witnesses directly.

## Required deliverable

Provide a constructive theorem:

`provider_constructive : StructuredLocalityProviderPartial`

with no new axioms, using the strict structured class `PpolyFormula`.

In the current code state, the concrete blocker is explicit:

- discharge `hCardHalf` constructively in the intended provider path
  (`restriction.alive.card ≤ Partial.tableLen p.n / 2`).

## Integration points

- `OPS_trigger_formulas_partial_of_provider`
- `NP_not_subset_PpolyFormula_from_partial_formulas_with_formulaizer`
- `NP_not_subset_PpolyFormula_final_with_formulaizer`

All are already in place; replacing the provider hypothesis is a drop-in step.

## Adjacent constructive goal

In parallel, close the localized embed gap via:

`GapPartialMCSPFormulaizer p`

from `pnp3/ThirdPartyFacts/PpolyFormula.lean`.
