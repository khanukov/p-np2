# Handoff: Structured Locality Provider (current)

Updated: 2026-02-22

## Current target

File: `pnp3/Magnification/LocalityProvider_Partial.lean`

Active proof surface uses `StructuredLocalityProviderPartial` with
`RestrictionLocalityPartial p` outputs.

## What is already wired

- Formula extraction route: `generalSolverOfFormula`.
- Certificate-driven stability route: `stableRestriction_of_certificate`.
- Auto cardinality discharge in main route:
  `HalfTableCertificateBound` + `locality_lift_partial_of_certificate_auto`.
- Engine-to-provider bridge:
  `constructiveLocalityEnginePartial_of_formulaCertificate` and
  `structuredLocalityProviderPartial_of_engine`.

## What is still missing

- Real certificate providers for target formula-extracted solver families
  (`FormulaCertificateProviderPartial` instances/default availability).

This is the practical remaining I-2/I-4 handoff boundary.

## Non-goal clarification

`FormulaHalfSizeBoundPartial` remains available as an alternative route,
but it is no longer required for the certificate-first main plumbing.
