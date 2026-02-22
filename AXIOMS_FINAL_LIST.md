# Complete Axiom Inventory - PNP3
## Official list for current `pnp3/` tree

**Revision Date**: 2026-02-22
**Total Active Axioms (`pnp3/`)**: 0

## Executive summary

The active `pnp3/` tree contains no global `axiom` declarations.
Remaining dependencies are explicit hypotheses/providers, not axioms.

| Category | File(s) | Active axioms | Status |
|---|---|---:|---|
| Switching/shrinkage layer | `pnp3/ThirdPartyFacts/Facts_Switching.lean` | 0 | witness/provider backed |
| Localized strict bridge | `pnp3/ThirdPartyFacts/PpolyFormula.lean` | 0 | internalized (`trivialFormulaizer`) |
| Partial locality-lift bridge | `pnp3/ThirdPartyFacts/PartialLocalityLift.lean` | 0 | certificate auto-cardinality path present |

## External inputs still required (non-axiomatic)

1. Real multi-switching/shrinkage witness/provider instances for target
   solver families.
2. Formula-certificate provider availability for default constructive locality
   provider wiring (`FormulaCertificateProviderPartial`).
3. Formula-to-`P/poly` bridge used by `P != NP` wrappers:
   `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.

## Scope note

This document tracks only global axioms. It does not claim unconditional
`P != NP`.
