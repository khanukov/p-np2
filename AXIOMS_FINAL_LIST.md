# Complete Axiom Inventory - PNP3
## Official list for current `pnp3/` tree

**Revision Date**: 2026-02-23
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

1. Default-provider packaging for wrapper-level entrypoints
   (`hasDefaultStructuredLocalityProviderPartial`) remains explicit.
2. Formula-to-`P/poly` bridge used by `P != NP` wrappers:
   `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.
3. Optional broader non-AC0 bridges, if desired, as separate explicit layers.

## Scope note

This document tracks only global axioms. It does not claim unconditional
`P != NP`.

I-4 note:
- Constructive I-4 core is closed on explicit AC0/CNF inputs (Path A);
  this is not a claim about a general `PpolyFormula -> AC0` conversion.

AC0 final-hook note:
- `pnp3/Magnification/FinalResult.lean` includes AC0-focused final hooks
  (`NP_not_subset_AC0_final*`) and fixed-parameter strict hooks
  (`NP_not_subset_AC0_at_param*`).
