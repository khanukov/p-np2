# Frequently Asked Questions

Updated: 2026-02-27

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## What is currently proved in code?

The active final surface is in `pnp3/Magnification/FinalResult.lean`:

- `NP_not_subset_PpolyFormula_final_with_provider`
- `NP_not_subset_PpolyFormula_final`
- `NP_not_subset_PpolyFormula_final_of_formulaCertificate`
- `NP_not_subset_PpolyFormula_final_of_default_supportBounds`
- `P_ne_NP_final_with_provider`
- `P_ne_NP_final`
- `P_ne_NP_final_of_formulaCertificate`
- `P_ne_NP_final_of_default_supportBounds`

These are machine-checked and compile on current tree.

## Is unconditional `P ≠ NP` proved here?

No. Current `P_ne_NP_final` is conditional.

## Conditional on what exactly?

Legacy `P_ne_NP_final` still requires four assumptions:

1. `hasDefaultStructuredLocalityProviderPartial`
2. `AsymptoticFormulaTrackHypothesis`
3. `StrictGapNPFamily`
4. `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`

Active constructive endpoint `P_ne_NP_final_of_default_supportBounds` replaces
item (1) with `hasDefaultFormulaSupportRestrictionBoundsPartial`.

## Why is `P_ne_NP_final` still meaningful for auditors?

It is a clean contract boundary:

- the AC0/formula-track route is explicit and type-checked;
- all remaining non-closed parts are isolated as named assumptions;
- removal of obsolete branches reduced ambiguity of which route is active.

## What is the constructive path auditors should trace first?

1. `pnp3/Models/Model_PartialMCSP.lean`:
   TM witness objects and NP-membership bridge.
2. `pnp3/Magnification/LocalityProvider_Partial.lean`:
   provider/certificate wiring.
3. `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`:
   bridge from lower-bound statements to separation interface.
4. `pnp3/Magnification/FinalResult.lean`:
   final theorem wrappers and assumption boundary.

## Where are anti-checker and lower-bound cores?

- `pnp3/LowerBounds/AntiChecker_Partial.lean`
- `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean`
- `pnp3/Magnification/PipelineStatements_Partial.lean`

## Is axiom/sorry hygiene clean?

Yes for active `pnp3/`:

- active global `axiom`: 0
- active `sorry/admit`: 0

Use:

```bash
./scripts/check.sh
```

## What changed in the recent cleanup?

- Removed dead theorem wrappers and compatibility aliases that were no longer
  referenced by active final route.
- Kept active final API stable.
- Kept build and audit checks passing.

## How do we verify nothing important was deleted?

Use this safety sequence:

1. Build/audit: `./scripts/check.sh`.
2. Confirm final API symbols in `FinalResult.lean`.
3. Confirm blockers in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` still match final
   theorem signatures.
4. Confirm no document claims unconditional status.

## Where is a longer narrative proof map?

See `PROOF_OVERVIEW.md`.
