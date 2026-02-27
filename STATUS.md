# Project Status (current)

Updated: 2026-02-27

Authoritative checklist: `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## Current verified state

- Active `axiom` declarations in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- `lake build` / `./scripts/check.sh` pass on current tree

## Active final theorem surface

File: `pnp3/Magnification/FinalResult.lean`

- `StrictGapNPFamily`
- `strictGapNPFamily_of_tmWitnesses`
- `AsymptoticFormulaTrackHypothesis`
- `NP_not_subset_PpolyFormula_final_with_provider`
- `NP_not_subset_PpolyFormula_final`
- `NP_not_subset_PpolyFormula_final_of_formulaCertificate`
- `NP_not_subset_PpolyFormula_final_of_multiswitching_contract`
- `NP_not_subset_PpolyFormula_final_constructive`
- `NP_not_subset_PpolyFormula_final_of_supportBounds`
- `P_ne_NP_final_with_provider`
- `P_ne_NP_final`
- `P_ne_NP_final_of_formulaCertificate`
- `P_ne_NP_final_of_multiswitching_contract`
- `P_ne_NP_final_constructive`
- `P_ne_NP_final_of_supportBounds`

## Interpretation

- The repository currently formalizes a constructive, axiom-clean,
  AC0-route formula-separation pipeline.
- Final `P ≠ NP` wrappers are conditional.
- The project does **not** currently contain an unconditional in-repo theorem
  `P ≠ NP`.

## Remaining blockers to unconditional status

Legacy wrapper `P_ne_NP_final` still has four external assumptions:

1. `hasDefaultStructuredLocalityProviderPartial`
2. `AsymptoticFormulaTrackHypothesis`
3. `StrictGapNPFamily`
4. `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`

Active constructive route (`P_ne_NP_final_of_default_supportBounds`) removes
the default-provider blocker. Remaining assumptions on this route:

1. `hasDefaultFormulaSupportRestrictionBoundsPartial`
2. `AsymptoticFormulaTrackHypothesis`
3. `StrictGapNPFamily`
4. `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`

Also available: explicit variant `P_ne_NP_final_of_supportBounds` with direct
`FormulaSupportRestrictionBoundsPartial`.

## Documentation policy

Any file claiming unconditional `P ≠ NP` before these four items are discharged
is incorrect and must be treated as outdated.
