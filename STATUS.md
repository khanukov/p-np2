# Project Status (current)

Updated: 2026-03-04

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
- `NP_not_subset_PpolyReal_final_with_provider`
- `NP_not_subset_PpolyReal_final`
- `NP_not_subset_PpolyReal_final_of_formulaCertificate`
- `NP_not_subset_PpolyReal_final_of_multiswitching_contract`
- `NP_not_subset_PpolyReal_final_constructive`
- `NP_not_subset_PpolyReal_final_of_supportBounds`
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

Active DAG final wrapper `P_ne_NP_final` requires two external inputs:

1. `NP_not_subset_PpolyDAG` (`hNPDag`)
2. `PsubsetPpolyInternalContractsIteratedCanonical` (`hPpolyContracts`)

Constructive compatibility wrapper `P_ne_NP_final_of_default_supportBounds`
keeps `hasDefaultFormulaSupportRestrictionBoundsPartial` in its signature,
but the DAG-final contradiction still depends on the same two inputs above.

Interpretation of current blocker surface:

1. AC0/formula-side separation is not yet internally connected to
   `NP_not_subset_PpolyDAG`.
2. Inclusion side `P ⊆ PpolyDAG` is available through explicit contract bundles,
   but not yet as a no-input closed theorem on the active final route.

## Documentation policy

Any file claiming unconditional `P ≠ NP` before these blockers are discharged
is incorrect and must be treated as outdated.
