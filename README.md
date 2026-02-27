# P!=NP formalization repository

Status date: 2026-02-27

Canonical blocker checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## Current state

- `pnp3/` builds and has 0 active `axiom`, 0 active `sorry/admit`.
- Active final entrypoints are in `pnp3/Magnification/FinalResult.lean`.
- Final `P ≠ NP` wrappers are conditional, not unconditional.

## Current final API

- `NP_not_subset_PpolyFormula_final_with_provider`
- `NP_not_subset_PpolyFormula_final`
- `NP_not_subset_PpolyFormula_final_of_formulaCertificate`
- `P_ne_NP_final_with_provider`
- `P_ne_NP_final`
- `P_ne_NP_final_of_formulaCertificate`

## Unconditional status

The repository does **not** currently prove unconditional `P ≠ NP`.
The exact blockers are the four assumptions of `P_ne_NP_final`; see
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## Primary docs

- `STATUS.md` (authoritative snapshot)
- `TODO.md` (execution order)
- `AXIOMS_FINAL_LIST.md` (axiom inventory)
- `FAQ.md` (reviewer-facing clarifications)
- `PROOF_OVERVIEW.md` (auditor proof map across modules/theorems)

## Build

```bash
lake build
lake test
./scripts/check.sh
```
