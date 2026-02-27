# P vs NP: Lean Formalization (Honest Status)

Status date: 2026-02-27.

Canonical checklist for unconditional readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## What This Project Is

This repository contains a machine-checked (Lean 4) formalization of a route of
the form:

`SAL -> Covering/Lower Bounds -> anti-checker -> magnification -> final wrapper theorems`.

The goal of the active `pnp3/` branch is not narrative claims, but a stable,
auditable contract: which parts are already constructively formalized and which
parts still remain explicit external assumptions.

## Current State (No Overstatement)

- `pnp3/` builds; `./scripts/check.sh` passes.
- Active `axiom` declarations in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- Final entrypoints are in `pnp3/Magnification/FinalResult.lean`.
- Final `P ≠ NP` wrappers are **conditional**.

Bottom line today: there is no unconditional in-repo theorem `P ≠ NP`.

## Final API (Active Surface)

- `NP_not_subset_PpolyFormula_final_with_provider`
- `NP_not_subset_PpolyFormula_final`
- `NP_not_subset_PpolyFormula_final_of_formulaCertificate`
- `P_ne_NP_final_with_provider`
- `P_ne_NP_final`
- `P_ne_NP_final_of_formulaCertificate`

## Main Solution Route in Current Code

1. Model/NP side (witness objects and problem linkage): `pnp3/Models/Model_PartialMCSP.lean`.
2. Lower-bound and anti-checker layer (partially parameterized route):
   `pnp3/LowerBounds/AntiChecker_Partial.lean`,
   `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean`.
3. Bridge into the magnification interface:
   `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`,
   `pnp3/Magnification/LocalityProvider_Partial.lean`.
4. Final theorems and assumption boundary:
   `pnp3/Magnification/FinalResult.lean`.

## What Remains Open

`P_ne_NP_final` still depends on 4 external hypotheses:

1. `hasDefaultStructuredLocalityProviderPartial`
2. `AsymptoticFormulaTrackHypothesis`
3. `StrictGapNPFamily`
4. `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`

Until these 4 items are internalized in-repo, any `P ≠ NP` statement here is
necessarily conditional.

## Core Difficulty

- It is not enough to obtain a formula-track separation; the transition to full
  non-uniform separation (`P/poly`) must also be closed without an ad hoc jump.
- The route must stay constructive while preserving formal hygiene
  (no active `axiom`, `sorry`, `admit` in the active branch).
- In practice, the bottleneck is the final bridge assumptions, not build
  infrastructure.

## What Is Scientifically/Technically New Here (At Current State)

Without overclaiming, the practical contribution is:

- a coherent machine-checked pipeline up to final wrapper theorems;
- remaining open obligations isolated into an explicit minimal 4-hypothesis contract;
- active branch cleaned to 0 active `axiom` and 0 active `sorry/admit`;
- a constructive helper transition `strictGapNPFamily_of_tmWitnesses`, reducing
  implicit gaps between model-side witnesses and final wrappers.

This is not an unconditional proof of `P ≠ NP`, but it narrows uncertainty in a
useful way by making the remaining obligations explicit.

## How To Verify State

```bash
lake build
lake test
./scripts/check.sh
```

## Primary Documents

- `STATUS.md` - authoritative current snapshot.
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` - canonical blocker checklist.
- `TODO.md` - execution order for remaining closure tasks.
- `PROOF_OVERVIEW.md` - active proof-route map for auditors.
- `FAQ.md` - short reviewer-facing clarifications.
- `AXIOMS_FINAL_LIST.md` - axiom/sorry hygiene inventory only.

## Wording Policy

Until the checklist is fully closed, any `P ≠ NP` statement in this repository
must explicitly indicate that final theorems are conditional.
