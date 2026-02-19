# Roadmap

Last updated: 2026-02-19

## Goal hierarchy
1. Keep the active cone mechanically stable and auditable.
2. Remove project-specific external scaffolding from the final theorem cone.
3. Improve constructive content where it affects maintainability and reproducibility.

## Completed
- Partial-MCSP active pipeline assembled end-to-end (`pnp3/`).
- Anti-checker partial cone refactored to constructive large-`Y` certificate flow.
- Critical anti-checker partial files guarded against `False.elim` regressions.
- Automated axiom dependency audits integrated in `scripts/check.sh`.
- Documentation index centralized in `docs/`.

## In progress / next (priority order)

### P0: Remove final-cone axiom
- Replace `localizedFamilyWitness_partial` with an internal theorem/derivation.
- Target file currently importing scaffold:
  - `pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`
- Target consumers:
  - `pnp3/Magnification/FinalResult.lean`
  - `pnp3/LowerBounds/LB_GeneralFromLocal_Partial.lean`

Acceptance:
- `rg "^axiom " pnp3` returns zero project-specific axioms.
- `P_ne_NP_final` depends only on Lean base axioms expected by the project.

### P1: Internalize witness production path
- Construct/internalize required witness flow for:
  - `FamilyIsAC0`
  - `FamilyIsLocalCircuit`
- Remove reliance on ad hoc external witness packaging where feasible.

Acceptance:
- Reduced witness hypotheses on key theorems in A/B/C bridge.
- Updated axiom audit remains stable.

### P2: Strengthen constructive artifacts in Part C
- Extend large-`Y` certificate to optional testset certificate (`T`, `ApproxOnTestset`, testset capacity bound) if needed by downstream consumers.

Acceptance:
- Clear certificate type and theorem API with no fake existence claims.

## Ongoing hygiene rules
- No new duplicate root-level status/planning docs.
- Any proof-status update must be reflected in:
  - `docs/CurrentState.md`
  - `docs/Publication.md`
  - `scripts/check.sh` (if it affects machine-checkable contracts)

## Deep technical workstreams
For detailed switching/multi-switching tasks and parameter-level notes, use module-local docs under `pnp3/Docs/`.
