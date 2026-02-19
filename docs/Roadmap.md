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

### P0: Keep zero-axiom status in active cone
- Preserve `rg "^axiom " pnp3` = 0 as a hard gate.
- Keep `P_ne_NP_final_asymptotic` dependencies at
  `[propext, Classical.choice, Quot.sound]`.
- Prevent reintroduction of scaffold files for localized witness.

### P1: Internalize witness production path (remove conditional hypotheses)
- Construct/internalize required witness flow for:
  - `FamilyIsLocalCircuit`
- Reduce or eliminate explicit `MagnificationAssumptions` hypotheses by replacing
  them with derived internal theorems where possible.
- Remove reliance on ad hoc external witness packaging where feasible.

Acceptance:
- Reduced witness hypotheses on key theorems in B/C/D bridge.
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
