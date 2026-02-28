# TODO / Roadmap (current)

Updated: 2026-02-27

Canonical blocker checklist lives in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## Snapshot

- Active `axiom` in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- Build baseline: `./scripts/check.sh` passes
- Final API is conditional (`pnp3/Magnification/FinalResult.lean`)

## What is already closed

1. AC0-route formula separation wiring is present and compiles.
2. TM-witness bridge helper exists: `strictGapNPFamily_of_tmWitnesses`.
3. Axiom/sorry hygiene for active `pnp3/` tree is clean.

## What still blocks unconditional `P ≠ NP`

Track these four items on the active constructive final route
`P_ne_NP_final_of_default_supportBounds`:

1. `hasDefaultFormulaSupportRestrictionBoundsPartial`
2. `AsymptoticFormulaTrackHypothesis`
3. `StrictGapNPFamily`
4. `hPsubsetReal`:
   `P_subset_PpolyReal`

Explicit constructive route `P_ne_NP_final_of_supportBounds` is also available.

## Execution order

1. Keep docs honest: no unconditional claim while the four blockers remain.
2. Continue removing dead branches only if final API + tests still pass.
3. Prioritize internalizing item (1) and item (4), then eliminate remaining
   asymptotic/NP-family assumptions.

## Done criteria

1. Final theorem route no longer needs external bridge/provider assumptions.
2. `./scripts/check.sh` and axiom audit pass unchanged.
3. Top-level docs report unconditional status consistently.
