# Technical Claims and Scope

## Verified contribution scope

The repository contributes a Lean-verified combinatorial pipeline around SAL and
capacity-style lower-bound infrastructure, plus machine-checked bridge plumbing
into anti-checker/magnification interfaces.

## Current claim level (2026-02-23)

- Active machine-checked strategic target: AC0-focused separation route.
- Final AC0 hooks are present in `pnp3/Magnification/FinalResult.lean`:
  `NP_not_subset_AC0_final`,
  `NP_not_subset_AC0_final_with_provider`,
  `NP_not_subset_AC0_final_of_engine`,
  `NP_not_subset_AC0_at_param_with_provider`,
  `NP_not_subset_AC0_at_param_of_engine`.
- No active global axioms in `pnp3/`.
- No active `sorry/admit` in `pnp3/`.

## Explicitly external parts

1. Multi-switching/provider witness packaging is still explicit at theorem
   interfaces.
2. Default-provider packaging (`hasDefaultStructuredLocalityProviderPartial`)
   remains an explicit dependency for wrapper-level entrypoints.
3. Bridge from formula-track separation to non-uniform separation
   (`NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`) used by `P != NP`
   wrappers.

## What is not claimed

- No claim that `P != NP` is unconditional in the current repository state.
- No claim of a global `PpolyFormula -> AC0` conversion.

## Naming interpretation

- In `pnp3/Magnification/FinalResult.lean`, theorem names containing
  `..._PpolyFormula_final...` should be read as AC0-route formula-separation
  wrappers, not as standalone global non-uniform separation claims.
- The preferred public-facing endpoints for this scope are the explicit AC0
  names (`NP_not_subset_AC0_*`).

## Positioning

The project is a formalized infrastructure and conditional pipeline with clear,
explicit dependency boundaries. Closing the remaining boundaries is ongoing
research/engineering work tracked in `TODO.md` and `STATUS.md`.
