# Technical Claims and Scope

## Verified contribution scope

The repository contributes a Lean-verified combinatorial pipeline around SAL and
capacity-style lower-bound infrastructure, plus machine-checked bridge plumbing
into anti-checker/magnification interfaces.

## Current claim level (2026-02-22)

- Active machine-checked separation target: conditional
  `NP_not_subset_PpolyFormula`.
- No active global axioms in `pnp3/`.
- No active `sorry/admit` in `pnp3/`.

## Explicitly external parts

1. Multi-switching/shrinkage witness construction for target families.
2. Provider-level certificate packages needed for default constructive locality
   provider instantiation.
3. Bridge from formula-track separation to non-uniform separation
   (`NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`) used by `P != NP`
   wrappers.

## What is not claimed

- No claim that `P != NP` is unconditional in the current repository state.
- No claim that I-4 is fully closed with internal real instances.

## Positioning

The project is a formalized infrastructure and conditional pipeline with clear,
explicit dependency boundaries. Closing the remaining boundaries is ongoing
research/engineering work tracked in `TODO.md` and `STATUS.md`.
