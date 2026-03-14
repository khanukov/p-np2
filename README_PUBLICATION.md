# PNP3: Publication-facing status snapshot

Updated: 2026-03-14

Canonical checklist for unconditional claim readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release wording/checklist for the current milestone:
`RELEASE_RC.md`.

## Current claim level

1. Active formalization is axiom-clean in `pnp3/`.
2. Final route compiles in `pnp3/Magnification/FinalResult.lean`.
3. `./scripts/check.sh` and current audit tests pass on current tree.
4. Final `P ≠ NP` wrappers are conditional on explicit assumptions.

## Public statement rule

Until the checklist is fully closed, do not claim unconditional `P ≠ NP`.

## Recommended publication wording for this release

1. Inclusion side for default final wrappers is internalized (`P ⊆ PpolyDAG`).
2. Final `P ≠ NP` endpoint is still conditional on
   `NP_not_subset_PpolyDAG`.
3. This is a milestone/RC release, not an unconditional final claim.
