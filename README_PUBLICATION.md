# PNP3: Publication-facing status snapshot

Updated: 2026-03-24

Canonical checklist for unconditional claim readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release wording/checklist for the current milestone:
`RELEASE_RC.md`.

## Current claim level

1. Active `pnp3/` formalization has no project-local axioms.
2. Final route compiles in `pnp3/Magnification/FinalResult.lean`.
3. `./scripts/check.sh` and current audit tests pass on current tree.
4. Audited theorem surface still uses standard Lean assumptions
   `propext`, `Classical.choice`, `Quot.sound` (but no project-local axioms).
5. Final `P ≠ NP` wrappers are conditional on explicit assumptions
   (including DAG-side support-bounds + `DAG → Formula` bridge wrappers).

## Public statement rule

Until the checklist is fully closed, do not claim unconditional `P ≠ NP`.

## Recommended publication wording for this release

1. Inclusion side for default final wrappers is internalized (`P ⊆ PpolyDAG`).
2. Final `P ≠ NP` endpoint is still conditional on
   `NP_not_subset_PpolyDAG`.
3. This is a milestone/RC release, not an unconditional final claim.
