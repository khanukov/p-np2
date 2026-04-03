# PNP3: Publication-facing status snapshot

Updated: 2026-04-03

Canonical checklist for unconditional claim readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release wording/checklist for the current milestone:
`RELEASE_RC.md`.

## Current claim level

1. Active `pnp3/` formalization has no project-local axioms and no
   `sorry/admit`.
2. Final route compiles in `pnp3/Magnification/FinalResult.lean`.
3. `./scripts/check.sh` and current audit tests pass on the current tree.
4. Audited theorem surface still uses standard Lean assumptions
   `propext`, `Classical.choice`, `Quot.sound`.
5. Additional honest DAG wrappers now exist for asymptotic fixed-slice collapse
   and for concrete `_TM` source/blocker routes.
6. Final `P ≠ NP` remains conditional on explicit assumptions.

## Public statement rule

Until the checklist is fully closed, do not claim unconditional `P ≠ NP`.

## Recommended publication wording for this release

1. Inclusion side for default final wrappers is internalized (`P ⊆ PpolyDAG`).
2. The repository now exposes richer DAG-facing theorem surfaces than before,
   including fixed-slice/asymptotic wrappers and fallback accepted-family
   closures.
3. The default public final theorem still depends on explicit DAG separation,
   so this remains a milestone/RC release rather than an unconditional final
   claim.
