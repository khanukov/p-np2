# Publishable AC0 Result Surface

Updated: 2026-04-23

Preferred paper-facing module:
`pnp3/LowerBounds/AC0_GapMCSP.lean`.

Implementation module:
`pnp3/LowerBounds/AC0_GapMCSP_Final.lean`.

This file is the restricted-model milestone surface that should be used for an
AC0-focused write-up.  It isolates the in-repo AC0 lower bound from the
research-gap machinery for unconditional `P != NP`.

Related literature positioning:
`pnp3/Docs/AC0_Related_Work.md`.

Candidate abstract / wording:
`pnp3/Docs/AC0_Formalization_Abstract.md`.

## Theorem Surface

For every fixed parameter package `p : GapPartialMCSPParams`, the paper-facing
module exports:

- `gapPartialMCSP_no_semantic_AC0_solver p :
   ∀ solver : SmallAC0Solver_Partial p, False`
- `gapPartialMCSP_no_syntactic_AC0_solver p`
- `gapPartialMCSP_no_constructive_AC0_solver p`
- `gapPartialMCSP_not_in_AC0 p :
   GapPartialMCSP_not_in_AC0 p`

The paper-facing predicates are:

- `GapPartialMCSP_in_AC0 p := ∃ solver : SmallAC0Solver_Partial p, True`
- `GapPartialMCSP_not_in_AC0 p := ¬ GapPartialMCSP_in_AC0 p`

The implementation predicate remains available:

- `GapPartialMCSP_NotInSmallAC0 p := ¬ ∃ solver : SmallAC0Solver_Partial p, True`

## What This Does Mean

- The active repository has an unconditional fixed-slice AC0 lower-bound
  endpoint for the Partial-MCSP promise problem.
- The proof does not use the refuted formula support-bounds route.
- The proof does not depend on `ResearchGapWitness`, asymptotic DAG pullbacks,
  or the final `P != NP` surface.

## What This Does Not Mean

- This is not yet a standardized external theorem of the form
  `GapMCSP \notin AC^0` in a fully general complexity-class interface.
- This is not progress on unconditional `P != NP`.
- This is not a claim that `AC0ApproxFamilyBridge` has been closed.

## Positioning

The honest claim is:

> the repository contains a machine-checked restricted-model lower-bound
> endpoint for the active Partial-MCSP AC0 solver interface.

That is a credible formalization milestone and a reasonable publishable
restricted-model artifact even though it is separate from the unresolved
general DAG / `P != NP` gap.

## Literature Posture

As a mathematical lower-bound claim for standard MCSP, the repository should
be positioned conservatively.  Stronger unconditional `AC^0` and `AC^0[p]`
lower bounds for MCSP already exist in the literature; see
`pnp3/Docs/AC0_Related_Work.md`.
