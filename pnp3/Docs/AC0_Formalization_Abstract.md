# Candidate Abstract for the AC0 Formalization Milestone

Updated: 2026-04-23

## Working Title

Machine-Checked AC0 Lower-Bound Surface for a Partial-MCSP Promise Problem

## One-Paragraph Abstract

We present a Lean formalization of a restricted-model lower-bound endpoint for
the active Partial-MCSP promise problem used in the `pnp3` repository.  The
main paper-facing theorem is exposed by
`pnp3/LowerBounds/AC0_GapMCSP.lean` and states, for every fixed parameter
package `p : GapPartialMCSPParams`, that the corresponding promise problem is
not solved by any circuit family in the repository's `SmallAC0Solver_Partial`
interface.  The formalization isolates this AC0 endpoint from the repository's
separate and still-open unconditional `P != NP` research gap, and it avoids
the support-bounds assumptions that were previously audited as inconsistent.
The result should be read as a machine-checked restricted-model theorem over
the active Partial-MCSP interface rather than as a new classical lower bound
for standard MCSP, for which stronger AC0 and `AC^0[p]` lower bounds are
already known in the literature.

## Short Positioning Paragraph

The right contribution claim is not "new AC0 lower bounds for MCSP".  The
right claim is "a clean, audited, machine-checked AC0 lower-bound surface for
the repository's active Partial-MCSP model, with explicit separation from the
open unconditional `P != NP` frontier".

## ITP/CPP-Length Abstract

We formalize in Lean a restricted-model AC0 lower-bound endpoint for the
active Partial-MCSP promise problem used in the `pnp3` repository.  The main
paper-facing theorem, exposed by `pnp3/LowerBounds/AC0_GapMCSP.lean`, states
that for every fixed parameter package `p : GapPartialMCSPParams`, the
corresponding promise problem is not solved by any circuit family in the
repository's `SmallAC0Solver_Partial` interface.  The development isolates
this AC0 milestone from the repository's separate and still-open unconditional
`P != NP` frontier, and it avoids support-bounds assumptions previously
audited as inconsistent.  We position the result as a machine-checked
restricted-model theorem over the active Partial-MCSP interface, rather than
as a new classical lower bound for standard MCSP, for which stronger `AC^0`
and `AC^0[p]` lower bounds are already known.

## Final Short Abstract

We present a Lean formalization of a restricted-model AC0 lower-bound
endpoint for the active Partial-MCSP promise problem in the `pnp3`
repository.  Our main theorem, exposed by
`pnp3/LowerBounds/AC0_GapMCSP.lean`, states that for every fixed parameter
package `p : GapPartialMCSPParams`, the corresponding promise problem is not
solved by any circuit family in the repository's `SmallAC0Solver_Partial`
interface.  The development cleanly separates this AC0 milestone from the
repository's still-open unconditional `P != NP` frontier and avoids the
support-bounds assumptions previously audited as inconsistent.  We position
the result as a machine-checked restricted-model theorem over the active
Partial-MCSP interface, not as a new classical lower bound for standard MCSP,
for which stronger `AC^0` and `AC^0[p]` lower bounds are already known.

## Scope Sentence for an Introduction

This artifact contributes proof engineering, interface hygiene, and
machine-checked restricted-model reasoning; it does not close the
research-level gap required for an unconditional separation such as
`P != NP`.
