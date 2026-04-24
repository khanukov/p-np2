# AC0 Intro / Related Work Draft

Updated: 2026-04-23

This file contains paper-ready paragraphs for introducing the AC0 milestone and
positioning it against prior work.

## Intro Paragraph

This artifact formalizes a restricted-model lower-bound endpoint for the active
Partial-MCSP promise problem used in the `pnp3` repository.  The main theorem,
exported by `pnp3/LowerBounds/AC0_GapMCSP.lean`, states that for every fixed
parameter package `p : GapPartialMCSPParams`, the corresponding promise problem
is not solved by any family in the repository's `SmallAC0Solver_Partial`
interface.  The contribution is therefore a machine-checked AC0 separation over
the repository's active fixed-slice Partial-MCSP model, with theorem names,
tests, and audit hooks organized as a standalone formalization surface.

## Scope / Honesty Paragraph

The result should be read as a formalization milestone, not as a new classical
lower bound for standard MCSP.  Stronger unconditional lower bounds for the
truth-table version of MCSP against `AC^0` and `AC^0[p]` are already known.
Our contribution is instead to isolate a clean proof-assistant endpoint over
the repository's active solver interface, while also separating this
restricted-model milestone from the repository's still-open unconditional
`P != NP` frontier.

## Why This Artifact Exists

The broader `pnp3` development contains substantial hardness-magnification and
DAG-endpoint infrastructure, but its unconditional `P != NP` route remains
blocked by a research-level mathematical gap.  The AC0 module is valuable
precisely because it does not pretend to close that gap.  It packages a
restricted-model theorem that survives the repository's later audits, avoids
the support-bounds assumptions refuted elsewhere in the tree, and can be read
independently of the unresolved general-DAG story.

## Related Work Paragraph

As pure complexity theory, the mathematical terrain around MCSP is already much
stronger than the statement formalized here.  Cheraghchi, Kabanets, Lu, and
Myrisiotis proved strong depth-`d` `AC^0` lower bounds for standard MCSP,
including bounds of the form `2^{Omega(N^{1/(d+2.01)})}` for truth-table length
`N` [ICALP 2019].  Golovnev, Ilango, Impagliazzo, Kabanets, Kolokolova, and Tal
proved strong `AC^0[p]` lower bounds for MCSP [ICALP 2019].  On the partial and
constant-depth side, Ilango studied hardness for constant-depth formula
versions and partial-function versions of MCSP [FOCS 2020].  Accordingly, the
novelty claim of the present artifact is not a new MCSP lower bound, but a
machine-checked formalization of a restricted-model endpoint for an active
Partial-MCSP interface.

## Novelty Paragraph

We are not aware of a prior Lean, Coq, or Isabelle publication that formalizes
this specific kind of MCSP or Partial-MCSP AC0 lower-bound endpoint as a
proof-assistant artifact.  This should be read cautiously: it is a literature
position based on targeted search, not a proof of nonexistence.  The right
claim is therefore "to the best of our knowledge" or "we are not aware of a
prior proof-assistant formalization of this specific endpoint", not a stronger
claim of uniqueness.

## Citation Stub

- Cheraghchi, Kabanets, Lu, Myrisiotis. *Circuit Lower Bounds for MCSP from
  Local Pseudorandom Generators*. ICALP 2019.
- Golovnev, Ilango, Impagliazzo, Kabanets, Kolokolova, Tal.
  *AC^0[p] Lower Bounds Against MCSP via the Coin Problem*. ICALP 2019.
- Ilango. *Constant Depth Formula and Partial Function Versions of MCSP are
  Hard*. FOCS 2020.
