# Research Method Boundary

Updated: 2026-04-23.

This file records the audit boundary for AC0/locality route bias and for
"proof by DevOps" drift.

## Method-Neutral Final Port

The active public closure target is method-agnostic:

```text
ResearchGapWitness
```

Its mathematical field is:

```text
ComplexityInterfaces.NP_not_subset_PpolyDAG
```

Therefore a future proof does not have to pass through AC0, random
restrictions, support sets, subcubes, shrinkage, or
`AcceptedFamilyCertificateAt`.  A non-combinatorial proof may plug in directly
by proving the DAG separation in `pnp3/Magnification/UnconditionalResearchGap.lean`.

Algebraic, spectral, finite-field polynomial, Fourier-analytic, SOS, or other
non-local methods should not be forced to extract a combinatorial support set
`S` merely to fit the historical route.

## Optional Combinatorial Routes

The AC0/multi-switching/locality stack remains useful for side results and for
possible sufficient routes:

- `SmallDAGImpliesAcceptedFamilyAt`
- `AcceptedFamilyCertificateAt`
- `SmallDAGImpliesPromiseYesSubcubeAt`
- support/locality/restriction/shrinkage packages

These are optional weak-route or compatibility surfaces.  They are not the
required interface for solving the remaining gap.

In particular, failure to express an algebraic lower-bound argument as an
`AcceptedFamilyCertificateAt` producer must not be treated as failure of the
argument.  The correct integration point for such an argument is the
method-neutral `ResearchGapWitness` boundary.

## DevOps Boundary

`./scripts/check.sh`, axiom audits, route-policy guards, and CI workflows are
proof-engineering hygiene.  They check that the repository has no active
project-local axioms, no `sorry/admit`, and no stale route wording.

Green CI is not mathematical progress toward `NP_not_subset_PpolyDAG` by
itself.  Refactoring weak routes, adding wrappers, or making audit surfaces
compile does not reduce the conceptual lower-bound gap unless it proves a new
non-vacuous source theorem for `ResearchGapWitness`.

## Future Requirement

When adding a new source route, state explicitly whether it is:

1. a direct method-neutral proof of `ResearchGapWitness`;
2. an optional combinatorial sufficient route, such as an accepted-family or
   subcube certificate producer;
3. a side-result route, such as an AC0 lower bound, that does not claim progress
   on general `P/poly` or general DAG lower bounds.

Canonical docs must keep these categories separate.
