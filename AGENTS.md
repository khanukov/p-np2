# Repository Agent Rules

These instructions are mandatory for coding agents working in this repository.
They are also checked by `scripts/check.sh`; do not weaken or delete them
without updating the route-policy guardrails deliberately.

## P-vs-NP Mainline

The only pnp4 work that counts as mainline progress toward `P != NP` is work
that reduces one of these source obligations:

- `VerifiedNPDAGLowerBoundSource`
- `SearchMCSPWeakLowerBound`

The endpoint must have the strength of an `NP` language lower bound against
`PpolyDAG`, represented in pnp4 by:

```lean
VerifiedNPDAGLowerBoundSource
```

or by the compression-magnification frontier:

```lean
SearchMCSPWeakLowerBound
  → VerifiedNPDAGLowerBoundSource
  → NP_not_subset_PpolyDAG
  → P_ne_NP
```

## Restricted Lower-Bound Side Track

The pnp4 `AC0[p]`, coin-problem, formula, and local-PRG lower-bound routes are
restricted lower-bound formalization tracks.  They are useful, but they are a
side track for `P != NP` unless they provide an explicit bridge to
`VerifiedNPDAGLowerBoundSource` or `PpolyDAG`.

Do not describe an `AC0[p]`, formula, local-PRG, or coin-problem exclusion as
unconditional progress toward `P != NP` unless it is paired with an explicit
`PpolyDAG`/`VerifiedNPDAGLowerBoundSource` bridge.

## Progress Classification

Before implementing new lower-bound work, classify it as one of:

- Mainline: reduces `SearchMCSPWeakLowerBound` or
  `VerifiedNPDAGLowerBoundSource`.
- Side track: formalizes restricted lower bounds such as `AC0[p]`, formula, or
  local-PRG consequences without a `PpolyDAG` bridge.
- Infrastructure: improves tests, build, audit, or API hygiene without reducing
  a mathematical source obligation.

Only the first category should be reported as P-vs-NP mainline progress.

## Check Requirements

Before committing lower-bound route changes:

- run `./scripts/check.sh`;
- keep pnp4 modules listed in `lakefile.lean`;
- update `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` for new
  public theorem surfaces;
- update `pnp4/Pnp4/Tests/AxiomsAudit.lean` for new audited theorem surfaces;
- do not add `axiom`, `sorry`, `admit`, or `native_decide` in active pnp3/pnp4
  code.

Do not push to a remote branch unless the user explicitly asks for a push.
