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

## Open Policy Question: The Uniform Sequential Port (2026-07)

The mainline rule above requires every accepted package to end in
`VerifiedNPDAGLowerBoundSource`, i.e. in the non-uniform separation
`NP ⊄ PpolyDAG`.  That is strictly stronger than `P != NP`.

The magnification theorem this project cites as its mainline reference does not
have that shape.  McKay-Murray-Williams (STOC 2019, Theorem 1.3), as restated by
Cheraghchi-Hirahara-Myrisiotis-Yoshida (ECCC TR20-103, Theorem 47), concludes
`P != NP` directly from a *uniform* one-pass streaming lower bound for MCSP, and
never produces a `P/poly` lower bound.  `SearchMCSPWeakLowerBound` therefore
cannot express it.

`pnp4/Pnp4/Frontier/SequentialMagnification/` supplies that missing port,
together with a kernel-checked falsifiability audit showing that the truth-table
hardwiring attack which refuted every earlier source predicate provably does not
apply to it.

Status of this directory under the present policy: **side track**, because it
does not bridge to `VerifiedNPDAGLowerBoundSource`.  Whether to recognise it as
a second mainline is a maintainer decision; the code records the proposed
widened endpoint as `PvsNPClosureRoute` but does not enact it, and neither
`spec/target.toml` nor `pnp3/Magnification/UnconditionalResearchGap.lean` has
been modified.

Rationale and quantitative frontier:
`outputs/sequential-magnification-route-2026-07.md`.

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
