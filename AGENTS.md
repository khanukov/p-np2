# Repository Agent Rules

These instructions are mandatory for coding agents working in this repository.
They are also checked by `scripts/check.sh`; do not weaken or delete them
without updating the route-policy guardrails deliberately.

## P-vs-NP Mainline

There are now **two** admissible mainlines.  Work counts as P-vs-NP mainline
progress if it reduces a source obligation of either one.  Both are accepted by
the widened endpoint
`Pnp4.Frontier.SequentialMagnification.PvsNPClosureRoute`.

### Mainline A — non-uniform route (unchanged)

Reduces one of:

- `VerifiedNPDAGLowerBoundSource`
- `SearchMCSPWeakLowerBound`

The endpoint has the strength of an `NP` language lower bound against
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

### Mainline B — uniform sequential route (added 2026-07-25)

Reduces the source obligation

- `MCSPStreamingHard` (a one-pass streaming lower bound for MCSP),

or the stronger sufficient obligation

- `LocalHSGWitness` (a local hitting-set generator against space-bounded
  one-pass streaming tests).

```lean
LocalHSGWitness
  → MCSPStreamingHard
  → P_ne_NP                    -- via the published MMWStreamingMagnification contract
```

Mainline B does **not** produce a `PpolyDAG` lower bound, and must not be
described as if it did.  Its magnification step is an explicit unproved
published contract (`MMWStreamingMagnification`, McKay-Murray-Williams STOC 2019
Theorem 1.3); every claim built on Mainline B must state that dependency.

Modules: `pnp4/Pnp4/Frontier/SequentialMagnification/`.
Falsifiability audit: `pnp4/Pnp4/Tests/SequentialMagnificationAudit.lean`.
Spec entry: `spec/target.toml::[secondary_target]` (spec_version 0.1.3).
Rationale: `outputs/sequential-magnification-route-2026-07.md`.

## Background: Why Mainline B Exists (2026-07)

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

Status: **recognised as Mainline B** (maintainer decision, 2026-07-25).  The
widened endpoint is `PvsNPClosureRoute`; the spec records it additively at
`spec/target.toml::[secondary_target]`.  The frozen `[target]` block and
`pnp3/Magnification/UnconditionalResearchGap.lean` are unchanged: Mainline A
keeps its original endpoint and its original guarantees.

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

- Mainline A: reduces `SearchMCSPWeakLowerBound` or
  `VerifiedNPDAGLowerBoundSource`.
- Mainline B: reduces `MCSPStreamingHard` or `LocalHSGWitness` on the
  sequential-magnification track.
- Side track: formalizes restricted lower bounds such as `AC0[p]`, formula, or
  local-PRG consequences without a `PpolyDAG` bridge.
- Infrastructure: improves tests, build, audit, or API hygiene without reducing
  a mathematical source obligation.

Only the two mainline categories should be reported as P-vs-NP mainline
progress.  Mainline B progress must always be reported together with its
dependency on the unproved `MMWStreamingMagnification` contract.

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
