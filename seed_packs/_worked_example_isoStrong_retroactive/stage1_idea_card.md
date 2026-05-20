# Stage 1 — Idea Card (Role A, retroactive)

**Role**: A — Idea Generator.

**Stance**: neutral.

## 1. Thesis

For the canonical Gap-Partial-MCSP language at parameters
`sYES = 1, sNO = 2`, any polynomial-size DAG family that decides
the language must satisfy an "iso-strong forcing" condition on
its YES set: there must exist a YES witness `yYes` and a coordinate
set `D` such that all valid encodings agreeing with `yYes` on `D`
are also in the YES set.  By formalising this forcing condition
and deriving a contradiction with a polynomial counting bound, we
obtain `NP ⊄ P/poly`.

## 2. Prerequisite techniques

- Truth-table encoding of partial-function MCSP (Hirahara FOCS 2022;
  Allender-Cheraghchi ECCC TR21-009).
- Polynomial DAG-size bound interface (`InPpolyDAG` in pnp3).
- Hardness magnification at canonical asymptotic spec (pnp3
  internal).
- Pigeonhole / diagonalisation on trace cardinality (folklore).

## 3. Expected mechanism

1. Show that any `InPpolyDAG` family deciding the Gap-Partial-MCSP
   language must induce a uniform structural property on its YES
   set — specifically, an iso-strong forcing condition.
2. Show that the iso-strong forcing condition implies a
   trace-image cardinality lower bound on bounded-size circuit
   traces.
3. Show that the bounded-size circuit trace count is too small to
   satisfy this lower bound at the canonical parameters.
4. Conclude that no polynomial-size DAG family decides the
   canonical Gap-Partial-MCSP language with the iso-strong forcing
   property — and via magnification to the general case, derive
   `NP ⊄ P/poly`.

## 4. Target pnp3 interface

`AsymptoticIsoStrongRoute` in
`pnp3/Magnification/FinalResultMainline.lean` —
`∀ hInDag, IsoStrongFamilyEventually F hInDag` for the eventual
slice family.

## 5. Self-assessment of novelty

**LOW**.  The technique combines well-known counting / pigeonhole
arguments (folklore) with the standard pnp3 hardness-magnification
chain.  No genuinely new mathematical idea.

(Retroactive note: this honest self-assessment was not made in the
original audit chain.  If it had been, the route would likely have
been deprioritised in favour of higher-novelty alternatives.)
