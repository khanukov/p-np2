# Sketch — psc_gapmcsp

**Status: DRAFT SKELETON for auditor review before engineer dispatch.**

## One-paragraph summary

Construct an explicit *almost-natural* property `P` of Boolean
functions that is **useful** against `P/poly` (false on every
poly-size DAG function), **true** on the `GapMCSP` truth table (an
explicit NP function), yet **sub-large** (held by only a `2^{-ω(n)}`
fraction of functions) and **not satisfiable by truth-table
hardwiring**.  Largeness is the only Razborov–Rudich condition we give
up (Chow's almost-natural route); the structure-vs-pseudorandomness
machinery (pseudo-calibration / low-degree analysis) is used **only as
a thinning mechanism** to certify sub-largeness, never as the proof
system.  If such a `P` exists, `GapMCSP ∉ P/poly`, which inhabits
`ResearchGapWitness.dagSeparation`.

## Source theorem

`SourceTheorem_psc_gapmcsp`: there exists a property `P` of Boolean
functions such that (1) `P` is constructive-enough or constructivity is
explicitly sacrificed; (2) for every poly-size-DAG function `f`,
`¬ P(f)`; (3) `P` holds on the `GapMCSP` truth table; (4) `P` is
sub-large; (5) `P` admits no truth-table / singleton-hardwired witness.
The Lean shape lives in `proof.lean` with (1)–(5) as abstract
parameters the engineer instantiates with the repo's real definitions.

## Bridge

`gap_from_psc_gapmcsp` connects the source theorem to a
`Pnp3.Magnification.ResearchGapWitness`.  The implication is the *easy*
direction: conjuncts (2) + (3) give `tt(GapMCSP) ≠ tt(C)` for every
poly-size DAG `C`, i.e. `GapMCSP ∉ PpolyDAG`, hence
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.  **Engineer obligation**:
retype the stub from `→ True` to `→ ResearchGapWitness` and prove this
derivation against the repo `PpolyDAG` / `gapPartialMCSP` defs (a short,
genuine proof — but it touches trust-root types, so write it carefully).

## The make-or-break crux (auditor reads this first)

By Razborov–Rudich (under standard PRG assumptions), a useful property
must sacrifice **constructivity OR largeness**.  Two collapse traps:

* stays large + constructive ⇒ hits RR (vacuous);
* thinned by hardwiring the target's truth table ⇒ hits the
  `hardwiring` NoGo (all 9 prior entries) and violates Rule 5.

The candidate is promising **iff** it exhibits a *third path*: a
sub-large, constructive-enough property holding on `GapMCSP` that is
**provably** not realizable by hardwiring/singleton provenance.  The
auditor's job is to decide whether the proposed thinning yields that
third path or silently lands in a trap.  See `barrier_certificate.md`.

## What the candidate is NOT

Per Rule 1, it does not claim a closed `P_ne_NP_unconditional` term.
Best realistic outcome of a *verified* candidate: a survivor entry;
most likely outcome: a high-quality `NoGoLog` entry that, for the first
time, explains the recurring `hardwiring` failure at the level of the RR
largeness dichotomy.

## What the candidate explicitly avoids

* Refuted predicates (Rule 6): no `FormulaSupportRestrictionBoundsPartial`,
  `FormulaSupportBoundsFromMultiSwitchingContract`, etc.
* Low-degree SoS/PC *as the proof system* — refuted for MCSP (CCC 2023);
  pseudo-calibration enters only as a sub-largeness witness.
* Typeclass-payload channels (Rule 16); arbitrary witness quantification
  without the Rule 5 exclusion lemma; collapse-not-contradiction (Rule 8).

## Connection to prior work

Chow shows sub-large "almost-natural" properties evade RR and that an
explicit `discrimination` property separates P/poly from NP *under the
RR assumption*.  What is structurally new to attempt here: target the
**specific** `GapMCSP` function (using its repo-formalized structure)
and use pseudo-calibration-style thinning to *engineer* sub-largeness
while keeping usefulness — a composition not carried out for worst-case
MCSP / `PpolyDAG`.  Full references in `manifest.toml::[prior_work]`.
