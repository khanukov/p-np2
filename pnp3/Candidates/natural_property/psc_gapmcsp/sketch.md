# Sketch — psc_gapmcsp

**Status: UNDER_REVIEW (auditor verdict, May 2026):
`STRUCTURALLY_HOLLOW_WITH_TWO_KILL_GATES`.**

The candidate's *shape* is correct (usefulness against plain `PpolyDAG`,
not the oracle-extended class — so it does not collide with B4 the way
`hdx_locality` did). But the deeper audit identified two kernel-checked
defects:

* **Gate A — `psc_two_conjuncts_iff_bare_separation`** (`proof.lean`):
  the two main conjuncts together are *equivalent* to the bare DAG
  separation. Sub-largeness adds no proof content; it only constrains
  the *form* of the witness. The candidate does not reduce the
  difficulty of `NP ⊄ PpolyDAG`, it relocates it into the witness.
* **Gate B — `psc_forbidden_target_collapse`** (`proof.lean`): if
  `IsGapMCSP` is instantiated to any repo-hardwired target, the source
  theorem is unconditionally False. The two obvious choices are
  forbidden: `fixedSlice_gapPartialMCSP_in_PpolyDAG` and
  `hInDag_for_canonicalAsymptoticHAsym` (both in
  `pnp3/Tests/HInDagTrivialityProbe.lean`).

Verdict: the candidate stays open as a **D0/D1 kill-first research
target**, not as an engineering implementation. Dispatching engineers to
write a *positive* proof against the current skeleton would burn time on
an already-equivalence-collapsed shape.

## Productive next deliverable (NEGATIVE meta-theorem)

Instead of attempting the positive lower bound, the highest-EV next
deliverable is a **negative characterisation** of when sub-large
properties admit only hardwired witnesses. Schematic statement:

```
PSC_Skeleton_Equivalence_Or_Hardwiring

For any property family P over truth tables of an NP language L,
if P is allowed to depend extensionally on the target tt(L_N),
then  sublarge(P) ∧ accepts(P, L) ∧ useful(P, PpolyDAG)
is equivalent to a singleton/hash/log-width hardwired encoding of
the desired separation L ∉ PpolyDAG.

Therefore any valid candidate must include an anti-hardwiring
condition NotHardwired(P) that is:
  (a) strong enough to exclude singleton/hash/log-width truth-table
      payloads of L_N (Probe 13 — already refuted family);
  (b) weak enough not to exclude genuine structural GapMCSP
      properties;
  (c) independent of the target truth table as advice.
```

If this theorem formalises, it gives the repo a *systematic kill* for
the whole class of "sub-large property" variants — saving every future
attempt's engineering budget. If it *fails* to formalise because of a
concrete structural counter-example, that counter-example would be the
genuine breakthrough seed.

## Repaired research target (NOT scaffolded — requires a new asymptotic NP language)

```
NonHardwiredAlmostNaturalGapMCSPSource

Data:
  L        : Language           -- new asymptotic NP language;
                                -- MUST NOT be fixed-slice gapPartialMCSP_Language p,
                                -- MUST NOT be canonical asymptotic GapMCSP
                                -- (both are repo-proved to lie in PpolyDAG).
  hNP      : NP L
  P        : ∀ N, (Bitstring N → Bool) → Prop

Required (each open research):
  accepts_L                : infinitely_many N, P_N (tt L_N)
  useful_against_PpolyDAG  : ∀ c, infinitely_many N, ∀ DAG C of size ≤ N^c + c,
                             ¬ P_N (eval C)                    -- the main gap
  sublarge                 : density(P_N) ≤ 2^{-ω(N)}          -- decorative
  anti_hardwiring          : excludes singleton/hash/log-width truth-table payload
                             and target-truth-table advice                (CRUX)
  non_inversion            : useful_against_PpolyDAG is FUNCTION hardness,
                             not certification indistinguishability        (CRUX)

Bridge: → VerifiedNPDAGLowerBoundSource → ResearchGapWitness → P ≠ NP.
```

The hard part is entirely `useful_against_PpolyDAG`; everything else is
either decorative (sub-large) or a constraint (anti-hardwiring,
non-inversion). The choice of `L` is itself an open design question —
the two natural candidates in the repo are forbidden by Gate B.

## What the candidate is NOT

Per Rule 1, it does not claim a closed `P_ne_NP_unconditional` term.
Realistic outcome under the corrected scope: a kernel-checked proof of
the PSC equivalence-or-hardwiring meta-theorem; failing that, a sharp
record of which conditions on `NotHardwired` are simultaneously
satisfiable. Either is high-value as a *systematic* result, distinct
from the per-candidate refutations the repo has accumulated.

## What the candidate explicitly avoids

* Refuted predicates (Rule 6): no `FormulaSupportRestrictionBoundsPartial`,
  `FormulaSupportBoundsFromMultiSwitchingContract`, etc.
* Low-degree SoS/PC *as the proof system* — refuted for MCSP (CCC 2023);
  pseudo-calibration enters only as a sub-largeness witness.
* `IsGapMCSP` instantiations against repo-hardwired targets (Gate B).
* Typeclass-payload channels (Rule 16); arbitrary witness quantification
  without the Rule 5 exclusion lemma; collapse-not-contradiction (Rule 8).

## Connection to prior work

Chow shows sub-large "almost-natural" properties evade RR (conditionally).
The candidate's structural problem is that almost-naturalness alone does
not produce the usefulness lower bound; it only allows it to bypass RR
once the lower bound is otherwise established. Carmosino–Impagliazzo–
Kabanets–Kolokolova provide the dual constraint (natural ⇒ learning).
The two-conjunct equivalence (Gate A) is the formal version of the
"sub-largeness is decorative" observation; the forbidden-target collapse
(Gate B) is the repo-internal analogue of `hdx_locality`'s
oracle-target collision. Full references in `manifest.toml::[prior_work]`.

---

## (Historical) original framing

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
