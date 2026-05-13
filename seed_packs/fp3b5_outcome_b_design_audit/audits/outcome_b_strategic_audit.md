# FP-3b.2 / Outcome B filter design — strategic audit

**Audit scope:** identify the highest-expected-value candidate
design family for the next mainline `ProvenanceFilter_v1` (the
reserved `accepted`-promotable Outcome B guard) given the
constraints imposed by the closed V2 audit-route family and the
adjacent-area scan outputs in `first_move_search_2026`.

**Operator decision (preview, see §6):** dispatch
**distinguisher-matrix audit route** (synthesised from Q4
Atserias-Müller 2025 + Chen-Hirahara-Oliveira et al. ITCS 2020)
as the top candidate.  Suggested follow-on seed pack name
`fp3b6_distinguisher_matrix_provenance/`.  Hold
**almost-natural property filters** (Q3) as soft-runner-up.
Hold **bounded-arithmetic-witnessed provenance** (Q1) as
high-variance reserve.

This is operator-scoped strategic audit, not a worker artifact.

## 1. Context

### 1.1 Mainline FP-3 pinpoint

Per `FixedParams_Probe.md` and the current state of
`pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`:

* FP-3 candidate filter is
  `FP3Attempt.InSupportFunctionalDiversity`.
* It formally excludes uniformly-bounded hardwiring (Probe-2
  shape) at audit-only `informal` status.
* It does **not** formally exclude NOGO-000006 arbitrary
  log-width truth-table hardwiring (the explicit FP-3b.2
  obligation).
* FP-3b.2 = strengthen or replace `InSupportFunctionalDiversity`
  so that it formally excludes NOGO-000006 while remaining
  non-vacuous, non-tautologous, and satisfying the V2 closure
  constraints.
* FP-4 (bridge construction +
  `ProvenanceFilter_v1` promotion to `accepted`) is **gated** on
  FP-3b.2 success (per `FixedParams_Probe.md` §8.6).

### 1.2 V2 family closure outcome

`seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/v2_family_closure_retrospective.md`
records the closure of the syntactic-only V2 audit-route family
for `accepted`-status promotion.  Five design subspaces closed:

* V2-A (syntactic filter) → NOGO-000008 (tautological rewrite
  attack);
* V2-A.1 (normalisation patch) → NOGO-000009 (structural
  normalisation meta-barrier);
* V2-A.2 full / minimal semantic quotient → priority refresh
  (Razborov-Rudich re-entry, NOGO-000009 analogue);
* V2-B cross-length coherence → priority refresh
  (`hold_for_nonvacuity`, parity-specific);
* V2-D shape signature → priority refresh (`reject_route`,
  bogus non-vacuity, adaptive NOGO-8 padding).

### 1.3 First-move adjacent-area scan inputs

`seed_packs/first_move_search_2026/reports/gpt55/` contains:

* **Q1 — bounded-arithmetic unprovability** (Pich-Santhanam 2019
  + 2021, Bydžovský-Krajíček-Oliveira 2015, Carmosino-Kabanets-
  Kolokolova-Oliveira 2021, Li-Oliveira 2023,
  Chen-Li-Oliveira 2025): formal proof-complexity barriers
  showing certain provenance-filter validation statements cannot
  be proved in weak feasible theories (S^1_2, V^0, APC_1).
  Suggests **"feasible-proof-system limitation"** filters as a
  fourth-barrier-style interface adjacent to natural proofs.
* **Q3 — descriptive non-natural filters** (Razborov-Rudich
  1997, Chow "almost-natural proofs" 2009,
  Carmosino-Impagliazzo-Kabanets-Kolokolova 2016,
  Allender-Buhrman-Koucký-van Melkebeek-Ronneburger 2006,
  Williams 2013): vocabulary for auditing filters against
  natural-proofs failure modes; identifies **almost-natural
  properties** (low-density, satisfying constructivity +
  usefulness without largeness) as a concrete non-natural class.
* **Q4 — distinguisher-matrix magnification** (Atserias-Müller
  2025, Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam ITCS
  2020, Oliveira-Pich-Santhanam, Chen-Jin-Williams FOCS 2019):
  **sparse distinguisher matrices** retaining code-like distance
  properties yield general magnification theorems; the structural
  audit object is a matrix + sparsity + distance preservation,
  not a syntactic property of the formula.

Q2 (fine-grained complexity barriers) and Q5 (relativization /
natural-proofs strengthenings) have not landed yet.  Their
absence is noted but not blocking: Q1+Q3+Q4 collectively provide
three concrete design seed families that survive the V2 closure
constraints by **structural design**, not by accidental escape.

## 2. Closure constraints (formal list for any FP-3b.2 candidate)

Any `ProvenanceFilter_v1` candidate dispatched after this audit
must satisfy ALL of:

**C1.** Excludes NOGO-000006 — arbitrary all-essential
log-width truth-table hardwiring family.  Concrete formal target:
`¬ ProvenanceFilter_v1 (adversaryWitness_v_natlog2_arbitrary_payload)`
as a kernel-checked Lean theorem.

**C2.** Not support-cardinality-only — formally, NOT
`IsSupportCardinalityOnly ProvenanceFilter_v1` (per the
predicate at
`pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/`).
Otherwise NOGO-000007 implies any honest sublinear-support
witness admitted by the filter has a hardwiring twin.

**C3.** Not syntactic-only-and-tautological-rewrite-vulnerable.
Concrete test: `¬ ProvenanceFilter_v1 (rewritePrefixAndWitness)`
where `rewritePrefixAndWitness` is the V2-A rewrite attack at
`pnp3/.../V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean`.

**C4.** Not self-defeating under context-uniform bottom-up
structural normalisation in the
`V2_A_NormaliseMetaBarrier.StructuralNormaliser` class.  Formally
either (a) the filter is invariant under such normalisation (so
NOGO-000009 doesn't apply) OR (b) it is provably outside the
StructuralNormaliser class's reach by structural reason (e.g.
the filter operates on semantic invariants rather than displayed
syntax post-normalisation).

**C5.** Non-vacuous: at least one honest `InPpolyFormula`
witness admitted, with a kernel-checked admission theorem
analogous to V2-A's `seededPrefixAndWitness_admitted`.  The
honest witness must survive any required filter pre-processing
(unlike V2-A.1's collapse under normalisation).

**C6.** Non-tautologous and `accepted`-promotable.  Per
`FixedParams_Probe.md` §3.B, accepted-status requires either:
* `Π ↔ KnownGuardCombination` (filter equivalent to a defined
  combination of existing accepted guards), OR
* `fixedParams ac0 sb ∧ Π → ExistingKnownGuard` with
  `standalone_factorization_target = true` (filter
  conjoined with FixedParams forces a non-trivial existing guard).
HardwiringGuard is currently the only `accepted` guard, but its
`standalone_factorization_target = false`, so it cannot be the
Outcome B partner.  Any `ProvenanceFilter_v1` candidate must
either (a) be paired with a new accepted guard not yet defined,
or (b) provide a self-contained accepted-promotion theorem.

**C7.** Razborov-Rudich naturality risk explicitly addressed.
Per RESEARCH_CONSTITUTION Rule 12 and the V2-A self-test pattern
at `pnp3/.../NaturalProofsSelfTest/RepresentationSensitivity.lean`,
any candidate filter must either:
* (a) explicitly demonstrate non-extensionality (analogous to
  V2-A) with kernel-checked anti-extensionality theorem, AND
  audit-classify against Razborov-Rudich constructivity / largeness
  / usefulness triad; OR
* (b) explicitly demonstrate one of the natural-proofs triad
  conditions fails (e.g., non-constructive, low-density, or
  classifying class wider than the route claims to attack); OR
* (c) cite a barrier-interface obstruction from Q1
  (bounded-arithmetic unprovability) explaining why the natural
  proofs barrier is structurally inapplicable.

**C8.** Adversarial-robustness self-test required.  Following
the fp3b3.2 pattern, any candidate must ship a self-attack
theorem analogous to
`v2A_rewrite_attack_prefixAnd` BUT showing the candidate
**resists** the tautological rewrite attack and any adaptation.

These eight constraints jointly define the FP-3b.2 design space.

## 3. Candidate design families — triage

Six candidate families considered.  Each evaluated against
constraints C1-C8.

### 3.1 Family A — Distinguisher-matrix audit route (from Q4)

**Idea:** filter accepts witness W iff W carries (or admits a
constructible) sparse distinguisher matrix D with the property
that the fingerprint map `x ↦ xD` separates positive from
"far-negative" inputs for the relevant promise problem, in the
sense of Atserias-Müller 2025.  The filter predicate inspects
D's sparsity profile + distance preservation, not displayed
formula syntax.

**Closure-constraint analysis:**
* C1 (excludes NOGO-6): plausible.  Arbitrary all-essential
  log-width TT payloads do not naturally carry distance-preserving
  sparse fingerprints; an arbitrary payload's distinguisher
  matrix would have to be constructed ad hoc and would not
  satisfy the magnification-strength sparsity profile.
* C2 (not support-cardinality-only): yes-survives.  Distinguisher
  matrix structure is independent of `|support|`.
* C3 (not tautological-rewrite-vulnerable): yes-survives.
  Tautological seed conjunction does not change the
  Boolean function, so the distinguisher matrix is unchanged.
* C4 (not normalisation-self-defeating): yes-survives by
  structural reason.  Distinguisher matrices are a semantic
  invariant of the Boolean function pair (W's family member at
  length n, the promise problem's positive set); structural
  syntactic normalisation does not alter Boolean function
  semantics, so the matrix is invariant.  This puts the filter
  **outside** the StructuralNormaliser class's reach.
* C5 (non-vacuity): credible.  Atserias-Müller construct explicit
  distinguisher matrices for sparse NP problems; honest families
  in the FP-N context (prefixAnd, parity, etc.) can be assigned
  trivial / explicit matrices.  However the precise non-vacuity
  witness must be designed.
* C6 (accepted-promotability): MEDIUM uncertainty.  The filter's
  validation depends on the magnification theorem connecting
  weak lower bounds to strong ones via the distinguisher.  This
  is a substantive Lean obligation but is in scope per
  `pnp4/Pnp4/Frontier/CompressionMagnification.lean` framework.
* C7 (NP risk addressed): YES.  Q4 cites
  Chen-Hirahara-Oliveira et al. ITCS 2020 which explicitly
  discusses MCSP-based magnification and the locality barrier.
  Atserias-Müller 2025 explicitly **sidesteps the locality
  barrier** via sparse distinguisher structure.  This is
  literature-grade NP risk argument.
* C8 (self-attack): can be designed; rewrite attack against
  distinguisher-matrix filter would need to construct a
  distinguishing matrix for a tautologically-rewritten witness,
  which (a) inherits the original matrix or (b) requires the
  adversary to forge a new matrix that the filter cannot
  distinguish from a legitimate one.  Forgery is the natural
  attack model; filter design must commit to a verification
  primitive (e.g., sparsity check + distance verification on a
  random promise instance).

**Effort estimate:** MEDIUM-HIGH.  ~6-10 engineer-weeks for
Phase-1 sketch + Phase-2 survivor surface.  New audit-route
directory under `pnp3/Magnification/AuditRoutes/`; new
predicates; explicit non-vacuity proof; explicit anti-NOGO
proofs; explicit Razborov-Rudich self-test.

**Verdict:** **TOP RECOMMENDATION.**  Highest constraint-set
compatibility; strongest literature foundation (Atserias-Müller
2025 is post-V2-closure-era state-of-the-art); semantic by
design so the V2 closure pattern does not directly apply;
explicit barrier-aware design.

### 3.2 Family B — Almost-natural property filters (from Q3)

**Idea:** filter accepts a low-density property class (Chow's
"almost-natural") rather than a large constructive class.
Density target: exp(-n^c) for some c > 0, satisfying
constructivity + usefulness in the Razborov-Rudich sense but
**failing largeness** by construction.  Filter membership is
defined by an explicit small structured predicate (e.g., "witness
family is parameterised by a fixed-arity bounded structure
satisfying property Q") rather than by an asymptotic property of
each individual Boolean function.

**Closure-constraint analysis:**
* C1 (excludes NOGO-6): depends on density-class choice.  If
  the small admitted class is structurally distinct from
  arbitrary log-width TT payloads, exclusion holds.  Concrete
  design required.
* C2 (not support-cardinality-only): yes-survives by design.
* C3 (not rewrite-vulnerable): depends.  If density is defined
  by a structural parameter invariant under tautological
  rewrite, yes-survives.  If by displayed syntax, vulnerable.
  Design must commit.
* C4 (not normalisation-self-defeating): depends similarly.
  If density-class membership is a semantic / parameterisation
  property, normalisation invariant.  If it's syntactic, vulnerable.
* C5 (non-vacuity): depends on density class.  Chow's
  construction shows non-vacuous almost-natural classes exist;
  embedding into FP-N requires constructing one.
* C6 (accepted-promotability): MEDIUM uncertainty.  Almost-natural
  classes can be combined with FixedParams to derive
  HardwiringGuard-style restrictions, but the formal bridge
  needs design.
* C7 (NP risk addressed): YES via Chow construction.
  Carmosino-Impagliazzo-Kabanets-Kolokolova 2016
  (natural→learning) is the anti-evidence direction; almost-natural
  density escapes this implication.
* C8 (self-attack): designable.  Tautological rewrite attack
  against an almost-natural filter would need to land in the
  small admitted class; if the class is structurally narrow,
  rewrite attacks are likely to miss it.

**Effort estimate:** MEDIUM.  ~4-8 engineer-weeks for Phase-1
sketch.  Requires committing to a specific density class
construction.

**Verdict:** **RUNNER-UP / SOFT-HOLD.**  Different risk profile
from Family A: smaller surface area but more design dependency.
Hold as fallback if Family A closes.

### 3.3 Family C — Bounded-arithmetic-witnessed provenance (from Q1)

**Idea:** filter accepts witness W iff there exists a feasible
proof in theory T (e.g., S^1_2, V^0) that W is constructed by
the intended provenance pattern.  The proof object IS the
provenance witness.  Filter predicate inspects the proof's
existence (via a structured proof-checker or KPT-extractable
witnessing program).

**Closure-constraint analysis:**
* C1 (excludes NOGO-6): yes-survives if arbitrary all-essential
  log-width payloads do not admit feasible provenance proofs
  for their construction.  This is precisely the Pich-Santhanam
  /Li-Oliveira unprovability direction.
* C2 (not support-cardinality-only): yes-survives.
* C3 (not rewrite-vulnerable): yes-survives.  Tautological seed
  conjunction may or may not be feasibly-provable; the proof
  obligation discriminates structurally.
* C4 (not normalisation-self-defeating): yes-survives.  Structural
  normalisation does not produce a feasible proof for free.
* C5 (non-vacuity): credible.  Honest constructions (e.g.,
  prefixAnd, parity) have explicit feasible-arithmetic
  constructibility proofs.
* C6 (accepted-promotability): UNCERTAIN.  Filter validation
  is bounded-arithmetic provability; per Q1 citations, this is
  unprovable in weaker theories, which could either be a feature
  (escaping natural proofs by unprovability) or a blocker
  (accepted-status requires a proof of validity).
* C7 (NP risk addressed): YES at the meta-level.  Q1 cites
  unprovability results that **explicitly classify** feasible
  proofs against natural-proofs-style barriers.
* C8 (self-attack): designable but technically demanding.

**Effort estimate:** HIGH.  ~12-20 engineer-weeks because of
required bounded-arithmetic infrastructure in Lean (S^1_2 / V^0
formalisation, KPT witnessing, proof-checker definitions).
**Most of the cost is infrastructure**, not design.

**Verdict:** **HIGH-VARIANCE RESERVE.**  Potentially highest
research payoff (introduces a new barrier-interface family) but
the infrastructure cost is prohibitive without an existing Lean
bounded-arithmetic library.  Hold as a reserve direction if
external research lands the prerequisite infrastructure.

### 3.4 Family D — Externally-witnessed provenance (operator brainstorm)

**Idea:** extend `InPpolyFormula` to carry an explicit
construction trace object alongside the formula family.  Trace
records the sequence of operations from primitive gates; filter
inspects the trace.

**Closure-constraint analysis:**
* C3 (not rewrite-vulnerable): **FRAGILE.**  Adversary can
  construct a malicious trace for the rewritten witness.  Trace
  forgery attack model.
* C4 (not normalisation-self-defeating): depends.  Structural
  normalisation could either preserve or destroy the trace;
  design must commit.
* C6 (accepted-promotability): UNCERTAIN.  Requires extending
  the InPpolyFormula record type, which is a trust-root edit
  (forbidden by current scope rules).

**Verdict:** **LOW PRIORITY.**  Trace-forgery attack is the
classical objection; would require sophisticated trace-verification
protocol to be a serious candidate.  Trust-root extension is a
governance blocker.

### 3.5 Family E — Cross-language coherence (V2-B generalised)

**Idea:** generalise V2-B's xor-successor equation to a class of
cross-length functional relations that admit non-parity families.

**Closure-constraint analysis:**
* C5 (non-vacuity): the same blocker that made V2-B "hold".
  No non-parity admitted family is known to exist for the
  xor-successor recurrence; finding one is research-grade.

**Verdict:** **DEPRIORITIZED.**  Inherits V2-B's non-vacuity
problem.  Generalising the recurrence to admit more families
shifts the problem to "what cross-length functional family
captures honest provenance without admitting hardwiring."  No
clear design direction yet.

### 3.6 Family F — Hybrid semantic+structural

**Idea:** combine a semantic invariant (e.g., distance
preservation) with a bounded structural constraint (e.g., gate
count) so the semantic invariant prevents NOGO-9 self-defeat.

**Closure-constraint analysis:**
* C4 (not normalisation-self-defeating): TRICKY.  The hybrid
  often inherits the structural component's NOGO-9 risk because
  normalisation can target the structural conjunct while
  leaving the semantic conjunct technically satisfied.

**Verdict:** **LOW PRIORITY.**  Combining components often
inherits both their risks; rarely solves them.  V2-A.1's
attempt was effectively a hybrid (structural normaliser +
syntactic V2-A) and that closed.

## 4. Triage summary table

| Family | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 | Effort | Verdict |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| A. Distinguisher matrix (Q4) | + | + | + | + | + | M | + | + | MED-HI | **TOP** |
| B. Almost-natural (Q3) | D | + | D | D | + | M | + | + | MED | RUNNER-UP |
| C. Bounded-arith (Q1) | + | + | + | + | + | U | + | + | HI | RESERVE |
| D. Externally-witnessed | + | + | **F** | D | D | U | D | F | MED | LOW |
| E. Cross-length (V2-B+) | + | + | + | + | **N** | U | + | + | HI | DEPRIORITIZED |
| F. Hybrid sem+struct | D | D | D | **T** | D | U | D | D | HI | LOW |

Legend: + = survives constraint; D = design-dependent;
M = medium uncertainty; U = uncertain; **F** = fragile;
**N** = non-vacuity blocker; **T** = tricky inheritance.

## 5. Cross-family observations

### 5.1 The semantic-vs-syntactic dimension

The V2 closure pattern shows that **syntactic-only filters fail
both NOGO-8 and NOGO-9** (and their natural patches fail one or
the other).  All three first_move-derived families (A, B, C) are
semantically grounded:

* A uses distance preservation, a property of the Boolean
  function pair, not the formula.
* B uses density / parameterisation, a property of the family
  membership, not displayed syntax.
* C uses feasible-arithmetic constructibility, a proof-system
  property of the construction, not the formula's gate inventory.

Operator note: **the design-space-shape constraint after V2
closure is that the filter must operate on a property that is
invariant under structural normalisation and tautological
rewriting.**  This rules out the entire syntactic-only design
family on which V2 was based.  All viable candidates after V2
closure operate on semantic / proof-theoretic / parameterised
properties.

### 5.2 The barrier-interface dimension

Families A, B, C each open a new barrier-style interface in the
repo (analogous to `pnp3/Barrier/NaturalProofs.lean`,
`pnp3/Barrier/Relativization.lean`,
`pnp3/Barrier/Algebrization.lean`):

* A → "locality / sparsity barrier" interface (per
  Chen-Hirahara-Oliveira et al. ITCS 2020).
* B → refined natural-proofs interface distinguishing largeness
  from constructivity + usefulness (per Chow 2009).
* C → "feasible-proof-system limitation" barrier interface (per
  Pich-Santhanam, Li-Oliveira, etc.).

Each is a substantive research artifact independent of its
direct FP-3b.2 utility.  Family A's barrier interface is the
most concrete and the most directly relevant to the
magnification path at `pnp4/Pnp4/Frontier/CompressionMagnification.lean`.

### 5.3 The accepted-promotion dimension

Per `FixedParams_Probe.md` §3.B and `spec/known_guards.toml`,
`ProvenanceFilter_v1` promotion to `accepted` requires either
KnownGuardCombination equivalence or ExistingKnownGuard
factorization with `standalone_factorization_target = true`.

* Family A's distinguisher-matrix filter could plausibly serve
  as a standalone factorization target if the distinguisher's
  magnification theorem yields a non-trivial restriction.
* Family B's almost-natural class might require pairing with
  an explicit guard combination.
* Family C's feasibly-provable-construction filter introduces
  a new guard surface that may itself need separate accepted
  promotion.

Family A's path to `accepted` is the most concrete because the
magnification framework already exists in `pnp4/Pnp4/Frontier/`.

## 6. Operator recommendation

**Primary recommendation: dispatch Family A — distinguisher-matrix audit route.**

Suggested successor seed pack:
`seed_packs/fp3b6_distinguisher_matrix_provenance/`

The seed pack should commit to:

1. **Phase 1 sketch** of a distinguisher-matrix-based filter
   predicate, including:
   * `SparseDistinguisherMatrix` predicate (bounded row/column
     support, controlled fingerprint output length, constructible
     indexing).
   * `DistancePreservingFingerprint` predicate (positive vs
     far-negative separation parameters per magnification
     theorem).
   * `ProvenanceFilter_v1_distinguisher` candidate combining
     the two.
2. **Required Phase-2 deliverables** (in priority order):
   * non-vacuity: a kernel-checked honest-family admission
     theorem (analogous to `seededPrefixAndWitness_admitted`);
   * NOGO-6 exclusion: `¬ ProvenanceFilter_v1_distinguisher
     (adversaryWitness_v_natlog2_arbitrary_payload)`;
   * NOGO-7 dodging: `¬ IsSupportCardinalityOnly
     ProvenanceFilter_v1_distinguisher`;
   * NOGO-8 anti-evidence: `¬ ProvenanceFilter_v1_distinguisher
     (rewritePrefixAndWitness)` AND a rewrite-invariance theorem
     formalising why the distance preservation is invariant
     under tautological seed conjunction;
   * NOGO-9 outside-class proof: explicit demonstration that
     the filter operates on the Boolean function pair, not on
     displayed syntax, so the `StructuralNormaliser` class's
     reach is irrelevant.
3. **Razborov-Rudich self-test analogous to V2-A's:** kernel-checked
   anti-naturality classification, citing the
   Chen-Hirahara-Oliveira ITCS 2020 locality-barrier discussion
   and Atserias-Müller 2025's barrier-sidestep argument.

The seed pack should be scoped as **audit-route Phase-1 design
sketch**, not lower-bound progress.  No `SourceTheorem_*`, no
`gap_from_*`, no `accepted` promotion, no final endpoint claims
until Phase-2 deliverables all land cleanly AND a separate
operator review approves accepted-status promotion.

**Secondary recommendation: hold Family B (almost-natural) as soft fallback.**

If Family A's Phase-2 survivor surface fails to materialise
(e.g., distinguisher matrices for honest families turn out to
require unproved magnification strength), reactivate Family B
under a new seed pack
`seed_packs/fp3b7_almost_natural_provenance/`.  Do not dispatch
both in parallel — Family A's literature foundation is stronger.

**Tertiary recommendation: hold Family C (bounded-arithmetic) as high-variance reserve.**

Family C requires substantial Lean bounded-arithmetic
infrastructure that does not exist in the repo.  Operator
recommendation: do not dispatch Family C as the primary track
unless / until either (a) the bounded-arithmetic Lean
infrastructure lands via external research, or (b) Families A
and B both close.

**Deprioritized: Families D, E, F.**  None survive triage at
operator-level.

## 7. Optional parallel work

These are non-mainline tracks that can run alongside the Family
A dispatch without competing for the same operator attention:

* **first_move_search_2026 completion:** Q2 (fine-grained
  complexity barriers) and Q5 (relativization / natural-proofs
  strengthenings) are unfilled.  Cost is low (LLM-driven
  literature scan with verification), value is bounded but
  non-zero.  Operator may dispatch Q2 and Q5 in parallel with
  Family A.
* **Magnification path priming:**
  `pnp4/Pnp4/Frontier/CompressionMagnification.lean` and
  `SearchMCSPMagnification.lean` are ready to receive a weak
  lower bound package.  No active candidacy is queued.  This
  is independent of FP-3b.2 and can run on its own timeline.
  Operator recommendation: do not pre-stage FP-4 / magnification
  package work until FP-3b.2 (Family A) lands or definitively
  closes.

## 8. Decision matrix

| Outcome of Family A dispatch | Operator next action |
| --- | --- |
| All Phase-2 deliverables land green | Operator review for `ProvenanceFilter_v1` accepted-status promotion.  If approved, opens FP-4 bridge work. |
| Phase-2 surfaces a Local closure | Identify the failure mode, patch the filter or replace.  Up to 2 retries before declaring `Local` exhausted. |
| Phase-2 surfaces a Global closure (NOGO-000010) | Distinguisher-matrix audit route closes.  Fallback to Family B. |
| Family A meta-barrier identified analogous to NOGO-000009 | Strategic re-audit; possibly the entire semantic-filter design family closes; pivot to Family C bounded-arithmetic OR to magnification path / external research. |

## 9. Lessons learned (for future strategic audits)

* **Audit before dispatch.**  This strategic audit costs ~1-2
  operator-days; expected to save 4-12 engineer-weeks of
  Phase-2 dispatch effort that would otherwise be spent on
  Families D / E / F (closed by triage here).
* **first_move scan inputs are high value.**  Q1/Q3/Q4
  collectively provided three barrier-aware design seed families.
  Without them, this audit would have brainstormed candidates
  ad hoc and might have missed the distinguisher-matrix
  literature foundation (Atserias-Müller 2025 is post-V2-closure
  era; would not have been discovered without targeted scan).
* **Closure constraints accumulate.**  After V2 closure, the
  design space for FP-3b.2 is narrower than for the original
  FP-3.  Each closed NOGO adds a constraint; the audit's
  C1-C8 constraint set is the current closure-residue.
* **Barrier-interface families have intrinsic research value.**
  Even if Family A's specific filter design closes, the
  distinguisher-matrix barrier-interface infrastructure
  (analogous to `Barrier/Relativization.lean` etc.) is itself a
  research artifact.  Operator should plan the Family A
  dispatch to leave behind a clean barrier-interface module
  regardless of whether the filter promotes.

## 10. Audit-only scope confirmation

This audit writes nothing to:
* `outputs/nogolog.jsonl` (no new NOGO).
* `outputs/attempts.jsonl`.
* `spec/known_guards.toml` (no `ProvenanceFilter_v1` promotion;
  `ProvenanceFilter_v1` remains reserved name with no Lean
  artifact).
* Any Lean module.
* Any existing seed pack.

No `accepted` promotions.  No FP-4 implications.  No final
endpoint implications.  No P ≠ NP claims.  The audit is
governance-scope only.

## 11. Cross-references

* V2 closure retrospective:
  `seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/v2_family_closure_retrospective.md`.
* fp3b3 priority refresh consolidation:
  `seed_packs/fp3b3_priority_refresh/audits/priority_refresh_operator_consolidation.md`.
* fp3b3.4 M2 operator review:
  `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/audits/M2_operator_review.md`.
* first_move adjacent-area scans:
  * Q1: `seed_packs/first_move_search_2026/reports/gpt55/Q1_bounded-arithmetic-unprovability.md`.
  * Q3: `seed_packs/first_move_search_2026/reports/gpt55/Q3_descriptive-nonnatural-filters.md`.
  * Q4: `seed_packs/first_move_search_2026/reports/gpt55/Q4_distinguisher-matrix-magnification.md`.
* FixedParams Probe spec: `FixedParams_Probe.md`
  (§3.B promotion criteria, §8.6 FP-4 gate, §8.7 non-vacuity
  obligation).
* Known guards registry: `spec/known_guards.toml`
  (`[guards.ProvenanceFilter_v1]` reserved name,
  `[guards.HardwiringGuard]` accepted but not
  standalone-factorization-target,
  `[guards.ProvenanceFilter_v2]` closed via NOGO-8/9).
* NOGO log: `outputs/nogolog.jsonl`
  (NOGO-000006/7/8/9 are the active closure constraint set).
* Magnification framework:
  * `pnp4/Pnp4/Frontier/CompressionMagnification.lean`.
  * `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`.
  * `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean`.
* RESEARCH_CONSTITUTION.md Rules: 0 (audit-only), 1 (no
  sorry/admit), 9 (append-only JSONL), 12 (natural-proofs
  discipline), 16 (no typeclass payload).

## 12. Closing note

This audit is intentionally conservative.  The "intuitive"
candidates after V2 closure (Families D, E, F) are deprioritized
not because they cannot work in principle but because the
audit's six-family triage finds three families with stronger
literature foundations and tighter closure-constraint
compatibility.

If the operator disagrees with the recommendation (e.g.,
prefers Family C's high-variance reserve as the primary
dispatch, or wants to revisit Families D/E/F under a different
design constraint), this audit is the input — not the binding
decision.  The operator's override pattern (analogous to the
fp3b3_4 M1 override that opened the meta-barrier track ahead of
`Global` classification) is fully respected; any override should
be documented with the override-reasoning per the standard
governance protocol.

**Recommended next operator action:** approve Family A dispatch,
draft `seed_packs/fp3b6_distinguisher_matrix_provenance/README.md`
and `WORKER_PROMPT.md`, dispatch Phase-1 sketch worker.
