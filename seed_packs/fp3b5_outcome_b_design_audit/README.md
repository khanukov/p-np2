# fp3b5 — Outcome B design strategic audit

## 0. TL;DR

Operator-grade strategic audit for FP-3b.2 filter design, opened
after the V2 audit-route family closure (2026-05-13).  Synthesises:

* V2 closure constraints (NOGO-000007 / 000008 / 000009 + priority
  refresh consolidation).
* `first_move_search_2026` adjacent-area scan outputs (Q1
  bounded-arithmetic unprovability, Q3 descriptive non-natural
  filters, Q4 distinguisher-matrix magnification).
* Mainline FP-3 obligation: strengthen / replace
  `InSupportFunctionalDiversity` to formally exclude NOGO-000006
  arbitrary log-width truth-table hardwiring without falling into
  NOGO-7/8/9.

**Audit outcome:** see
`audits/outcome_b_strategic_audit.md` for the triage of
candidate design families and the operator recommendation.

This pack is **strategic / meta-review**.  It produces no Lean,
no candidate package, no `SourceTheorem`, no `gap_from_*`, no
`ResearchGapWitness`, no FP-4 surface, no `accepted` promotion,
no final endpoint.

## 1. Why this pack exists

After NOGO-000008 + NOGO-000009 closed the syntactic-only V2
audit-route family, the FP-N mainline faces the same design
problem on the FP-3b.2 filter strengthening track: any candidate
`ProvenanceFilter_v1` (the reserved `accepted`-promotable guard
name) must exclude NOGO-000006 arbitrary log-width TT hardwiring
while satisfying:

* not support-cardinality-only (NOGO-000007);
* not syntactic-only and circumventable by tautological rewriting
  (NOGO-000008);
* not self-defeating under context-uniform bottom-up structural
  normalisation (NOGO-000009);
* non-vacuous: at least one honest formula family admitted;
* non-tautologous: `accepted`-promotable per
  `FixedParams_Probe.md` §3.B requires either `Π ↔
  KnownGuardCombination` OR `Π → ExistingKnownGuard` with
  `standalone_factorization_target = true`.

The V2 closure pattern (5+ candidates closed across NOGOs
7/8/9) shows that "intuitive" syntactic filter designs do not
survive.  This pack triages candidate design families **before**
committing to a Phase-2 seed pack dispatch, applying the same
rigorous-discipline pattern that produced clean V2 closures.

The expected output is one of:

* **Recommend dispatch:** open a specific successor seed pack
  (suggested name `fp3b6_<design_family>/`) with a particular
  filter design family that the audit identifies as having
  highest expected value.
* **Recommend hold / pivot:** if no candidate family survives
  the closure constraints with credible non-vacuity, recommend
  pivot to alternative research direction (magnification path,
  external-mathematics-driven, etc.).

## 2. Dispatch model

This pack uses the **operator-direct audit** model:

* The audit document at `audits/outcome_b_strategic_audit.md`
  is operator-grade synthesis (analogous to the M2 operator
  review pattern from fp3b3_4).
* No worker prompt is dispatched in this round.  Operator
  integrates existing context (V2 closure trail + first_move
  Q1/Q3/Q4 reports + repo trust-root facts) directly.
* `reports/` is reserved for any subsequent independent worker
  audit that the user might dispatch to challenge or extend the
  operator audit.  Empty at landing.

If the user later wants an independent worker perspective, the
suggested dispatch would be: a single-handle markdown audit
running the same triage on the same closure constraints, with
operator's recommendation withheld from the worker's input to
preserve independence.

## 3. Allowed / forbidden scope

### Allowed

* Markdown audit document under `audits/`.
* Reading any existing file in the repo.
* Citing Lean line numbers from `pnp3/` / `pnp4/`.
* Citing NOGO entries, spec/known_guards.toml entries,
  RESEARCH_CONSTITUTION.md rules.
* Citing first_move_search_2026 reports (with verification
  that the cited content matches the referenced report).

### Forbidden (HARD)

* Lean file creation or edits.
* `outputs/nogolog.jsonl` writes.
* `outputs/attempts.jsonl` writes.
* `spec/known_guards.toml` writes (no `ProvenanceFilter_v1`
  promotion).
* Trust-root edits.
* V2-A / V2-A.1 / V2-B / V2-D / V2_A_NormaliseMetaBarrier
  Lean module edits.
* `Candidates/` creation.
* `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / final
  endpoint / P ≠ NP language.
* `accepted`-status promotion of any guard.

## 4. Pack status

**OPEN — strategic audit landed; dispatch decision pending operator.**

The audit document at `audits/outcome_b_strategic_audit.md`
contains the operator recommendation and the suggested follow-on
seed pack name.  The user reads the audit and either:

(a) approves the recommendation → opens the follow-on seed pack
    in a separate session;
(b) overrides with a different design family → opens a different
    follow-on seed pack;
(c) holds → leaves this pack as documentation, defers FP-3b.2
    track in favour of magnification path or other priority.

This pack stays in-tree as durable strategic documentation
regardless of the next dispatch decision.

## 5. Cross-references

* V2 closure retrospective:
  `../fp3b3_provenance_filter_v2_design/operator_reviews/v2_family_closure_retrospective.md`
* fp3b3 priority refresh:
  `../fp3b3_priority_refresh/audits/priority_refresh_operator_consolidation.md`
* fp3b3.4 M2 review:
  `../fp3b3_4_v2_a_normalise_meta_barrier/audits/M2_operator_review.md`
* first_move adjacent-area scans:
  `../first_move_search_2026/reports/gpt55/Q1_bounded-arithmetic-unprovability.md`
  `../first_move_search_2026/reports/gpt55/Q3_descriptive-nonnatural-filters.md`
  `../first_move_search_2026/reports/gpt55/Q4_distinguisher-matrix-magnification.md`
* FixedParams Probe spec: `FixedParams_Probe.md`.
* Known guards registry: `spec/known_guards.toml`.
* NOGO log: `outputs/nogolog.jsonl` (NOGO-000006 through 000009
  are the active constraint set for this audit).
