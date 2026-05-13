# fp3b3_3 T1 retry track — PAUSE decision post-M1

**Decision subject:** g55r1 T1 retry failure
(`failures/T1_g55r1.md`) + M1 meta-barrier finding
(`../fp3b3_4_v2_a_normalise_meta_barrier/candidates/M1_m1nova.md`,
operator review at
`../fp3b3_4_v2_a_normalise_meta_barrier/audits/M1_m1nova_operator_review.md`).
**Operator decision:** **PAUSE the fp3b3_3 T1 retry track.**
**Status of fp3b3_3 seed pack:** STALLED pending M2 meta-barrier
Lean formalisation OR explicit V2-A.1 redesign decision.

This is **operator-scoped governance** — not a worker artifact.

## 1. Summary of state after g55r1 + M1

* g55r1 T1 retry (commit `c6b63d7` / PR #1240) shipped a `Local`
  failure report.  Worker followed the canonical-output invariant
  recipe but hit a proof-engineering wall on local AND/OR identity
  lemmas (`normaliseAnd (canonicalNormalise c) (const true) =
  canonicalNormalise c` needs abstract-canonical-term helper
  lemmas before instantiation).  Failure is fixable with the
  factoring recipe in `T1_g55r1.md` §4 — a third T1 attempt
  could in principle land syntactically.

* M1 meta-barrier candidate by m1nova (commit `8c45586` /
  PR #1241) recommended `PROCEED to M2`.  Operator review
  promoted M1 and verified the argument against trust-rooted
  Lean files (`NonVacuity.lean:36-40`,
  `ExcludesPrefixAnd.lean:29-43`).

* **Critical synthesis:** the meta-barrier observation is
  reachable **directly from the seed pack's published spec** —
  not just from m1nova's fold class.  Specifically, any T1
  attempt satisfying the HARD-minimum reductions (post-g55 patch,
  README §3 T1) forces `canonicalNormalise (seededPrefixAndFamily
  n) ≠ seededPrefixAndFamily n` for `n ≥ 1`, with the normalised
  witness collapsing to `canonicalNormalise prefixAnd` which has
  zero OR + zero NOT gates.  V2-A's mixed-gate clause at `n ≥ 2`
  then forces V2-A.1's filter (T2) to reject the normalised
  seeded witness — i.e. `v2A_1_admits_seededPrefixAndWitness` is
  **false**.

## 2. Why T1 retry track is paused

The fp3b3_3 README §T2 scope rule (lines 377-388) explicitly
encodes this failure mode and lists only two escapes:

* "**Refine the family**" — requires editing V2-A NonVacuity,
  **forbidden** by fp3b3_3 §4 (V2-A is import-only).
* "**Refine T1**" — requires dropping either `canonicalNormalise_seedGate`
  (kills the NOGO-000008 elimination goal — the whole purpose of
  fp3b3_3) or one of the AND-identity reductions (g55's audit
  confirmed these are derivation-forced from the rest of the
  HARD-minimum surface, so dropping one re-introduces the spec
  inconsistency that g55 already documented).

Both escapes are structurally blocked.  Therefore additional T1
retries — no matter how syntactically clean — cannot resolve the
T2 design-space closure.  Dispatching `g55r2` / `<other>r1` /
etc. is **wasted compute**.

## 3. Status of the fp3b3_3 seed pack

* **Round 1 T1 retry:** **PAUSED**.  No new retry dispatch.
  g55r1's failure report stays in-tree as the most recent
  attempt artifact.
* **Round 1 T2:** **PAUSED**.  T2 was already gated on T1; now
  paused for design-space reasons regardless of T1 status.
* **Round 2 T3 / T4 / T5:** **PAUSED**.  Already gated on T1+T2
  landing.
* **Seed pack archival status:** NOT YET archived.  Status is
  STALLED pending M2 Lean formalisation of the meta-barrier
  theorem (which would tighten the operator-level closure into
  a published theorem and trigger archival), OR explicit
  operator decision to redesign V2-A.1 with a different
  non-vacuity witness / filter shape (which would re-open
  fp3b3_3 under a new dispatch round with revised T1/T2 specs).

## 4. What about the fixable T1 proof-engineering issue?

g55r1's failure is `Local` and the recipe in `T1_g55r1.md` §4
(factor abstract-canonical-term helper lemmas, then instantiate)
would plausibly land T1 syntactically.  Operator decision:

* **Do NOT dispatch a third T1 retry now.**  Even if T1 lands,
  T2 cannot prove the required non-vacuity (see §2).
* **Preserve the g55r1 lessons for any future re-dispatch.**  If
  fp3b3_3 is later re-opened under a redesigned T1/T2, the
  g55r1 factoring recipe should be added to WORKER_PROMPT §2A
  as a third load-bearing finding (alongside g55's two).

## 5. What about NOGO-000009?

The natural successor question: should this design-space closure
be recorded as a new NOGO entry?

Operator decision: **NOT YET.**  The argument is currently
markdown-grade (M1 candidate + this operator review verifying it
against Lean trust-rooted facts).  NOGO-grade entries should be
backed by Lean theorems.  Wait for M2 to formalise the meta-barrier
theorem, then add NOGO-000009 alongside M2's landing.

If M2 fails to formalise the meta-barrier (e.g. the
`NoInventsMixedGatesOnAndOnly` field turns out to be more delicate
than M1 estimated), the operator may revisit whether to add a
NOGO-000009 anyway based on the operator-level argument — but the
default is "wait for M2".

## 6. Decision matrix going forward

After M2 dispatch:

* **M2 lands meta-barrier theorem** → add NOGO-000009 (V2-A.1
  design-space closed by structural-normalisation meta-barrier),
  archive fp3b3_3, plan V2-A.2 / V2-B / V2-D priority refresh.
* **M2 fails: meta-barrier statement turns out vacuous or too
  narrow** → M2 worker ships `no-viable-statement` failure, operator
  re-audits.  Two sub-options: (a) refine class formalisation and
  re-dispatch M2; (b) accept that the design-space closure is
  operator-level-only (no Lean theorem) and re-open fp3b3_3 with
  revised non-vacuity witness.
* **M2 surfaces a counterexample to the meta-barrier** → operator
  re-audits the operator-level argument in this document, finds
  the flaw, and either resumes fp3b3_3 T1 retry (if the flaw
  invalidates §2's reasoning) or refines the meta-barrier class
  to exclude the counterexample (if the flaw is in M1's class
  formalisation).

Operator dispatches M2 in the same coordinated commit as this
decision.

## 7. Why this is operator decision, not waiting for explicit
   `Global` classification

The seed pack's §10 negative-pivot protocol gates the meta-barrier
pivot on a worker shipping `Global` obstruction classification.
g55r1's failure is `Local`.  Strict protocol reading: this
document overrides §10.

Justification for the override:
* The meta-barrier observation is **operator-level reachable**
  from the seed pack's own §T2 scope rule plus the verified
  Lean facts (review §2).  Waiting for a worker to ship `Global`
  on a T1 retry that itself succeeds syntactically would mean
  pretending we don't already know T2 is structurally blocked.
* The §10 protocol's purpose is to prevent premature pivots on
  shallow local failures.  Here the pivot is justified by a
  separate research track (fp3b3_4 M1) that did its job
  precisely as intended — surface the meta-barrier hypothesis,
  let operator audit verify it.
* The override is documented (this section), reversible if M2
  fails, and does not modify §10 for future dispatches.

## 8. Cross-references

* g55r1 failure: `failures/T1_g55r1.md`
* g55r1 worker commit: `c6b63d7` (merged via PR #1240).
* M1 candidate: `../fp3b3_4_v2_a_normalise_meta_barrier/candidates/M1_m1nova.md`
* M1 worker commit: `8c45586` (merged via PR #1241).
* M1 operator review: `../fp3b3_4_v2_a_normalise_meta_barrier/audits/M1_m1nova_operator_review.md`
* Verified Lean facts:
  * `pnp3/.../V2_A_gpt55/NonVacuity.lean:24-40` (seedGate +
    seededPrefixAndFamily structure)
  * `pnp3/.../V2_A_gpt55/ExcludesPrefixAnd.lean:29-43`
    (prefixAnd zero OR + zero NOT)
  * `pnp3/.../V2_A_gpt55/ExcludesPrefixAnd.lean:46-63` (V2-A
    mixed-gate clause contradicts zero OR at support ≥ 2)
* Initial T1 g55 audit (pre-M1): `audits/T1_g55_operator_audit.md`.

## 9. Audit-only scope confirmation

This decision writes nothing to:
* `outputs/nogolog.jsonl` (deferred to post-M2; see §5).
* `outputs/attempts.jsonl`.
* `spec/known_guards.toml`.
* Any Lean module.

The decision is governance-scope only.  No `accepted` promotions,
no FP-4 implications, no final-endpoint implications.  No P ≠ NP
claims.  The fp3b3_3 seed pack stays in-tree as STALLED
documentation pending M2.
