# Stream X V2 family — closure retrospective

**Audit subject:** the full V2 audit-route design family for
`ProvenanceFilter_v2` (V2-A, V2-A.1, V2-A.2, V2-B, V2-D).
**Operator decision:** **CLOSED for accepted-status promotion.**
The syntactic-only V2 audit-route family is formally exhausted by
the NOGO log and the priority refresh consolidation; further
dispatches in this family are below operator threshold for
expected value.

This is operator-scoped retrospective documentation — not a worker
artifact, not a new dispatch, not a barrier theorem.  It
consolidates the V2 family arc and explicitly hands the next
session a clean closure point.

## 1. Episode arc (chronological)

| Stream X stage | Pack | Outcome |
| --- | --- | --- |
| Phase-1 design search | `fp3b3_provenance_filter_v2_design` | V2-A through V2-D candidate sketches; V2-A elected as Phase-2 survivor. |
| V2-A natural-proofs self-test | `fp3b3_1_v2a_natural_proofs_self_test` | V2-A confirmed non-extensional; `representation_sensitive_escape_plausible` classification. |
| V2-A adversarial robustness | `fp3b3_2_v2a_adversarial_robustness` | **NOGO-000008** lands: tautological seed rewrite circumvents V2-A's syntactic exclusion. |
| V2-A.1 minimal normalisation patch | `fp3b3_3_v2_a_1_minimal_normalisation` | Two `Local` T1 failures (g55, g55r1).  Parallel `fp3b3_4` opens. |
| V2-A normalise meta-barrier | `fp3b3_4_v2_a_normalise_meta_barrier` | M1 candidate (m1nova) + M2 Lean theorem land **NOGO-000009**.  V2-A.1 design space formally closed. |
| Successor priority refresh | `fp3b3_priority_refresh` | V2-A.2 → meta-review-only; V2-B → hold for non-vacuity; V2-D → rejected (non-vacuity false on De Morgan basis). |
| Episode closure | this retrospective | V2 family CLOSED for `accepted` promotion. |

## 2. What the closure means (and doesn't mean)

### What is closed

* **V2-A** as a Phase-2 survivor remains an in-tree audit-only
  object (`informal` registry status), but `accepted`-status
  promotion is **formally blocked** by NOGO-000008 +
  NOGO-000009 + the priority refresh consolidation.
* **V2-A.1** structural-normalisation patch space is closed by
  the kernel-checked meta-barrier theorem
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean::v2_a_structural_normalisation_meta_barrier`
  and NOGO-000009.
* **V2-A.2 full / minimal semantic quotient** variants are
  blocked pending explicit Natural Proofs bypass plans;
  operator default is to **not** open proof-oriented seed packs
  for these.
* **V2-B** Phase-2 dispatch is held on non-vacuity grounds —
  the current sketch is effectively a parity recogniser.
* **V2-D** is rejected as a route (defeated by adaptive
  NOGO-000008-style padding + bogus non-vacuity claim).
* The broader syntactic-only V2 design family is closed for
  `accepted`-status promotion.  NOGO-000008 alone closes
  "syntactic-only exclusion is circumventable by tautological
  rewriting"; NOGO-000009 + priority refresh close all known
  natural patches.

### What is NOT closed

* **V2-A.2 partial rule-generated quotient** remains a possible
  future direction (under explicit Natural Proofs audit
  obligation); operator decision is **dispatch_only_meta_review**
  if pursued.  Suggested seed pack name recorded:
  `seed_packs/fp3b3_5_v2_a_2_partial_quotient_metareview/`.
* **V2-B non-vacuity refresh** remains a possible future
  direction; operator decision is **hold** indefinitely.
  Suggested seed pack name recorded:
  `seed_packs/fp3b3_5_v2_b_cross_length_nonvacuity_refresh/`.
* **Non-V2 audit-route families** (semantic complexity
  invariants, externally-witnessed provenance, audit-route
  categories not yet sketched) are not within the scope of this
  closure.  They are open for future research, but no operator
  dispatch is queued.
* **Mainline FP-3 / FP-4 work** is independent of this closure.
  The FixedParams Probe path to Outcome B does not require an
  `accepted` ProvenanceFilter_v2 guard; HardwiringGuard remains
  the formalised Outcome A guard, and Outcome B requires a
  different guard family per `FixedParams_Probe.md` §3.B.

## 3. The "soft hold" doctrine

The two suggested follow-on seed pack names are recorded as
**soft holds**, not as scheduled dispatches:

```
fp3b3_5_v2_a_2_partial_quotient_metareview/      ← V2-A.2 partial variant
fp3b3_5_v2_b_cross_length_nonvacuity_refresh/    ← V2-B non-parity search
```

Neither directory exists; neither has a worker prompt.  Soft
holds mean: a future operator (human or LLM session) who wants
to revisit V2-* family work has a precomputed starting point and
the priority refresh consolidation as context, but no commitment
to dispatch.  Closing this episode does **not** delete the soft
holds.

## 4. Forward-looking notes for next session

These are informational, not actions in this commit.

### Audit-route candidates outside V2 family

* **Non-syntactic provenance.**  No formal predicate sketched.
  Would require new design work starting from "what semantic
  invariant distinguishes honest families from hardwiring
  payloads without requiring extensionality or syntactic
  matching?".  Higher uncertainty than V2-A.2-partial.
* **Cross-language provenance.**  V2-B touched cross-length
  semantics; cross-language (e.g. closure under reductions)
  semantics is unexplored.
* **Externally-witnessed provenance.**  Provenance carried by
  an explicit construction object alongside the witness, not
  inferred from the witness.  Outside the InPpolyFormula
  type but possibly definable as an extension.

### Mainline tracks

* **FP-3 / FixedParams Probe.**  Continuation does not require
  V2-* work.  Outcome A is formally satisfied by
  `HardwiringGuard`; Outcome B requires a different accepted
  guard, which V2-* now provably cannot supply.
* **FP-4.**  Per `FixedParams_Probe.md`, FP-4 is the next stage
  after FP-3's reduction lands.  Pre-staging FP-4 work in
  parallel with FP-3 is operator discretion.

### Recommendations (operator informal, NOT a commitment)

1. **Default next move:** pivot to a non-V2-family stream.
   Whichever of FP-3 mainline, Stream Y, Stream Z, or
   non-syntactic provenance work has the highest operator
   priority.
2. **Re-engaging V2 family** is only worth doing under one of
   these conditions: (a) a new design idea outside the current
   syntactic / quotient / cross-length / shape signature
   categories surfaces; (b) external research progress (e.g.
   new natural-proofs bypass machinery) makes V2-A.2 partial
   tractable; (c) the FP-3 / FP-4 mainline reaches a state where
   an audit-only `informal` V2 guard would unblock something
   concrete.
3. **Soft holds are cheap.**  Operator should resist the temptation
   to delete the suggested fp3b3_5_* names just to enforce
   closure tidiness.  The cost of leaving them as documentation
   is zero; the value if anyone returns is non-zero.

## 5. Lessons learned (for future audit-route design)

* **Specification consistency.**  g55's first attempt surfaced a
  spec inconsistency (HARD-minimum lemmas force a derivation not
  listed as HARD-minimum).  Lesson: lemma surfaces should be
  closed under specialisation **before** dispatch.  Future seed
  packs should include a "specification consistency check" as a
  pre-dispatch operator gate.
* **Parallel meta-barrier track is cheap insurance.**  fp3b3_4
  M1 was operator-opened ahead of `Global` classification per a
  soft override (audit §5(B) of `T1_g55_operator_audit.md`).
  The override paid off: M1 surfaced the closure argument before
  T1 retries could accumulate.  Lesson: when a worker ships
  `Local` failure but the failure mode hints at a structural
  issue, opening a parallel meta-barrier track is cheaper than
  serial retries.
* **Operator-level closure beats worker `Global` classification.**
  The fp3b3_3 design space was closeable directly from its own
  §T2 scope rule + the verified Lean facts, without needing a
  worker to ship `Global` obstruction.  Operator review
  consolidating the M1 candidate + Lean trust-root facts +
  the seed pack's own published spec was sufficient.  Lesson:
  the §10 negative-pivot protocol's `Global` gate is a sanity
  guard, not a strict prerequisite — operator reviews with
  trust-root verification can supersede it when the closure is
  operator-level reachable.
* **NOGO entries should be Lean-backed.**  NOGO-000009 was
  deferred until M2 Lean formalisation landed; NOGO-000010 (V2-D
  closure) was **not** added because no Lean theorem formalises
  the V2-D adaptive attack.  Lesson: NOGO entries codify
  research findings at Lean-kernel quality.  Markdown-grade
  findings stay in operator reviews; they upgrade to NOGO only
  when a Lean theorem lands.
* **Priority refresh after every NOGO landing.**  After
  NOGO-000009 closed V2-A.1, the priority refresh quickly
  triaged V2-A.2 / V2-B / V2-D as a batch.  Lesson: whenever a
  NOGO closes a meaningful design subspace, a short priority
  refresh dispatch is high-value — it prevents future operators
  from re-litigating closed routes.

## 6. Cross-references

* NOGO log: `outputs/nogolog.jsonl` lines 8 (NOGO-000008) and 9
  (NOGO-000009).
* Lean barriers:
  * `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean::v2A_rewrite_attack_prefixAnd`
    (NOGO-000008 formal witness).
  * `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean::v2_a_structural_normalisation_meta_barrier`
    (NOGO-000009 formal witness).
* Operator reviews:
  * `V2_A_gpt55_promotion_review.md` (V2-A six-attack re-review).
  * `fp3b3_1_and_fp3b3_2_landing_review.md` (V2-A self-test +
    rewrite attack landing).
  * `../../../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_g55_operator_audit.md`
    (V2-A.1 attempt #1 audit).
  * `../../../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_retry_pause_post_M1.md`
    (V2-A.1 pause + meta-barrier early opening).
  * `../../../fp3b3_4_v2_a_normalise_meta_barrier/audits/M1_m1nova_operator_review.md`
    (M1 candidate review).
  * `../../../fp3b3_4_v2_a_normalise_meta_barrier/audits/M2_operator_review.md`
    (M2 Lean theorem operator review).
  * `../../../fp3b3_priority_refresh/audits/priority_refresh_operator_consolidation.md`
    (V2-A.2 / V2-B / V2-D triage).
* Worker failure reports:
  * `../../../fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55.md`
  * `../../../fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55r1.md`
* Soft holds (suggested but not opened):
  * `seed_packs/fp3b3_5_v2_a_2_partial_quotient_metareview/`
  * `seed_packs/fp3b3_5_v2_b_cross_length_nonvacuity_refresh/`
* Spec registry:
  * `spec/known_guards.toml` `[guards.ProvenanceFilter_v2]`
    (status `informal`, with closure cross-references updated
    in the same commit as this retrospective).

## 7. Audit-only scope confirmation

This retrospective writes to:
* `spec/known_guards.toml` (V2-A audit field cross-refs updated
  in the same commit; status stays `informal`).

This retrospective writes nothing to:
* `outputs/nogolog.jsonl` (no new NOGO).
* `outputs/attempts.jsonl`.
* Any Lean module.
* Any V2-A / V2-A.1 / V2-A.2 / V2-B / V2-D / V2-A.NormaliseMetaBarrier
  file.

No `accepted` promotions.  No new candidates.  No FP-4 implications.
No final-endpoint implications.  No P ≠ NP claims.  The closure
is local to the V2 audit-route design family.

## 8. Closure timestamp

Stream X V2 episode closure recorded 2026-05-13.
