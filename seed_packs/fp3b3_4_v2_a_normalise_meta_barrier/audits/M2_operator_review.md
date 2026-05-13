# M2 operator review (V2_A_NormaliseMetaBarrier/Barrier.lean)

**Review subject:** `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean`
**Worker landing commit context:** `186bffc` (merged via PR #1242 → `4399636`).
**Outcome:** **APPROVE M2 LANDING.**  V2-A.1 design space is now
**formally closed** by a kernel-checked Lean theorem.

This is **operator-scoped review** — not a worker artifact.

## 1. Build verification

* `lake build PnP3 Pnp4` — **GREEN**.  3087 modules built;
  `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_NormaliseMetaBarrier.Barrier`
  is the new module (step 3086/3087).
* `./scripts/check.sh` — **PASS_SHAPE_ONLY** across 17/17 steps,
  including the post-NOGO-000009 append (see §5 below).
* `lakefile.lean:173` wires the new module under the existing
  `Glob.one ...` list.
* Smoke test under `pnp3/Tests/` was OPTIONAL per WORKER_PROMPT
  §3; worker did not add one.  Acceptable.

## 2. Scope compliance — no forbidden constructs

`grep -nE "sorry|admit|axiom|opaque|Fact |Classical\."` against
`Barrier.lean` returns **zero matches**.  The Lean module uses
only:

* `propext`, `Classical.choice`, `Quot.sound` — these are
  Mathlib's standard axiom backbone (visible in pnp3/pnp4
  `AxiomsAudit` summaries: 362 / 358 / 362 occurrences in pnp3,
  152 / 141 / 141 in pnp4).  Adding the new module did not
  change these counts.
* No `axiom` declarations of its own.
* No `opaque`, no `Fact`-typeclass-payload.
* No `sorry` / `admit`.
* No `Classical.choose` anywhere.
* No truth-table reconstruction in the proof (which would have
  been incoherent — the meta-barrier is precisely about ruling
  out such proofs for the normaliser class).

Forbidden-scope rules per `WORKER_PROMPT_M2.md` §4 are all
honoured.  No V2-A trust-root edits, no fp3b3_3 edits, no
edits to existing JSONL log entries (NOGO-000009 append is
operator-scope, not worker-scope).

## 3. Theorem signature verification

```lean
theorem v2_a_structural_normalisation_meta_barrier
    (𝒩 : StructuralNormaliser)
    (hSeed : ∀ {n : Nat} (h : 1 ≤ n),
      𝒩.normalise (seedGate n h) = FormulaCircuit.const true)
    (hAndTrue : ∀ {n : Nat} (C : FormulaCircuit n),
      𝒩.ops.mkAnd C (FormulaCircuit.const true) = C) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter
        (normalisedWitness 𝒩 seededPrefixAndWitness)
```

(Barrier.lean:268-275.)  Reads as: any structural normaliser
in the local-fold class that satisfies fp3b3_3 §3 T1 HARD-minimum
seed elimination (`hSeed`) and `mkAnd C (const true) = C` reduction
(`hAndTrue`) is rejected by V2-A's filter on V2-A's own seeded
non-vacuity witness.

**Hypothesis form note (audit):** the worker correctly used the
WORKER_PROMPT-specified hypothesis form
`𝒩.ops.mkAnd C (const true) = C` (uniform in `C`).  This is a
slightly stronger condition than fp3b3_3 §3 T1 HARD-minimum #5
which was stated specialised:
`canonicalNormalise (and c (const true)) = canonicalNormalise c`.
Under `𝒩.normalise_eq_fold`, the specialised form translates to
`𝒩.ops.mkAnd (foldFormula 𝒩.ops c) (const true) = foldFormula 𝒩.ops c`
— uniform only over **folded** `c`.  The uniform form (over
**all** `c`) implies the specialised form but not conversely.

In practice the gap is zero: any natural structural simplifier
implements `mkAnd` as a local function independent of whether
the input was folded (this is exactly what g55r1's attempted
`normaliseAnd` did — see `seed_packs/fp3b3_3_*/failures/T1_g55r1.md`
lines 80-91).  So the meta-barrier's reach covers the intended
T1 normaliser class.  The operator notes this for completeness;
it does not weaken the closure.

## 4. Proof structure verification

The 12-step proof outline specified in WORKER_PROMPT_M2.md §2.3
was followed.  Key load-bearing lemmas, with line refs:

* `foldFormula_eval` (Barrier.lean:75-83) — semantic preservation
  by structural induction.  4 cases, simp-driven.
* `normalise_eval` (Barrier.lean:86-90) — via `normalise_eq_fold`.
* `foldFormula_size_le` (Barrier.lean:93-109) — size non-increase
  by induction + `omega` on per-constructor size bounds.
* `foldFormula_prefixAnd_orGateCount_zero` / `_notGateCount_zero`
  (Barrier.lean:131-148) — induction on `k`, using the operator-required
  `mkAnd_orGateCount_pres` / `notGateCount_pres` fields.
* **Support at `n = 2`** (Barrier.lean:150-207) — concrete computation:
  the worker built test inputs `allTrue2` and `falseAt2 i` for `i ∈ {0, 1}`,
  proved `prefixAnd 2 2` distinguishes them, derived that both
  variables remain in the support of the fold via
  `FormulaCircuit.eval_eq_of_eq_on_support`.  This is the **cleanest
  available** approach — it sidesteps a general
  `support_normalise = support` lemma (which the worker prompt
  permitted as a fallback) in favour of a concrete 2-variable
  computation.  Operator approves the choice.
* `support_normalise_seededPrefixAnd_two`
  (Barrier.lean:210-225) — fold expansion of
  `seededPrefixAndFamily 2 = and prefixAnd seedGate`, application of
  `hSeed` + `hAndTrue` to reduce to `foldFormula prefixAnd`, support
  lower-bound applied.
* `normalise_seededPrefixAnd_two_orGateCount_zero` /
  `_notGateCount_zero` (Barrier.lean:228-261) — same fold-expansion
  pattern + `foldFormula_prefixAnd_*_zero`.
* **Main theorem** (Barrier.lean:268-283) — extracts `hMix` from
  the filter, applies at `n = 2`, gets `hOrPos : 0 < orGateCount ...`,
  rewrites via `hOrZero` and concludes `Nat.lt_irrefl 0 hOrPos`.
  Mirrors the structural pattern of the V2-A
  `excludes_adversaryWitness_v_natlog2` proof at
  `ExcludesPrefixAnd.lean:46-63`, as the WORKER_PROMPT anticipated.

## 5. Sanity-inhabitant

`identity_structuralNormaliser_exists` (Barrier.lean:286-324)
constructs the identity normaliser:
* `mkNot := FormulaCircuit.not`, `mkAnd := FormulaCircuit.and`,
  `mkOr := FormulaCircuit.or`.
* All eval / size / no-invention fields discharged with `rfl` /
  `simp`.
* `normalise := id`, `normalise_eq_fold` proved by structural
  induction.

This witnesses **class non-vacuity** without satisfying the
`hSeed` antecedent (the identity normaliser preserves `seedGate`
unchanged).  The meta-barrier theorem is therefore **not
vacuously true**: there exist `StructuralNormaliser` instances,
just not ones satisfying `hSeed + hAndTrue`.

## 6. NOGO-000009 append

Per the fp3b3_3 pause decision
`audits/T1_retry_pause_post_M1.md` §5, NOGO-000009 was deferred
to post-M2 Lean formalisation.  M2 has landed.  The NOGO entry
has been appended to `outputs/nogolog.jsonl` in the same
coordinated commit as this review:

* `id: NOGO-000009`
* `candidate_id: fp3b3_3_v2_a_1_minimal_normalisation`
* `formal_witness:
  pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean:268`
* `regression_test:` same file.
* `status: formalized`
* `structural_pattern:` "Structural-normalisation patch on
  V2-style syntactic filters is self-defeating: any context-uniform
  bottom-up normaliser that eliminates a displayed tautological
  seed also eliminates the same seed from the filter's own
  non-vacuity witness."
* `why_generalizes:` together with NOGO-000008, closes the
  syntactic-only V2 design family for `accepted`-status
  promotion.  Successor design spaces (V2-A.2 semantic quotient,
  V2-B / V2-D) remain open under their own barrier-audit
  obligations.
* No SourceTheorem, no `gap_from_*`, no `ResearchGapWitness`,
  no candidate package, no final endpoint introduced.

JSONL validation step in `check.sh` step 11 ("jsonl_validation")
passes with the new entry.

## 7. fp3b3_3 archival

The fp3b3_3 seed pack (`seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/`)
is **archived in-tree** as STALLED documentation, not deleted.
Concretely:

* README §10 banner updated from STALLED to **CLOSED** post-M2,
  with cross-reference to NOGO-000009 and to this review.
* `WORKER_PROMPT.md` DISPATCH PAUSED banner remains (now
  permanent — pack is closed).
* All existing audits (`T1_g55_operator_audit.md`,
  `T1_retry_pause_post_M1.md`) and failure reports
  (`T1_g55.md`, `T1_g55r1.md`) remain in-tree as research
  documentation.

No deletion is necessary because the seed pack's audit trail is
itself part of the research artifact — it documents the design
attempt, the operator audit chain, and the meta-barrier closure
in chronological order.

## 8. M3 disposition

M3 (audit-route-suite integration alongside
`SupportCardinalityBarrier`) remains DEFERRED.  Operator decision:
**DO NOT dispatch M3 in this round.**  Reasoning:

* The meta-barrier theorem is already wired into `lakefile.lean`
  and visible in the audit-route filesystem.  M3 would consolidate
  it into a barrier-suite registry (analogous to
  `SupportCardinalityBarrier`'s integration) but this is
  cosmetic — the theorem is already kernel-checked and registered
  via NOGO-000009.
* The Stream X immediate priority shifts to other tracks (V2-A.2
  audit, V2-B / V2-D priority refresh).  Operator-time on M3
  consolidation has lower marginal value.
* M3 can be revisited later as a hygiene pass when the
  audit-route-suite gets a registry refactor.

## 9. Next-stream operator notes (informational)

Post-NOGO-000009 the active design spaces for
ProvenanceFilter_v2 audit-route candidates are:

* **V2-A.2 (semantic quotient).** Trades structural normalisation
  for semantic equivalence quotient.  Carries natural-proof
  exposure that V2-A.1 was explicitly designed to avoid.  Before
  dispatching, requires a natural-proofs risk audit analogous to
  the V2-A self-test at
  `pnp3/.../V2_A_gpt55/NaturalProofsSelfTest/RepresentationSensitivity.lean`.
* **V2-B / V2-D successor surfaces.** Alternative Phase-2 survivor
  designs from the original fp3b3 search; none of these have
  shipped formal predicates yet.  Operator priority refresh
  recommended before opening new seed packs.
* **Stream Y / Z continuations.** Independent of V2 design; no
  V2-barrier blockers.

No new seed pack is opened in this commit.  Operator may dispatch
V2-A.2 audit, V2-B / V2-D design refresh, or another stream as a
separate session decision.

## 10. Audit-only scope confirmation

This review writes to:
* `outputs/nogolog.jsonl` (NOGO-000009 append — per pause
  decision §5, this is operator-scope).

This review writes nothing to:
* `outputs/attempts.jsonl` (no attempt registry update needed).
* `spec/known_guards.toml` (no V2-A.1 entry was ever promoted;
  V2-A's existing entry remains `informal` per its current
  status).
* Any V2-A Lean module.
* The trust root.

No `accepted` promotions.  No FP-4 implications.  No
final-endpoint implications.  No P ≠ NP claims.  The closure
is **local to FP-N filter design**.

## 11. Cross-references

* M2 Lean file:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean`
  (330 LOC, single module).
* M2 worker commit: `186bffc` (merged via PR #1242 → `4399636`).
* M1 candidate: `candidates/M1_m1nova.md`.
* M1 operator review: `audits/M1_m1nova_operator_review.md`.
* fp3b3_3 pause decision:
  `../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_retry_pause_post_M1.md`.
* fp3b3_3 g55 initial audit:
  `../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_g55_operator_audit.md`.
* fp3b3_3 g55 + g55r1 failure reports:
  `../fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55.md`
  and `T1_g55r1.md`.
* NOGO-000009 entry: `outputs/nogolog.jsonl` line 9.
* Sibling barrier (template for the registration style):
  `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`.
* Predecessor NOGO entries:
  * NOGO-000008 (V2-A syntactic-only filter circumvented by
    rewrite attack) — fp3b3_3 was the patch attempt.
  * NOGO-000007 (support-cardinality barrier) — earlier audit-route
    closure.
