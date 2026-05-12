# fp3b3_4 — V2-A normalise meta-barrier (parallel research insurance)

## 0. TL;DR

This seed pack opens a **parallel research track** that
investigates whether there is a formal **meta-barrier theorem**
of the rough shape:

> Any structural syntactic normaliser `normalise : FormulaCircuit
> n → FormulaCircuit n` satisfying eval-preservation,
> size-non-increase, and the V2-A.1 HARD-minimum reduction
> requirements **cannot** simultaneously
>   (a) eliminate the NOGO-000008 tautology seed shape, and
>   (b) preserve V2-A's `seededPrefixAndWitness`-admission as-is,
> within the structural-recursion class
> (no truth-table, no semantic quotient, no `Classical.choose`).

If such a theorem exists and is formalisable, it would close the
V2-A.1 design space and join the audit-route barrier suite
alongside
`pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`,
the natural-proofs / relativization / algebrization classics.

This pack is **not** a "T1 globally failed" pivot under the
fp3b3_3 §10 protocol — that protocol gates the pivot on a
**Global** obstruction classification, and g55's failure was
classified `Local` (audit confirms — see
`../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_g55_operator_audit.md`).
Instead, this pack is **operator-opened research insurance**:
running a meta-barrier exploration in parallel with the
fp3b3_3 retry track is cheap, and the two outcomes are
informative regardless of which lands first.

## 1. Why now (not after Global failure)?

Per fp3b3_3's §10 negative-pivot protocol, the meta-barrier
pack should open only after a worker ships a `Global`
obstruction report.  g55 shipped `Local`, audit confirmed
`Local`.  By that protocol, this pack would not open yet.

Operator overrides for one specific reason: the first T1
dispatch revealed an **internal spec inconsistency** on the
HARD-minimum lemma surface (see audit §1–§2).  That is a
**weak meta-signal** — not structural evidence, but enough that
the operator judges parallel meta-barrier exploration to be
cheaper than a sequence of T1 retries that may each surface
similar spec-evolution costs.

The override is recorded in the audit document at
`../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_g55_operator_audit.md`
§5(B).

## 2. Scope and slot decomposition

This pack is **research-grade exploration** at this stage, not a
full theorem dispatch.  The slots are deliberately exploratory:

### M1 — Formal statement candidate

Produce a **Lean-syntax candidate statement** for the
meta-barrier theorem.  This is a `.md` artifact, not a Lean
proof.  The deliverable answers:

* What is the precise predicate class `StructuralNormaliser` on
  `FormulaCircuit n → FormulaCircuit n` that captures
  "structural syntactic recursion, no truth-table, no choice"
  in Lean-formalisable terms?
* What is the precise non-vacuity / barrier-elimination
  conjunction that the meta-barrier negates?
* Are there candidate statements that **trivially fail**
  (counterexample by hand)?  Are there candidate statements
  that are **trivially true** (vacuous)?  The useful
  statement sits between these.

**Output:** `M1_meta_barrier_statement_<HANDLE>.md` with a
formal Lean-syntax candidate, plus a "what counterexamples did
we check" section.  100–300 LOC of markdown.

### M2 — Proof-strategy sketch

Given a candidate statement from M1 that survives
counterexample analysis, sketch the proof strategy.  Likely
shapes:

* **Adversarial-rewrite argument:** for any structural
  normaliser preserving (b), construct a syntactic variant of
  the rewrite attack family that the normaliser cannot detect
  without violating (a).
* **Pumping / diagonalisation argument:** show the structural
  normaliser's syntactic depth bound interacts with the
  rewrite family's structural variation.
* **Information-theoretic argument:** structural normalisation
  is a finite syntactic transformation; the rewrite family has
  semantic diversity exceeding the normaliser's syntactic
  resolution.

**Output:** `M2_proof_strategy_<HANDLE>.md`.  No Lean code yet.
200–400 LOC of markdown.

### M3 — Minimal Lean attempt

If M1 and M2 land convincingly, attempt a minimal Lean
formalisation of the meta-barrier theorem in:

```
pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean
```

This slot is **only opened by explicit operator dispatch** —
not by worker initiative.  M1 + M2 must be reviewed first.

## 3. What this pack is NOT

* **Not a T2 dependency.**  fp3b3_3 T2 does not depend on
  fp3b3_4 in any direction.  T2 still depends on T1.
* **Not a V2-A.2 dispatch.**  V2-A.2 (semantic quotient) is a
  separate seed pack (`fp3b3_5_*`) that would open only **after**
  this pack lands a meta-barrier theorem **and** natural-proof
  risk review on V2-A.2 clears.
* **Not a `Candidates/` creation.**  This pack creates no
  candidate, no Source theorem, no gap.
* **Not promotion-eligible.**  Meta-barrier theorems (if
  landed) take their own audit-route path; they do not promote
  `ProvenanceFilter_v2` to `accepted` and they do not unlock
  FP-4.

## 4. Forbidden scope (worker dispatch, when it opens)

When M1 / M2 / M3 are dispatched to workers, the forbidden
scope inherits fp3b3_3's hard rules plus:

* No editing fp3b3_3 files (this pack is parallel, not
  successor).
* No editing V2-A files.
* No editing trust-root.
* No `axiom` / `opaque` / `Fact` / `sorry` / `admit` in any
  Lean attempt.
* No `Classical.choose` in any Lean attempt.
* No truth-table reconstruction in any Lean attempt.
* No promotion of any guard, no `accepted` flips.
* No appending to `outputs/nogolog.jsonl` — meta-barriers are
  positive theorems about a design space, not NOGO entries.
* No appending to `outputs/attempts.jsonl` — this pack is
  exploratory; registry updates happen at operator review,
  not at worker landing.

## 5. Slot acceptance criteria

* **M1 complete** when: (a) Lean-syntax candidate statement is
  written and parses as Lean syntax (does NOT need to typecheck
  against current `pnp3` modules at M1 stage); (b)
  counterexample analysis lists at least three trivial-failure
  candidates and three vacuous candidates and explains why the
  proposed statement avoids both; (c) operator review
  countersigns or returns with revisions.
* **M2 complete** when: (a) M1 has landed; (b) a proof-strategy
  document exists naming the argument class and the key
  sub-lemmas; (c) at least one alternative strategy is
  considered and rejected with reasons.
* **M3 complete** when: (a) M1+M2 landed and reviewed; (b)
  operator explicitly dispatches M3 (this is a separate
  decision); (c) Lean file compiles with no `sorry`/`admit`;
  (d) `lake build PnP3 Pnp4` green; (e) `./scripts/check.sh`
  green.

## 6. Failure criterion

If M1 produces only trivially-failing or vacuous candidates
after honest exploration, the meta-barrier hypothesis is
**discredited**.  The deliverable is:

```
seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/failures/M1_no_viable_statement_<HANDLE>.md
```

with four sections (what was attempted, where it broke, local
vs global, what an integrator must know).

If the meta-barrier hypothesis is discredited, **fp3b3_3 T1
retry becomes the priority track**, and this pack is archived
with the failure report as documentation that the V2-A.1
design space is not structurally barred.

## 7. Cross-references

* Parent pack: `../fp3b3_3_v2_a_1_minimal_normalisation/README.md`
* Audit that opened this pack:
  `../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_g55_operator_audit.md`
* g55 failure report that triggered the audit:
  `../fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55.md`
* V2-A trust root (import-only):
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`
* Sibling audit-route barrier (template for M3 if reached):
  `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`

## 8. Dispatch status

* **M1:** READY for dispatch — operator may issue WORKER_PROMPT.md
  for M1 when desired.  No M1 worker has been dispatched yet.
* **M2:** GATED on M1 landing + review.
* **M3:** GATED on M1 + M2 landing + explicit operator dispatch decision.

This pack is **opened** (directory exists, README written) but
**no worker has been dispatched yet**.  Operator may choose to
keep it cold (audit-only existence) or warm it by writing
`WORKER_PROMPT_M1.md` and dispatching.
