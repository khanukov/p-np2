# T1 g55 operator audit

**Audit subject:** `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55.md`
**Audit commit context:** worker landed at `7840ef4` (merged via PR #1239 → `f120b78`).
**Operator decision after audit:** **HOLD on T1 retry dispatch.**  No
follow-up T1 worker is granted retry rights until this audit's
recommendations are addressed and operator-side parallel
investigation `fp3b3_4_v2_a_normalise_meta_barrier/` produces
preliminary findings.

This audit is **not** a worker artifact; it is operator-scoped
governance to determine whether g55's `Local` classification
is correct and what the next dispatch should look like.

## 1. Sanity-check of the over-constrained-spec claim

g55 claims that two HARD-minimum reduction lemmas in the seed
pack README §3 (post-commit `3d52fad`) specialise to the same
left-hand side and together force a derivation that was not
listed as a HARD-minimum reduction.  We verify this directly.

The two lemmas at issue:

```lean
canonicalNormalise_and_self_not_self :
    ∀ {n : Nat} (C : FormulaCircuit n),
      canonicalNormalise (and C (not C)) = const false

canonicalNormalise_and_true_const :
    ∀ {n : Nat} (C : FormulaCircuit n),
      canonicalNormalise (and (const true) C) = canonicalNormalise C
```

Specialise the first at `C := const true`:

```lean
canonicalNormalise (and (const true) (not (const true))) = const false   -- (E1)
```

Specialise the second at `C := not (const true)`:

```lean
canonicalNormalise (and (const true) (not (const true)))
  = canonicalNormalise (not (const true))                                -- (E2)
```

Combining (E1) and (E2):

```lean
canonicalNormalise (not (const true)) = const false                      -- (D1)
```

Symmetrically, specialising
`canonicalNormalise_and_not_self_self` at `C := const true`
and `canonicalNormalise_and_const_true` at `C := not (const true)`:

```lean
canonicalNormalise (and (not (const true)) (const true)) = const false   -- (E3)
canonicalNormalise (and (not (const true)) (const true))
  = canonicalNormalise (not (const true))                                -- (E4)
```

Combining yields the same (D1).  And the dual via the
const-false specialisations forces:

```lean
canonicalNormalise (not (const false)) = const true                      -- (D2)
```

**Verdict:** g55's mathematical observation is correct.  Our
seed pack's HARD-minimum lemma surface **does** force two
constant-negation reductions (D1) and (D2) as **derived**
requirements that are not explicitly listed as HARD-minimum
reductions in README §3.  This is a real spec inconsistency,
not a worker error.

## 2. Verification of g55's classification: `Local` vs `Global`

g55 classified the obstruction as `Local` on three grounds:

1. No forbidden definition shape was used (no truth-table
   reconstruction, no semantic argmin, no semantic quotient,
   no `Classical.choose`, no meta-level
   `Decidable (FormulaCircuit.eval _ _)`).
2. The obstruction is a discoverable internal inconsistency in
   the spec, not a structural impossibility.
3. g55 supplied a concrete recipe for repair.

We audit each:

* **(1) Forbidden shapes:** g55's attempted definition was a
  structural recursion with local syntactic equality on
  subtrees (used only for literal complement detection).  This
  matches the seed pack §3 T1 critical scope rule
  (post-commit `3d52fad`).  Confirmed not-forbidden.

* **(2) Discoverability:** the obstruction surfaced as a
  proof-engineering failure on `normaliseNot (normaliseNot C)
  = C` after adding (D1)+(D2).  This is consistent with the
  observation that the local NOT normaliser, after constant
  negation is added, is no longer an unconditional involution
  on raw `FormulaCircuit` syntax — it is only involutive on
  the **image** of `canonicalNormalise`.  This is a standard
  rewrite-system phenomenon, not a structural barrier.

* **(3) Repair recipe:** g55 proposes (a) explicitly
  normalising constants under NOT, (b) introducing a
  canonical-output predicate (something like `NotStable C` or
  `IsCanonical C`) that excludes `not (const _)` and
  `not (not _)` at the root, (c) proving every output of
  `canonicalNormalise` satisfies this predicate, and (d)
  deriving `canonicalNormalise_double_not` from the predicate
  rather than via unconditional local involution.  This is a
  standard syntactic normal-form technique and is
  well-known to scale (cf. confluent term-rewriting
  literature).

**Verdict on classification:** g55's `Local` classification is
**provisionally correct** based on the math and the proposed
recipe, but operator-side caution applies for two reasons:

(a) g55 did **not** complete the recipe.  The proof
    that the image invariant approach actually closes T1 is
    speculative until executed.  A second worker attempting
    the recipe may discover that the invariant-based proof of
    `canonicalNormalise_double_not` interacts badly with
    `canonicalNormalise_and_*` lemmas because the invariant
    must be propagated through compound constructors —
    historically this is where syntactic normal-form proofs
    grow proof-engineering debt.

(b) The fact that our first dispatch had an internal
    spec inconsistency on its own HARD-minimum lemma list is
    itself a weak meta-signal.  If we are unable to write a
    consistent HARD-minimum specification for V2-A.1 on the
    first try, that is mild evidence (not yet structural
    evidence) that the V2-A.1 design space is harder to
    specify cleanly than the operator estimated.  This is the
    reason the parallel meta-barrier track is opened (see §5).

Therefore the audit upgrades the operator's confidence in
`Local` from "worker-asserted" to "math-checked, recipe-plausible,
not-yet-executed".  This is enough to NOT pivot to V2-A.2 yet,
but NOT enough to autograph a retry dispatch.

## 3. Identified spec-bug and corrective patch (pending; not committed)

The seed pack §3 T1 HARD-minimum reductions list omits the two
derived requirements (D1) and (D2).  When the retry dispatch
is approved (see §5 conditions), the seed pack should be
patched to:

1. Add to HARD-minimum reductions:

   ```lean
   canonicalNormalise_not_const_true   : canonicalNormalise (not (const true))  = const false
   canonicalNormalise_not_const_false  : canonicalNormalise (not (const false)) = const true
   ```

2. Reformulate `canonicalNormalise_double_not` from an
   unconditional local-involution shape to an
   **image-invariant** shape:

   ```lean
   /-- Canonical-output normal-form predicate.  Excludes
   syntactic shapes that any canonical output must avoid. -/
   inductive IsCanonical : {n : Nat} → FormulaCircuit n → Prop
     | -- exclude (not (const _)) at root
     | -- exclude (not (not _)) at root
     | -- structural recursion clauses
     ...

   theorem canonicalNormalise_isCanonical {n : Nat}
       (C : FormulaCircuit n) :
       IsCanonical (canonicalNormalise C)

   theorem canonicalNormalise_double_not_canonical {n : Nat}
       (C : FormulaCircuit n) (h : IsCanonical C) :
       canonicalNormalise (not (not C)) = C

   /-- Wrapper: the full requested theorem, derived. -/
   theorem canonicalNormalise_double_not {n : Nat}
       (C : FormulaCircuit n) :
       canonicalNormalise (not (not C)) = canonicalNormalise C
   ```

   The wrapper recovers the originally-requested theorem shape
   while routing the proof through the invariant.

3. The seed pack README §3 should also note explicitly that
   adding (D1)+(D2) is **derivation, not extension** — i.e. it
   makes implicit-derivable-requirements explicit, not a new
   weakening of the spec.

These three changes constitute the spec refinement gate before
any retry dispatch.

## 4. g55 status in registry

Per operator decision (post-audit poll): **status = HOLD pending
audit**.  Concretely:

* g55 is **not blacklisted** — the failure report is research-grade.
* g55 is **not granted retry rights** automatically — see §5
  for the conditions under which retry rights are released.
* The failure report `T1_g55.md` is the audit artifact for
  Round 1 attempt #1; it remains in-tree as durable
  documentation.
* If g55 (or any worker) is later granted retry rights, the
  retry handle should be `g55r1` / `g55r2` / ... so the
  registry can distinguish attempts and the audit chain stays
  navigable.

## 5. Operator decision matrix

The operator polled three governance questions after reading
the failure report.  Selected outcomes (recorded for audit):

* **Next move:** _Pivot к `fp3b3_4` meta-barrier_ — open the
  meta-barrier exploration track in parallel.
* **g55 status:** _Hold review pending operator audit_ — no
  automatic retry.  This audit document is that review.
* **Spec refinement direction:** _Canonical-output invariant
  approach_ — encoded in §3 above for the eventual retry.

**Operationalisation (REVISED — parallel dispatch):**

The initial draft of this section listed a sequential retry
gate (no T1 retry until fp3b3_4 produces preliminary findings).
Operator reconsidered and **revised to parallel dispatch** on
the following reasoning:

* The fp3b3_3 spec patch is deterministic and well-understood
  (add the derived constant-negation reductions explicitly +
  reformulate `canonicalNormalise_double_not` via the
  canonical-output invariant the audit §3 already specifies).
  Risk of "another spec inconsistency surfaces" is low because
  the lemma surface is now closed under the specialisations
  that broke attempt #1.
* The fp3b3_4 M1 deliverable is **markdown-only** (no Lean), so
  worker effort is bounded and reversible.
* If fp3b3_4 M1 lands `DISCREDITED` (anti-meta-barrier
  counterexample succeeds), T1 retry is already in flight —
  saved one operator roundtrip.
* If fp3b3_4 M1 lands `PROCEED to M2` (meta-barrier
  hypothesis plausible), T1 retry can be paused at the next
  worker check-in with minimal sunk cost.

(A) **Patched fp3b3_3 §3 T1 spec is committed in the same
    coordinated commit as this audit revision.**  See seed pack
    README §3 T1 for the patched HARD-minimum reduction set
    (now seven items including the two constant-negation
    reductions) and the canonical-output invariant approach.

(B) **T1 retry dispatch is approved** under the revised gate:

    1. seed pack `fp3b3_3` §3 T1 patched — **DONE** (this commit).
    2. WORKER_PROMPT.md §2A explicitly walks T1 retry workers
       through g55's three load-bearing findings — **DONE**.
    3. operator countersignature for retry dispatch —
       **countersigned in this audit revision** (see §6 below).
    4. Retry handle convention: `g55r1` for g55's own retry,
       fresh `<other>r1` for independent attempts.

(C) **`fp3b3_4` M1 dispatch is approved** in parallel:

    1. `fp3b3_4` README written — **DONE** (separate commit).
    2. `fp3b3_4/WORKER_PROMPT_M1.md` written — **DONE** (this commit).
    3. M1 is markdown-only; worker dispatch is operator
       discretion.

(D) **`fp3b3_3` seed pack remains the primary Stream X
    track.**  Opening `fp3b3_4` does **not** demote
    `fp3b3_3`.  Both tracks may end with:
    * `fp3b3_3` lands → V2-A.1 successor candidate, meta-barrier
      track closes with a "no obstruction" report.
    * `fp3b3_4` lands a meta-barrier theorem → V2-A.1 design space
      is closed, `fp3b3_3` is archived as anti-evidence.
    * Both stall → operator escalates: archive both,
      re-evaluate V2-A.2 / V2-A.3 / V2-B / V2-D priorities.

## 6. Operator countersignature for T1 retry

Per audit §5(B), T1 retry dispatch is countersigned subject to:

* Worker MUST read `audits/T1_g55_operator_audit.md` (this
  document) and `failures/T1_g55.md` before starting.  This is
  enforced by `WORKER_PROMPT.md` §2A.
* Worker MUST follow the canonical-output invariant approach
  (see audit §3 / README §3 T1).  Any deviation requires a
  documented top-of-file comment block.
* Worker MUST adopt a retry handle (`g55r1` for g55 reattempt,
  or a fresh `<handle>r1`-style suffix for independent
  attempts).  This keeps the audit chain navigable.
* If retry surfaces another spec inconsistency (analogous to
  g55's finding), worker MUST ship a structured failure report
  documenting the new inconsistency.  Operator will then
  re-audit and either patch the spec again OR re-classify the
  obstruction as `Global` and pivot per the original §10
  protocol.
* Round 2 (T3 / T4 / T5) remains gated on T1 + T2 landing
  cleanly.  Round 2 must not be pre-staged in retry commits.

This countersignature applies to the current spec at commit
hash recorded at landing time; if the spec evolves further
before retry dispatch, the countersignature must be re-issued.

## 7. Cross-references

* g55 failure report:
  `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55.md`
* g55 worker commit: `7840ef4` (merged via PR #1239 → `f120b78`).
* Seed pack initial dispatch commit: `3d52fad`.
* Audit + fp3b3_4 opening commit: `59a20ac`.
* Spec patch + audit revision + M1 prompt commit:
  recorded at this commit.
* Parallel track opened:
  `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/`
  with `README.md` + `WORKER_PROMPT_M1.md`.
* Negative-pivot protocol pre-staged in seed pack README §10
  (operator activated the meta-barrier opening early, ahead
  of `Global` classification, per the §5 reasoning above).

## 8. Audit-only scope confirmation

This audit document writes nothing to:

* `spec/known_guards.toml` (no V2-A.1 entry yet; promotion gate
  remains closed).
* `outputs/nogolog.jsonl` (no new NOGO; g55's failure is local
  and well-documented in-tree).
* `outputs/attempts.jsonl` (no attempt registry update needed;
  the registry records seed packs, not worker handles).
* Any Lean module under `pnp3/` or `pnp4/`.

The audit is governance-scope only.  No `accepted`-promotion
implications; no FP-4 implications; no final-endpoint
implications.
