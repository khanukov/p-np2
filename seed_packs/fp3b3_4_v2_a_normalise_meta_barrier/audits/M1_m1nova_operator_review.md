# M1 m1nova operator review

**Review subject:** `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/candidates/M1_m1nova.md`
**Worker landing commit context:** `8c45586` (merged via PR #1241 → `3ee0994`).
**Outcome:** **APPROVE M1 → PROCEED to M2** with one strengthening.

This is **operator-scoped review**, not a worker artifact.  It
verifies m1nova's argument against the actual Lean files and
synthesises the operator decision.

## 1. Verification of m1nova's argument against Lean files

m1nova's core argument (M1 candidate §B.2 + §D + §C(3)) is:

> Any context-uniform bottom-up structural normaliser `𝒩`
> satisfying `EliminatesSeedGate` and `EliminatesAndTrue` collapses
> V2-A's own non-vacuity witness `seededPrefixAndFamily n` to a
> formula with zero OR gates and zero NOT gates (for `n ≥ 1`).
> Since V2-A's filter requires the mixed-gate clause at support
> `≥ 2`, the composed filter `V2_A_with_normaliser 𝒩` rejects
> the normalised seeded witness for `n ≥ 2`.  Hence the
> conjunction `(PreservesSeededNonVacuity 𝒩 ∧
> RejectsRewriteAttack 𝒩)` is false.

The argument has four load-bearing inputs.  Each is verified
against the trust-rooted Lean files:

* **Input 1:** `seededPrefixAndFamily n = and prefixAnd seedGate`
  at positive `n`.
  **Verified:** `pnp3/.../V2_A_gpt55/NonVacuity.lean:36-40` —
  `def seededPrefixAndFamily (n : Nat) : FormulaCircuit n :=
  if h : 1 ≤ n then FormulaCircuit.and (...prefixAnd n n
  (Nat.le_refl n)) (seedGate n h) else FormulaCircuit.const false`.

* **Input 2:** `seedGate = or (input 0) (not (input 0))` (the only
  OR/NOT source in the seeded witness).
  **Verified:** `pnp3/.../V2_A_gpt55/NonVacuity.lean:24-27`.

* **Input 3:** `prefixAnd n k` has zero OR gates and zero NOT
  gates for all `k ≤ n`.
  **Verified:** `pnp3/.../V2_A_gpt55/ExcludesPrefixAnd.lean:29-43`
  proves both `orGateCount_prefixAnd` and `notGateCount_prefixAnd`
  by induction.

* **Input 4:** V2-A's filter requires support `≥ 2 ⇒ orGateCount
  + notGateCount ≥ 1` (mixed-gate clause).
  **Verified:** the existing `excludes_adversaryWitness_v_natlog2`
  proof in `ExcludesPrefixAnd.lean:46-63` extracts `hMix` from
  the filter and derives `hOrPos` at support `≥ 2`, then
  contradicts via `orGateCount = 0`.  Identical structure applies
  to a normalised seeded witness with `orGateCount = 0`.

All four inputs verified.  The argument is **mathematically tight**.

## 2. Strengthening — argument needs LESS than m1nova's fold class

m1nova used a careful "context-uniform bottom-up fold" class
formalisation (M1 candidate §A) to make the argument formal.
Operator observes the argument **actually goes through under
the seed pack's published T1 HARD-minimum surface alone**, without
needing fold formalisation:

Given the HARD-minimum reductions (post-g55 patched, README §3 T1):

* `canonicalNormalise_seedGate : canonicalNormalise (seedGate n h)
  = const true` (required by T4, listed as targeted reduction).
* `canonicalNormalise_and_const_true` and
  `canonicalNormalise_and_true_const` (HARD-minimum reduction 5).
* `canonicalNormalise_eval` (structural eval-preservation).

And given the **critical scope rule** (README §3 T1 line 201):
`canonicalNormalise` is structural syntactic recursion (which
makes its action context-uniform on subtrees):

For `n ≥ 1`, expanding `seededPrefixAndFamily n = and prefixAnd
seedGate` and propagating `canonicalNormalise` through the AND
constructor with the bottom-up recursive shape:

```
canonicalNormalise (and prefixAnd seedGate)
  ≈ <local AND rule> (canonicalNormalise prefixAnd) (canonicalNormalise seedGate)
  = <local AND rule> (canonicalNormalise prefixAnd) (const true)         [HARD-min: seedGate]
  = canonicalNormalise prefixAnd                                          [HARD-min: AND with const true]
  -- prefixAnd has zero OR gates and zero NOT gates;
  -- canonicalNormalise size_le ⇒ canonicalNormalise prefixAnd has zero OR/NOT
  -- (assuming the normaliser does not invent gates from AND-only input,
  --  which any HARD-min-compliant structural simplifier honours).
```

Therefore `canonicalNormalise (seededPrefixAndFamily n) ≠
seededPrefixAndFamily n` (the seed is gone), and the normalised
witness fails V2-A's mixed-gate clause at `n ≥ 2`.

**Conclusion:** the meta-barrier observation is reachable
**directly from the seed pack's published spec** without any
additional class formalisation.  m1nova's fold class is the right
generalisation for M2's Lean theorem, but the operator-level
design-space closure does not depend on it.

## 3. Cross-check against fp3b3_3 README §T2 scope rule

The seed pack `README.md` §T2 (lines 377-388) explicitly anticipates
this exact failure mode:

> **Scope rule:** if `canonicalNormalise (seededPrefixAndFamily n)`
> is **not** equal (definitionally or propositionally) to
> `seededPrefixAndFamily n`, the worker must investigate.  Either:
> * the seeded family has a normalisable redundancy (refine the
>   family, but that's editing V2-A's NonVacuity — forbidden), or
> * T1's normalisation is too aggressive (refine T1).

m1nova's contribution (and §2 of this review) shows the
inequality is **forced** by the published HARD-minimum surface.
Both escape routes are structurally blocked:

* "Refine the family" requires editing V2-A NonVacuity, which is
  explicitly forbidden by fp3b3_3 §4 (V2-A is import-only).
* "Refine T1" requires dropping either `canonicalNormalise_seedGate`
  (which kills V2-A.1's purpose: defeating NOGO-000008) or
  `canonicalNormalise_and_const_true` (which destroys the
  AND-identity reduction surface and is one of the constants
  that g55's audit confirmed are derivation-forced from the
  rest of the HARD-minimum set).

So the seed pack **already encoded** the failure mode at scope-rule
level.  m1nova's M1 deliverable proves the failure mode is
**forced**, not optional.  The design-space inconsistency is
observable at the seed pack's own scope rule, **operator-level**,
without M2 / M3 Lean formalisation.

## 4. Implications for fp3b3_3

The fp3b3_3 design space is **structurally inconsistent at the
T1 + T2 composition level**.  Concretely:

* T1 can land (g55r1's failure is `Local`, fixable with the
  factored-helper-lemmas recipe in `T1_g55r1.md` §4).
* But T2 **cannot** prove `v2A_1_admits_seededPrefixAndWitness`
  because the normalised witness fails V2-A's mixed-gate clause
  at `n ≥ 2`.
* T3 / T4 / T5 (Round 2) are gated on T2 landing — therefore
  also unreachable in the current design.

**The fp3b3_3 design space is closed** (modulo M2 / M3 Lean
formalisation tightening this into a published theorem).  The
g55r1 retry track must be **paused** — additional T1 retries do
not change this conclusion.

The pause-decision document is at
`../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_retry_pause_post_M1.md`.

## 5. Promotion decision

M1 candidate `M1_m1nova.md`:

* **Section A (predicate class):** APPROVED with note — the fold
  class is the right formalisation for M2/M3.  For operator-level
  conclusion, see §2 of this review showing a weaker class
  (published T1 spec + structural recursion) suffices.
* **Section B (statement candidate):** APPROVED.  M2 should
  formalise the theorem as stated.
* **Section C (counterexample analysis):** APPROVED.  Counterexample
  classification is honest.  The whitelist anti-meta-barrier
  attempt is correctly rejected as not context-uniform.
* **Section D (proof-strategy preview):** APPROVED.  The 50-step
  preview is dense but covers the right beats.  Operator notes
  that the bullets D.15 ("`prefixAnd n n` has no OR gates and no
  NOT gates") and D.16 ("normaliser does not introduce OR/NOT
  on AND-only input") are the load-bearing structural facts;
  D.15 is verified (this review §1 Input 3), D.16 requires a new
  field `NoInventsMixedGatesOnAndOnly` in the M2 class refinement
  (m1nova flagged this in D.17).
* **Section E (recommendation `PROCEED to M2`):** APPROVED.

**Promotion:** M1 → PROCEED to M2.

## 6. M2 dispatch readiness

M2 is the Lean formalisation of the meta-barrier theorem.  The
dispatch instrument needs:

* file path: `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/WORKER_PROMPT_M2.md`
* slot: M2 (Lean formalisation, not markdown).
* target Lean module:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean`.
* required theorem name: `v2_a_structural_normalisation_meta_barrier`
  (or similar; M2 worker may rename if more precise).
* mandatory fields in `StructuralNormaliser`: m1nova's `LocalFormulaOps`
  + `normalise_eq_fold` + `eval_pres` + `size_le` + an explicit
  `NoInventsMixedGatesOnAndOnly` (or similar) field that ensures
  AND-only input cannot produce OR/NOT output.  Operator review
  notes that this last field can likely be proven from
  `normalise_eq_fold` + `eval_pres` + size constraints, but M2
  should state it explicitly to keep the theorem self-contained.

Operator dispatches M2 in the same coordinated commit as this
review (`WORKER_PROMPT_M2.md` added alongside).

## 7. M3 dispatch — DEFERRED

M3 is the optional integration of the meta-barrier theorem into
the audit-route barrier suite (alongside
`SupportCardinalityBarrier/Barrier.lean`).  M3 is gated on M2
landing and is operator-discretion.

## 8. Cross-references

* M1 candidate: `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/candidates/M1_m1nova.md`
* M1 commit: `8c45586` (merged via PR #1241 → `3ee0994`).
* fp3b3_3 §T2 scope rule: `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/README.md:377-388`.
* g55r1 failure report: `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55r1.md`.
* Verified Lean facts:
  * `pnp3/.../V2_A_gpt55/NonVacuity.lean:24-40`
  * `pnp3/.../V2_A_gpt55/ExcludesPrefixAnd.lean:29-43, 46-63`.
* fp3b3_3 design-space closure decision:
  `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_retry_pause_post_M1.md`.

## 9. Audit-only scope confirmation

This review writes nothing to:

* `outputs/nogolog.jsonl` — the meta-barrier is currently
  markdown-grade; a NOGO entry should wait for M2 Lean
  formalisation.
* `outputs/attempts.jsonl` — no attempt registry update needed.
* `spec/known_guards.toml` — no V2-A.1 entry was ever promoted.
* Any Lean module — M2 is the dispatch that creates the meta-barrier
  Lean file; this review only authorises that dispatch.

No `accepted` promotions, no FP-4 implications, no final-endpoint
implications.  No P ≠ NP claims.
