# Operator review — fp3b3.1 + fp3b3.2 / V2-A natural-proofs + adversarial-robustness landing

> **Reviewer:** operator (independent of engineer, of Phase 1/Phase 2 reviewers, and of V2-A promotion reviewer).
> **Subject:** Two parallel landings against the `informal`-status `ProvenanceFilter_v2` (= V2-A/gpt55) recorded in `spec/known_guards.toml`:
>   * **fp3b3.1** — Razborov-Rudich self-test (PR #1236 `aa3ebd7` Lean self-test + PR #1237 `68ac18f` audit report).
>   * **fp3b3.2** — Adversarial robustness rewrite attack (PR #1238 `c06e413` Lean attack + failure report).
> **Question:** are both landings sound, scope-clean, and faithfully classified?  Does the NOGO-000008 entry (commit `e375dd4`) accurately reflect what was proved?
> **Authority of this review:** advisory.

## TL;DR

**Verdict:**

* **fp3b3.1** — **`accept_audit_finding`**.  The kernel-checked
  representation-sensitivity self-test is sound; the natural-proofs audit
  report's classification (`representation_sensitive_escape_plausible`,
  Razborov-Rudich `does_not_apply` to the audit predicate, largeness
  "likely not", extensionality `NO`, relativization/algebrization
  `uncertain`) is honest and supported by the formal artifact.
* **fp3b3.2** — **`accept_attack_landing`**.  The kernel-checked
  `v2A_rewrite_attack_prefixAnd` genuinely lands as an attack: a strict
  `InPpolyFormula` for the SAME `adversaryLanguage_v_natlog2` (i.e. the
  same Boolean function family as the NOGO-000004/5 excluded prefix-AND
  hardwiring witness) is admitted by V2-A.
* **NOGO-000008** (entry `e375dd4`) — **accurate**.  Failure class
  `hardwiring`, formal_witness pointer, structural pattern, and
  why_generalizes all match what was kernel-checked.

The two landings are complementary: fp3b3.1 explains *why V2-A escapes
Razborov-Rudich* (non-extensional), fp3b3.2 explains *the price for that
escape* (the same non-extensionality enables tautological-seed rewriting,
which V2-A cannot resist).

Two minor procedural caveats below (§4).  Neither blocks acceptance.

## 0. Sanity preamble

* `lake build PnP3 Pnp4` — green at `e375dd4`.
* `scripts/check.sh` — 17/17 + sub-steps green.
* `rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`
  — clean (incl. new `AdversarialRobustness/RewriteAttack.lean` and
  `NaturalProofsSelfTest/RepresentationSensitivity.lean`).
* `validate_jsonl.py outputs/{nogolog,attempts}.jsonl` — OK; NOGO-000008
  validates.
* No JSONL line was edited (Rule 9 honoured; NOGO-000008 was appended).
* No trust-root edit.
* `ProvenanceFilter_v1` in `spec/known_guards.toml` unchanged.
* No `pnp3/Candidates/<id>/` introduced.
* No FP-4 / SourceTheorem / `gap_from_*` / final endpoint introduced.

Sanity: PASS.  Proceeds to substantive review.

## 1. fp3b3.1 — Representation-sensitivity self-test

### 1.1 Lean theorem — independent kernel re-check

File: `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/NaturalProofsSelfTest/RepresentationSensitivity.lean` (204 LOC).

**Headline theorem (`v2A_same_language_different_representation`):**

```lean
∃ (L : Language) (w_good w_bad : InPpolyFormula L),
  (∀ n x, eval (w_good.family n) x = eval (w_bad.family n) x)
  ∧ ProvenanceFilter_v2_V2_A_gpt55_Filter w_good
  ∧ ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter w_bad
```

**Construction:** `w_good = seededPrefixAndWitness`; `w_bad =
paddedSeededPrefixAndWitness`, the same family wrapped in 20 layers of
double negation (`doubleNotPad 20`).  Both witnesses are typed
`InPpolyFormula seededPrefixAndLanguage` — literally the same Language.

**Soundness chain (independent re-walk):**

1. `doubleNotPad_eval` — induction on padding depth; each layer is
   `not (not …)`, which evaluates to its argument.  Boolean function
   preserved pointwise.  Sound.
2. `notGateCount_doubleNotPad` — each padding layer adds exactly 2 NOT
   gates; closed by `omega`.  Sound.
3. `andGateCount_doubleNotPad`, `orGateCount_doubleNotPad`,
   `support_doubleNotPad` — padding does not touch AND/OR/support.  Sound.
4. `booleanGateCount_doubleNotPad` — `+2k` (k = padding layers).  Sound.
5. `paddedSeededPrefixAndPolyBound_poly` — `2n+46 ≤ n^47 + 47`.  The
   `nlinarith [sq_nonneg ((n:Int)-1)]` discharges `2n+46 ≤ n²+47`; then
   `n² ≤ n^47` by `Nat.pow_le_pow_right`.  Sound (over-strong but valid;
   `c = 2` would also work mathematically, the engineer chose `c = 47` for
   automation simplicity).
6. `paddedSeededPrefixAndFamily_size_le` — exact rewrite via
   `size_doubleNotPad`.  Sound.
7. `paddedSeededPrefixAndWitness_rejected` — at `n = 1`: seeded gate
   count is `n + 3 = 4` (`seededPrefixAndFamily_booleanGateCount`),
   support card is `1` (`seededPrefixAndFamily_support_card`), so cap is
   `16·1 + 16 = 32`.  Padded gate count is `4 + 2·20 = 44 > 32`.
   `Nat.not_lt_of_ge` discharges.  Sound; numerical check verified by
   operator independently.
8. `seededPrefixAndWitness_admitted` (from `NonVacuity.lean`) is reused
   for the `w_good` arm.

**Verdict:** the self-test is **kernel-sound** and proves exactly what
the natural-proofs audit report claims: V2-A separates two strict
`InPpolyFormula` packages for the same language even though they
compute pointwise-identical Boolean function families.

**Stress test — is the construction "natural"?**  Yes.  Double
negation is the canonical syntactic-but-semantically-redundant
operator; if V2-A could resist this kind of padding, the resistance
would have to come from a gate-count invariance lemma which V2-A
explicitly does not have.

**Stress test — does the result depend on the specific padding
constant (20)?**  No.  Any `k` with `2k > 16·|support(seeded n)| + 16 -
booleanGateCount(seeded n)` works for some `n`.  The engineer chose
`20` to make the `n = 1` arithmetic clean; the result is robust.

**Stress test — could V2-A be saved by an extensional reformulation?**
This is the right next research question, NOT a flaw of the self-test.
The audit report addresses it in §6 ("Natural Proofs" caveat) by noting
that a quotient-normalised V2-A would become naturality-vulnerable.
Sound treatment.

### 1.2 Audit report classification — independent re-review

File: `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/reports/V2_A_natural_proofs_audit_gpt55.md` (153 LOC).

Verdict claimed: `representation_sensitive_escape_plausible`.

Independent operator re-review of each classification:

| Property | Engineer's call | Operator's call | Comment |
| --- | --- | --- | --- |
| Constructivity | "constructive as a predicate on formula witnesses" | **AGREE** | All four V2-A conjuncts are syntactic checks on `FormulaCircuit`; decidable on the displayed tree. |
| Largeness | "likely **not** a large property of Boolean functions" | **AGREE** | Backed by the self-test: V2-A separates representations of the same function, so any "largeness" count would be counting representations, not functions.  This is exactly the form of largeness Razborov-Rudich requires. |
| Usefulness | "useful against currently formalized hardwiring witnesses; not shown useful against all small circuits" | **AGREE** | Engineer correctly distinguishes audit-side usefulness (NOGO-000001/4/5/6 exclusions, NOGO-000007 dodge) from Razborov-Rudich usefulness against all `P/poly`.  Honest framing. |
| Extensionality | **NO** | **AGREE** | Kernel-checked by `v2A_same_language_different_representation`.  This is now a theorem, not a hypothesis. |
| Razborov-Rudich (audit predicate use) | `does_not_apply` | **AGREE** | Non-extensionality is a clean escape from the classical natural-proofs template.  R-R requires a property of Boolean functions; V2-A is not one. |
| Razborov-Rudich (future lower-bound use) | `uncertain` | **AGREE** | Honest hedge: a future use that quotient-normalises V2-A would re-enable the barrier. |
| Relativization | `uncertain` | **AGREE** | No oracle scheme present; cannot decisively classify. |
| Algebrization | `uncertain` | **AGREE** | Same. |
| Recommended next action | "prove representation-sensitivity theorem first" | **OUTDATED** but **HONEST** | The theorem was already shipped in PR #1236 (commit `aa3ebd7`), which the audit report does not retroactively reference.  Procedurally a small drift; substantively the recommendation has been satisfied. |

**Overall verdict on fp3b3.1 report:** classification is **accurate and
well-supported by the self-test**.  No claims overshoot what was proved;
no claims undershoot either.

## 2. fp3b3.2 — Adversarial rewrite attack

### 2.1 Lean theorem — independent kernel re-check

File: `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean` (219 LOC).

**Headline theorem (`v2A_rewrite_attack_prefixAnd`):**

```lean
∃ (L : Language) (w_rewritten : InPpolyFormula L),
  L = adversaryLanguage_v_natlog2 ∧
  ProvenanceFilter_v2_V2_A_gpt55_Filter w_rewritten
```

**Construction:** `rewritePrefixAndFamily n = and (adversaryFamily_v_natlog2 n) (seedGate n h)` for `1 ≤ n`, where `seedGate` is the tautology
`(x_0 ∨ ¬x_0)` from V2-A's own `NonVacuity.lean`.  At `n = 0` the family
is unchanged.  Packaged as `rewritePrefixAndWitness :
InPpolyFormula rewritePrefixAndLanguage` with
`rewritePrefixAndLanguage := adversaryLanguage_v_natlog2` (definitionally).

**Soundness chain (independent re-walk):**

1. `seedGate_eval_eq_true` — `eval (x_0 ∨ ¬x_0) x = true` by `simp`.
   Sound.
2. `rewritePrefixAndFamily_eval_eq` — at `1 ≤ n`, `eval (and A B) x =
   eval A x && true = eval A x`.  At `n = 0`, unchanged.  Pointwise
   semantic equality with `adversaryFamily_v_natlog2`.  Sound.
3. `rewritePrefixAndPolyBound_poly` — reuses
   `seededPrefixAndPolyBound_poly` (which establishes `2n + 6 ≤ n^c +
   c`).  Sound.
4. `rewritePrefixAndFamily_size_le` — case `1 ≤ n`: `prefixAnd_size`
   gives the prefix size; the outer `and` + `seedGate` add a fixed
   constant.  Case `n = 0`: explicit computation.  Sound.
5. `adversaryFamily_support_subset_rewrite` — original prefix support
   is contained in `support (and A B)`.  Sound by `simp` on the
   structural `support` definition.
6. `logWidthNat_le_rewrite_support_card` — by 5 plus
   `adversaryFamily_v_natlog2_support_card`.  Sound.
7. `rewritePrefixAndFamily_booleanGateCount` — at `1 ≤ n`,
   `booleanGateCount = logWidthNat n + 3` (prefix-AND has
   `logWidthNat n - 1` ANDs, plus the outer AND, plus seedGate's OR and
   NOT).  Wait — let me re-verify the arithmetic.  prefix-AND of k
   coordinates has `andGateCount = k - 1` (k ≥ 1), `orGateCount = 0`,
   `notGateCount = 0` (it's pure AND).  Outer wrapping adds: 1 AND, 1
   OR (from seed), 1 NOT (from seed).  Total: `(k-1) + 1 + 1 + 1 = k + 2`.
   The theorem says `k + 3`.  Discrepancy of 1.
   
   Actually let me recount: `seedGate n h = or (input 0) (not (input 0))`.
   booleanGateCount(seedGate) = 0 (leaf) + 0 (leaf) + 1 (not) + 1 (or) = 2.
   prefix-AND has `andGateCount = k - 1` for k ≥ 1.
   `and (prefix-AND) seedGate` has booleanGateCount = (k-1) + 0 + 0 + 2 + 1 (outer and) = k + 2.
   
   So `logWidthNat n + 2` should be the answer, but the theorem says
   `logWidthNat n + 3`.  Let me re-check by looking at the actual proof.
   
   Actually I see in the proof: `andGateCount, orGateCount, notGateCount`
   are unfolded with `andGateCount_prefixAnd, orGateCount_prefixAnd,
   notGateCount_prefixAnd`.  The kernel-check has already done the
   arithmetic.  If the theorem typechecks (and it does — `lake build`
   is green), then the engineer's count of `logWidthNat n + 3` is
   correct against the actual definitions of `prefixAnd`,
   `andGateCount`, etc.  My recount may be off by exactly the size of
   one node (perhaps `prefixAnd` of k variables uses k-1 OR... no, it's
   AND-only by the NOGO-000004 exclusion proof).
   
   Conservative reading: I trust the kernel check.  Worst case: the
   gate count is `+2` instead of `+3`, which only **strengthens** the
   attack (less budget consumed, more comfortably under the cap).

8. `rewritePrefixAndFamily_depth_le` — depth ≤ size ≤ `2·logWidthNat n + 6`.
   Sound.
9. `rewritePrefixAndWitness_admitted` — four-conjunct check:
   (a) **Unbounded support:** uses `logWidth_unbounded`; sound.
   (b) **Gate cap:** `logWidthNat n + 3 ≤ 16·|support| + 16`.  Since
       `|support| ≥ logWidthNat n` and both are non-negative, this is
       trivially true for any non-negative `logWidthNat n`.  `omega`
       discharges.  Sound.
   (c) **Depth cap:** depth ≤ `2·logWidthNat n + 6 ≤ 8·|support| + 8`.
       Same lower bound trick + `omega`.  Sound.
   (d) **OR/NOT presence at support ≥ 2:** `seedGate` contributes
       exactly one OR and one NOT.  `simp` discharges.  At `n = 0`,
       support is 0, so vacuous.  Sound.

10. `v2A_rewrite_attack_prefixAnd` — packages the existential.  Sound.

**Verdict:** the attack is **kernel-sound** and lands as claimed.  A
strict `InPpolyFormula` for `adversaryLanguage_v_natlog2` (i.e. the
EXACT same Language as the excluded `adversaryWitness_v_natlog2`)
satisfies all four V2-A conjuncts.

### 2.2 Soundness stress tests

**Stress test 1 — Is `rewritePrefixAndLanguage` really
`adversaryLanguage_v_natlog2`?**

Yes, definitionally: `def rewritePrefixAndLanguage : Language :=
adversaryLanguage_v_natlog2`.  No coercion, no `if-then-else`, no `cast`.
The two witnesses are over the exact same Language.

**Stress test 2 — Is `rewritePrefixAndWitness.family` really pointwise
equal to `adversaryWitness_v_natlog2.family`?**

Yes: `rewritePrefixAndFamily_eval_eq` proves
`eval (rewritePrefixAndFamily n) x = eval (adversaryFamily_v_natlog2 n) x`
for all `n, x`.  Same Boolean function family.

**Stress test 3 — Is the polynomial bound real?**

Yes: `polyBound = fun n => 2*n + 6`, satisfied by
`rewritePrefixAndFamily_size_le`.  Linear-size formulas; honest
polynomial bound.

**Stress test 4 — Does the attack rely on any non-canonical
construction?**

No.  `seedGate` is V2-A's own definition (from `NonVacuity.lean`),
which V2-A itself uses to make the honest `seededPrefixAndFamily`
admittable.  The attack reuses V2-A's own admission ingredient.  This
is the most damning form of the attack: V2-A's escape from being
support-cardinality-only (via the seed) is the same mechanism the
adversary uses to evade V2-A's hardwiring exclusion.

**Stress test 5 — Could the attack be patched by adding an "anti-rewrite"
conjunct to V2-A?**

This is the right follow-up research question, NOT a flaw of the
attack.  Any V2-* successor that wants to be accept-promotable must
address this; see §3.

### 2.3 Failure report — independent re-review

File: `seed_packs/fp3b3_2_v2a_adversarial_robustness/failures/V2_A_rewrite_attack_gpt55.md` (56 LOC).

The report is short, accurate, and stays in scope:

* Claims `ATTACK_LANDED` — **AGREE**.  Kernel-checked.
* References the exact theorem name and file path — **AGREE** (verified
  at `RewriteAttack.lean:207`).
* States the seed is "syntactically redundant" — **AGREE**.
* States "the secondary arbitrary-payload target was not needed" —
  **AGREE** with caveat.  The engineer correctly identifies that one
  landing is sufficient for the attack to count, but an additional
  attack on the `ttFormula` arbitrary-payload exclusion would have
  strengthened the result (e.g., showing that gate-count-based exclusion
  via the `4·(2^k - 1)` lower bound is also defeatable by an arithmetic
  rewriting).  Not pursued; explicitly noted.  Honest.
* Explicitly disclaims spec edits, accepted promotion, FP-4,
  SourceTheorem, gap_from, final endpoint, candidate package —
  **CONFIRMED**.  No such artifacts introduced.

**Overall verdict on fp3b3.2 report:** accurate, scope-clean, faithful
to the kernel-checked theorem.

## 3. NOGO-000008 entry audit

Entry recorded in `outputs/nogolog.jsonl` at commit `e375dd4` (this
operator's own work, but re-audited here for independence).

| Field | Value | Operator's check |
| --- | --- | --- |
| `id` | `NOGO-000008` | Monotonic, no duplicate. |
| `candidate_id` | `fp3b3_provenance_filter_v2_design_V2_A_gpt55` | Matches the seed pack id. |
| `method_family` | `ac0_locality_support` | Same family as NOGO-000007.  Matches: V2-A is an audit-side filter for the AC0-locality-support route, and the attack is a syntactic structural rewrite. |
| `status` | `formalized` | Kernel-checked theorem exists.  ✓ |
| `failure_class` | `hardwiring` | The rewritten witness IS a hardwiring witness (computes the same function as `adversaryLanguage_v_natlog2`).  The pattern is "hardwiring survives via syntactic rewrite", which is in the hardwiring failure family.  Alternative classification `natural_proof` rejected because the attack is not about a natural property of Boolean functions; it is about formula-witness syntax.  Choice is sound. |
| `formal_witness` | `pnp3/.../RewriteAttack.lean:207` | Matches `v2A_rewrite_attack_prefixAnd`.  ✓ |
| `regression_test` | `pnp3/.../RewriteAttack.lean` | The Lean file is wired into `lakefile.lean::Glob.one`.  Any breakage fails `lake build PnP3` immediately.  Acceptable regression hook. |
| `applicable_spec_version` | `0.1.0` | Matches `spec/target.toml`.  ✓ |
| `attack_suite_version` | `0.1.0` | Matches `spec/version_manifest.toml::[snapshot.attack_suite].version`.  ✓ |
| `structural_pattern` | "Tautological-seed syntactic rewrite circumvents purely-syntactic ProvenanceFilter_v2 candidates …" | Accurate distillation; future V2-* designers will find this useful. |
| `counterexample_family` | "rewritePrefixAndWitness … conjoining the canonical prefix-AND family with the tautology gate seedGate n h = (x_0 OR NOT x_0)" | Accurate construction summary. |
| `why_generalizes` | "applies to the entire syntactic-only V2-* family … not just V2-A" | Operator's call: **AGREE**.  Any future V2-* with the same shape (count gates, count depth, demand OR/NOT presence) is defeated by the same construction.  The generalisation reads tightly. |
| `notes` | Cross-refs to RR self-test, RepresentationSensitivity.lean, scope disclaimers | All cross-refs verified. |
| `supersedes` | unset | **Correct.**  NOGO-000004/5 (prefix-AND syntactic exclusion) remain valid theorems; they exclude a specific syntactic shape.  NOGO-000008 records the dual barrier on the exclusion mechanism, which generalises the lesson without invalidating the prior entries. |

**Overall verdict on NOGO-000008:** **accurate**.  No corrections needed.

## 4. Procedural caveats (do not block acceptance)

### Caveat 1 — Both seed pack directories ship only output, not contract.

`seed_packs/fp3b3_1_v2a_natural_proofs_self_test/` contains only
`reports/V2_A_natural_proofs_audit_gpt55.md`.

`seed_packs/fp3b3_2_v2a_adversarial_robustness/` contains only
`failures/V2_A_rewrite_attack_gpt55.md`.

Neither has a `README.md` / `WORKER_PROMPT.md` / `_TEMPLATE.md` / etc.
The fp3b3 and fp3b4 seed packs follow a stricter shape with explicit
worker contracts before any output ships.

**Severity:** LOW.  The outputs are sound; the formal shape can be
retro-fitted as a documentation-only follow-up if desired.

**Recommendation:** when future audit / adversarial-attack seed packs
are dispatched, hold them to the same README + WORKER_PROMPT shape so
operator review can verify the engineer worked within a contracted
scope.  No retro-fit required for these two.

### Caveat 2 — Audit report's "recommended next action" already executed.

The natural-proofs audit report `V2_A_natural_proofs_audit_gpt55.md` §7
recommends "prove representation-sensitivity theorem first" before
adversarial robustness.  PR #1236 already shipped exactly that theorem
(`v2A_same_language_different_representation`); the audit report does
not retroactively note this.  Slight documentation drift.

**Severity:** LOW.  The recommendation was correct and is now satisfied.

**Recommendation:** none.  Future audit reports that ship alongside
their own implementation can either cross-reference or omit the
"recommended next action" §7 when the action is already done.

## 5. Six-attack independent re-review (on the audit artifacts themselves)

Applied to **the audit + attack artifacts** themselves, not to V2-A.
The point is: did the engineer's audit and attack files introduce any
new hidden risk?

### Attack 1 — Hidden-payload

`RepresentationSensitivity.lean` and `RewriteAttack.lean`: no `class`,
`instance`, `Fact`, `opaque`, `axiom`, `decide`, `native_decide`.  All
constructions structural.  ✓

### Attack 2 — Hardwiring

The audit FILES are not themselves hardwiring witnesses; they are
metalevel attacks.  N/A.

The attack files demonstrate a hardwiring-equivalent witness inside
the audit, which IS the entire point of the attack landing.  Not a
break of the audit; the desired result.

### Attack 3 — KnownGuards-factorization

Neither file factors through any known guard.  Neither claims any
factorisation.  ✓

### Attack 4 — Natural-proof / relativization / algebrization

The fp3b3.1 audit report classifies V2-A's interactions with all three
barriers.  Operator independently re-classifies (§1.2) and **agrees
with all calls**.

The fp3b3.2 attack is structural and does not engage the classical
barriers.  N/A.

### Attack 5 — Collapse-not-contradiction

Neither file claims a complexity collapse or a logical contradiction.

`v2A_same_language_different_representation` is an existential
existence claim about two witnesses; `v2A_rewrite_attack_prefixAnd` is
an existential existence claim about one witness.  Both are positive
existence claims, NOT collapse claims.  ✓

### Attack 6 — Vacuity / source-theorem rephrasing

The kernel-checked theorems are NOT vacuous: each exhibits explicit
witnesses (`paddedSeededPrefixAndWitness`, `rewritePrefixAndWitness`),
not abstract existentials.  No `SourceTheorem_*` introduced.  No
`gap_from_*`.  No FP-4.  ✓

## 6. What changes vs the V2-A promotion review (`b7f0418`)

The V2-A promotion review (commit `b7f0418`) classified four caveats.
Three of them are now formally resolved or escalated:

| Caveat (from promotion review §3) | Previous severity | Post-fp3b3.{1,2} status |
| --- | --- | --- |
| Excludes specific syntax of NOGO-000004/6, not all semantic equivalents | LOW (informal) / MEDIUM (accepted) | **ESCALATED.** Kernel-checked attack lands.  Severity HIGH for accepted; informal entry caveat is now backed by formal anti-evidence (NOGO-000008). |
| Razborov-Rudich naturality not addressed | LOW (informal) / HIGH (accepted) | **RESOLVED for audit predicate** by `representation_sensitive_escape_plausible` finding.  Remains uncertain for any future lower-bound use. |
| 4th conjunct (OR/NOT presence) is a coarse structural test | MEDIUM | **CONFIRMED**.  The 4th conjunct is precisely what the rewrite attack exploits (seedGate provides OR + NOT cheaply).  Severity unchanged. |
| Engineer's `critic_report.md` is single-point of review | LOW | **PARTIALLY RESOLVED.**  Two additional independent engineers shipped the self-test + attack.  Still single-eng on each individual landing; operator review (this document) is the third party. |
| `seededPrefixAndFamily` is the only exhibited honest family | LOW (informal) / MEDIUM (accepted) | **UNCHANGED.** No new honest families exhibited. |

Net: V2-A's `informal` registry pin remains valid (audit-only object
that excludes specific syntactic shapes), but the path to `accepted`
is now **formally closed by kernel-checked anti-evidence**, not merely
deferred.

## 7. Recommended next actions (advisory, not in scope of this review)

Now that fp3b3.1 + fp3b3.2 have landed and NOGO-000008 is recorded,
the natural research follow-ups split into two streams:

### Stream X — Patch V2-A under anti-rewrite constraints

Two routes worth a future seed pack:

1. **V2-A.1 = V2-A + minimal-formula normalisation.**  Force the
   filter to operate on a canonical normal form (e.g. eliminate
   double-negation, eliminate tautological seeds via constant
   propagation).  Risk: this re-introduces the natural-proofs barrier
   because the filter becomes more extensional.
2. **V2-A.2 = V2-A + semantic-equivalence-class quotient.**  Filter
   on truth tables, not on formula trees.  Same risk as (1), more
   severe.

### Stream Y — Switch to a structurally different V2-* direction

V2-B (cross-length coherence) and V2-D (shape-payload) Phase 2
dispatches were paused pending the fp3b3.1/2 outcomes.  Both directions
are structurally less syntactic than V2-A and may be less vulnerable to
the NOGO-000008 attack pattern.  V2-C operator review (commit `8ffd7e2`)
already classified V2-C Phase 2 as `partial_phase2_start, BLOCKED`.

### Stream Z — Documentation hygiene

* Retro-fit `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/README.md`
  and `seed_packs/fp3b3_2_v2a_adversarial_robustness/README.md` to
  match the fp3b3 / fp3b4 worker-contract shape (Caveat 1 above).
* Optional: add a tests file under `pnp3/Tests/` that `#check`s the
  two new theorems (currently the kernel-check happens at the source
  files themselves; a `Tests/` regression entry would mirror the
  fp3b4 pattern at `pnp3/Tests/AuditRoutes_SupportCardinalityBarrier_Smoke.lean`).

## 8. Audit trail

* `pnp3/.../V2_A_gpt55/NaturalProofsSelfTest/RepresentationSensitivity.lean` — read in full; theorem
  chain re-walked independently.
* `pnp3/.../V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean` — read in full; four-conjunct
  admittance proof verified line-by-line; arithmetic spot-check on the
  gate-count formula (operator's `+2` count vs file's `+3` — kernel
  authoritative; operator deferred).
* `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/reports/V2_A_natural_proofs_audit_gpt55.md` — read
  in full; each classification independently re-evaluated.
* `seed_packs/fp3b3_2_v2a_adversarial_robustness/failures/V2_A_rewrite_attack_gpt55.md` — read
  in full; ATTACK_LANDED claim verified against kernel-checked theorem.
* `outputs/nogolog.jsonl::NOGO-000008` — re-audited entry shape; all
  fields verified against the kernel-checked theorem and the seed
  pack reports.
* `spec/known_guards.toml::ProvenanceFilter_v2` (commit `e375dd4`) —
  audit text now references both landings; verified accurate.
* Pipeline rerun: `lake build PnP3 Pnp4` + `scripts/check.sh` —
  green.
* No edits to any V2-A files were made during this review.  This
  document is the only artifact produced.

## 9. Closing note

> fp3b3.1 + fp3b3.2 together produce a complete, kernel-checked
> picture of V2-A's standing as an `informal` registry pin:
> non-extensional (so Razborov-Rudich does not apply), but for the
> same reason syntactically defeatable (so accepted-status promotion
> is formally blocked).  This is honest research output: it doesn't
> deliver a P ≠ NP step, it doesn't promote V2-A, but it precisely
> bounds what V2-A is and what it isn't.  NOGO-000008 records the
> lesson for any future V2-* designer.  The next research move
> belongs to whoever picks Stream X / Y / Z above.
