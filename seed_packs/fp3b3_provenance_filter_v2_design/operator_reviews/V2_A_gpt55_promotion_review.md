# Operator review — fp3b3 V2-A/gpt55 promotion path

> **Reviewer:** operator (independent of engineer + engineer's reviewer).
> **Subject:** fp3b3 V2-A Phase 2 redo, commit `7d29c0d`.
> **Question:** does V2-A clear the promotion-path bar to
> `spec/known_guards.toml::ProvenanceFilter_v2 status="informal"`?
> **Authority of this review:** advisory.  Promotion to `informal`
> requires a separate operator-approved PR; promotion to `accepted`
> is not in scope and is forbidden by the seed pack regardless.

## 0. Sanity preamble

* `lake build PnP3 Pnp4` — green.  All 7 V2-A modules compile.
* `scripts/check.sh` — 17/17 + sub-steps green.
* `rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`
  — clean.
* `validate_jsonl.py outputs/{nogolog,attempts}.jsonl` — OK.
* No JSONL line was edited (Rule 9 honoured).
* No trust-root edit.
* `ProvenanceFilter_v1` in `spec/known_guards.toml` unchanged
  (still `informal`, `formal_name = ""`).
* No `pnp3/Candidates/<id>/` introduced.
* No FP-4 / SourceTheorem / `gap_from_*` / final endpoint
  introduced.

Sanity: PASS.  Proceeds to substantive review.

## 1. Five mandatory deliverables — independent kernel re-check

### 1.1 `ProvenanceFilter_v2_V2_A_gpt55_not_support_cardinality_only`

`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/NotSupportCardinalityOnly.lean:70`

**Statement:**

```lean
¬ IsSupportCardinalityOnly @ProvenanceFilter_v2_V2_A_gpt55_Filter
```

**Proof shape:** exhibit two `InPpolyFormula` witnesses with
identical support-cardinality profile (both `n ↦ n`) but
different filter membership:

* `seededPrefixAndWitness` — admitted (proven by
  `seededPrefixAndWitness_admitted` in `NonVacuity.lean`).
* `fullPrefixCanonicalWitness` — rejected (proven by
  `excludes_fullPrefixAnd_canonicalWitness` in this file).
  The canonical witness is `canonicalHardwiringWitness id …`,
  i.e. fp3b4's full-prefix-AND, which has zero OR gates,
  violating the 4th conjunct.

Apply `IsSupportCardinalityOnly.apply` (from fp3b4) to transport
admittance from seeded to canonical, contradicting rejection.

**Soundness:** kernel-checked.  No `sorry`, no `axiom`.  The
witnesses are explicitly constructed; the support-profile
equality is proved via `seededPrefixAndFamily_support_card` (T2
of fp3b4 + V2-A's local identity) + `canonicalHardwiringFamily_support_card`
(fp3b4's T2).  Tight argument.

**Stress test — could the proof be extracted as a hidden
contradiction?**  No.  The two witnesses are distinct
`InPpolyFormula L_*` records for distinct languages.  Distinct
languages prevent `seededPrefixAndWitness = fullPrefixCanonicalWitness`
collapse.  The contradiction lives at filter-membership-level
only.

**Verdict:** sound; gating obligation met.

### 1.2 `excludes_bounded_support` (NOGO-000001 surface)

`ExcludesOverbroad.lean:28`.

**Statement:** `∀ w B, (∀ n, |support|.card ≤ B) → ¬ Filter w`.

**Proof shape:** filter's 1st conjunct demands unbounded
support; bounded contradicts directly.

**Soundness:** trivial, sound.

**Stress test — does this actually capture NOGO-000001?**  NOGO-000001
is about `OverbroadUniformProvenance` (overbroad provenance shape
combined with `FixedParamsRoute` reconstructing the refuted
support-bounds route).  The hardwiring witness underlying it
(`fixedSlice_gapPartialMCSP_in_PpolyFormula` of Probe 2) is
actually a *single-slice* truth-table shape with bounded
support (support card = `n_0` at one length, `0` elsewhere).
That has `polyBound n = if n = n_0 then 2^{n_0} else 1`, hence
bounded by `max(2^{n_0}, 1)`.  By `excludes_uniform_polyBound`
(corollary in same file), bounded polyBound ⇒ bounded support
⇒ filter rejects.  The chain works.

The theorem does NOT, however, formally refute every possible
`OverbroadUniformProvenance` instance — only those which
manifest as a specific `InPpolyFormula` record with bounded
support.  The engineer's docstring acknowledges this scope.

**Verdict:** sound; NOGO-000001 obstruction covered for the
canonical witness shape.

### 1.3 `excludes_adversaryWitness_v_natlog2` (NOGO-000004/000005 surface)

`ExcludesPrefixAnd.lean:46`.

**Statement:** filter rejects fp3b1's `adversaryWitness_v_natlog2`
(prefix-AND on `Nat.log2 (n+1)` window).

**Proof shape:** at `n = 3`, `widthFn(3) = log2(4) = 2`, so
support card = 2 ≥ 2.  Filter's 4th conjunct demands
`0 < orGateCount`.  But prefix-AND is AND-only:
`orGateCount_prefixAnd` proves `orGateCount = 0`.  Contradiction.

**Soundness:** kernel-checked.  All three helpers
(`andGateCount_prefixAnd`, `orGateCount_prefixAnd`,
`notGateCount_prefixAnd`) are sound by structural induction.

**Stress test — could prefix-AND be rewritten to satisfy V2-A?**
Yes — semantically.  E.g., `x_0 ∧ x_1 = ¬(¬x_0 ∨ ¬x_1)` would
have OR and NOT gates while computing the same Boolean function.
But that is a DIFFERENT `FormulaCircuit` term, not the
canonical `prefixAnd` that NOGO-000004 references.  The
exclusion theorem refutes the SPECIFIC `prefixAnd`-syntax
witness, not all functions equivalent to it.

This is the syntax-sensitivity caveat.  Acceptable for a Phase 2
survivor; flagged in §3.

**Verdict:** sound; NOGO-000004/000005 obstruction covered for
the canonical witness syntax.

### 1.4 `excludes_adversaryWitness_v_arbpayload` (NOGO-000006 surface)

`ExcludesArbitraryPayload.lean:43`.

**Statement:** filter rejects every fp3b2 arbitrary all-essential
payload `adversaryWitness_v_arbpayload F hF`.

**Proof shape:** at `n = 64`, `widthFn(64) = log2(65) = 6`.
ttFormula gate count is `4·(2^k - 1) = 4·63 = 252` exactly
(`booleanGateCount_ttFormula` in `Filter.lean`).  Support card is
`widthFn(64) = 6`.  Filter's 2nd conjunct requires
`booleanGateCount ≤ 16·6 + 16 = 112`.  But 252 > 112.

**Soundness:** kernel-checked.  The exact gate-count theorem is
clean structural induction; `widthFn_sixtyFour` resolves
`Nat.log2 65 = 6` via `Nat.log_eq_iff` + `norm_num`.

**Stress test — does this scale to ALL arbitrary all-essential
payloads, not just one?**  Yes — the theorem is universally
quantified over `F : PayloadFamily` with `hF : AllEssentialPayload`,
and the exact gate count `4·(2^k - 1)` is INDEPENDENT of payload
semantics.  Any choice of `F` produces the same gate count at
fixed width.  Robust.

**Stress test — what if width were tuned to satisfy the cap?**
For `widthFn(n) = k`, ttFormula has `4·(2^k - 1)` gates and
support card `k`.  Cap is `16k + 16`.  Solving `4·(2^k - 1) ≤
16k + 16`: at k=4, `4·15 = 60 ≤ 80` (passes); at k=5, `4·31 =
124 > 96` (fails).  So width up to 4 SURVIVES the cap.  But for
log-width = `Nat.log2(n+1)`, this reaches 5 at n=31 and 6 at
n=63.  So the obstruction kicks in for n ≥ 32.  The theorem
just picks n=64 as a clean witness.

A family with FIXED width ≤ 4 would survive the cap but FAIL
the unbounded-support 1st conjunct (support card = 4 < 5, etc.).
So narrow-width hardwiring is excluded by 1st conjunct.

**Verdict:** sound; NOGO-000006 obstruction fully covered.

### 1.5 `seededPrefixAndWitness_admitted` (non-vacuity)

`NonVacuity.lean:135`.

**Statement:** `Filter seededPrefixAndWitness`.

**Proof shape:** verifies all four conjuncts:
1. **Unbounded support:** `seededPrefixAndFamily_support_card`
   proves `support card = n` for all `n`, so for any `B` take
   `n = B+1`.
2. **Boolean gate cap:** `seededPrefixAndFamily_booleanGateCount`
   gives `n+3` for `n ≥ 1`, `0` for `n = 0`; both ≤ `16·card+16`.
3. **Depth cap:** depth ≤ size ≤ `2n+6` ≤ `8n+8` for `n ≥ 0`.
4. **OR/NOT presence at `card ≥ 2`:** the seed `(x_0 ∧ ¬x_1) ∨
   (¬x_0 ∧ x_1)` contains both OR and NOT, and the seed is
   present in `seededPrefixAndFamily(n)` for `n ≥ 2`.

**Soundness:** kernel-checked.  Reviewer-approved family used.

**Stress test — does seededPrefixAnd compute anything
"interesting"?**  At `n ≥ 2`, it computes:
`(x_0 XOR x_1) AND x_2 AND … AND x_{n-1}`.

This is non-trivial (depends essentially on every variable),
non-monotone (uses XOR), polynomial-size, formula-tree.  It is a
genuine non-hardwiring family.  Real non-vacuity.

**Verdict:** sound; non-vacuity established with a substantively
honest family.

## 2. Six-attack independent re-review

Following `spec/critic_protocol.md` §1, I re-run the six attacks
*independently* of the engineer's `critic_reports/V2_A_gpt55.md`.

### Attack 1 — Hidden-payload

**status:** `no break found` (concurs with engineer).

* No `class`, `instance`, `Fact`, `opaque`, `axiom`, `decide`,
  `native_decide` in any of the 7 V2-A files.
* All filter conjuncts are explicit `Prop` over decidable
  arithmetic predicates.
* The non-vacuity proof uses `simp` + structural unfolding only
  (no `Classical.choose`-based existential witness extraction
  beyond Mathlib's standard `simp` set).
* No payload smuggled via record fields: all `InPpolyFormula`
  fields are concrete (`polyBound`, `polyBound_poly`, `family`,
  `family_size_le`, `correct = fun _ _ => rfl`).

### Attack 2 — Hardwiring

**status:** `no break found` for currently formalised
hardwiring shapes.  See §1.3, §1.4.  The filter excludes:

* prefix-AND on log-width window (canonical fp3b1 witness)
* arbitrary all-essential `ttFormula` payload on log-width
  window (fp3b2 family)
* bounded-support / bounded-polyBound shapes (NOGO-000001 hook)

**Caveat (not a break):** the filter uses *syntactic* exclusion
(gate-count cap + AND-free at the prefix-AND level).  An
adversary can produce a hardwiring-shaped family by:

1. Picking a wider truth-table `f_n : Bitstring k(n) → Bool` with
   `k(n) = O(1)` (constant width).  Such a family has bounded
   support, fails the 1st conjunct.  Excluded.
2. Picking a function class with polynomial-size **non-tree**
   formulae (DAGs).  V2-A only inspects `FormulaCircuit` (tree
   syntax).  But `FormulaCircuit` is the only formula type in
   the trust root's `InPpolyFormula` shape, so DAG-rewriting
   would have to first translate to a tree (which loses
   polynomial size for arbitrary `f_n`).
3. **Open route:** picking a Boolean function family whose
   canonical `FormulaCircuit` representation happens to satisfy
   all 4 conjuncts.  Engineer flagged this in `critic_report.md`.
   I cannot exhibit such a family in the current repo, but I
   also cannot prove no such family exists.

This is the substantive caveat.  See §3 for severity assessment.

### Attack 3 — KnownGuards-factorization

**status:** `no break found`.

* The filter does NOT factor through `HardwiringGuard` or
  `OverbroadUniformProvenance` (which are predicates over
  *languages* / *AC0 parameters*, not `InPpolyFormula` records).
* The filter is strictly stronger than the unboundedness
  conjunct of `FP3Attempt.InSupportFunctionalDiversity`: V2-A
  also requires gate counts, depth, and OR/NOT presence.
* `ProvenanceFilter_v1` is `informal` and not referenced.
* No `gap_from_*` shortcut.

### Attack 4 — Natural-proof / relativization / algebrization

**status:** `attack not applicable` for the current audit
artifact, BUT a precondition for any further promotion.

* V2-A is a Lean predicate on `InPpolyFormula L`.  It is not
  itself a complexity-class separation.  The classical barriers
  (`pnp3/Barrier/{Relativization,NaturalProofs,Algebrization}.lean`)
  apply to lower-bound proofs, not audit predicates.
* **However:** if V2-A were ever used as part of a P ≠ NP path
  (FP-4 + magnification + bridge), Razborov-Rudich would apply.
  V2-A's predicate is constructive (decidable arithmetic), and
  asks for specific syntactic properties (`booleanGateCount`,
  `depth`, gate counts).  Constructive + useful + large
  ⇒ "natural" in Razborov-Rudich's sense.  V2-A has not been
  shown to satisfy any anti-natural-proof escape hatch.
* This is **not a current break** (V2-A is audit-only, not yet
  in a separation chain) but **is a future bar** that any
  promotion beyond `informal` must clear.

### Attack 5 — Collapse-not-contradiction

**status:** `no break found`.

* All exclusion theorems have `False`-conclusion (i.e., `¬
  Filter`); they don't claim a complexity collapse or a
  contradiction in `ZFC`.
* The non-vacuity theorem is `Filter w`; it doesn't claim
  membership in a class beyond what an `InPpolyFormula` record
  literally provides.
* The survivor surface is a conjunction of these; no
  hidden-collapse risk.

### Attack 6 — Vacuity / source-theorem rephrasing

**status:** `no break found`.

* **Vacuity:** filter admits `seededPrefixAndWitness`, a
  concretely-defined non-trivial family with full support `n` at
  length `n` and an honest formula structure.  Filter is
  non-vacuous.
* **Source-theorem rephrasing:** V2-A is a `Prop` on
  `InPpolyFormula`; it is not a `SourceTheorem_*` and does not
  bridge to `ResearchGapWitness`.  No FP-4 surface introduced.

## 3. Caveat severity assessment

The engineer's caveat (V2-A is syntax-sensitive) is real but
**not severe enough to block `informal` promotion**.  Severity
analysis:

| Caveat | Concrete impact | Severity for `informal` promotion | Severity for `accepted` promotion |
| --- | --- | --- | --- |
| Excludes specific syntax of NOGO-000004/6, not all semantic equivalents | Adversary may rewrite a hardwiring function into a mixed-gate form. Existing fp3b1/fp3b2 witnesses use the canonical syntax; future witnesses might not. | LOW — V2-A is by construction an audit predicate over the formal repo's existing witnesses. New witnesses → new exclusions. | MEDIUM — `accepted` status would mean V2-A is a robust filter; syntactic-rewrite attacks must be handled. |
| Razborov-Rudich naturality not addressed | If V2-A enters a separation proof, the natural-proofs barrier kicks in. | LOW — V2-A is audit-only. | HIGH — must address before `accepted`. |
| 4th conjunct (OR/NOT presence) is a coarse structural test | A family that has SOME OR + SOME NOT but is otherwise hardwiring-shaped passes. | MEDIUM — but no such family is in the formal repo, and constructing one would itself be a valuable research artifact. | MEDIUM — same. |
| Engineer's `critic_report.md` is the engineer's self-attack, not independent | Single point of review failure. | LOW — operator's six-attack re-review (this document) is the second pair of eyes. | LOW — same. |
| `seededPrefixAndFamily` is the only exhibited honest family | Vacuity ruled out, but the filter's "useful range" is narrow. | LOW — non-vacuity established. | MEDIUM — operator may want richer honest examples (parity, AC0-computable circuits, etc.). |

Net: severity of all caveats is LOW-to-MEDIUM for `informal`,
MEDIUM-to-HIGH for `accepted`.

## 4. NOGO-chain integrity

| Entry | Status | V2-A interaction |
| --- | --- | --- |
| NOGO-000001 (overbroad uniform provenance) | formalized | covered via `excludes_bounded_support` + `excludes_uniform_polyBound` |
| NOGO-000004 (prefix-AND on log-width) | formalized | covered via `excludes_adversaryWitness_v_natlog2` |
| NOGO-000005 (NOGO-000004 scope correction) | formalized | inherited (V2-A handles the prefix-AND-only specialisation) |
| NOGO-000006 (arbitrary all-essential ttFormula payload) | formalized | covered via `excludes_adversaryWitness_v_arbpayload` |
| NOGO-000007 (support-cardinality meta-barrier) | formalized | DODGED via `not_support_cardinality_only` |

V2-A is consistent with the entire kernel-checked NOGO chain,
both as exclusion target (NOGO-000001/4/5/6) and as meta-barrier
escapee (NOGO-000007).

## 5. Promotion verdict

### Recommended verdict: **`approve_for_informal_promotion`** in a separate operator-approved PR.

V2-A passes all five mandatory Phase 2 deliverables with
kernel-checked, sound proofs.  It dodges fp3b4's
`support_cardinality_barrier`.  It admits a substantively
honest family (`seededPrefixAndFamily`).  It has been
independently re-reviewed for six attacks.  It is consistent
with the entire NOGO chain.

The proposed `informal` promotion in
`spec/known_guards.toml::ProvenanceFilter_v2`:

* `status = "informal"` (NOT `"accepted"`).
* `formal_name = "Pnp3.Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ProvenanceFilter_v2_V2_A_gpt55_phase2"`.
* `caveats =` list of the four documented caveats above.
* `survivor_surface_witness = "pnp3/.../V2_A_gpt55/Survivor.lean::v2_A_gpt55_phase2_survivor_surface"`.

### Why NOT `accepted`

Promotion to `accepted` is forbidden by the seed pack and
inappropriate for the following structural reasons:

* **Razborov-Rudich self-test missing.**  V2-A is constructive
  and useful in the natural-proofs sense.  An anti-natural-proofs
  argument would need to be shipped before any further promotion.
* **Adversarial robustness against rewritings unproven.**  An
  adversary can in principle rewrite hardwiring functions into
  mixed-gate forms.  No anti-rewrite formal lemma exists.
* **Honest-family richness limited.**  Only `seededPrefixAndFamily`
  exhibited.  An `accepted` filter would want diverse honest
  families (parity, AC0-computable Boolean functions, etc.).
* **No FP-4 bridge.**  `accepted` would imply V2-A connects to
  the magnification chain, which requires FP-4 work.

### What `informal` promotion enables

* Future seed packs may reference V2-A as a candidate filter
  to strengthen, attack, or formalise further.
* The Lean theorem name becomes a stable target.
* Engineering work on V2-A→V2-A.1 / V2-B / etc. has a kernel-
  checked starting point.

### What `informal` promotion does NOT enable

* No claim of P ≠ NP progress.
* No claim that V2-A excludes all hardwiring shapes — only the
  currently formalised ones.
* No FP-4 / SourceTheorem / `gap_from_*` / final endpoint.
* No suspension of the seed pack's forbidden scope.

## 6. Recommended next actions (not in scope of this review)

After `informal` promotion, the natural research follow-ups:

1. **`fp3b3.1_v2A_razborov_rudich_self_test`** — prove V2-A is
   either anti-natural (escapes the barrier) or document why the
   barrier doesn't apply.  Likely route: V2-A's
   booleanGateCount conjunct is poly-time but its behavior
   under random functions is not proven "large" in
   Razborov-Rudich's sense.  A `fp3b3.1` seed pack could
   formalise this.
2. **`fp3b3.2_v2A_adversarial_robustness`** — formalise an
   anti-rewrite lemma: "for every Boolean function `f`, every
   `FormulaCircuit n` computing `f` either fails V2-A or is
   provably 'non-hardwiring' in some structural sense."
3. **V2-B / V2-C / V2-D Phase 2** — the other three directions
   are still open; their results may strengthen or refute V2-A
   (e.g., V2-C's bounded-incremental-info filter might
   complement V2-A's gate-shape filter).
4. **CL-0 formalisation** — the cross-length coherence direction
   (V2-B target + the existing CL-0 audit module) remains
   research-target Props, not theorems.

## 7. Audit trail

* Proof modules read in full: Filter.lean, NotSupportCardinalityOnly.lean,
  ExcludesOverbroad.lean, ExcludesPrefixAnd.lean,
  ExcludesArbitraryPayload.lean, NonVacuity.lean, Survivor.lean.
* Engineer's critic report read for cross-reference, not for
  authority.
* Pipeline rerun: `lake build PnP3 Pnp4` + `scripts/check.sh` +
  `validate_jsonl.py` — all green.
* `rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`
  — clean.
* No edits to V2-A files were made during this review.  This
  document is the only artifact produced.

## 8. Closing note

> V2-A is the first FP-N filter candidate that survives all
> currently-formalised hardwiring obstructions while admitting a
> substantively honest family.  It is a real research artifact.
> It is also a NARROW result: it is a syntactic predicate on
> `InPpolyFormula L` records, not a complexity-class separation.
> The promotion path from `informal` to `accepted` is steep and
> requires further formal work; the path from `survivor candidate`
> to `informal` is short and is what this review approves.
