# Seed pack `fp3b3_1_v2a_natural_proofs_self_test`

> **Track:** Research-A — sub-pack of `fp3b3_provenance_filter_v2_design/`.
> **Method family:** `ac0_locality_support`.
> **Parent:** the `V2-A / gpt55` candidate ProvenanceFilter_v2 (commit `b7f0418` operator review →
> `approve_for_informal_promotion`; commit `66a900a` registry pin
> `informal`).
> **Status:** **COMPLETED**.  Lean self-test landed in PR #1236 (commit
> `aa3ebd7`); audit report landed in PR #1237 (commit `68ac18f`);
> operator review at commit `33c8925` →
> `accept_audit_finding`.
> **Purpose of this README (retro-fit):** record what the seed pack
> aimed at, what was shipped, and how the result interfaces with
> Razborov-Rudich.  Wires this seed pack into the standard
> documentation shape (`fp3b3` / `fp3b4`-style).

## 0. TL;DR

V2-A is the first ProvenanceFilter_v2 candidate that survived all
three structural NOGOs (NOGO-000001/4/5/6) AND admits a named honest
family (`seededPrefixAndFamily`).  Operator review pinned it as
`informal` pending a Razborov-Rudich naturality self-audit.

This sub-pack ran the self-audit and proved, kernel-checked, that V2-A
is **representation-sensitive on Boolean functions** — it accepts and
rejects different syntactic encodings of the same Boolean function
family.  Consequence: V2-A cannot be a natural property of Boolean
functions in the Razborov-Rudich sense, so the classical naturality
barrier **does not apply to the audit predicate as stated**.

This is a clean escape from one barrier — and, as a side effect,
opens the route to the rewrite-attack landing recorded in sibling
sub-pack `fp3b3_2_v2a_adversarial_robustness`.

## 1. Why this self-audit was necessary

V2-A is built from four conjuncts on a `FormulaCircuit`:

1. unbounded support,
2. `booleanGateCount ≤ 16·|support| + 16`,
3. `depth ≤ 8·|support| + 8`,
4. at `|support| ≥ 2`: presence of at least one OR-gate and one
   NOT-gate.

These are all **syntactic** predicates on the displayed formula tree.
The natural-proofs barrier (Razborov-Rudich) requires a property to be
*extensional* on Boolean functions — i.e. defined on the function
itself, not on a chosen encoding.  Without a self-audit, an operator
cannot tell whether V2-A is:

* an extensional property in disguise (in which case it would inherit
  the naturality barrier), or
* genuinely non-extensional (in which case the barrier doesn't
  apply, at the price of being syntactically defeatable — see
  sibling sub-pack `fp3b3_2`).

This self-test is the kernel-checked instrument that decides between
these two readings.

## 2. Goal (as it was specified)

Produce a kernel-checked theorem of the shape

```lean
theorem v2A_same_language_different_representation :
    ∃ (L : Language) (w_good w_bad : InPpolyFormula L),
      (∀ n x, eval (w_good.family n) x = eval (w_bad.family n) x)
      ∧ ProvenanceFilter_v2_V2_A_gpt55_Filter w_good
      ∧ ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter w_bad
```

plus a short companion audit report classifying V2-A against the four
classical natural-proofs criteria (constructivity, largeness,
usefulness, extensionality) and the three standard barriers
(Razborov-Rudich, relativization, algebrization).

No `sorry`/`admit`, no `axiom`, no spec edits, no candidate package.

## 3. What shipped

### 3.1 Lean self-test

**File:** `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/NaturalProofsSelfTest/RepresentationSensitivity.lean`
(204 LOC; PR #1236, commit `aa3ebd7`).

Headline theorem at `RepresentationSensitivity.lean:175`:

```lean
theorem v2A_same_language_different_representation :
    ∃ (L : Language) (w_good w_bad : InPpolyFormula L), …
```

Supporting construction:

| Name | Role | Where |
| ---- | ---- | ----- |
| `doubleNotPad k c` | Wraps a formula in `k` layers of `¬¬`; preserves Boolean evaluation, adds exactly `2k` NOT gates, leaves AND/OR/support untouched. | `RepresentationSensitivity.lean:35` |
| `paddedSeededPrefixAndFamily` | `doubleNotPad 20 (seededPrefixAndFamily n)`. | `:127` |
| `paddedSeededPrefixAndWitness` | The padded family typed as `InPpolyFormula seededPrefixAndLanguage`. | `:146` |
| `paddedSeededPrefixAndWitness_rejected` | At `n = 1`: cap is `16·1 + 16 = 32`; padded has `4 + 40 = 44` boolean gates → rejected. | `:158` |
| `v2A_same_language_different_representation` | Headline existential. | `:175` |
| `v2A_not_extensional_on_witness_representations` | Weaker corollary. | `:196` |

Six supporting lemmas (`doubleNotPad_eval`,
`notGateCount_doubleNotPad`, `andGateCount_doubleNotPad`,
`orGateCount_doubleNotPad`, `support_doubleNotPad`,
`booleanGateCount_doubleNotPad`, `size_doubleNotPad`) discharge the
mechanical invariance / `+2k` arithmetic.

### 3.2 Audit report

**File:** `reports/V2_A_natural_proofs_audit_gpt55.md` (153 LOC; PR
#1237, commit `68ac18f`).

Classification table:

| Property | Verdict | Operator concur (commit `33c8925`) |
| --- | --- | --- |
| Constructivity | "constructive as a predicate on formula witnesses" | AGREE |
| Largeness | "likely **not** a large property of Boolean functions" | AGREE |
| Usefulness | "useful against currently formalized hardwiring witnesses; not against all small circuits" | AGREE |
| Extensionality | **NO** (kernel-proven) | AGREE |
| Razborov-Rudich (audit predicate use) | `does_not_apply` | AGREE |
| Razborov-Rudich (future lower-bound use) | `uncertain` | AGREE |
| Relativization | `uncertain` | AGREE |
| Algebrization | `uncertain` | AGREE |

Headline verdict: `representation_sensitive_escape_plausible`.

## 4. Allowed / forbidden scope (as it was)

### Allowed

* New file under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/NaturalProofsSelfTest/`.
* `lakefile.lean` — append the new module under existing
  `Glob.one ...` list.
* `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/reports/<report>.md`.

### Forbidden (HARD)

* Trust root: `pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/**`,
  `pnp3/Magnification/{UnconditionalResearchGap,LocalityProvider_Partial,FinalResultMainline,FinalResultAuditRoutes}.lean`.
* Editing `ProvenanceFilter_v2_V2_A_gpt55_Filter` itself — attack the
  ALREADY-COMMITTED candidate as written.
* Editing fp3b3 V2-A `NonVacuity.lean` / `ExcludesOverbroad.lean` /
  `ExcludesPrefixAnd.lean` / `ExcludesArbitraryPayload.lean` /
  `NotSupportCardinalityOnly.lean` / `Survivor.lean` theorem bodies —
  use them as imports.
* Editing existing JSONL log entries (Rule 9 — append-only).
* `axiom` / `opaque` / `Fact` / typeclass-payload (Rule 16).
* `sorry` / `admit` (Rule 1).
* `pnp3/Candidates/<id>/` creation.
* `gap_from_*`, `SourceTheorem_*` (FP-4 territory).
* Promoting `ProvenanceFilter_v2` to `accepted`.

## 5. Acceptance criteria (as verified)

1. `lake build PnP3 Pnp4` green at commit `aa3ebd7`.  ✓
2. `./scripts/check.sh` 17/17 + sub-steps green.  ✓
3. `rg "\bsorry\b|\badmit\b" -g"*.lean"
   pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/NaturalProofsSelfTest/`
   — clean.  ✓
4. No file outside §4 allowed scope was modified.  ✓
5. Audit report exists and follows the natural-proofs classification
   shape.  ✓

## 6. Retroactive six-attack critic angles (operator-verified)

These were re-checked at operator-review time (commit `33c8925`,
review document
`seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/fp3b3_1_and_fp3b3_2_landing_review.md` §5).

1. **Hidden-payload.**  No `class`/`instance`/`Fact`/`opaque`/`axiom`/`decide`/`native_decide`.  All structural.  Clean.
2. **Hardwiring.**  N/A — the self-test is metalevel, not a candidate
   witness.
3. **KnownGuards factorization.**  N/A — no factorisation claim.
4. **Barriers (natural / relativization / algebrization).**  Audit
   report classifies all three; classifications operator-verified.
5. **Collapse-not-contradiction.**  Headline theorem is a positive
   existence claim, not a collapse claim.
6. **Vacuity / source-theorem rephrasing.**  Witnesses are exhibited
   explicitly (`seededPrefixAndWitness`, `paddedSeededPrefixAndWitness`).
   No `SourceTheorem_*` introduced.

## 7. What this sub-pack does NOT do

* Patch V2-A — the patch route (Stream X in the operator review §7)
  is left to a future sub-pack (`fp3b3_3_v2_a_*`).
* Promote V2-A to `accepted` — operator review explicitly blocks this
  (kernel-checked anti-evidence via sibling sub-pack
  `fp3b3_2_v2a_adversarial_robustness`).
* Touch any classical barrier file
  (`pnp3/Barrier/{Relativization,NaturalProofs,Algebrization}.lean`).
* Construct a fourth barrier theorem at the level of the
  Razborov-Rudich main statement — the self-test is locally scoped
  to V2-A only.
* Open a new dispatch round.

## 8. Cross-references

* Audit report:
  `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/reports/V2_A_natural_proofs_audit_gpt55.md`.
* Lean theorem chain:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/NaturalProofsSelfTest/RepresentationSensitivity.lean`.
* Sibling sub-pack (adversarial-robustness attack):
  `seed_packs/fp3b3_2_v2a_adversarial_robustness/`.
* Operator review at commit `33c8925`:
  `seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/fp3b3_1_and_fp3b3_2_landing_review.md`.
* V2-A parent seed pack: `seed_packs/fp3b3_provenance_filter_v2_design/`.
* V2-A registry entry (`informal`):
  `spec/known_guards.toml::ProvenanceFilter_v2`.
* V2-A promotion review:
  `seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/V2_A_gpt55_operator_review.md`.
* Classical Razborov-Rudich barrier (audit-only, not edited by this
  sub-pack): `pnp3/Barrier/NaturalProofs.lean`.

## 9. Closing note

> Together with sibling sub-pack `fp3b3_2_v2a_adversarial_robustness`,
> this self-test produces a complete diagnostic: V2-A is
> non-extensional on Boolean functions, hence outside the
> Razborov-Rudich naturality barrier, hence — for the same reason —
> defeatable by tautological-seed syntactic rewriting (NOGO-000008).
> The two findings are the same coin's two faces.
