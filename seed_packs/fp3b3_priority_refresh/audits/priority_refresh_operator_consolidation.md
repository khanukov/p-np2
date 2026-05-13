# fp3b3 priority refresh — operator consolidation

**Review subjects:**

* `reports/V2_A2_semantic_quotient_gpt55.md` (PR #1243, commit `91a663c`)
* `reports/V2_B_cross_length_gpt55.md` (PR #1244, commit `1c7ee80`)
* `reports/V2_D_shape_signature_gpt55.md` (PR #1245, commit `9ffc1f1`)

**Operator decisions:**

* V2-A.2 → **`dispatch_only_meta_review`** (per report).  No
  proof-oriented seed pack opened.
* V2-B → **`hold_for_nonvacuity`** (per report).  No Phase-2
  dispatch.  Suggested successor name recorded.
* V2-D → **`reject_route`** (per report).  Route archived;
  Sketch.lean kept in-tree as Phase-1 documentation with a
  documented contested non-vacuity claim.

This is operator-scoped consolidation, not a worker artifact.

## 1. V2-A.2 — operator review

The report distinguishes three V2-A.2 meanings:

* **A. Full semantic quotient** — filter membership depends only
  on Boolean function at each length.  Removes NOGO-000008
  distinction trivially but **likely re-enters Razborov-Rudich**
  because the filter becomes a property of Boolean functions /
  truth tables.
* **B. Minimal-formula quotient** — choose minimum representative
  then apply V2-A syntactic checks.  Faces:
  * Natural Proofs risk via minimization-as-Boolean-function-property;
  * `Classical.choose` opacity if canonical representative is
    nonconstructive;
  * Direct NOGO-000009 analogue self-defeat: if minimum
    representative of `seededPrefixAndFamily` collapses to pure
    prefix-AND, V2-A's mixed-gate clause kills non-vacuity.
* **C. Partial semantic quotient** — rule-generated equivalence
  over named local moves (tautological seed insertion/removal,
  bounded associativity).  Only viable variant.  Patches
  NOGO-000008 by explicit invariance theorem without claiming
  full Boolean extensionality.  Still requires a fresh
  natural-proofs audit because a sufficiently broad local
  rewrite system can silently become truth-table-complete.

**Operator verification (sanity checks):**

* The repository's V2-A natural-proofs self-test at
  `pnp3/.../V2_A_gpt55/NaturalProofsSelfTest/RepresentationSensitivity.lean::v2A_same_language_different_representation`
  proves V2-A is non-extensional.  This is what kept V2-A out of
  the formal Razborov-Rudich net (Outcome B of the V2-A natural
  proofs audit at
  `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/reports/V2_A_natural_proofs_audit_gpt55.md`).
  The report's claim that **a full semantic quotient removes
  exactly that escape hatch** is correct: extensionality at the
  filter level converts witness-level provenance into a
  Boolean-function property.
* The report's NOGO-000009 analogue argument is correct: if
  the minimum-formula quotient elects pure `prefixAnd` as the
  canonical representative of `seededPrefixAndFamily`, the V2-A
  mixed-gate clause rejects it.  This is the **same structural
  failure** the M2 Lean theorem closed for the syntactic
  normaliser class, just reproduced semantically.  NOGO-000009
  does not formally apply (`StructuralNormaliser` is a syntactic
  class), but the design lesson generalises.
* The report's partial-quotient framing is honest about the
  remaining risks (creep toward full quotient, hidden
  truth-table completeness).

**Decision: `dispatch_only_meta_review` — APPROVED.**

The report's recommendation matches the operator's reading.  No
proof-oriented seed pack
(`seed_packs/fp3b3_5_v2_a_2_semantic_quotient/`) is opened in
this round.  If V2-A.2 is later pursued, the first dispatch must
be a narrow meta-review producing a go/no-go decision between
the three variants, with C the only operator-allowed default
(A and B require explicit Natural Proofs bypass plans before
proof-oriented dispatch is considered).

## 2. V2-B — operator review

The report classifies V2-B as semantic cross-length recurrence
with parity-shaped transition.  Key findings:

* **NOGO interaction:** V2-B survives direct NOGO-000008 attack
  (semantic eval, not displayed syntax) and NOGO-000009
  (no bottom-up structural normaliser).  Survives NOGO-000007
  because cross-length recurrence is not support-cardinality-only.
  NOGO-000006 survival uncertain pending Phase-2 quantifier
  discipline.
* **Non-vacuity:** the xor-successor equation
  `family (n + 1)(x ++ [b]) = family n x XOR b` is satisfied by
  cumulative parity by construction.  The report verifies that
  OR, AND, and `seededPrefixAnd` do **not** satisfy the equation.
  No additional admitted family currently demonstrated.

**Operator verification:**

* The report's OR/AND/seededPrefixAnd disqualification is
  correct.  At `family n = OR x_0 ... x_{n-1}`, if old value is
  true and `b = true`, xor-successor demands `false`, but OR at
  `n+1` remains true — fails.  Similar for AND.  `seededPrefixAnd`
  is `and prefixAnd seedGate`; the seed is semantically neutral,
  so the recurrence collapses to the prefixAnd recurrence which
  also doesn't satisfy xor-successor.
* Operator concurs that the current V2-B sketch is effectively a
  parity recogniser.  Cumulative parity satisfies the xor-successor
  recurrence; the question is whether ANY non-affine-over-GF(2)
  family does.
* The report's natural-proofs / relativization / algebrization
  caveats are honest.  Cross-length xor recurrence is naturally
  algebrizing (it can be lifted to GF(2)-linear computation), so
  the route is not algebrization-resistant.

**Decision: `hold_for_nonvacuity` — APPROVED.**

V2-B does not get a Phase-2 dispatch in this round.  Operator
records the suggested follow-on seed pack name for future
reference:

```
seed_packs/fp3b3_5_v2_b_cross_length_nonvacuity_refresh/
```

The suggested slot decomposition in the report §6 (T1-T6 with
T2 dedicated to non-parity admitted families) is reasonable but
not committed to in this consolidation.  If V2-B is opened later,
the operator may revise the slot list.

## 3. V2-D — operator review

The report recommends `reject_route` on three independent grounds:

1. Adaptive NOGO-000008 attack via padding over missing variables.
2. NOGO-000009-style self-defeat under normalize-then-filter
   (either tautologies remain or normalization deletes the exact
   syntax V2-D needs).
3. **Stated parity/XOR non-vacuity claim is mathematically false.**

**Operator verification of finding 3 (the load-bearing one):**

V2-D Sketch.lean lines 76-81 claim the standard parity family
encoded as `xor a b = (a ∧ ¬ b) ∨ (¬ a ∧ b)` with balanced or
left-associated fold gives `inputOccurrences 0 = 1`.  Direct
expansion at the smallest non-trivial case `n = 2`:

```text
xor x_0 x_1 = (x_0 ∧ ¬x_1) ∨ (¬x_0 ∧ x_1)
inputOccurrences 0 = count occurrences of x_0
                   = 1 (in (x_0 ∧ ¬x_1)) + 1 (in (¬x_0 ∧ x_1))
                   = 2
```

So at `n = 2`, `inputOccurrences 0 = 2`, not 1.  The claim
**fails at the smallest non-trivial length**.  Folding for `n ≥ 3`
duplicates subformulas further, making the count strictly grow.

Conclusion: the comment-level non-vacuity story in V2-D
Sketch.lean is mathematically false for the De Morgan basis V2-D
itself uses.  The report's analysis is **correct**.

**Operator verification of finding 1 (NOGO-000008 adaptation):**

The proposed adaptive attack
`C_n ↦ C_n ∧ ⋀_{i ∉ support(C_n)} (x_i ∨ ¬x_i)`
preserves Boolean function (each factor is tautological),
inflates displayed support to full ambient set, and can avoid
adding occurrences of coordinate 0 if the padding ranges over
`i ∈ {1, ..., n-1} \ support`.  The original `prefixAnd n n`
already has `x_0` appearing exactly once when the prefix-window
covers position 0; padding outside coordinate 0 preserves
`inputOccurrences 0 = 1`.  The adapted attack satisfies both V2-D
conjuncts while computing the same Boolean function as the
sublinear-support prefix hardwiring V2-D was meant to exclude.

So V2-D is defeated by a tautological-padding adaptation of the
NOGO-000008 pattern.

**Operator verification of finding 2 (NOGO-000009 self-defeat
analogue):**

Any structural normaliser strong enough to remove the
"⋀ (x_i ∨ ¬x_i)" padding will also delete `(x_0 ∨ ¬x_0)`-style
seeds from honest formulas, which can collapse the exact
`inputOccurrences 0 = 1` signature V2-D's second conjunct
requires.  Conversely, a normaliser that preserves
`(x_i ∨ ¬x_i)` factors leaves the adaptive attack accepted.  The
fork mirrors NOGO-000009: either the route stays
representation-sensitive and is defeated, or it normalises and
loses its only non-cardinality signal.

**Decision: `reject_route` — APPROVED.**

V2-D is archived as a rejected route.  The Sketch.lean file
remains in-tree as Phase-1 sketch documentation; the operator
does **not** edit it in this consolidation (forbidden-scope rule
on existing V2-D Lean module would require a separate seed pack
dispatch).  However, the operator records here:

* V2-D Sketch.lean's docstring comment on parity/XOR
  non-vacuity (lines 75-81) is **contested as mathematically
  false on the De Morgan basis**.  Any future worker reading
  V2-D Sketch.lean for inspiration should read this
  consolidation document and the V2-D report first to avoid
  wasting effort formalising a false claim.
* V2-D is NOT promoted to any registry, and remains absent from
  `spec/known_guards.toml`.

## 4. NOGO log decision

**No NOGO-000010 is added in this round.**

Reasoning:

* V2-D's adaptive-attack pattern is conceptually covered by
  NOGO-000008's `structural_pattern` and `why_generalizes` fields,
  which already state: "syntactic-only exclusion of any
  hardwiring witness can be neutralised by O(1) tautological
  rewriting."  V2-D is a syntactic-only exclusion (via
  `inputOccurrences`), so it falls under NOGO-000008's reach.
* V2-D never had a Lean-kernel-checked Phase-2 survivor surface.
  There is no `formal_witness` Lean theorem proving the V2-D-specific
  adaptive attack.  Adding NOGO-000010 with the V2-D report as
  `formal_witness` would be markdown-grade, which is below the
  NOGO-entry standard set by NOGO-000007 / 000008 / 000009.
* V2-B and V2-A.2 are HOLD / META-REVIEW only.  No new NOGO is
  generated by `hold` or `meta_review` outcomes.

If a future dispatch produces a Lean theorem formalising the
V2-D adaptive attack (analogous to
`RewriteAttack.lean::v2A_rewrite_attack_prefixAnd` for NOGO-000008),
NOGO-000010 may be added at that point with the Lean theorem as
formal_witness.  Operator notes this as deferred, not blocked.

## 5. Cross-route synthesis

After NOGO-000008 + NOGO-000009 closed the syntactic-only V2
family, the priority refresh reports collectively show:

| Route | NOGO-000008 | NOGO-000009 | Natural Proofs | Non-vacuity | Decision |
| --- | --- | --- | --- | --- | --- |
| V2-A.2 full | survives | uncertain | likely re-enters | uncertain | block |
| V2-A.2 minimal | survives if seed removed | analogous risk | medium-high | risk | block |
| V2-A.2 partial | covers explicit rules | outside class | lower but audit-required | OK | meta-review |
| V2-B | survives | survives | uncertain | parity-only risk | hold |
| V2-D | adapts → defeats | self-defeats | uncertain | false as written | reject |

The pattern across all three routes: **NOGO-000008 + NOGO-000009
durably ruled out the entire syntactic-only V2 design family,
including all natural patches** (normalisation, full extensional
quotient, minimum-formula quotient, displayed-occurrence
signature).  The only routes that survive at all are:

* V2-A.2 partial quotient (narrow, rule-generated, audit-required);
* V2-B cross-length semantic recurrence (non-vacuity refresh
  needed);
* genuinely new design surfaces not yet proposed.

The space of plausible audit-route survivors has shrunk
materially.  Operator notes this as a candid update: V2 family
audit routes for `ProvenanceFilter_v2` are running out of natural
syntactic-or-quotient design moves.  Future dispatches should
either invest in V2-A.2-partial / V2-B-refresh under careful
barrier discipline, OR pivot to a different family entirely
(non-syntactic provenance, semantic complexity invariants,
external audit-route categories).

This is informational; no new pivot decision is issued here.

## 6. Per-route next-action summary

* **V2-A.2:** no dispatch.  If user later wants to pursue: open
  `seed_packs/fp3b3_5_v2_a_2_partial_quotient_metareview/` with
  markdown-only deliverable producing a go/no-go between full /
  minimal / partial variants.  Full and minimal require explicit
  Natural Proofs bypass plans; partial requires a future
  natural-proofs audit comparable to the V2-A self-test at
  `pnp3/.../V2_A_gpt55/NaturalProofsSelfTest/`.
* **V2-B:** no dispatch.  If user later wants to pursue: open
  `seed_packs/fp3b3_5_v2_b_cross_length_nonvacuity_refresh/`
  with slot decomposition focused on finding non-parity admitted
  families OR proving the route is intentionally parity-specific
  and scoping it as an audit-only artifact.
* **V2-D:** route archived.  No follow-on dispatch.  Sketch.lean
  remains in-tree as Phase-1 documentation; this consolidation
  flags the contested non-vacuity claim.

## 7. Audit-only scope confirmation

This consolidation writes nothing to:
* `outputs/nogolog.jsonl` (NOGO-000010 not added — see §4).
* `outputs/attempts.jsonl`.
* `spec/known_guards.toml`.
* Any V2-A / V2-B / V2-D / V2-A.1 Lean module.
* The trust root.

No `accepted` promotions, no FP-4 implications, no final-endpoint
implications, no P ≠ NP claims.

## 8. Cross-references

* fp3b3_4 M2 closure: `../fp3b3_4_v2_a_normalise_meta_barrier/audits/M2_operator_review.md`.
* fp3b3_3 closure: `../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_retry_pause_post_M1.md`.
* NOGO-000008 / NOGO-000009: `outputs/nogolog.jsonl` lines 8-9.
* V2-A trust root:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`.
* V2-B sketch:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_B_gpt55/Sketch.lean`.
* V2-D sketch (contested non-vacuity claim, lines 75-81):
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_D_GPT55/Sketch.lean`.
