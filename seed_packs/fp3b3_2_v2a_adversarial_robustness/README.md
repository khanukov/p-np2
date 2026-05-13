# Seed pack `fp3b3_2_v2a_adversarial_robustness`

> **Track:** Research-A — sub-pack of `fp3b3_provenance_filter_v2_design/`.
> **Method family:** `ac0_locality_support`.
> **Parent:** the `V2-A / gpt55` candidate ProvenanceFilter_v2 (commit `b7f0418` operator review →
> `approve_for_informal_promotion`; commit `66a900a` registry pin
> `informal`).
> **Sibling:** `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/`
> (representation-sensitivity self-test).
> **Status:** **COMPLETED — ATTACK_LANDED**.  Lean attack landed in
> PR #1238 (commit `aa9c3a2` / underlying `c06e413`); NOGO-000008
> recorded at commit `e375dd4`; operator review at commit `33c8925`
> → `accept_attack_landing`.
> **Purpose of this README (retro-fit):** record what the seed pack
> aimed at, what was shipped, and the resulting structural barrier
> on the entire syntactic-only V2-* family.  Wires this seed pack
> into the standard documentation shape (`fp3b3` / `fp3b4`-style).

## 0. TL;DR

V2-A is purely syntactic (four conjuncts on the displayed
`FormulaCircuit` tree).  Its sibling sub-pack `fp3b3_1` already proved
that V2-A is non-extensional on Boolean functions.  Open question:
**does that non-extensionality break V2-A as an audit predicate?**

This sub-pack ran an adversarial-robustness test and proved,
kernel-checked, that the answer is **yes**: a strict `InPpolyFormula`
for the **same** `adversaryLanguage_v_natlog2` that NOGO-000004/5
exclude is **admitted** by V2-A, simply by conjoining the canonical
prefix-AND hardwiring with a tautological seed gate
(`x_0 ∨ ¬x_0`).

The attack lands because V2-A's own non-vacuity strategy (the
`seedGate`) is the same mechanism the adversary uses.  V2-A admits
its honest family BECAUSE it accepts an OR + NOT presence cheaply
attached to anything — so it admits a hardwiring with the SAME
ornament too.

NOGO-000008 records the structural lesson.  It generalises: any future
V2-* candidate whose admission criterion is gate-type-count and
depth + a presence check is defeated by the same construction.

## 1. Why this attack was necessary

V2-A's `informal` registry pin came with an operator caveat (commit
`b7f0418` §3, caveat 1): "excludes specific syntax of NOGO-000004/6,
not all semantic equivalents — severity MEDIUM-unproven."  Without a
formal anti-evidence test, V2-A could plausibly have been promoted to
`accepted` by a future operator who skipped the syntactic-rewrite
audit.

An adversarial-robustness test produces one of two outcomes, both
useful:

* **`ATTACK_LANDED`:** kernel-checked construction that V2-A admits.
  Promotes the operator caveat from MEDIUM-unproven to HIGH-refuted;
  formally blocks `accepted` promotion.  Records a structural barrier
  on the entire V2-* design family.
* **`ATTACK_NOT_FOUND`:** structured failure report explaining what
  was attempted, where it broke, whether the obstruction is local or
  global.  A clean `ATTACK_NOT_FOUND` would strengthen V2-A's
  promotability.

The actual outcome was `ATTACK_LANDED`.

## 2. Goal (as it was specified)

Produce a kernel-checked theorem of the shape

```lean
theorem v2A_rewrite_attack_prefixAnd :
    ∃ (L : Language) (w_rewritten : InPpolyFormula L),
      L = adversaryLanguage_v_natlog2 ∧
      ProvenanceFilter_v2_V2_A_gpt55_Filter w_rewritten
```

The witness must compute the **same Boolean function family** as
`adversaryWitness_v_natlog2` (which V2-A's
`excludes_adversaryWitness_v_natlog2` rejects), be packaged as a
strict `InPpolyFormula` (NOT a lazy `LiftPpolyFormula`), and satisfy
all four V2-A conjuncts.

If the primary prefix-AND target landed, the worker could optionally
also attack the `ttFormula` arbitrary-payload exclusion
(`NOGO-000006`-shaped); not required for the seed pack to count.

No `sorry`/`admit`, no `axiom`, no spec edits, no candidate package
promotion, no FP-4 territory.

## 3. What shipped

### 3.1 Lean attack

**File:** `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean`
(219 LOC; PR #1238, commit `c06e413`).

Headline theorem at `RewriteAttack.lean:207`:

```lean
theorem v2A_rewrite_attack_prefixAnd :
    ∃ (L : Language) (w_rewritten : InPpolyFormula L),
      L = adversaryLanguage_v_natlog2 ∧
      ProvenanceFilter_v2_V2_A_gpt55_Filter w_rewritten
```

Supporting construction:

| Name | Role | Where |
| ---- | ---- | ----- |
| `seedGate n h` | The tautology `(x_0 ∨ ¬x_0)`; reused from V2-A's own `NonVacuity.lean`. | (imported) |
| `rewritePrefixAndFamily n` | At `n ≥ 1`: `and (adversaryFamily_v_natlog2 n) (seedGate n h)`; at `n = 0`: unchanged. | `RewriteAttack.lean:48` |
| `rewritePrefixAndFamily_eval_eq` | Semantic equality with `adversaryFamily_v_natlog2`. | `:65` |
| `rewritePrefixAndLanguage` | Definitionally `adversaryLanguage_v_natlog2`. | `:82` |
| `rewritePrefixAndPolyBound` | `fun n => 2*n + 6`; linear poly bound. | `:88` |
| `rewritePrefixAndFamily_size_le` | Size bound `2n+6`. | `:96` |
| `adversaryFamily_support_subset_rewrite` | Original support ⊆ rewritten support. | `:114` |
| `logWidthNat_le_rewrite_support_card` | Support card ≥ `logWidthNat n`. | `:122` |
| `rewritePrefixAndFamily_booleanGateCount` | At `n ≥ 1`: `logWidthNat n + 3`. | `:130` |
| `rewritePrefixAndFamily_depth_le` | Depth ≤ size. | `:151` |
| `rewritePrefixAndWitness` | The `InPpolyFormula` packaging. | `:163` |
| `rewritePrefixAndWitness_admitted` | All four V2-A conjuncts satisfied. | `:175` |
| `v2A_rewrite_attack_prefixAnd` | Headline existential. | `:207` |

### 3.2 Failure report (engineer-side)

**File:** `failures/V2_A_rewrite_attack_gpt55.md` (56 LOC; PR #1238).

Honestly named `failures/` — this is the engineer's failure report on
the **filter** (V2-A failed to resist the attack), not on the worker's
own task.  Sub-pack convention: the `failures/` directory is for
*adversarial outcomes against the parent candidate*, irrespective of
whether the worker considers it a success on their own end.

The report:

* declares `ATTACK_LANDED`;
* points at the exact theorem name and file:line;
* explicitly disclaims spec edits, accepted promotion, FP-4,
  SourceTheorem, `gap_from_*`, final endpoint, candidate package
  creation — operator-verified at commit `33c8925`;
* notes the secondary `ttFormula` arbitrary-payload attack was not
  pursued (one landing suffices for the seed pack outcome).

### 3.3 NOGO-000008 entry

**File:** `outputs/nogolog.jsonl::NOGO-000008` (commit `e375dd4`).

| Field | Value |
| --- | --- |
| `id` | `NOGO-000008` |
| `candidate_id` | `fp3b3_provenance_filter_v2_design_V2_A_gpt55` |
| `method_family` | `ac0_locality_support` |
| `status` | `formalized` |
| `failure_class` | `hardwiring` |
| `formal_witness` | `pnp3/.../RewriteAttack.lean:207` (`v2A_rewrite_attack_prefixAnd`) |
| `regression_test` | the Lean file, wired into `lakefile.lean::Glob.one` |
| `structural_pattern` | "Tautological-seed syntactic rewrite circumvents purely-syntactic ProvenanceFilter_v2 candidates …" |
| `why_generalizes` | "applies to the entire syntactic-only V2-* family, not just V2-A" |
| `supersedes` | unset (NOGO-000004/5 remain valid syntactic-shape exclusions; NOGO-000008 records the meta-barrier on the exclusion mechanism). |

## 4. Allowed / forbidden scope (as it was)

### Allowed

* New file under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/`.
* `lakefile.lean` — append the new module under existing
  `Glob.one ...` list.
* `seed_packs/fp3b3_2_v2a_adversarial_robustness/failures/<report>.md`.
* `outputs/nogolog.jsonl` — append `NOGO-000008` (governance side,
  shipped separately in commit `e375dd4`).

### Forbidden (HARD)

* Trust root: `pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/**`,
  `pnp3/Magnification/{UnconditionalResearchGap,LocalityProvider_Partial,FinalResultMainline,FinalResultAuditRoutes}.lean`.
* Editing `ProvenanceFilter_v2_V2_A_gpt55_Filter` itself — attack the
  ALREADY-COMMITTED candidate as written.
* Editing V2-A `Filter.lean` / `NonVacuity.lean` / `ExcludesOverbroad.lean` /
  `ExcludesPrefixAnd.lean` / `ExcludesArbitraryPayload.lean` /
  `NotSupportCardinalityOnly.lean` / `Survivor.lean` theorem bodies —
  use them as imports.
* Editing existing JSONL log entries (Rule 9 — append-only).
* `axiom` / `opaque` / `Fact` / typeclass-payload (Rule 16).
* `sorry` / `admit` (Rule 1).
* `pnp3/Candidates/<id>/` creation.
* `gap_from_*`, `SourceTheorem_*` (FP-4 territory).
* Promoting `ProvenanceFilter_v2` to `accepted`.
* Replacing V2-A with a "patched" V2-A.1 / V2-A.2 — that's Stream X
  in the operator review §7, future sub-pack.

## 5. Acceptance criteria (as verified)

1. `lake build PnP3 Pnp4` green at commit `c06e413`.  ✓
2. `./scripts/check.sh` 17/17 + sub-steps green.  ✓
3. `rg "\bsorry\b|\badmit\b" -g"*.lean"
   pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/`
   — clean.  ✓
4. No file outside §4 allowed scope was modified.  ✓
5. Failure report exists and disclaims out-of-scope artifacts.  ✓
6. NOGO-000008 validated by `validate_jsonl.py` post-append.  ✓

## 6. Retroactive six-attack critic angles (operator-verified)

These were re-checked at operator-review time (commit `33c8925`,
review document
`seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/fp3b3_1_and_fp3b3_2_landing_review.md` §5).

1. **Hidden-payload.**  No `class`/`instance`/`Fact`/`opaque`/`axiom`/`decide`/`native_decide`.  All structural.  Clean.
2. **Hardwiring.**  The attack DEMONSTRATES a hardwiring-equivalent
   witness inside the audit.  That IS the result, not a flaw of the
   attack.  Operator review classified `failure_class = hardwiring` for
   NOGO-000008 on this basis.
3. **KnownGuards factorization.**  No factorisation claim.
4. **Barriers (natural / relativization / algebrization).**  The
   attack is structural, not engaging classical barriers.  Sibling
   sub-pack `fp3b3_1_v2a_natural_proofs_self_test` handles the
   barrier-side classification.
5. **Collapse-not-contradiction.**  Headline theorem is a positive
   existence claim, not a collapse claim.
6. **Vacuity / source-theorem rephrasing.**  Witness exhibited
   explicitly (`rewritePrefixAndWitness`).  No `SourceTheorem_*`
   introduced.  No `gap_from_*`.

## 7. What this sub-pack does NOT do

* Patch V2-A — the patch route (Stream X in the operator review §7)
  is left to a future sub-pack (`fp3b3_3_v2_a_*` for V2-A.1 minimal
  normalisation; `fp3b3_4_v2_a_*` for V2-A.2 semantic quotient).
* Attack the secondary `ttFormula` arbitrary-payload exclusion — one
  landing was sufficient.  A future sub-pack could land a parallel
  attack on `NOGO-000006`-shape if desired.
* Touch any classical barrier file
  (`pnp3/Barrier/{Relativization,NaturalProofs,Algebrization}.lean`).
* Open a new dispatch round on V2-A directly — V2-A is now formally
  closed for promotion.

## 8. Cross-references

* Failure report:
  `seed_packs/fp3b3_2_v2a_adversarial_robustness/failures/V2_A_rewrite_attack_gpt55.md`.
* Lean attack:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean`.
* Sibling sub-pack (natural-proofs self-test):
  `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/`.
* Operator review at commit `33c8925`:
  `seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/fp3b3_1_and_fp3b3_2_landing_review.md`.
* V2-A parent seed pack: `seed_packs/fp3b3_provenance_filter_v2_design/`.
* V2-A registry entry (`informal`):
  `spec/known_guards.toml::ProvenanceFilter_v2`.
* V2-A promotion review:
  `seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/V2_A_gpt55_operator_review.md`.
* NOGO-000008 entry: `outputs/nogolog.jsonl` (governance commit
  `e375dd4`).
* Related concrete NOGOs: NOGO-000004 (prefix-AND syntactic
  exclusion) and NOGO-000005 (its hardwiring twin), both remaining
  valid Lean theorems and NOT superseded by NOGO-000008.

## 9. Closing note

> Together with sibling sub-pack `fp3b3_1_v2a_natural_proofs_self_test`,
> this attack produces a complete diagnostic: V2-A is non-extensional
> on Boolean functions, hence outside the Razborov-Rudich naturality
> barrier, hence — for the same reason — defeatable by tautological-
> seed syntactic rewriting.  V2-A remains an `informal` registry pin
> (audit-only, excludes specific syntactic shapes), but `accepted`
> promotion is formally closed by kernel-checked anti-evidence.
> The lesson generalises: NOGO-000008 invalidates the entire purely
> syntactic V2-* family in advance.
