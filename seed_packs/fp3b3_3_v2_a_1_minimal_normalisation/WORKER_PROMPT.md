# Worker prompt — fp3b3_3_v2_a_1_minimal_normalisation (Round 1: T1 + T2)

> Send this entire file as the prompt body to one independent
> research engineer (human + LLM session) per slot.  Workers
> self-pick `<YOUR-HANDLE>` and `<SLOT>`.  Multiple workers may
> attack the same slot; the cleanest output is merged at
> audit-review.  This is **Round 1**: only T1 and T2 are open.

---

You are working on slot `T1` or `T2` of seed pack
`fp3b3_3_v2_a_1_minimal_normalisation/`.  The seed pack defines
**V2-A.1**, a successor to the V2-A audit-only ProvenanceFilter_v2
candidate that targets NOGO-000008's syntactic rewrite attack via a
canonical syntactic normalisation pass.

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN before you start.  If RED on a fresh
checkout, stop and report.

## 1. Required reading (in order)

1. `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/README.md` — the
   goal, slot decomposition, allowed/forbidden scope.
2. **The Stream X origin (background context, critical):**
   `seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/fp3b3_1_and_fp3b3_2_landing_review.md` §7.
3. **The attack you're patching:**
   `outputs/nogolog.jsonl::NOGO-000008` and the underlying Lean theorem
   `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean::v2A_rewrite_attack_prefixAnd`.
   In particular, study `seedGate` and `rewritePrefixAndFamily`
   (defined in `RewriteAttack.lean:37–48`).
4. **The companion natural-proofs self-test** (so you understand why
   V2-A is non-extensional and what V2-A.1 trades for the patch):
   `pnp3/.../V2_A_gpt55/NaturalProofsSelfTest/RepresentationSensitivity.lean`
   — especially `doubleNotPad`, `paddedSeededPrefixAndFamily`, and
   `v2A_same_language_different_representation`.
5. **The V2-A predicate you're composing with** (READ-ONLY):
   `pnp3/.../V2_A_gpt55/Filter.lean::ProvenanceFilter_v2_V2_A_gpt55_Filter`
   (line 160), and its phase-2 expansion at line 146.
6. **The honest family that must remain admitted:**
   `pnp3/.../V2_A_gpt55/NonVacuity.lean::seededPrefixAndWitness` and
   the accompanying gate-count / support-card lemmas.
7. **The trust root** (READ-ONLY; if you find yourself wanting to
   edit it, STOP):
   `pnp3/Complexity/Interfaces.lean` for `FormulaCircuit`, `eval`,
   `support`, `size`, `depth`, `andGateCount`, `orGateCount`,
   `notGateCount`, `booleanGateCount`.
8. `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 9, 12, 16.

## 2. Slot list — Round 1 (pick ONE)

**Dependency chain:**

```text
T1 (canonicalNormalise + reduction lemmas)  ← independent
T2 (filter definition + non-vacuity)        ← depends on T1
```

T1 has no dependencies and is the highest-risk slot (the structural
design of the normalisation pass).  T2 is gated on T1 landing.  If
multiple workers attack T1 in parallel, T2 picks the cleanest landed
T1 to import.

If T1 has not yet landed in the tree when you start T2, DO NOT
redefine `canonicalNormalise` in your T2 file.  Instead, ship a
structured **blocker report** at
`seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T2_<HANDLE>_blocked_on_T1.md`
with one section:
"T1 not yet in tree as of `<commit-hash>`; resuming when T1 lands."
Then stop.

| Slot | File | Goal | Depends on |
| ---- | ---- | ---- | ---------- |
| T1 | `V2_A_1_<HANDLE>/Normalisation.lean` | `canonicalNormalise`, `canonicalNormalise_eval`, `canonicalNormalise_size_le`, and the four targeted reduction lemmas listed in README §3 T1. | — |
| T2 | `V2_A_1_<HANDLE>/Filter.lean` + `V2_A_1_<HANDLE>/NonVacuity.lean` | `normalisedWitness`, `ProvenanceFilter_v2_V2_A_1_<HANDLE>_Filter`, `v2A_1_admits_seededPrefixAndWitness`. | **T1** |

T3 / T4 / T5 are NOT in this dispatch round; do not pick them.

## 3. File-path convention

Pick `<YOUR-HANDLE>` (short, lowercase, alphanumeric — e.g. `gpt55`,
`claude46`, `sonnet46`).  Your files go under

```
pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_1_<YOUR-HANDLE>/
```

The trailing handle on the directory means multiple workers can
attack the same Round 1 in parallel without colliding (each lands
its own V2-A.1 attempt).  At Round 2 review, the cleanest landed
attempt is selected as the canonical V2-A.1.  Until then, all
attempts coexist.

Wire each new module into `lakefile.lean` under the existing
`Glob.one ...` list.  Optional smoke at
`pnp3/Tests/AuditRoutes_V2A1_<YOUR-HANDLE>_Smoke.lean` is allowed
but not required for Round 1.

## 4. Allowed / forbidden scope

See seed pack `README.md` §4.  Hard rules:

* No trust-root edit.  In particular, no edits to
  `pnp3/Complexity/Interfaces.lean`.
* **No editing any V2-A file** in
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`.
  V2-A is an IMPORT, not editable.  Specifically: do NOT edit
  `Filter.lean`, `NonVacuity.lean`, the exclusion proofs, or the
  natural-proofs / adversarial-robustness sub-directories.
* No editing existing JSONL log entries (Rule 9 — append-only).
* No `sorry` / `admit` in committed Lean (Rule 1).
* No `axiom` / `opaque` / `Fact` / typeclass-payload (Rule 16).
* No `pnp3/Candidates/<id>/` creation.
* No `gap_from_*` / `SourceTheorem_*` / final endpoint.
* No promotion of `ProvenanceFilter_v2` or `V2_A_1_<HANDLE>` to
  `accepted`.
* No truth-table semantics inside `canonicalNormalise` (this is the
  V2-A.1 vs V2-A.2 boundary; truth-table normalisation is V2-A.2
  territory).
* No appending NOGO entries; V2-A.1 is a positive result.

## 5. Output (exactly ONE of two)

### Outcome A — slot theorem(s) landed

Submit a unified diff or branch named
`worker/fp3b3_3/<SLOT>_<YOUR-HANDLE>` containing:

* New Lean file(s) at the slot path with the named theorem(s).
* Updated `lakefile.lean` wiring.
* Optional `pnp3/Tests/AuditRoutes_V2A1_<HANDLE>_Smoke.lean`.
* One-paragraph commit message naming each new theorem and its
  file:line.

**Acceptance checklist (all must be true):**

- [ ] `lake build PnP3 Pnp4` green.
- [ ] `./scripts/check.sh` green (17/17 + sub-steps).
- [ ] `rg "\bsorry\b|\badmit\b" -g"*.lean"
       pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_1_<HANDLE>/`
      returns nothing.
- [ ] No file outside §4 allowed scope is modified.
- [ ] Targeted reduction lemmas listed in README §3 T1 are all
      shipped (for T1) OR T2's non-vacuity proof goes through (for T2).

### Outcome B — structured failure report

If the slot is structurally unreachable, ship a markdown file at

```
seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T<k>_<YOUR-HANDLE>.md
```

with EXACTLY these four sections:

1. **What was attempted.**
2. **Where it broke.**  Paste the Lean error verbatim.
3. **Local vs global obstruction.**
   * Local: missing helper lemma; recoverable.
   * Global: V2-A.1's syntactic-normalisation route is structurally
     wrong.  Concretely: `canonicalNormalise` cannot be defined to
     satisfy *both* (a) it eliminates the NOGO-000008 seed gate AND
     (b) it leaves `seededPrefixAndFamily` admitted as-is.  This is
     a research result — V2-A's non-extensional-but-defeatable
     trade-off may be inseparable for any purely-syntactic
     normalisation, forcing V2-A.2 (semantic quotient) as the only
     route.  Document carefully — the operator may decide to
     dispatch `fp3b3_4_*` (V2-A.2) instead.
4. **What an integrator must know.**

Broken Lean files MUST NOT be committed.  Failure markdown is the
only artifact in this outcome.

## 6. What success means scientifically

This seed pack is dispatched under the operator's **"positive with
negative-pivot readiness"** stance.  Both outcomes produce durable
artifacts; neither is wasted compute.

If T1 + T2 land (Outcome A), V2-A.1 has:

* A canonical structural normalisation pass on `FormulaCircuit` that
  eliminates the syntactic redundancies exploited by NOGO-000008
  (double negation, tautological `seedGate`, AND-identity with
  `const true`, plus the symmetric AND-contradiction case).
* A composite filter `ProvenanceFilter_v2_V2_A_1_<HANDLE>_Filter`
  that admits the honest seeded prefix-AND family.

This is the structural foundation Round 2 needs to ship the four
classical exclusions (T3), the anti-rewrite theorem (T4), and the
honest Razborov-Rudich re-classification (T4 companion markdown).
Round 2 lands → V2-A.1 enters the registry pipeline as an `informal`
candidate eligible for `accepted` promotion review.

If T1 fails globally (Outcome B with `Global` obstruction; the
normalisation pass cannot be defined syntactically to thread the
needle), that is itself a research result.  The operator will pivot
to seed pack `fp3b3_4_v2_a_normalise_meta_barrier/` whose target is
a **meta-barrier theorem** stating that no structural syntactic
normaliser can both preserve V2-A's non-vacuity and resist
NOGO-000008.  See seed pack README §10 for the pivot protocol.

**Worker scope:** ignore the pivot path — pursue Outcome A or
Outcome B honestly.  The pivot is an operator decision based on
independent review of your failure report's `Global` classification.
Do NOT stage `fp3b3_4_*` artifacts in this dispatch.

## 7. Begin

1. Pick `<YOUR-HANDLE>` and `<SLOT>` (T1 or T2).
2. Verify the green baseline.
3. Read §1 materials in order.
4. Sketch the normalisation cases on paper before writing Lean
   (for T1) or sketch the composition before writing (for T2).
5. Iterate until Outcome A or Outcome B.
6. Submit and stop.

End of prompt.
