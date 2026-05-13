# fp3b3 priority refresh — V2 successor-design-space audits

## 0. TL;DR

This pack is **operator-scoped meta-review**, dispatched after
NOGO-000009 closed V2-A.1.  Three short markdown audits assess
the remaining V2-* successor design spaces: V2-A.2 (semantic
quotient), V2-B (cross-length coherence), V2-D (shape/provenance
signature).  No Lean code, no JSONL writes, no spec writes, no
candidate creation.

**Outcomes (operator decisions, see `audits/priority_refresh_operator_consolidation.md`):**

* **V2-A.2:** `dispatch_only_meta_review` — do NOT open
  proof-oriented seed pack; only the partial-rule-generated
  variant survives natural-proofs risk audit and that survival
  depends on a future audit.
* **V2-B:** `hold_for_nonvacuity` — survives NOGO-000008/9 but
  may be a parity-only filter.  Future seed pack
  `fp3b3_5_v2_b_cross_length_nonvacuity_refresh` is the
  recommended successor (NOT dispatched here).
* **V2-D:** `reject_route` — displayed-syntax-sensitive, defeated
  by adaptive NOGO-000008-style padding over missing variables,
  AND its stated parity/XOR non-vacuity claim is mathematically
  false on the De Morgan basis.

## 1. Dispatch model

This pack does NOT follow the standard worker-prompt + slots
dispatch model used by `fp3b3_3`.  Instead:

* One short audit-report per route, written by an independent
  reviewer (handle `gpt55` for all three reports as of this
  landing).
* The reports are markdown-only.  No Lean code, no `Candidates/`
  creation, no JSONL writes, no spec writes.
* Operator consolidation reviews each report against existing
  artifacts and issues per-route next-action decisions.

Future dispatches (if any of the routes is opened as a full seed
pack) will use the standard model.  This pack is the **gate**
between rejecting/holding routes vs.  opening proof-oriented
successor packs.

## 2. Reports landed

* `reports/V2_A2_semantic_quotient_gpt55.md` — PR #1243, commit
  `91a663c`.  Distinguishes three V2-A.2 meanings (full / minimal
  / partial semantic quotient).  Verdict:
  `dispatch_only_meta_review`.
* `reports/V2_B_cross_length_gpt55.md` — PR #1244, commit
  `1c7ee80`.  Verdict: `hold_for_nonvacuity`.
* `reports/V2_D_shape_signature_gpt55.md` — PR #1245, commit
  `9ffc1f1`.  Verdict: `reject_route`.

## 3. Allowed / forbidden scope (worker reports)

### Allowed

* Markdown files under `reports/<route>_<handle>.md`.
* Reading any existing file in the repo.
* Citing line numbers from `pnp3/` / `pnp4/` / `spec/` / `outputs/`.

### Forbidden (HARD)

* Lean file creation or edits.
* `outputs/nogolog.jsonl` / `outputs/attempts.jsonl` /
  `spec/known_guards.toml` edits.
* Trust-root edits (`pnp3/Complexity/Interfaces.lean`).
* V2-A / V2-B / V2-D existing Lean module edits.
* `Candidates/` creation.
* `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / final
  endpoint / P ≠ NP language.
* `accepted`-status promotion.

## 4. Cross-references

* NOGO-000008: `outputs/nogolog.jsonl` line 8 (V2-A rewrite
  attack, syntactic-only V2-* design family closed).
* NOGO-000009: `outputs/nogolog.jsonl` line 9 (V2-A.1
  normalize-then-filter meta-barrier).
* V2-A trust root:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`.
* V2-B current sketch:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_B_gpt55/Sketch.lean`.
* V2-D current sketch:
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_D_GPT55/Sketch.lean`.
* fp3b3_3 closure: `../fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_retry_pause_post_M1.md`.
* fp3b3_4 closure: `../fp3b3_4_v2_a_normalise_meta_barrier/audits/M2_operator_review.md`.

## 5. Pack status

**OPEN — closure decisions issued; no follow-on seed pack
dispatched.**

The pack remains in-tree as a meta-review artifact.  Future
dispatches (V2-A.2 narrow meta-review, V2-B non-vacuity refresh,
or any new V2-* successor) will be tracked as separate seed packs
referencing this one.
