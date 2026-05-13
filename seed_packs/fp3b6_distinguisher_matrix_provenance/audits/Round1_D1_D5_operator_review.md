# fp3b6 Round 1 — D1 + D5 operator review

**Review subjects:**

* D1 worker landing: PR #1246 (commit `680c5b7`), merged via `2671b7d` → `e1b516d`.
  File: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/MatrixPrimitives.lean` (169 LOC).
* D5 worker landing: PR #1247 (commit `2113e0b`), merged via `e1b516d`.
  File: `seed_packs/fp3b6_distinguisher_matrix_provenance/failures/D5_gpt55.md` (45 LOC).

**Operator decisions:**

* **D1: APPROVE LANDING** with one noted deviation (cleaner XOR-only fingerprint formulation instead of XOR-of-AND; mathematically equivalent under the rowSupport restriction).
* **D5: ACCEPT AS WORKFLOW ARTIFACT, NOT RESEARCH FINDING.**  Worker correctly refused to fabricate context.  D5 task remains TODO under an enriched dispatch.

This is operator-scoped review, not a worker artifact.

## 1. D1 verification

### 1.1 Build status

* `lake build PnP3 Pnp4` — GREEN.  Module built as step 3087/3088
  (`Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives`).
* `./scripts/check.sh` — PASS_SHAPE_ONLY across 17/17 steps.
* `lakefile.lean` wires the new module under
  the existing `Glob.one ...` list pattern (one-line addition).
* Module inherits standard Mathlib axiom backbone (`propext`,
  `Classical.choice`, `Quot.sound`); counts unchanged (358/362
  in pnp3).

### 1.2 Forbidden-construct scan

`grep -cE "sorry|admit|axiom|opaque|Fact |Classical\."` on
`MatrixPrimitives.lean` returns **0**.  Module is kernel-clean
per Rules 1, 16, and the pack's §4 forbidden-scope list.

### 1.3 Definition coverage vs WORKER_PROMPT §3.1

| Required | Status | Notes |
| --- | --- | --- |
| `BoolMatrix m n` | ✓ at line 28 | exact spec match |
| `rowSupport` | ✓ at line 31 | exact spec match |
| `colSupport` | ✓ at line 36 | exact spec match |
| `SparseDistinguisherMatrix` | ✓ at line 49 | exact spec match (k as first argument; minor ordering choice) |
| `fingerprint` | ✓ at line 75 | **see §1.5 deviation note** |
| `MatrixRowSupportCard` | ✓ at line 41 | additional convenience definition |
| `MatrixColSupportCard` | ✓ at line 45 | additional convenience definition |
| `zeroMatrix` | ✓ at line 54 | additional, used by `fingerprint_zero` |
| `transpose` | ✓ at line 58 | additional, used by `*_transpose` lemmas |
| `oddBool` | ✓ at line 62 | local parity helper |
| `supportParity` | ✓ at line 66 | local helper supporting `fingerprint` |

All required definitions present.  Five additional convenience
definitions added (`MatrixRowSupportCard`, `MatrixColSupportCard`,
`zeroMatrix`, `transpose`, `oddBool`, `supportParity`) — these are
within scope and contribute to the lemma surface.

### 1.4 Lemma coverage vs WORKER_PROMPT §3.2

| Required | Status | Notes |
| --- | --- | --- |
| `sparseDistinguisherMatrix_transpose` | **DEVIATION** | Not present as a single lemma; instead split into `rowSupport_transpose` (line 80), `colSupport_transpose` (line 86), and `row_col_transpose_sanity` (line 92).  Together these cover the same conceptual ground (transpose preserves sparsity profile).  Accept the split as equivalent. |
| `fingerprint_codomain` | ✓ at line 97 (`fingerprint_codomain_sanity`) | trivially `True` placeholder; the codomain match is Lean-checked at the definitional level so the runtime theorem is just a canary. |
| `fingerprint_local` | ✓ at line 120 | exact spec match |
| `fingerprint_zero` | ✓ at line 139 | exact spec match |
| `sparseDistinguisherMatrix_zero` (zero matrix sparsity) | ✓ at line 145 (`zero_matrix_sparsity`) | renamed; semantically identical |

Plus two operator-helpful additions:
* `rowSupport_card_le_n` (line 154): row support bounded by `n`.
* `colSupport_card_le_m` (line 160): column support bounded by `m`.

These tighten the basic support-size invariants and are useful
for Round-2 D2/D3 work.

### 1.5 Deviation note: XOR-of-AND vs row-restricted XOR

WORKER_PROMPT §3.1 specified:

```
(fingerprint D x) i = bigXor (j ∈ row support) (x j ∧ D i j)
```

i.e., XOR over all columns with the AND-with-matrix-entry guard.
Worker simplified to:

```
fingerprint D x i = supportParity (rowSupport D i) x
                 = oddBool ((rowSupport D i).filter (x j = true)).card
```

i.e., XOR over `x j` for `j` already in `rowSupport D i`.

**Mathematical equivalence:** by definition of `rowSupport D i`
(line 31), `j ∈ rowSupport D i ↔ D i j = true`.  Therefore
`(x j) AND (D i j) = (x j) AND true = x j` for `j ∈ rowSupport D i`;
and for `j ∉ rowSupport D i`, `(x j) AND (D i j) = (x j) AND false = false`,
contributing 0 to the XOR.  So the row-restricted XOR equals the
full XOR-of-AND.

**Operator verdict:** the worker's simplification is **cleaner**
than the spec — it makes the locality dependence on `rowSupport`
explicit at the definition level and avoids the algebraic
`Bool.and` distribution step.  Accept the deviation.

The encoding via `oddBool ((s.filter predicate).card)` matches
the standard Mathlib parity-over-finset pattern and integrates
cleanly with Mathlib's `Finset.card` calculus, simplifying D2 / D3
proof obligations.

### 1.6 Scope compliance

* No trust-root edit (`pnp3/Complexity/Interfaces.lean`
  imported, not modified).
* No edits to existing audit-route modules.
* No `outputs/`/`spec/` writes.
* `lakefile.lean` adds exactly one `Glob.one` line for the
  new module — within allowed scope.
* Optional smoke test under `pnp3/Tests/` not added — allowed
  per WORKER_PROMPT §3.4 (smoke is optional).

### 1.7 D1 verdict

**APPROVED.**  D1 lands as the foundation for Round 2 (D2 toy
separation + D3 anti-collapse).  Operator notes the spec
deviation in §1.5 but accepts it as a strict improvement over
the literal spec.

The `supportParity` + `oddBool` encoding gives D2/D3 workers a
clean parity-over-finset primitive that integrates with Mathlib's
`Finset` API.  Recommended: D2/D3 workers build on
`supportParity_local` (line 106) and `fingerprint_local` (line
120) as the locality discipline.

## 2. D5 dispatch-workflow analysis

### 2.1 What happened

The D5 worker's failure report (sections 1-4) honestly
documents:

1. The worker searched the local checkout for the required
   inputs (pack README, WORKER_PROMPT, fp3b5 strategic audit,
   Q4 first-move report, NOGO log, Research Constitution).
2. All inputs were absent.
3. Worker correctly refused to fabricate citations or
   parameter mappings without grounding.
4. Worker classified as `Local` (checkout/materials problem,
   not a global research obstruction).

### 2.2 Root cause: branch divergence

The dispatch pipeline routed the D5 worker to a checkout based
off `main` (commit `91693ef` lineage), which does **not** contain
the seed-pack materials that live on the dev branch
`claude/research-governance-phase0-lmZBP`.

The dev branch contains:
* `seed_packs/fp3b6_distinguisher_matrix_provenance/README.md`
* `seed_packs/fp3b6_distinguisher_matrix_provenance/WORKER_PROMPT.md`
* `seed_packs/fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md`
* `seed_packs/first_move_search_2026/reports/gpt55/Q4_distinguisher-matrix-magnification.md`
* `outputs/nogolog.jsonl` (with NOGO-000006/7/8/9 entries)
* `RESEARCH_CONSTITUTION.md`
* All V2 closure audits.

These exist in PR #1225 (the long-running governance PR) but are
not yet merged to `main`.  D1 worker succeeded because the D1
PR description embedded enough WORKER_PROMPT context to reconstruct
the spec without local-file dependence; D5 worker correctly
refused that fallback because D5 requires reading multiple
upstream artifacts (Q4 report parameters, NOGO entries, etc.)
that cannot be reconstructed from a prompt body.

### 2.3 Verdict on D5 worker behaviour

**Worker behaviour is CORRECT.**  Honoured the
no-fabrication discipline (Rule 12 spirit, even though the
worker may not have seen the constitution).  Shipped a
4-section failure report per pack §6 schema.  Local
classification is accurate.  No scope violations.

This is the **gold standard** for "missing context" failures:
worker exits gracefully with documented obstruction rather than
fabricating outputs.  Operator commends the worker's discipline.

### 2.4 D5 task status

D5 task itself remains **TODO**.  The failure report is a
workflow artifact, not a research finding.  Re-dispatch is
required once the branch divergence is resolved.

## 3. Operator next-action recommendation

Two options for resolving the D5 re-dispatch:

### Option I: merge dev branch into main (RECOMMENDED)

Merge `claude/research-governance-phase0-lmZBP` into `main`,
making the seed-pack materials globally visible.  Future worker
dispatches (D2, D3, D4, D5 re-dispatch) automatically have the
inputs they need.

**Pros:**
* Workers don't need to know about per-development branches.
* All seed packs, audits, V2 closure trail visible everywhere.
* fp3b3 / fp3b4 / fp3b5 / fp3b6 packs become canonical.

**Cons:**
* PR #1225 is the long-running dev-branch PR (originally for
  the Research Constitution v0.1 / Phase 0 governance work).
  Merging closes the multi-month accumulation in one commit.
* Conventional Git history loses the dev-branch grouping.

**Mitigation:** create a merge commit (not squash) so the
dev-branch history is preserved as a merge ancestor.

### Option II: enrich D5 worker prompt with materials inline

Re-dispatch D5 with the seed pack README, WORKER_PROMPT, Q4
report, and relevant NOGO entries embedded directly into the
worker prompt body.  Worker still checks out main but has
context inline.

**Pros:**
* No structural changes to the branch model.
* Preserves the long-running PR #1225 for whenever the operator
  chooses to merge.

**Cons:**
* Worker prompt becomes very long (~10000+ lines of inline
  context).
* Cannot easily reference NOGO log line numbers without inline
  duplication.
* Doesn't scale: every future fp3b6 / fp3b7 dispatch requires
  the same inlining.
* Future workers cannot cross-reference materials they discover
  during their work.

### Operator recommendation

**Option I (merge dev branch).**  Reasoning:

* The V2 episode closure already shipped to dev branch +
  retrospective documented.  There's no governance reason to
  hold the dev branch open longer.
* The remainder of Round 1 (D5) + all of Round 2 (D2 + D3) +
  Round 3 (D4) requires cross-pack reading.  Inlining for each
  worker dispatch will quickly become impractical.
* Long-running PR #1225 is approaching ~50 commits of accumulated
  governance + research-stream work.  Merge timing is operator
  discretion; the current state (V2 closure + fp3b5 audit + fp3b6
  Round 1 open) is a clean milestone.

The merge is the user's decision.  Operator does **not** execute
the merge in this review (it's a structural Git action; user
should approve explicitly).

If the user prefers Option II (workflow-preserving inlining),
operator can prepare an enriched WORKER_PROMPT_D5_v2.md for
re-dispatch.

## 4. Round 2 readiness

Independent of the D5 re-dispatch decision, **D2 and D3 are
unblocked by D1 landing**.  D1's foundation primitives are
sufficient to attempt:

* **D2** — toy sparse-language separation theorem (Lean), gated
  on D1 ✓.  Recommended next dispatch.
* **D3** — log-width payload anti-collapse (Lean, CENTERPIECE),
  gated on D1 ✓.  Recommended next dispatch.

The same branch-divergence issue would affect D2 and D3 workers
if they dispatch off `main` without the seed-pack materials.
Therefore: **resolve the branch divergence (Option I or II)
before dispatching D2 / D3**.

## 5. fp3b6 pack status update

* **D1:** LANDED ✓ (worker `gpt55`, PR #1246).
* **D5:** TODO (worker `gpt55` failure report documented;
  re-dispatch needed once branch issue resolved).
* **D2:** READY for dispatch (gated on D1, now unblocked).
* **D3:** READY for dispatch (gated on D1, now unblocked).
* **D4:** GATED on D1 + D2 + D3.

Pack status remains OPEN.

## 6. Lessons for governance

* **Worker no-fabrication discipline is load-bearing.**  D5
  worker's behaviour (refuse to invent context, ship structured
  failure report) is exactly the discipline that makes
  worker-driven research safe.  Same discipline showed up in
  g55 / g55r1 T1 failures (fp3b3_3).  This is a stable
  empirical finding: workers given a clear no-fabrication
  rule + a structured failure-report template return useful
  obstruction reports rather than hallucinated results.
* **Branch-divergence as a workflow risk.**  The dispatch model
  routes workers off `main` (presumably for simplicity);
  long-running dev branches accumulate context that becomes
  invisible to workers.  Recommendation: include a
  "dispatch-branch check" in the dispatch instrument's §0
  setup section, OR merge dev branches before opening new
  worker-facing seed packs.
* **D5-style markdown slots may benefit from enriched prompts
  even after Option I.**  Even with merged dev branch, citation
  verification slots benefit from inline pointers to the cited
  papers.  Worker prompt §1 "Required reading" partially
  serves this; future markdown slots should consider whether
  to inline key passages from cited reports.

## 7. Audit-only scope confirmation

This review writes nothing to:
* `outputs/nogolog.jsonl`.
* `outputs/attempts.jsonl`.
* `spec/known_guards.toml`.
* Any Lean module (D1 was landed by the worker; this review
  only verifies it).

No `accepted` promotions.  No FP-4 implications.  No final
endpoint implications.  No P ≠ NP claims.

## 8. Cross-references

* D1 PR: `https://github.com/khanukov/p-np2/pull/1246`
  (merged via `e1b516d` into `main`).
* D5 PR: `https://github.com/khanukov/p-np2/pull/1247`
  (merged via `e1b516d` into `main`).
* D1 Lean module:
  `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/MatrixPrimitives.lean`.
* D5 failure report:
  `seed_packs/fp3b6_distinguisher_matrix_provenance/failures/D5_gpt55.md`.
* fp3b6 pack README + WORKER_PROMPT:
  `seed_packs/fp3b6_distinguisher_matrix_provenance/`.
* fp3b5 strategic audit:
  `../fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md`.
* Long-running governance PR holding dev branch:
  `https://github.com/khanukov/p-np2/pull/1225`.
