# fp3b6 — Distinguisher-matrix provenance audit route

## 0. TL;DR

Audit-route Phase-1 design sketch for `ProvenanceFilter_v1`
candidate based on **sparse distinguisher matrices** and
**fingerprint-separation predicates**, inspired by
Atserias-Müller 2025 and the
Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam ITCS 2020
locality-barrier discussion.

Opened per fp3b5 operator strategic audit recommendation
(`../fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md`
§6).  This pack is the **dispatched concrete design instance** of
"Family A" from the strategic audit triage.

**Scope discipline (HARD):**

* Phase-1 sketch only.  No full Atserias-Müller magnification
  formalisation (that would be years, not months).
* The first milestone is **NOGO-000006 anti-collapse**: show
  that arbitrary all-essential log-width truth-table payloads
  do not automatically satisfy fingerprint separation without
  an explicit matrix witness.
* `accepted`-status promotion is **out of scope** for this
  pack.  No `ProvenanceFilter_v1` registry promotion.
* No `SourceTheorem_*`, no `gap_from_*`, no
  `ResearchGapWitness`, no FP-4 bridge, no final endpoint, no
  P ≠ NP claims.

## 1. Why this pack exists

After the V2 family closure (NOGO-000008 + NOGO-000009) ruled
out syntactic-only `ProvenanceFilter_v2` candidates for
`accepted`-status promotion, the FP-3b.2 mainline obligation
remained open: a `ProvenanceFilter_v1` candidate must:

* exclude NOGO-000006 (arbitrary log-width TT hardwiring);
* not be support-cardinality-only (NOGO-000007);
* not be syntactically rewrite-vulnerable (NOGO-000008);
* not be structural-normalisation-self-defeating (NOGO-000009);
* be non-vacuous, non-tautologous, and `accepted`-promotable.

The fp3b5 strategic audit identified the distinguisher-matrix
audit route (Family A) as having the highest expected value:
the filter operates on a **semantic Boolean-function invariant**
(distance preservation under fingerprint map) rather than on
displayed syntax, so the V2 closure pattern does not directly
apply.  See `../fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md`
§3.1 + §6 for the triage and recommendation.

## 2. Goal (precise)

Land an audit-route Lean module
`pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/`
containing:

* `SparseDistinguisherMatrix` predicate — finite Boolean
  matrix with bounded row support, bounded column support,
  and controlled fingerprint output length.
* `FingerprintSeparation` predicate — Hamming-distance
  separation between fingerprints of a YES-set and far-NO set
  at the magnification-theorem-relevant radius.
* `FingerprintFormulaCost` predicate — fingerprint bits
  composable with the target weak model within
  near-threshold size bound.
* `NonLocalPayloadGuard` predicate — acceptance is NOT
  invariant under replacing a small support window by an
  arbitrary all-essential truth-table formula; the global
  fingerprint/separation contract is required, not only
  support size.
* **Anti-collapse theorem (centerpiece):** arbitrary
  all-essential log-width truth-table payloads renamed into
  the ambient `Fin n` do NOT imply `FingerprintSeparation`
  without an explicit matrix witness.

A future Phase-2 dispatch (separate seed pack, NOT in this
round) would target a full `ProvenanceFilter_v1` definition
that combines these predicates and proves the full
NOGO-7/8/9 self-attack surface.

## 3. Slot decomposition (DAG)

```
D1 (matrix primitives, Lean)        D5 (literature-to-parameter table, MD)
        |                                            |
        +-> D2 (toy separation theorem, Lean)        |
        |                                            |
        +-> D3 (log-width anti-collapse, Lean)       |
        |                                            |
        +-> D4 (barrier checklist, MD) <------------+
```

### Round 1 (parallel-dispatchable, no inter-deps)

* **D1 — finite matrix primitives.**
  `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/MatrixPrimitives.lean`.
  Define:
  * `SparseDistinguisherMatrix n m k` — a Boolean matrix
    `Matrix (Fin m) (Fin n) Bool` whose every row has
    support ≤ k and every column has support ≤ k.
  * `fingerprint D x : Bitstring m` — XOR-of-AND fingerprint
    map, `(fingerprint D x) i = bigXor (j ∈ D.row i) (x j ∧ D i j)`.
  * `MatrixRowSupportCard D i` and `MatrixColSupportCard D j`.
  * Basic lemmas: fingerprint is computable, fingerprint
    cardinality bound, sparsity preservation under restrictions.
  Expected LOC: 150-250.

* **D5 — literature-to-parameter table.**
  `reports/D5_literature_parameter_table_<HANDLE>.md`.
  Markdown table mapping the audit-skeleton parameters
  (row/col support k, fingerprint output length m, separation
  radius r, distance preservation bound) to the corresponding
  parameters from:
  * Atserias-Müller 2025 (arXiv:2503.24061);
  * Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam ITCS 2020
    (arXiv:1911.08297);
  * Oliveira-Pich-Santhanam (Theory of Computing 17(11), 2021);
  * Chen-Jin-Williams FOCS 2019 (DOI 10.1109/FOCS.2019.00077).
  For each: which parameters are copied directly, which are
  deliberately omitted for the first audit pass, and why.

### Round 2 (gated on D1 landing)

* **D2 — toy sparse-language separation theorem.**
  `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/ToySeparation.lean`.
  Specify and prove a small finite theorem: for some explicit
  small matrix `D` and explicit small YES/NO sets, the
  fingerprint map separates YES-positives from far-NO at the
  audit's chosen separation radius.  The theorem must be
  **kernel-checked** (no `sorry` / `admit`).  Concrete suggested
  size: `n ≤ 8`, `m ≤ 4`, `k ≤ 2`.  Purpose: demonstrate that
  separation is a semantic condition, not derivable from
  cardinality.  Expected LOC: 100-200.

* **D3 — log-width payload anti-collapse.**
  `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/AntiCollapse.lean`.
  **CENTERPIECE.**  Prove:
  ```lean
  theorem allEssentialLogWidthPayload_no_fingerprintSeparation
      (P : <arbitrary all-essential log-width truth-table>)
      (renaming : ...) :
      ¬ ∃ (D : SparseDistinguisherMatrix n m k),
        FingerprintSeparation (renamedPayloadFamily P renaming) D
  ```
  i.e., having an arbitrary all-essential log-width truth-table
  payload + sublinear renamed support does NOT imply the
  fingerprint-separation contract for any sparse matrix.  The
  formal target should be precise about quantifier order:
  what's required is "there exists a payload such that no
  matrix separates it from far-negatives", NOT "for every
  payload no matrix exists" (the latter is wrong because trivial
  payloads admit trivial matrices).  Expected LOC: 200-400
  depending on quantifier discipline.

### Round 3 (gated on D1+D2+D3 landing)

* **D4 — barrier checklist.**
  `audits/D4_barrier_checklist_<HANDLE>.md`.
  Markdown audit documenting:
  * Relativization: which audit ingredient is non-oracle-invariant
    (per Q4 report §5 — likely the MCSP / meta-complexity
    component if magnification is invoked).  Honestly classify:
    "neutral", "risk", or "explicit non-relativizing".
  * Natural-proofs: confirm that `FingerprintSeparation` is
    NOT a large constructive Razborov-Rudich property; cite
    Chen-Hirahara-Oliveira et al. ITCS 2020.  Honestly
    classify: "not-large by construction", "constructive but
    not useful by construction", or "risk".
  * Algebrization: cleanly state no bypass is claimed; flag
    whether finite-matrix machinery survives algebraic-oracle
    substitutions.
  D4 is **markdown-only**, no Lean.

## 4. Allowed / forbidden scope

### Allowed (per slot, Round 1)

* Lean files under
  `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_<HANDLE>/`
  for D1-D3 attempts (per-worker subdirectory so multiple
  attempts coexist).
* Markdown audit/literature files under
  `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/`,
  `reports/`, `failures/`.
* `lakefile.lean` edit to wire new modules under the existing
  `Glob.one ...` list.
* Optional smoke test at
  `pnp3/Tests/AuditRoutes_DistinguisherMatrix_<HANDLE>_Smoke.lean`.
* Reading any existing file in the repo.

### Forbidden (HARD)

* **No trust-root edit** to `pnp3/Complexity/Interfaces.lean`.
* **No editing existing audit-route modules** under
  `pnp3/Magnification/AuditRoutes/FixedParamsProbe/`,
  `LogWidthAdversary/`, `ArbitraryLogWidthTT/`,
  `SupportCardinalityBarrier/`, `ProvenanceFilterV2/`,
  `V2_A_NormaliseMetaBarrier/`,
  `CrossLengthCoherence_NoGo.lean`.
* **No editing V2 trust-root** modules (V2-A is import-only
  even though V2 family is closed).
* **No `sorry` / `admit` / `axiom` / `opaque` / `Fact` /
  typeclass-payload** in committed Lean (Rules 1, 16).
* **No `Classical.choose`** in matrix-primitive or anti-collapse
  definitions (Q4 report §3 implicitly requires constructive
  matrix constructions).
* **No truth-table reconstruction** as a definition primitive
  (no `ttFormula (eval _)` patterns).
* **No `Π → ProvenanceFilter_v1` factorisation theorem** in
  this pack — that is a Phase-2 deliverable.  This pack proves
  the **audit interface**, not the bridge.
* **No `Candidates/` creation.**
* **No appending to `outputs/nogolog.jsonl`** — Phase-1 sketch
  audits do not yet warrant NOGO entries.  NOGO-grade entries
  may arise from a future Phase-2 closure or anti-evidence.
* **No appending to `outputs/attempts.jsonl`** — pack-level
  records, not worker-level.
* **No `spec/known_guards.toml` edits** — no
  `ProvenanceFilter_v1` promotion.
* **No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` /
  final endpoint / P ≠ NP language.**
* **No FP-4 bridge work.**  FP-4 is gated on FP-3b.2 success
  per `FixedParams_Probe.md` §8.6.

## 5. Slot acceptance criteria

* **D1 complete** when: (a) Lean module compiles, (b)
  `lake build PnP3 Pnp4` green, (c) `./scripts/check.sh` green,
  (d) `SparseDistinguisherMatrix`, `fingerprint`,
  `MatrixRowSupportCard`, `MatrixColSupportCard` are all
  defined and have basic compute/extension lemmas.
* **D2 complete** when: (a) D1 has landed, (b) concrete small
  matrix D (n ≤ 8, m ≤ 4, k ≤ 2) is defined, (c) explicit
  YES/NO sets are defined, (d) a kernel-checked
  `toy_fingerprint_separation` theorem is proven, (e) build
  green, (f) `./scripts/check.sh` green.
* **D3 complete** when: (a) D1 has landed, (b) anti-collapse
  theorem `allEssentialLogWidthPayload_no_fingerprintSeparation`
  (or equivalent) is proven with the correct quantifier
  discipline (per slot description), (c) build green, (d)
  `./scripts/check.sh` green.
* **D4 complete** when: (a) D1+D2+D3 have landed, (b) barrier
  checklist markdown is filled with **honest** classifications
  (no false bypass claims), (c) operator review countersigns
  the classifications.
* **D5 complete** when: parameter table is filled with verified
  citations (every cited paper has a working DOI/arXiv/page
  identifier), and explicitly states which parameters are
  copied vs deliberately omitted, with reasons.

## 6. Per-slot failure criterion

If any slot surfaces an obstruction that cannot be resolved
within the pack's scope, ship a structured failure report at:

```
failures/<SLOT>_<HANDLE>.md
```

with EXACTLY four sections:

1. **What was attempted.**  Definitions, lemmas, proofs tried.
2. **Where it broke.**  Lean error verbatim, or precise
   prose obstruction.
3. **Local vs global obstruction.**  Local: this attempt's
   approach didn't work; another might.  Global: the entire
   distinguisher-matrix audit route faces a structural
   obstruction (would invalidate fp3b5 strategic audit's
   §3.1 verdict and trigger Family B fallback).
4. **What an integrator must know.**  Recipe for next attempt,
   or pivot recommendation.

If a `Global` failure surfaces, this pack closes and operator
re-audits per the fp3b5 strategic audit §8 decision matrix:

* If `Global` failure invalidates the semantic-by-design
  argument → cascade to Family B (almost-natural) dispatch.
* If `Global` failure is locality-barrier-bypass-fails → may
  still salvage parts of the matrix primitive infrastructure
  for a different filter design.

## 7. Negative-pivot protocol

This pack is dispatched under "**positive with readiness to
pivot negative**" stance (same governance pattern as fp3b3_3).
Workers always pursue the positive goal — but the dispatcher
pre-stages a negative-result pivot path.

**Pivot trigger:** D3 (anti-collapse centerpiece) ships a
structured `Global`-classified failure report AND independent
operator review confirms the obstruction is structural rather
than implementation detail.

**Pivot action (operator only):**

* Cascade to Family B (almost-natural) per fp3b5 audit §6
  "secondary recommendation" — open
  `seed_packs/fp3b7_almost_natural_provenance/`.
* Add NOGO-000010 (distinguisher-matrix provenance closure)
  with the failed anti-collapse attempt as `formal_witness`
  if it's Lean-formalised, OR with markdown failure report as
  markdown-grade evidence (Lean theorem preferred per NOGO
  standard).
* Archive fp3b6 as STALLED → CLOSED documentation.

**Pivot does NOT trigger** on `Local` D3 failures.  Up to 2
retries with adjusted proof strategy before declaring `Local`
exhausted.

## 8. Critic angles (for future T5-style critic dispatch)

These are pre-staged adversarial questions a critic-report
dispatch would explore in Round 2 / Round 3:

1. **Cardinality smuggling.**  Is `FingerprintSeparation` in
   practice equivalent to a support-cardinality predicate
   when the matrix is chosen adversarially?  Concrete test:
   construct a "bad" matrix that makes the separation
   condition vacuous for some hardwiring witness.
2. **Forgery attack.**  Can an adversary construct an explicit
   matrix `D'` for a hardwiring witness that satisfies
   `FingerprintSeparation` formally but is "fake"?  If yes,
   the filter is matrix-forgery-vulnerable.
3. **Tautological rewrite revisited.**  Does conjoining
   `(x_0 ∨ ¬x_0)` change the fingerprint map's separation
   properties?  Should be NO (semantic invariant), but
   verify formally.
4. **Trivial-payload acceptance.**  Does a constant-true
   formula family admit a trivial fingerprint-separating
   matrix?  If so, the filter may be too permissive.  Address
   in D2 / D3 by including constant families in the YES/NO
   discrimination.
5. **Magnification-strength gap.**  Are the parameters in the
   audit skeleton (k, m, r) compatible with at least one
   known magnification theorem's strength threshold?  Document
   in D5.
6. **Relativization invariance.**  Q4 §5 noted the finite-matrix
   argument may be oracle-insensitive.  Address in D4.

## 9. What this pack does NOT do

* No full Atserias-Müller magnification formalisation.
* No `ProvenanceFilter_v1` complete definition or
  `accepted`-promotion.
* No `Π → ResearchGapWitness` factorisation.
* No NOGO-7/8/9 anti-evidence proofs (those are Phase-2,
  separate seed pack).
* No final P ≠ NP endpoint.
* No editing of any existing audit-route or trust-root module.

## 10. Cross-references

* Strategic audit that opened this pack:
  `../fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md`.
* First-move scan report sourcing the design idea:
  `../first_move_search_2026/reports/gpt55/Q4_distinguisher-matrix-magnification.md`.
* V2 closure retrospective (anti-evidence for syntactic-only
  filters; motivates this semantic-by-design route):
  `../fp3b3_provenance_filter_v2_design/operator_reviews/v2_family_closure_retrospective.md`.
* NOGO-000006 (the adversary this pack's centerpiece anti-collapse
  resists): `outputs/nogolog.jsonl` line 6.
* Magnification framework (downstream consumer of any successful
  v1 filter):
  * `pnp4/Pnp4/Frontier/CompressionMagnification.lean`.
  * `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`.
  * `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean`.
* RESEARCH_CONSTITUTION.md Rules: 0 (audit-only), 1 (no
  sorry/admit), 12 (natural-proofs discipline), 16 (no
  typeclass payload).
* Q4-cited literature (verify identifiers in D5):
  * Atserias-Müller 2025, arXiv:2503.24061.
  * Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam ITCS 2020,
    arXiv:1911.08297 / DOI 10.4230/LIPIcs.ITCS.2020.70.
  * Oliveira-Pich-Santhanam, Theory of Computing 17(11), 2021.
  * Chen-Jin-Williams FOCS 2019, DOI 10.1109/FOCS.2019.00077.
  * Cheraghchi-Hirahara-Myrisiotis-Yoshida STACS 2021, DOI
    10.4230/LIPIcs.STACS.2021.23.

## 11. Pack status

**OPEN — Round 1 (D1 + D5) READY for dispatch.**

D1 and D5 can be dispatched in parallel (no inter-deps).  D2
and D3 are gated on D1 landing.  D4 is gated on D1+D2+D3
landing.

See `WORKER_PROMPT.md` for the dispatch instrument.
