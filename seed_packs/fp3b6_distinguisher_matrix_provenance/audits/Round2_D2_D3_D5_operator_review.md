# fp3b6 Round 2 — D2 + D3 + D5 operator review

**Review subjects:**

* **D2** worker landing: commit `95e8aa0` (Add toy sparse fingerprint separation).
  File: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/ToySeparation.lean` (94 LOC).
* **D3** worker landing: commit `4d86cf8` (Add D3 distinguisher anti-collapse audit theorem).
  File: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/AntiCollapse.lean` (115 LOC).
* **D5** worker landing: commit `e2ce9bf` (Add D5 literature parameter table).
  File: `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_literature_parameter_table_gpt55.md` (203 LOC).

All three landed via direct merges to `main` after operator's V2 closure + fp3b6 Round 1 governance merge.

**Operator decisions:**

* **D2: APPROVE LANDING** as an explicit smoke / non-vacuity witness for the D1 predicate surface. Does not by itself establish anything beyond predicate non-emptiness on one toy instance.
* **D3: ACCEPT AS SKELETON, REJECT AS SURVIVOR-SIGNAL.** The committed theorem is honest and kernel-checked but logically a **conjunction of an already-known support-card lemma with a payload-independent self-separation triviality**. It does **not** discharge the README §3 anti-collapse obligation. Slot remains **MATERIALLY OPEN** as `D3'`.
* **D5: ACCEPT AS CONSERVATIVE LITERATURE ALIGNMENT.** All 5 cited papers bibliographically verified; matrix-shape vocabulary copied from Atserias–Müller. **All theorem-level constants explicitly marked `[unverified]`.** A follow-up slot `D5-tight` is opened for theorem-by-theorem extraction from Atserias–Müller arXiv:2503.24061 v2.

This is operator-scoped review, not a worker artifact. No NoGoLog entries, no spec edits, no `accepted`-status changes, no FP-4 / `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / P ≠ NP language.

---

## 1. D2 verification

### 1.1 Structural compliance

| Check | Status | Note |
| --- | --- | --- |
| Lives under `V_gpt55/` per-handle subdir | ✓ | `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/ToySeparation.lean` |
| `lakefile.lean` updated with one `Glob.one` line | ✓ | per commit `95e8aa0` (1 line added) |
| Imports D1 only (no upstream audit-route edits) | ✓ | `import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives` |
| No `sorry` / `admit` / `axiom` / `opaque` / `Fact` / `Classical.choose` | ✓ | verified by reading |
| Concrete sizes within budget (n ≤ 8, m ≤ 4, k ≤ 2) | ✓ | `n = 4`, `m = 2`, `k = 2` (`toyMatrix : BoolMatrix 2 4`) |
| Kernel-checked positive separation theorem | ✓ | `toy_fingerprint_separation` line 83-87 closes by `decide` after substituting the singleton elements |

### 1.2 Substantive content

The module proves three concrete facts about an explicit `2 × 4` matrix `toyMatrix` whose row 0 reads input bit 0 and row 1 reads input bit 1:

1. `toyMatrix_sparse : SparseDistinguisherMatrix 2 4 2 toyMatrix` (`ToySeparation.lean:63-68`) — row/col supports ≤ 2 by `fin_cases ... <;> decide`.
2. `toy_fingerprint_distance_eq_one` (`ToySeparation.lean:71-74`) — Hamming distance between the fingerprints of the two singletons is exactly 1, by `decide`.
3. `toy_fingerprint_separation : ToyFingerprintSeparation toyMatrix toyYES toyNO 1` (`ToySeparation.lean:83-87`) — for the singleton YES = `{0000}` and singleton NO = `{1000}`, the radius-1 separation holds.

`toyFingerprintDistance` (line 23-25) and `ToyFingerprintSeparation` (line 30-32) are local-to-D2 helpers. The README §3 D2 acceptance criteria are met: concrete D, explicit YES/NO sets, kernel-checked separation theorem, sizes within budget.

### 1.3 What D2 does NOT establish

* Non-vacuity of `FingerprintSeparation` on **honest-structured Boolean function families** (e.g., sparse NP language templates from CJW 2019). D2 is a one-point smoke test, not a non-vacuity theorem against the family the audit route targets.
* That the predicate distinguishes honest families from hardwired ones. This is the D3 obligation.
* That `FingerprintSeparation` (the D3-level predicate, defined separately in `AntiCollapse.lean`) is non-vacuous; D2 uses its own local `ToyFingerprintSeparation` definition.

**D2 is a smoke artifact.** Status APPROVED as smoke.

---

## 2. D3 substantive critique (load-bearing)

### 2.1 What the committed D3 theorem actually says

The headline statement at `AntiCollapse.lean:96-108`:

```lean
theorem allEssentialLogWidthPayload_no_fingerprintSeparation
    (F : PayloadFamily)
    (hF : AllEssentialPayload F)
    (n : Nat) :
    (FormulaCircuit.support (adversaryFamily_v_arbpayload F n)).card = widthFn n ∧
      ∀ (m k r : Nat) (x : Bitstring n),
        ¬ ∃ D : BoolMatrix m n,
          SparseDistinguisherMatrix m n k D ∧
            FingerprintSeparation D ({x} : Finset (Bitstring n)) ({x}) (r + 1)
```

The proof:

```lean
constructor
· exact adversaryFamily_v_arbpayload_support_card F hF n   -- pre-existing lemma
· intro m k r x
  exact no_sparse_matrix_separates_overlapping_singletons (m := m) (n := n) (k := k) x r
```

### 2.2 Why this is **not** the D3 obligation

The README §3 D3 specification explicitly fixes the quantifier discipline:

> *"the formal target should be precise about quantifier order: what's required is 'there exists a payload such that no matrix separates it from far-negatives', NOT 'for every payload no matrix exists' (the latter is wrong because trivial payloads admit trivial matrices)."*

The committed theorem fails this discipline along **two independent axes**:

**Axis (a) — payload independence of the load-bearing conjunct.**  
The second conjunct quantifies over `(m, k, r, x)` and asserts no matrix separates `{x}` from `{x}`. The variable `F` does not appear in this conjunct. The proof routes through `no_self_fingerprintSeparation` (`AntiCollapse.lean:59-66`), whose content is

```lean
hammingDistance_self : hammingDistance a a = 0    (line 36-38)
```

i.e. "Hamming distance of a string from itself is zero". This is independent of any payload, any sparsity bound, any radius — it is the trivial impossibility of positive-radius separation of a singleton from itself.

**Axis (b) — overlapping YES/NO is forbidden by the audit semantics.**  
A YES/NO relation with `YES = NO = {x}` is **degenerate**: by the magnification-relevant promise formulation (OPS 2021 gap-thresholds `s₁ < s₂`, Atserias–Müller code-like distance preservation), the YES set must be at far Hamming distance from the NO set in input space, not coincide with it. The committed theorem refutes separation for an audit relation that the audit route would never consider valid.

### 2.3 What an honest reading of the committed theorem yields

Define `AntiCollapseStrong(F)` as the statement that **the README §3 obligation** would prove:

```lean
AntiCollapseStrong(F) :=
  ∀ matrix-witness machinery using only F's support data,
  the resulting matrix fails FingerprintSeparation on the
  canonical YES_F / NO_F derived from F's truth table.
```

What is actually proven is

```lean
AntiCollapseTrivial(F) :=
  support_card(adversaryFamily F) = widthFn n
  ∧
  no matrix can separate any singleton from itself at positive radius.
```

These differ: `AntiCollapseTrivial(F)` is logically equivalent to

```lean
support_card(adversaryFamily F) = widthFn n
∧
(generic: ∀ singleton x, no matrix separates {x} from {x} at radius ≥ 1).
```

The right conjunct is a free theorem of the predicate `FingerprintSeparation`. The full statement therefore reduces to **the pre-existing `adversaryFamily_v_arbpayload_support_card` lemma** with an added vacuous decoration.

The doc-comment on the theorem (lines 91-94) anticipates this critique:

> *"The result does **not** say that every payload defeats every possible matrix relation. It says that the payload support theorem by itself is too weak to derive fingerprint separation; an explicit, non-overlapping semantic relation together with a matrix witness is additional data."*

This is honest **self-acknowledgement**, but it amounts to: *the committed theorem is a discipline-pinning skeleton, not a survivor-signal.* Worker discipline is correct (no sorry, no false claim, doc-comment explicitly disclaims the strong reading). Operator agrees with the worker's own framing.

### 2.4 Why this matters for fp3b6 governance

The README §3 anti-collapse requirement is the **acceptance criterion** for fp3b6's first milestone (README §0 TL;DR, §2 Goal, §5 D3 complete-when). Without a non-trivial F-dependent anti-collapse theorem, fp3b6 has not yet demonstrated:

* That it survives NOGO-000006 (arbitrary all-essential log-width TT payload) in the **fingerprint** domain;
* That `FingerprintSeparation` is not a relabelled support-cardinality predicate (NOGO-000007 lift);
* That the route gives any non-trivial barrier-relevant content beyond what `ArbitraryLogWidthTT` already gives.

The committed theorem **is consistent with** the route succeeding (it does not refute fp3b6), but it is **not evidence** that the route succeeds.

### 2.5 D3 verdict

**STATUS: skeleton accepted; D3 obligation OPEN as `D3'`.**

The committed file may stay in `V_gpt55/` as kernel-checked infrastructure (`FingerprintSeparation` definition, `hammingDistance` helpers, `no_self_fingerprintSeparation` as a sanity invariant). A new slot `D3'` is opened in §5 below.

This is **not a NoGoLog event**: there is no formalised obstruction, only an unmet obligation. NoGoLog is reserved for formalised barrier proofs (Rule 0 audit-only + NoGoLog discipline). Re-dispatch follows the negative-pivot protocol (README §7): up to 2 retries on `Local` before considering a `Global` classification.

---

## 3. D5 verification

### 3.1 Bibliographic verification

All 5 papers cited in README §10 are bibliographically verified in the report's §8 "Verified references":

| Source | Verified identifier | Verifier |
| --- | --- | --- |
| Atserias–Müller 2025 | arXiv:2503.24061, submitted 2025-03-31 | arXiv page |
| CHOPRS ITCS 2020 | LIPIcs 151:70, pp. 70:1–70:48, DOI 10.4230/LIPIcs.ITCS.2020.70 | Dagstuhl/DROPS |
| OPS ToC 2021 | ToC 17:11, pp. 1–38, DOI 10.4086/toc.2021.v017a011 | Theory of Computing page |
| CJW FOCS 2019 | FOCS 2019 pp. 1240–1255, DOI 10.1109/FOCS.2019.00077, ECCC TR19-118 | DBLP / ECCC |
| CHMY STACS 2021 | LIPIcs 187:23, pp. 23:1–23:19, DOI 10.4230/LIPIcs.STACS.2021.23; journal DOI 10.1007/s00224-022-10113-9 | Dagstuhl/DROPS + DBLP |

Each entry separates **bibliographic verification** from **parameter extraction**. The report consistently marks theorem-level constants as `[unverified]` rather than inferring them, which complies with the README §5 D5 acceptance criterion ("verified citations" + "which parameters are copied vs deliberately omitted, with reasons").

### 3.2 Substantive content

The report's per-paper mapping (§3) and per-source notes correctly:

* Identify **Atserias–Müller 2025** as the **only** direct source for the matrix-shape vocabulary (`SparseDistinguisherMatrix`, `fingerprint`, `FingerprintSeparation`). All other papers contribute context only.
* Treat **CHOPRS ITCS 2020** as the **locality-barrier checklist** source (relevant to D4, not the matrix primitive).
* Treat **OPS ToC 2021** as the **gap/radius dictionary** (symbolic `s₁(N)`, `s₂(N)`, `β`, `ε`, `c`); explicitly does NOT formalise Gap-MCSP / Gap-MKtP in this pack.
* Treat **CJW FOCS 2019** as **sparse-language motivation**, with the explicit warning that language sparsity ≠ matrix sparsity.
* Treat **CHMY STACS 2021** as **restricted-model context only**, not fp3b6 mainline progress.

The §5 NOGO-interaction table is well-aligned: the design rule "`k_row`/`k_col` necessary but not sufficient; semantic separation predicate is load-bearing" directly addresses NOGO-000006 and NOGO-000007.

### 3.3 What D5 does NOT establish

* **No theorem-level parameter validation.** Exact Atserias–Müller row-support, column-support, output length, distance-loss formulas are explicitly `[unverified]`. The report itself (§7, §8) recommends a separate follow-up slot for theorem-by-theorem extraction.
* **No claim of magnification-strength match.** README §8 critic angle 5 ("Magnification-strength gap — are the parameters in the audit skeleton (k, m, r) compatible with at least one known magnification theorem's strength threshold? Document in D5.") is **not discharged** by this report; it is acknowledged as future work.

### 3.4 D5 verdict

**ACCEPT AS CONSERVATIVE VOCABULARY ALIGNMENT.** The report does what it claims to do: a first-pass mapping of audit-skeleton parameters to literature vocabulary, with NOGO-aware design rules and honest `[unverified]` markers on theorem-level content.

The 7 sibling D5 reports that were not landed (operator notes "all essentially the same") are not a problem: a single coherent report is preferable to 8 near-duplicates. The discipline that all 8 converged is itself a weak signal that the conservative-vocabulary reading is the natural one.

A follow-up slot `D5-tight` is opened in §5 below.

---

## 4. Cross-pack discipline check

Operator confirms no scope violations across the three landings:

* **Trust root** (`pnp3/Complexity/Interfaces.lean`): imported only; not modified.
* **Existing audit-route modules** (`FixedParamsProbe/`, `LogWidthAdversary/`, `ArbitraryLogWidthTT/`, `SupportCardinalityBarrier/`, `ProvenanceFilterV2/`, `V2_A_NormaliseMetaBarrier/`, `CrossLengthCoherence_NoGo.lean`): not edited. `AntiCollapse.lean` only **imports** from `ArbitraryLogWidthTT/Family` (allowed; explicit upstream consumer).
* **V2 trust-root**: not edited.
* **`outputs/`**: no edits.
* **`spec/`**: no edits.
* **`Candidates/`**: not created.
* **No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP language** in any of the three landings.

All three landings comply with README §4 "Forbidden (HARD)" list.

---

## 5. New slot dispatch

### 5.1 `D3'` — F-dependent anti-collapse (centerpiece, RE-DISPATCH)

**Intent.** Discharge the README §3 anti-collapse obligation with the correct quantifier discipline: the F-dependence must appear in the **load-bearing** conjunct, and the YES/NO relation must be **non-overlapping** (semantically meaningful).

**Target theorem shape (proposed).** Let `F : PayloadFamily` be all-essential log-width. Define a canonical YES_F / NO_F separation derived from F's truth-table — for example:

```lean
-- Canonical YES_F / NO_F associated to an all-essential payload F.
-- Suggested (worker may refine): YES_F := { x | F maps x's log-width window to true },
-- NO_F  := { x | F maps x's log-width window to false }.
-- Both sets are populated by all-essentialness of F.
```

(Worker is expected to fix the canonical definition with the README §3 critic angle 4 in mind: constant-true / constant-false payloads should be handled honestly — they may not yield a non-trivial separation, and that should be openly acknowledged in the theorem's hypotheses.)

Then prove **at least one of**:

**D3'-A (existential).**

```lean
theorem antiCollapseExistential :
  ∃ F : PayloadFamily, AllEssentialPayload F ∧
    ∀ n (m k r : Nat), k ≤ kBudget n → r ≥ 1 →
      ¬ ∃ D : BoolMatrix m n,
        SparseDistinguisherMatrix m n k D ∧
          FingerprintSeparation D (YES_F n) (NO_F n) r
```

where `kBudget n` is some sub-linear bound (e.g. `kBudget n = widthFn n` or `Nat.log2 n`). The `F` must be **explicitly constructed**, not pulled from `Classical.choose`.

**D3'-B (uniform under hardwiring-twin).**

```lean
theorem antiCollapseHardwiringTwin
  (H : HonestFamily) (T : HardwiringTwin H) :
    same_support_profile H T  ∧
    (∃ D : BoolMatrix _ _, FingerprintSeparation D (YES H) (NO H) r)  ∧
    ¬ ∃ D' : BoolMatrix _ _, FingerprintSeparation D' (YES T) (NO T) r
```

i.e., honest family admits a matrix witness, but its hardwiring twin (with identical support profile) does not. This directly addresses NOGO-000007.

Either D3'-A or D3'-B counts as discharging the obligation; D3'-B is preferred (stronger NOGO-007 connection). Worker may negotiate which is feasible without `Classical.choose` and without `sorry`.

**Forbidden additions for D3'.**

* No `Classical.choose` in the matrix or payload construction.
* No appeal to `ttFormula (eval _)` as a definitional primitive.
* No new edits to upstream audit-route modules (still only `import`).
* No promotion to `accepted` status anywhere.
* No NoGoLog append.
* No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / P ≠ NP.

**Acceptance criterion.** As README §5 D3, but the proven theorem must:

1. Have `F` (or `H`/`T`) as a non-spurious dependency of the load-bearing conjunct.
2. Use a non-overlapping YES/NO relation (YES_F ∩ NO_F = ∅ provable, or visibly disjoint by construction).
3. Discharge at least one of D3'-A or D3'-B.

**Dispatch handle.** New handle, not `gpt55` (cross-V audit). Suggested: any worker that has not previously seen the gpt55 attempt. Worker receives this section as the spec; the existing `V_gpt55/AntiCollapse.lean` stays as reference but is **not** to be imported (otherwise the worker may inherit the conjunction trick).

**Failure pivot.** Per README §7. Two `Local` retries before considering `Global`. A `Global` D3' failure would trigger the fp3b7 Family-B (almost-natural) cascade per fp3b5 strategic audit §6.

### 5.2 `D5-tight` — Atserias–Müller theorem-level parameter extraction

**Intent.** Discharge the residual `[unverified]` markers in the D5 report by extracting **theorem-level constants** from Atserias–Müller arXiv:2503.24061 v2.

**Deliverable.** `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_tight_atserias_muller_<HANDLE>.md` with:

* Theorem-by-theorem citations from arXiv:2503.24061 v2: each cited theorem identified by section / theorem number, with the exact statement copied (verbatim or paraphrased with clear marker).
* Exact row-support function `k_row(n)` if specified by the paper, with page/theorem reference.
* Exact column-support function `k_col(n)` if specified, with reference.
* Exact fingerprint output length `m(n)` if specified, with reference.
* Exact distance-preservation bound `δ(n)` or `Δ(n)` if specified, with reference.
* Each extracted constant explicitly tagged `verified-from-page-X` vs `inferred-from-context-Y` vs `not-stated-in-paper`.
* Explicit comparison table: D1/D3 audit-skeleton parameter ↔ paper's parameter, with deltas marked.

**Forbidden.**

* No claim that fp3b6 parameters **equal** Atserias–Müller's optimal threshold without page-level citation.
* No re-classification of any `[unverified]` constant to `verified` without an explicit page reference.
* No NoGoLog append.
* No Lean writes (markdown only, like D5).

**Acceptance criterion.** Every extracted constant has either:

(a) a page-and-theorem reference from arXiv:2503.24061 v2; or
(b) an explicit `not-stated-in-paper` tag with reasoning; or
(c) an explicit `inferred-from-context` tag with the context derivation written out.

**Dispatch handle.** Any worker comfortable reading magnification literature. May overlap with D3' worker if convenient.

### 5.3 `D4` — REMAINS GATED

D4 (barrier checklist) is gated on D1 + D2 + D3 in README §3. With `D3` materially open as `D3'`, **D4 stays gated**. A barrier-checklist over a discipline-skeleton-only `D3` would assess the barrier-safety of a near-vacuous predicate; not useful.

D4 dispatch deferred until D3' lands.

---

## 6. fp3b6 pack status update

| Slot | Status | Note |
| --- | --- | --- |
| D1 | LANDED ✓ (`V_gpt55`) | Round 1 |
| D5 | LANDED ✓ (`V_gpt55`) | conservative; D5-tight follow-up opened |
| D2 | LANDED ✓ (`V_gpt55`) | smoke / non-vacuity on one toy point |
| D3 | **MATERIALLY OPEN** | committed gpt55 attempt is a discipline-skeleton; `D3'` re-dispatch open |
| D3' | OPEN for dispatch | new handle, not gpt55 |
| D5-tight | OPEN for dispatch | theorem-level constants extraction |
| D4 | GATED on D3' | unchanged |

Pack status: **OPEN** (Round 2 partially landed, D3 obligation re-opened as D3'; Round 3 D4 still gated).

---

## 7. Cross-references

* D2 PR (merged): commit `95e8aa0`.
* D3 PR (merged): commit `4d86cf8`. PR #1249.
* D5 PR (merged): commit `e2ce9bf`. PR #1250.
* D1 review (prior): `Round1_D1_D5_operator_review.md` (same directory).
* D1 Lean module: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/MatrixPrimitives.lean`.
* D2 Lean module: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/ToySeparation.lean`.
* D3 Lean module: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/AntiCollapse.lean`.
* D5 report: `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_literature_parameter_table_gpt55.md`.
* fp3b6 pack README: `seed_packs/fp3b6_distinguisher_matrix_provenance/README.md`.
* fp3b6 WORKER_PROMPT: `seed_packs/fp3b6_distinguisher_matrix_provenance/WORKER_PROMPT.md`.
* fp3b5 strategic audit (negative-pivot protocol): `../fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md` §6, §8.
* NOGO-000006 (the hardwiring adversary D3' must resist): `outputs/nogolog.jsonl`.
* RESEARCH_CONSTITUTION.md Rules 0 (audit-only), 1 (no sorry/admit), 12 (natural-proofs discipline), 16 (no typeclass payload).

---

## 8. Audit-only scope confirmation

This review writes nothing to:

* `outputs/nogolog.jsonl` (no formalised barrier emerged; D3 is unmet, not refuted).
* `outputs/attempts.jsonl`.
* `spec/known_guards.toml` (no `accepted`-status promotion).
* Any Lean module (D1/D2/D3 landed by workers; this review only assesses them).

No `accepted` promotions. No FP-4 implications. No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` writes. No final endpoint implications. No P ≠ NP claims.

---

## 9. Addendum — post-review landings (commits `3a95fdb`, `e484f70`)

After the Round 2 review (commit `e42a9c1`) was published, two further landings reached `main`:

* **Commit `3a95fdb`** — `Add D2 toy fingerprint separation` (new handle `codex`).
  File: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_codex/ToySeparation.lean` (108 LOC).
* **Commit `e484f70`** — `Strengthen D3 anti-collapse implication guard` (same handle `gpt55`).
  File: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/AntiCollapse.lean` (+32 LOC).

### 9.1 V_codex D2 — first cross-V landing

The `V_codex` D2 module is an independent, self-contained smoke test:

* Imports **only** `V_gpt55.MatrixPrimitives` (D1).  No edits to V_gpt55, no shared local types beyond D1's `BoolMatrix`, `fingerprint`, `SparseDistinguisherMatrix`.
* Defines an `identity-style 2 × 2` matrix `D_id`, explicit YES/NO bitstrings `toyYes = 11` / `toyNo = 00`, and a local separation predicate `ToySeparated D yes no := fingerprint D yes ≠ fingerprint D no`.
* Closes `D_id_sparse`, the two per-coordinate `fingerprint_D_id_toyYes_zero/one` lemmas, and `toy_fingerprint_separation` (the headline) by `decide` / `funext + fin_cases <;> decide`.
* No `sorry` / `admit` / `axiom` / `opaque` / `Fact` / `Classical.choose`.
* `lakefile.lean` extended by one entry in the existing `Glob.one ...` pattern (within allowed scope per README §4).

**Significance.**  This is **the first cross-V landing** for fp3b6.  The V_codex worker reused V_gpt55's D1 primitives across handle boundaries without modification.  This is a weak positive signal for **D1's interface quality**: a second worker, working independently, was able to consume D1 cleanly.

**What V_codex D2 does NOT establish.**  Exactly the same caveats as V_gpt55 D2 (Round 2 review §1.3).  A single explicit `2 × 2` separation does not establish non-vacuity on honest-structured families, nor distinguish honest from hardwired payloads.  V_codex D2 is a smoke test, not a non-vacuity theorem.

**V_codex D2 verdict.**  APPROVE LANDING.  Cross-V signal: D1 interface is multi-worker-usable.

### 9.2 V_gpt55 D3 strengthening — **syntactic re-packaging, not content strengthening**

The +32-LOC addition introduces a new theorem `no_supportProfile_implication_to_overlapping_separation` (`AntiCollapse.lean:81-110`):

```lean
theorem no_supportProfile_implication_to_overlapping_separation
    (F : PayloadFamily)
    (hF : AllEssentialPayload F)
    (n m k r : Nat)
    (x : Bitstring n) :
    ¬ (((FormulaCircuit.support (adversaryFamily_v_arbpayload F n)).card =
          widthFn n) →
        ∃ D : BoolMatrix m n,
          SparseDistinguisherMatrix m n k D ∧
            FingerprintSeparation D ({x} : Finset (Bitstring n)) ({x}) (r + 1))
```

**Logical content analysis.**  Let
`P_F := (FormulaCircuit.support (adversaryFamily_v_arbpayload F n)).card = widthFn n`,
`R   := ∃ D, SparseDistinguisherMatrix m n k D ∧ FingerprintSeparation D ({x}) ({x}) (r+1)`.

The new theorem is `¬(P_F → R)`.  Classically (which Lean's `Classical.em` admits in the ambient logic):

```
¬(P_F → R)   ≡   P_F ∧ ¬R
```

i.e., the new statement is **logically equivalent** to the conjunction form already present in `allEssentialLogWidthPayload_no_fingerprintSeparation` (Round 2 review §2.1).  The proof of the new theorem at `AntiCollapse.lean:101-110` confirms this directly:

```lean
intro hderive
have hSupport : … = widthFn n := adversaryFamily_v_arbpayload_support_card F hF n
exact no_sparse_matrix_separates_overlapping_singletons (m := …) (n := …) (k := …) x r
  (hderive hSupport)
```

It uses exactly the same two ingredients as the original conjunction: (a) the pre-existing `adversaryFamily_v_arbpayload_support_card` support-card lemma; (b) `no_self_fingerprintSeparation` via `hammingDistance_self = 0`.

**The two structural problems from Round 2 review §2.2 persist.**

* **Axis (a) — payload independence of the load-bearing factor.**  `¬R` (the right-hand factor in `P_F ∧ ¬R`) does not depend on `F`.  It is the universal self-separation impossibility for any singleton at positive radius.
* **Axis (b) — overlapping YES/NO is not the audit-route YES/NO.**  The relation `{x}` vs `{x}` is degenerate.  Magnification-relevant separation (per OPS 2021 `s₁ < s₂`, per Atserias–Müller code-like distance) requires non-overlapping YES vs far-NO in input space.

**What the strengthening clarifies.**  The new framing — *"no black-box implication from support-cardinality facts to an overlapping-singleton separator exists"* — is a useful **rhetorical** clarification of the same skeleton.  It makes explicit that the D3 lesson is "no automatic derivation principle from support facts to matrix witness".  The doc-comment correctly says: *"the payload facts are real and kernel-checked, but the matrix/relation witness is not derivable from them alone."*  This is honest.

**What the strengthening does NOT do.**

* It does not introduce a non-overlapping YES/NO relation.
* It does not make the second factor (`¬R`) depend on `F`.
* It does not refute the **strong** anti-collapse statement (existential or hardwiring-twin form per Round 2 review §5.1) — that statement remains neither proved nor refuted.
* It does not discharge the README §3 D3 obligation.

**V_gpt55 D3 strengthening verdict.**  ACCEPT as rhetorical clarification of the D3 skeleton.  **D3' (per Round 2 review §5.1) remains MATERIALLY OPEN.**  No status change to the slot.

### 9.3 Updated pack status

| Slot | Status (post-addendum) | Note |
| --- | --- | --- |
| D1 | LANDED ✓ (`V_gpt55`) | Round 1 |
| D5 | LANDED ✓ (`V_gpt55`) | conservative; D5-tight follow-up still open |
| D2 | LANDED ✓ (`V_gpt55`, `V_codex`) | **cross-V smoke confirmation** for D1 |
| D3 | **MATERIALLY OPEN** | `V_gpt55` skeleton clarified rhetorically; logical content unchanged |
| D3' | OPEN for dispatch | unchanged from Round 2 review §5.1 |
| D5-tight | OPEN for dispatch | unchanged from Round 2 review §5.2 |
| D4 | GATED on D3' | unchanged |

Pack status: **OPEN** (Round 2 fully landed including cross-V D2; D3 obligation still re-opened as D3').

### 9.4 Discipline note for D3' re-dispatch

The V_gpt55 strengthening pattern — converting a conjunction `P ∧ ¬R` into a negated implication `¬(P → R)` to make the framing rhetorically sharper without changing logical content — should be **explicitly flagged in the D3' dispatch prompt** as a non-discharging move.  Workers attacking D3' must:

* Either prove `D3'-A` (existential F with no separator against a **non-overlapping** YES_F / NO_F derived from F's truth table), or
* Prove `D3'-B` (honest H admits a witness; hardwiring twin T of H does not), or
* Ship a structured `failures/D3prime_<HANDLE>.md` with `Local` / `Global` classification.

Any return-trip that produces yet another `(payload-fact) ∧ ¬(degenerate-separation)` shape — in any logical encoding (conjunction, negated implication, contrapositive, etc.) — is **not** a discharge of D3' and should be reviewed as such, **not** merged as a strengthening.
