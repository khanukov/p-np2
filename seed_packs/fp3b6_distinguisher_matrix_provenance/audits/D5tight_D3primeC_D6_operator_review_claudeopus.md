# fp3b6 D5-tight + D3'-C + D6 operator review — claudeopus

**Slot:** combined operator review (D5-tight parameter extraction, D3'-C sharpness, D6 budget reconciliation).
**Handle:** claudeopus (claude-opus-4-7).
**Branch reviewed against:** `main` @ `ba678b5`.

**Review subjects:**

* **D5-tight** — commit `3c58ea3` (`Add D5 tight parameter extraction report`), worker `gpt55`. File: `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_tight_parameter_extraction_gpt55.md` (253 LOC).
* **D3'-C Sharpness** — commit `0a1e986` (`Add D3 prime full-window sharpness theorem`), worker `codexd3c`. File: `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_codexd3c/Sharpness.lean` (173 LOC).
* **D6 Budget reconciliation** — commit `1ed4e60` (`Add D6 budget reconciliation report`), worker `gpt55`. File: `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D6_budget_reconciliation_gpt55.md` (201 LOC).

This is **operator-scoped review**. No Lean edits, no JSONL / spec / known_guards edits, no trust-root edits, no `ProvenanceFilter_v1` promotion, no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claims.

---

## 1. Combined verdict

| Artifact | Verdict | Note |
| --- | --- | --- |
| **D5-tight** (gpt55) | **APPROVE LANDING.** Parameter extraction is internally consistent and the executive verdict `D3prime_budget_regime_too_weak` is mathematically sound. | Verified by reading. |
| **D3'-C Sharpness** (codexd3c) | **APPROVE LANDING.** Kernel-checked converse to D3'-A: the budget cliff is **sharp**. | `rg sorry|admit` clean; CI green at merge `f9a578a`. |
| **D6 Budget reconciliation** (gpt55) | **APPROVE LANDING.** Strategic synthesis of D5-tight + D3'-C; explicit `local_only_not_magnification_ready` verdict and explicit `NO` on D3'-B Lean dispatch are correctly derived. | Verified by reading. |

**Overall fp3b6 strategic status (post-review):**

* **D3'-A as local anti-collapse:** intact and kernel-checked.
* **fp3b6 as Family A magnification route:** **STALLED.** Current parameter regime is incompatible with Atserias–Müller theorem-level budgets, and the D3'-C sharpness theorem confirms there is no nearby budget enlargement that preserves the anti-collapse argument inside the `widthFn n` window.
* **D3'-B Lean dispatch:** **BLOCKED** until a budget-repair design pass lands (per D6 §7).
* **D4 barrier checklist:** **PREMATURE** for the same reason (would assess a route the strategic audit no longer considers magnification-ready).

Pack status moves from `OPEN (Round 2/3 in progress)` to `OPEN-with-stall (budget-repair pending OR Family B cascade)`.

---

## 2. D5-tight verification

### 2.1 What the report claims

D5-tight extracts theorem-level parameters from Atserias–Müller arXiv:2503.24061 v1 (TeX source, fetched 2026-05-14) and produces nine `[verified]` subsections (§3.1–§3.9). Key extracted constants:

| Source theorem | Output length | Weight / fan-in | Sampled count | Source-level reading |
| --- | --- | --- | --- | --- |
| Theorem 1 / `dist` (basic) | `m_AM ≤ n^7` | `w_AM ≤ ⌈2n^ε⌉` | n/a | full footprint `m_AM·w_AM ≤ O(n^{7+ε})` |
| Proposition `dist` | `m_AM = dn` | `≤ 1/ε` | n/a | linear output length |
| Theorem `strdist` (strongly explicit) | `m_AM ≤ n^11` | `≤ 8 log(2n)/ε` | n/a | enhanced explicitness |
| Lemma `localform` | n/a | n/a | sampled count `r` with success at `bρ - bq ≥ n` | sampled XOR with oracle input `10r log m` |
| Main `thm:main` | `m ≤ n^7` | `w = ⌈2n^ε⌉` | `r = 17⌈n^γ⌉` | sampled footprint `r·w = Θ(n^{γ+ε})` |
| `parityP` (uniform MCSP) | `m ≤ n^11` | `8 log(2n) n^ε` | `r = ⌈16q+32⌉` with `q = n^{2γ}` | sampled footprint `Θ(n^{2γ+ε} log n)` |

### 2.2 Math consistency check

The exponent arithmetic in §3 is self-consistent:

* `m_AM · w_AM ≤ n^7 · 2n^ε = O(n^{7+ε})`. ✓
* `r · w_AM = 17⌈n^γ⌉ · ⌈2n^ε⌉ = Θ(n^{γ+ε})`. ✓
* `10 r log m_AM = 10 · 17⌈n^γ⌉ · 7 log n = Θ(n^γ log n)`. ✓ (for polynomial `m_AM`)
* Uniform MCSP version: `r · w = Θ(n^{2γ}) · Θ(n^ε log n) = Θ(n^{2γ+ε} log n)`. ✓

None of these is `O(log n)` for fixed positive `γ`, `ε`. The D3'-A budget cliff `m*k + ρ ≤ widthFn n = Nat.log2(n+1)` is therefore strictly below every extracted footprint in every reading (full / sampled / oracle).

### 2.3 Three readings, three rejections

§5 of D5-tight considers three possible mappings of fp3b6 symbols to AM quantities (full distinguisher / sampled fingerprint / oracle-input) and rejects each by direct exponent comparison. All three rejections are mathematically valid given the extracted constants. The report does not overstate: it explicitly does not claim AM as a whole is impossible, only that the **theorem-level surfaces inspected** put their footprints **strictly outside** the `widthFn n` window.

### 2.4 Honest unverified disclosures

§7 of D5-tight explicitly lists what was **not** verified:

* Full AM proofs line-by-line (only theorem-level statements).
* Per-input-coordinate output sparsity (fp3b6 column support analogue stays `[unverified]`).
* Whether an ultra-sparse subcase `q(n) = O(log n)` plus nonstandard approximation radius could force `r·w = O(log n)` (not in the main theorem-level regime).
* Version drift beyond v1.
* Other 4 literature sources from the original D5 report (CHOPRS, OPS, CJW, CHMY) — explicitly out of scope of D5-tight.

This is exactly the discipline pattern from the original D5 (`[unverified]` markers preserved, scope tight). No fabricated constants.

### 2.5 D5-tight caveat

I cannot independently verify the arXiv TeX source from this operator-review environment (no web access). The report's parameter extraction relies on the worker's reading of `arXiv:2503.24061v1`. Consistency checks I can run:

* Internal exponent arithmetic — consistent (§2.2 above).
* Cross-comparison with the prior D5 report (`D5_literature_parameter_table_gpt55.md`) — consistent: the prior D5 marked exactly these constants as `[unverified]`, and D5-tight now resolves them with explicit values.
* The shape of the construction (kernel sampling, `r δ - q ≥ 2` slack, XOR-of-AND fan-in) matches the family of constructions standard in magnification literature (CJW, OPS, AM).

**Operator note:** the report should be considered **verified-modulo-source-fidelity**. A second independent reader with web access could re-check arXiv:2503.24061v1 against the cited section names (`Theorem 1`, `Theorem dist`, `Proposition dist`, `Theorem strdist`, `Definition K(Q,D,r)`, `Lemma kernel`, `Lemma localform`, `Theorem thm:main`, `Theorem parityP`). I have no reason to suspect fabrication, but this layer of verification is deferred.

### 2.6 D5-tight verdict: APPROVE LANDING

The report is well-disciplined, internally consistent, and yields a clear executive verdict that aligns with my D3'-A review caveat 3 (which flagged the budget regime as `[unverified]` against AM constants). D5-tight resolves that caveat in the negative direction: the budget regime is **not** magnification-ready.

---

## 3. D3'-C Sharpness verification

### 3.1 What the file proves

The file `V_codexd3c/Sharpness.lean` constructs `payloadIdentityMatrix : BoolMatrix (widthFn n) n` (line 37-38):

```lean
def payloadIdentityMatrix (n : Nat) : BoolMatrix (widthFn n) n :=
  fun i j => decide (j = payloadEmbed n i)
```

i.e., row `i` selects exactly the embedded ambient coordinate `payloadEmbed n i`, and zero everywhere else.

It then proves:

1. Each row has support exactly `{payloadEmbed n i}` (`rowSupport_payloadIdentityMatrix`, line 41-44), so row card = 1 (`payloadIdentityMatrix_row_card`, line 47-49).
2. Each column has support ≤ 1 (`payloadIdentityMatrix_col_card_le_one`, line 52-61), via `payloadEmbed_injective`.
3. Therefore the matrix is `SparseDistinguisherMatrix (widthFn n) n 1` (`payloadIdentityMatrix_sparse`, line 64-70).
4. Singleton-support parity reduces to bit projection (`supportParity_singleton`, line 73-98) — careful case split on `x j ∈ {true, false}`.
5. The fingerprint with `payloadIdentityMatrix` is **literally the payload-window projection** (`fingerprint_payloadIdentity_apply`, line 101-104): `fingerprint (payloadIdentityMatrix n) x i = x (payloadEmbed n i)`.
6. Headline: `payloadIdentity_separates_payloadYes_farNo` (line 149-166) — this matrix DOES separate `payloadYesSet n` from `payloadFarNoSet n ρ` at radius 1, whenever `ρ ≥ 1`.

### 3.2 Relation to D3'-A

D3'-A's budget hypothesis is `m * k + ρ ≤ widthFn n`. In Sharpness, the chosen matrix has `m = widthFn n`, `k = 1`, so `m * k = widthFn n`. With `ρ ≥ 1`, we have `m * k + ρ = widthFn n + ρ > widthFn n` — the budget **fails**. D3'-A therefore says **nothing** about this case; Sharpness fills the gap by showing the budget cliff is **tight**:

* Below the cliff (`m*k + ρ ≤ widthFn n`): no separation by any sparse matrix at radius 1 (D3'-A).
* At/above the cliff (`m*k ≥ widthFn n`): separation is trivial via the payload-identity matrix (D3'-C).

This is exactly the right shape for an audit-route sharpness pair. The doc-comment (line 145-147) correctly states this: *"This does not refute D3′-A: the D3′-A theorem assumes a budget inequality that leaves payload coordinates unqueried, while this matrix intentionally uses one row for every payload coordinate and reads the whole payload window."*

### 3.3 Scope compliance

* Imports `V_codexd3a.AntiCollapsePrime` (allowed — explicit upstream).
* `open V_gpt55` for D1 primitives, `open V_codexd3a` for D3'-A geometry. Allowed.
* No edits to existing audit-route modules.
* No `sorry` / `admit` / `axiom` / `opaque` / `Fact` / `Classical.choose` (`rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` returns empty).
* `Mathlib.Tactic` imported; computation closes by `simp`/`decide`/`omega`-style tactics.
* Module path `V_codexd3c/` per fp3b6 README §4 V-handle convention. Allowed.

### 3.4 Strategic significance

D3'-C is a **strategic gift, not just hygiene**. Before D3'-C, one might have argued: "OK, D3'-A's `m*k + ρ ≤ widthFn n` is too tight for AM, but maybe with a slight budget relaxation the proof still works." D3'-C kills that: the moment `m*k` reaches `widthFn n`, separation is **trivial** (one-coordinate-per-row identity matrix solves it). There is no "almost-but-not-quite" zone where the anti-collapse persists at a slightly enlarged budget. This is exactly why D6 then concludes `local_only_not_magnification_ready`.

### 3.5 D3'-C verdict: APPROVE LANDING

Kernel-clean, scope-compliant, strategically informative.

---

## 4. D6 Budget reconciliation verification

### 4.1 What the report says

D6 takes D5-tight + D3'-C (implicitly, via the budget cliff argument) and produces:

* **Executive verdict** `local_only_not_magnification_ready` (§1).
* Three possible parameter interpretations A (full footprint), B (sampled footprint), C (oracle/kernel input), each analyzed for `widthFn n` compatibility, `widthFn`-modification feasibility (constrained by `InPpolyFormula` polynomial-size hardwiring), and NOGO-000006 relevance (§3).
* **Hardwiring-window constraint** (§4): the same `widthFn n = Nat.log2(n+1)` that makes arbitrary truth-table hardwiring polynomial (`2^{widthFn n} = poly(n)`) **also** makes the payload small enough for AM-scale fingerprints to read entirely. The constraint is **structural**, not cosmetic.
* **Five salvage options** (§5):
  - A. Keep D3'-A as local-only (safest, default).
  - B. Change payload width from `log n` to `q(n)` — kills polynomial truth-table hardwiring unless `q(n) = O(log n)`.
  - C. Charge matrix description/cost instead of sparsity — plausible but requires new design pack.
  - D. Require payload-independent matrix witness — plausible but risks NOGO-000007/008/009 traps.
  - E. Move to Family B (fp3b7 almost-natural) — sequencing recommendation.
* **Recommended next seed pack** (§6): **`fp3b7_almost_natural_provenance`** (primary) OR **`fp3b6_budget_repair`** (fallback if operator wants to preserve Family A).
* **Explicit go/no-go on D3'-B** (§7): **NO** — D3'-B Lean dispatch should not proceed until a markdown budget-repair pass specifies (i) what `m`/`k`/`ρ` denote in the repaired regime, (ii) whether payload remains arbitrary truth-table hardwiring, (iii) why a larger-budget fingerprint cannot just inspect all payload bits, (iv) how the candidate avoids NOGO-000007/008/009 traps.

### 4.2 Logical soundness audit

§4's **central reconciliation argument** is the key strategic claim. Stated precisely:

> Arbitrary all-essential truth-table payload of width `q(n)` has formula size `~ 2^{q(n)}`. For this to be polynomial (i.e., for the NOGO-000006 hardwiring witness to remain in `InPpolyFormula`), we need `q(n) = O(log n)`. But then `q(n) ≤ widthFn n`, and any AM-scale fingerprint with footprint `> widthFn n` can simply query all payload bits — defeating the row-union hiding argument of D3'-A.

This is a real **double-bind**: the same logarithmic window that makes NOGO-000006 valid (polynomial-size hardwiring) is exactly what makes AM-scale fingerprints win against D3'-A's hiding argument. Neither parameter can be moved without breaking the other side.

I verify this is sound:

* `2^{q(n)} = poly(n) ⟺ q(n) ≤ c log n` for some constant `c`. Standard.
* AM main theorem footprint `r * w_AM = Θ(n^{γ+ε})` (per D5-tight §3.6). Standard.
* For `n^{γ+ε} > c log n` (true for any `γ + ε > 0` and large `n`), AM footprint exceeds the polynomial-hardwiring window. **The double bind is real.**

This is a **structural** obstruction, not a parameter-tuning issue. Salvage options B (enlarge `q`) and D (payload-independent witness) both correctly identify that escaping the bind requires moving outside arbitrary truth-table hardwiring or outside sparse-fingerprint accounting.

### 4.3 Compatibility with fp3b5 strategic audit and README §7 pivot

fp3b5 strategic audit §6 secondary recommendation: **"if `Global` failure invalidates the semantic-by-design argument → cascade to Family B (almost-natural) dispatch."**

D6's strategic finding is **not exactly a `Global` failure** in README §7's literal sense:

* D3'-A did **not** ship a `Global`-classified failure report. It shipped a clean kernel-checked theorem.
* The obstruction is **discovered downstream**, in D5-tight's parameter audit and D3'-C's sharpness counter-direction.
* D3'-A's mathematical content is intact; only its strategic role (Family A magnification bridge) is invalidated.

This is a **new failure mode** the README §7 protocol did not anticipate: *the theorem is mathematically correct but in the wrong parameter regime, with no nearby regime that fixes both the polynomial-hardwiring and the magnification-bridge requirements simultaneously.*

D6's pivot recommendation (fp3b7 primary, fp3b6_budget_repair fallback) is **consistent in spirit** with fp3b5's protocol even though the trigger differs in form. The operator should record this clearly: fp3b6 is not closed by a Lean-formalized NOGO; it is reclassified as `local-only` by a parameter-extraction + sharpness-counter-direction combined witness.

### 4.4 NOGO-000010 consideration

Should D5-tight + D3'-C + D6 generate a new NOGO entry?

**Tentative answer: not yet, and not in this review.**

* The pattern documented is a **parameter-regime mismatch with a structural lock**, not a classical hardwiring or natural-proofs barrier in the sense of NOGO-000006–000009.
* NoGoLog entries in fp3b6's existing chain are all kernel-checked formal witnesses (`formal_witness` field in `outputs/nogolog.jsonl`). D3'-C is kernel-checked, but it documents the **sharpness** of a local theorem, not a barrier against a filter family.
* The fp3b6 README §4 explicitly forbids appending to `outputs/nogolog.jsonl` from this seed pack ("Phase-1 sketch audits do not yet warrant NOGO entries").
* The honest framing in `outputs/nogolog.jsonl`-grade language would be something like: *"Distinguisher-matrix provenance with `m*k + ρ ≤ widthFn n` budget admits payload-anchor anti-collapse but is sharp at `m*k = widthFn n`, and the AM theorem-level distinguisher footprints exceed `widthFn n`."* This deserves recording somewhere, but **not as a NoGoLog entry in this review**.

A future operator decision is needed:

* **Option (a):** keep fp3b6 OPEN with a `STALLED` substatus, no NoGoLog change; defer to fp3b7 dispatch.
* **Option (b):** archive fp3b6 with a NOGO-000010 entry documenting the magnification-regime mismatch, similar in spirit to NOGO-000007 (closure of a filter design subspace).
* **Option (c):** open `fp3b6_budget_repair` as a markdown-only design pack to attempt salvage option C or D from D6 §5, before deciding on (a) or (b).

I do **not** make this decision in this review (scope: review only, no JSONL writes). Operator should choose.

### 4.5 D6 verdict: APPROVE LANDING

Strategically sound, mathematically consistent, scope-compliant. The `NO` on D3'-B Lean dispatch is well-reasoned. The pivot recommendation (fp3b7 primary, fp3b6_budget_repair fallback) is a clean read of the situation.

---

## 5. Updated fp3b6 status

| Slot | Pre-D5-tight | Post-D6 |
| --- | --- | --- |
| D1 (matrix primitives) | LANDED ✓ | LANDED ✓ |
| D2 (toy separation) | LANDED ✓ (V_gpt55 + V_codex) | LANDED ✓ |
| D3'-A (anti-collapse) | LANDED ✓ (V_codexd3a) | LANDED ✓ — **strategically reclassified as local-only** |
| D3'-C (sharpness) | (n/a) | LANDED ✓ — **confirms cliff is sharp** |
| D5 (lit table) | LANDED ✓ | LANDED ✓ |
| D5-tight (param extraction) | OPEN | LANDED ✓ — **verdict: budget too weak for AM** |
| D6 (reconciliation) | (n/a) | LANDED ✓ — **verdict: local_only_not_magnification_ready** |
| D3'-B (hardwiring twin) | OPEN for dispatch | **BLOCKED** until budget-repair markdown lands |
| D4 (barrier checklist) | gated | **PREMATURE** — gating technically met, strategically not informative |

Pack status: **OPEN-with-stall.** D3'-A is a valid local anti-collapse fact; fp3b6 as a Family A magnification route is stalled.

---

## 6. Recommended next step

Decision tree for the operator:

```
                Was D3'-A's local-only reclassification
                acceptable for the project's strategic goals?
                            |
              ┌─────────────┴─────────────┐
              │                           │
            YES                          NO
              │                           │
   ┌──────────┴──────────┐               │
   │                     │               │
Family B cascade     Salvage attempt    Salvage attempt
(open fp3b7)         (open             (open
                      fp3b6_budget_     fp3b6_budget_
                      repair markdown)  repair markdown)
   │                     │               │
   ▼                     ▼               ▼
fp3b6 archived       fp3b6_budget_     fp3b6_budget_
with STALLED         repair design     repair design
substatus; no        pass first        pass first
NOGO-000010 yet      (then either      (then either
                     fp3b7 cascade     re-dispatch or
                     or D3'-B redux)   accept failure)
```

**Operator-recommended path (one of three):**

1. **Open `fp3b7_almost_natural_provenance` immediately** (D6 primary recommendation). Treat D3'-A as a valid local result, archive fp3b6 as STALLED (not CLOSED), defer NOGO-000010 question. **Lowest risk of further wasted effort; highest strategic re-deployment of effort to Family B.**
2. **Open `fp3b6_budget_repair` markdown-only design pack** (D6 fallback). Required deliverable per D6 §7: pin down `m`/`k`/`ρ` semantics in the repaired regime, with NOGO-000007/008/009 self-attack analysis, and an on-paper proof that the new budget still blocks NOGO-000006. **Higher risk of getting stuck in same double-bind; preserves Family A option.**
3. **Open both in parallel** (most expensive in dispatch terms, lowest risk of strategic regret). fp3b6_budget_repair as a markdown-only sanity attempt; fp3b7 as the primary forward bet.

My operator preference, if forced to choose: **option 1 (fp3b7).** Reason: the double-bind documented in D6 §4 is structural, not parametric. Salvage options C/D in D6 §5 require essentially a new semantic predicate, which is exactly what fp3b7 (almost-natural / Family B) is for. Spending dispatcher effort on `fp3b6_budget_repair` risks reproducing the same trap with new symbols.

This recommendation is **deferred to the operator** — I make no dispatch action and write no JSONL/spec/known_guards/registry changes.

---

## 7. Commands run

* `git fetch origin && git checkout main && git pull origin main --ff-only` → synced to `ba678b5`.
* `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` → **no output** (Lean sources clean across all of pnp3 and pnp4, including new `V_codexd3c/Sharpness.lean`).
* `lake build PnP3 Pnp4` — **NOT RUN.** No Lean toolchain in operator-review environment. CI green at merges `79903d9` (D5-tight), `f9a578a` (D3'-C), `ba678b5` (D6).
* `./scripts/check.sh` — **NOT RUN** (same reason).

---

## 8. Scope violations

**None.** This review writes only the present file at the allowed path `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/D5tight_D3primeC_D6_operator_review_claudeopus.md`. No Lean edits, no `outputs/nogolog.jsonl` append (NOGO-000010 question deferred to operator), no `outputs/attempts.jsonl` append, no `spec/known_guards.toml` edit, no trust-root edit, no `ProvenanceFilter_v1` promotion, no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP language.

---

## 9. Output summary

```
Review target: D5-tight + D3'-C + D6 (consolidated)
Handle: claudeopus
Verdicts:
  - D5-tight: APPROVE_LANDING (executive D3prime_budget_regime_too_weak verified
    consistent; verification modulo arXiv source fidelity)
  - D3'-C Sharpness: APPROVE_LANDING (kernel-clean; budget cliff is sharp at
    m*k = widthFn n)
  - D6 Budget reconciliation: APPROVE_LANDING (strategic verdict
    local_only_not_magnification_ready well-founded; double-bind argument
    structurally sound)
Review file: seed_packs/fp3b6_distinguisher_matrix_provenance/audits/D5tight_D3primeC_D6_operator_review_claudeopus.md
fp3b6 strategic status: OPEN-with-stall (Family A magnification route stalled;
                        D3'-A intact as local-only anti-collapse)
D3'-B Lean dispatch: BLOCKED (per D6 §7) until budget-repair markdown lands
D4 barrier checklist: PREMATURE (gating technically lifted, strategically not informative)
NOGO-000010: NOT FILED IN THIS REVIEW (deferred to operator)
Recommended next step: open fp3b7_almost_natural_provenance (primary) OR
                       fp3b6_budget_repair (fallback markdown design pack);
                       operator-recommended preference: fp3b7 primary
Commands run:
  - git fetch / checkout main / pull --ff-only → ba678b5
  - rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4 → no output
  - lake build / scripts/check.sh → NOT RUN (no toolchain; CI green at merges)
Scope violations: none
```
