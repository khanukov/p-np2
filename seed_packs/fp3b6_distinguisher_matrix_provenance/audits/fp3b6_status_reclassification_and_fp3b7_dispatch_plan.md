# fp3b6 status reclassification + fp3b7 dispatch plan — operator strategic decision

**Author:** operator-side strategic decision (claudeopus).
**Branch reviewed against:** `main` @ `ba678b5`.
**Prior context:** PR #1260 (`D5tight_D3primeC_D6_operator_review_claudeopus.md`).

This is an **operator strategic decision document**. It writes only the present markdown file. It does **not** edit Lean modules, `outputs/nogolog.jsonl`, `outputs/attempts.jsonl`, `spec/known_guards.toml`, trust-root, any V-handle subdirectory, or any existing seed pack outside this audits directory. It does **not** create `seed_packs/fp3b7_almost_natural_provenance/` skeleton files (that is a separate dispatcher action, not an operator-decision action). It does **not** promote `ProvenanceFilter_v1`, write `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness`, or claim FP-4 / final endpoint / P ≠ NP.

---

## 1. Executive decision

```text
fp3b6 status:        OPEN-with-stall  →  STALLED  (not CLOSED, not NoGoLog'd yet)
fp3b6_budget_repair: NOT OPENED
fp3b7:               OPEN with single starting slot fp3b7-D0
                     (barrier-aware feasibility check, markdown-only)
NOGO-000010:         DEFERRED  (no formal Lean witness yet; decision after fp3b7-D0)
D3'-B Lean:          BLOCKED  (per D6 §7; unchanged)
D4 (fp3b6):          PREMATURE  (unchanged; stays gated even though README §3 gating technically lifted)
```

**Headline reasoning.** The fp3b6 stall is caused by a **structural double-bind**, not a parameter mistake. Repairing fp3b6 by tweaking budget symbols is high-risk for re-discovering the same bind. The honest move is to (a) keep fp3b6 STALLED as a documented dead route for the Family-A magnification-bridge interpretation while preserving its valid local artifacts, and (b) open Family B (fp3b7) with a **single barrier-aware feasibility slot** before any full multi-slot dispatch, to avoid pattern-matching into the same trap.

---

## 2. fp3b6 status reclassification

### 2.1 New status: STALLED

`fp3b6_distinguisher_matrix_provenance` is moved from `OPEN (Round 2/3 in progress)` to **STALLED — Family A magnification-bridge interpretation not viable under current double-bind**.

`STALLED` (not `CLOSED`) is the deliberate choice. It records that:

* No NoGoLog entry has been formally filed for this stall.
* Some salvage avenues exist in principle but require essentially a new semantic predicate (D6 §5 options C, D), which would make the resulting work a new family rather than fp3b6 continued.
* The pack's existing artifacts remain valid as documented intermediate work.

### 2.2 What remains valid

* **D1 primitives** (`V_gpt55/MatrixPrimitives.lean`) — kernel-clean, multi-handle-usable, retained as a Lean infra module.
* **D2 toy separations** (`V_gpt55/`, `V_codex/`) — retained as kernel-checked smoke tests for the primitives.
* **D3'-A anti-collapse** (`V_codexd3a/AntiCollapsePrime.lean`) — retained as a **local-only** anti-collapse theorem. It is mathematically correct and remains a useful side-result about the log-window sparse-fingerprint regime; it is **not** a magnification-route survivor.
* **D3'-C sharpness** (`V_codexd3c/Sharpness.lean`) — retained as the matching converse showing the D3'-A budget cliff is tight.
* **D5 / D5-tight literature reports** — retained; provide the AM theorem-level constants that triggered this reclassification.
* **D6 budget reconciliation** — retained; documents the structural double-bind explicitly.
* **Round 1 / Round 2 / D3'-A / D5-tight+D3'-C+D6 operator reviews** — retained as governance record.

### 2.3 What is forbidden against this pack going forward

While STALLED:

* No new V-handle subdirectory under `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/`.
* No D3'-B Lean dispatch (per D6 §7).
* No D4 barrier-checklist dispatch.
* No `fp3b6_budget_repair` markdown pass (see §3 below for explicit rationale against this).
* No edits to existing fp3b6 Lean modules — they are frozen as STALLED-artifact documentation.
* New audit-side notes (markdown) added under `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/` remain allowed for governance updates, retrospectives, or cross-reference notes from successor packs.

### 2.4 What is permitted to reopen this pack

`STALLED → OPEN` requires either:

* An operator decision after fp3b7-D0 lands (see §4 below) that explicitly authorizes a `fp3b6_budget_repair` design pass with a **pre-specified new semantic predicate**, not a parameter tweak; or
* A successor pack (fp3b7, fp3b8, …) discovering that an fp3b6 Lean artifact (D1 primitives or D3'-A / D3'-C theorems) can be reused in a new context — that reuse is allowed without re-opening fp3b6, as long as the reuse path doesn't claim fp3b6 itself is alive again.

### 2.5 Why STALLED and not CLOSED

`CLOSED` would imply either:

* A formalized NoGoLog entry exists (NOGO-000010), or
* A definitive proof that no extension of the route can work.

Neither holds today:

* The D6 double-bind argument is honest and structurally compelling, but it relies on parameter-extraction from one paper (Atserias–Müller arXiv:2503.24061 v1) and on the polynomial-hardwiring constraint of NOGO-000006. A Lean formalization of the double-bind as a class-level barrier theorem (analogous to NOGO-000007 / NOGO-000009 meta-barriers) does **not** exist yet.
* Salvage options C (cost-charged matrix witness) and D (payload-independent witness) in D6 §5 are not refuted; they are deferred because they require a new semantic predicate, which is outside fp3b6's scope.

Therefore `STALLED` is the epistemically correct status. The operator deliberately does not file NOGO-000010 in this decision — see §5 below for the deferral rationale.

---

## 3. Why not `fp3b6_budget_repair`

`fp3b6_budget_repair` (markdown-only design pack to attempt salvage options C or D from D6 §5) was the visible fallback option in D6 §6. The operator declines to open it. Reasoning:

### 3.1 Salvage options are predicate-replacement, not budget tweaks

D6 §5.C says the matrix-cost-charging route "is not a D3′-B Lean task yet; the budget and theorem statement would need to be redesigned first." D6 §5.D says the payload-independent-witness route "needs a semantic/provenance definition, not a quick local Lean extension." Both options require a **new semantic predicate**. A pack called `fp3b6_budget_repair` that produces a new semantic predicate is dishonestly named: it is a new family, not a repair of fp3b6.

### 3.2 Risk of re-discovering the same double-bind

The double-bind documented in D6 §4 is between two requirements:

```text
(R1)  arbitrary all-essential truth-table payload of width q(n)
      remains polynomial-size hardwiring  ⟺  q(n) = O(log n)
(R2)  AM-style fingerprint footprint operates in the magnification regime
      ⟹  fingerprint footprint  =  Ω(n^{γ+ε})  ≫  q(n) when q(n) = O(log n)
```

Any "budget repair" that keeps both (R1) and (R2) will hit this bind regardless of which intermediate symbol is renamed. Markdown design passes inside the same conceptual frame typically rediscover the constraint without recognizing it as the same one. This is a well-attested failure mode in lower-bounds research (Razborov–Rudich was famously discovered by people trying to "fix" lower-bound proofs without realising they were inside the natural-proofs barrier).

### 3.3 Sunk cost is not a reason

We have invested in fp3b6 across multiple rounds. That is not a justification to invest further. The kill-machine framework's whole point is that early kills are the value, not the loss.

### 3.4 If the operator changes mind later

The decision against `fp3b6_budget_repair` is not permanent. The natural reversal is: if fp3b7-D0 (§4) lands GREEN-light on Family B, then `fp3b6_budget_repair` is moot. If fp3b7-D0 lands RED-light (Family B has its own structural lock), then the operator may revisit `fp3b6_budget_repair` as a remaining option, but **only** with a specific salvage option (C or D) pre-pinned and a pre-written justification why it escapes the (R1, R2) bind.

---

## 4. fp3b7 dispatch plan

`fp3b7_almost_natural_provenance` is OPENED, but **with a single starting slot fp3b7-D0**, not a full multi-slot Round 1 dispatch.

### 4.1 Why a single starting slot

The fp3b5 strategic audit (§6) ranked Family A as primary and Family B as secondary. That ranking was based on then-available information. fp3b6's stall does **not** automatically upgrade Family B; it only removes Family A from the top of the queue. Before committing dispatch effort to a multi-slot Round 1 Family-B build-out, we want a cheap markdown-only barrier-aware feasibility check, **analogous to the D5-tight pass that just stalled fp3b6**.

This is the kill-machine discipline pattern: **before** large investment, run a cheap check that the route's natural parameter regime is at least plausibly compatible with the obstruction class it needs to address.

### 4.2 fp3b7-D0 slot specification

```
Slot:          fp3b7-D0
Title:         Barrier-aware feasibility check for almost-natural / Family B
Type:          markdown-only design audit
Expected LOC:  150–400 lines
Handle policy: any handle (single worker; cross-V deferred until D0 lands GREEN-light)
```

**Deliverable.** A markdown report at `seed_packs/fp3b7_almost_natural_provenance/reports/D0_barrier_feasibility_<HANDLE>.md` answering:

1. **What does an "almost-natural" filter look like?** Specifically, what are the candidate semantic predicates (representation-sensitivity, semantic quotient, distribution-controlled usefulness, etc.) that aim to thread the Razborov–Rudich barrier from a different angle than displayed-syntax filters?
2. **What is the natural parameter regime?** Symbolically: what quantities does an almost-natural filter charge, and how do they relate to circuit size, formula size, sparsity, or hardness-magnification thresholds?
3. **Does Family B have a structural double-bind analogous to fp3b6 §4?** Specifically: is there a pair of requirements `(R1', R2')` such that the natural choice of one breaks the other (e.g., "remain a useful property" vs "remain not-large" vs "operate in the magnification regime")?
4. **Cross-check against NOGO-000006, 000007, 000008, 000009.** Does the almost-natural framing collapse into support-cardinality (NOGO-000007), syntactic-only (NOGO-000008), or normalisation-self-defeating (NOGO-000009) patterns in the limit?
5. **Cross-check against fp3b5 strategic audit §3.2.** Does the Family-B "lower expected value" assessment in fp3b5 still hold, or does the fp3b6 stall change it?

**Forbidden inside fp3b7-D0.**

* No Lean code.
* No editing of fp3b6 modules.
* No NoGoLog append.
* No `ProvenanceFilter_v1` promotion.
* No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claims.
* No claim that fp3b6 is dead or that fp3b7 is alive — those are operator decisions after D0 lands.
* No theorem-level constant extraction from literature beyond what is publicly visible in abstracts and verified bibliographic pages (the AM-specific theorem-level extraction discipline from D5-tight is the precedent, but fp3b7-D0 should remain at the "is the regime even plausible?" level, not at the "exact constants" level).

**Allowed inside fp3b7-D0.**

* Reading fp3b6 README, D5-tight, D6, this strategic-decision document, fp3b5 strategic audit, RESEARCH_CONSTITUTION, all NoGoLog entries.
* Reading first-move report family from `seed_packs/first_move_search_2026/reports/` if any of those reports touched almost-natural / representation-sensitivity directions.
* Citing public abstracts / titles / DOIs from the magnification, natural-proofs, and meta-complexity literature for orientation. Citations must be bibliographically verified per the D5-discipline rules.

**Acceptance criteria.**

* `GREEN-light`: D0 report concludes that almost-natural / Family B has a **structurally different** parameter regime than fp3b6's `widthFn n` cliff, and that the cross-check against NOGO-000006–000009 does **not** trivially collapse to a prior pattern. Operator then dispatches a full Round 1 for fp3b7 in a separate decision.
* `RED-light`: D0 report concludes that Family B has its own structural double-bind (or collapses into one of NOGO-000007/008/009), and recommends not dispatching multi-slot Round 1. Operator then re-evaluates: either open a different family (e.g., Family C / fp3b8 if such exists in the strategic audit), revisit `fp3b6_budget_repair` with a pre-pinned salvage option (per §3.4 above), or file NOGO-000010 + NOGO-000011 documenting both family closures.
* `INCONCLUSIVE`: D0 report explicitly says the question cannot be answered at markdown level and needs Lean-formalised investigation. Operator then decides whether to escalate or to treat INCONCLUSIVE as `RED-light` for cost-control reasons.

### 4.3 What fp3b7 looks like AFTER fp3b7-D0

Only **after** fp3b7-D0 lands and the operator countersigns its verdict:

* **GREEN-light path:** open `seed_packs/fp3b7_almost_natural_provenance/` skeleton with full README, WORKER_PROMPT, slot decomposition (D1 primitives, D2 toy, D3 anti-collapse, D5 lit table — pattern-following fp3b6, but with Family-B-appropriate semantic predicates), and dispatch Round 1.
* **RED-light path:** open `seed_packs/fp3b7_almost_natural_provenance/closure/` with a one-page closure report citing fp3b7-D0, and treat as input to the next operator decision (Family C, fp3b6_budget_repair revisit, or NoGoLog double-closure).

### 4.4 What this strategic-decision document does NOT do for fp3b7

* It does **not** create `seed_packs/fp3b7_almost_natural_provenance/README.md`.
* It does **not** create `seed_packs/fp3b7_almost_natural_provenance/WORKER_PROMPT.md`.
* It does **not** assign a handle to fp3b7-D0.
* It does **not** specify the dispatch instrument (operator + dispatcher decide).

Those are **dispatcher actions**, not operator-decision actions. The role of this document is to authorise the dispatcher to spin up the fp3b7 skeleton **with only the D0 slot**.

---

## 5. NOGO-000010 deferral rationale

The fp3b6 stall is documented in D5-tight + D3'-C + D6 + the prior operator review (PR #1260). It is **not** filed as NOGO-000010 in this strategic decision. Reasons:

### 5.1 No kernel-checked formal witness yet

The NoGoLog discipline (visible in NOGO-000006–000009) requires a `formal_witness` field pointing to a kernel-checked Lean module. The fp3b6 double-bind currently has:

* A kernel-checked **local-only** D3'-A anti-collapse theorem (positive content).
* A kernel-checked **converse** D3'-C sharpness theorem (positive content showing budget cliff is tight).
* Markdown D5-tight and D6 documenting the **strategic-level** double-bind via parameter extraction from one paper.

What is **missing** is a kernel-checked Lean theorem stating the class-level bind, analogous to NOGO-000007's `any_honest_sublinear_support_witness_has_hardwiring_twin` or NOGO-000009's `V2_A_NormaliseMetaBarrier`. Without that, filing NOGO-000010 with markdown-only `formal_witness` would dilute NoGoLog discipline.

### 5.2 The bind is meta-mathematical, not purely formal

The double-bind couples a Lean-side fact (D3'-A + D3'-C: budget cliff at `widthFn n`) with a literature-side fact (AM footprints exceed `widthFn n`). The literature-side fact lives outside the Lean trust root by design. Encoding it formally would require pulling AM-magnification machinery into Lean, which is far beyond fp3b6's scope.

A NoGoLog entry for this kind of mixed bind is conceptually new. It deserves its own discipline pass before being filed. Concretely: a future seed pack might attempt to **internalise** the class-level statement as a Lean theorem about "any sparse-fingerprint filter operating on log-width truth-table payloads in the AM magnification regime"; if that succeeds, NOGO-000010 can be filed at that point. Until then, deferring is honest.

### 5.3 Operator decision after fp3b7-D0

A natural deferred decision point is **after fp3b7-D0 lands**. Three scenarios:

* fp3b7-D0 `GREEN-light` and full fp3b7 Round 1 proceeds: NOGO-000010 may be filed at the operator's discretion as part of formal fp3b6 closure, possibly bundled with the Lean-side double-bind theorem if a follow-up worker can produce one cheaply.
* fp3b7-D0 `RED-light`: both fp3b6 and fp3b7 face closure decisions. The operator may file NOGO-000010 + NOGO-000011 together with the documented closures.
* fp3b7-D0 `INCONCLUSIVE`: NOGO-000010 deferral continues; operator evaluates further escalation.

In all three scenarios, the deferral until at least one of these triggers is preferable to filing now.

### 5.4 Design-note registration as the cheap alternative

A lightweight alternative to a full NoGoLog entry is a **design note** under `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/` registering the cross-cutting design constraint:

> **Design constraint (fp3b6-DC-001).** Any provenance filter intending to address NOGO-000006 by **payload-window hiding** (i.e., relying on the fingerprint not being able to query all payload bits) must explain why the filter's fingerprint footprint cannot exceed `widthFn n`. If the footprint exceeds `widthFn n`, the row-union hiding argument of D3'-A no longer applies, and a different anti-collapse mechanism (e.g., encoding cost, payload independence, semantic invariant on the truth table) is required.

This is a **route-design lesson**, not a NoGoLog entry. The operator authorises a future audit-only worker to write this design note as a 1–2 page artifact at `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/design_constraints_DC001_payload_window_hiding.md` if desired, but does not commit to dispatching that worker right now (it is low priority compared to fp3b7-D0).

---

## 6. Sequencing summary

```
NOW:
  1. This operator strategic decision lands.
  2. fp3b6 reclassified STALLED.
  3. fp3b7-D0 authorised; dispatcher spins up fp3b7 skeleton with only D0 slot.

NEXT (after fp3b7-D0 lands):
  4. Operator reviews fp3b7-D0 verdict (GREEN-light / RED-light / INCONCLUSIVE).
  5. Operator decides full fp3b7 Round 1 OR closure-and-pivot.
  6. Operator decides whether to file NOGO-000010 (and possibly NOGO-000011 if fp3b7-D0 is RED-light).

LATER (deferred without timeline):
  7. Optionally write fp3b6 design note DC-001 as 1–2 page audit artifact.
  8. Optionally formalise the fp3b6 double-bind as a class-level Lean barrier theorem.
     Required for filing NOGO-000010 with discipline parity to NOGO-000006–000009.
  9. Optionally revisit fp3b6_budget_repair if fp3b7-D0 RED-lights and no other family is open.
```

---

## 7. Cross-references

* PR #1260 (consolidated D5-tight + D3'-C + D6 operator review).
* `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/D5tight_D3primeC_D6_operator_review_claudeopus.md`.
* `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_tight_parameter_extraction_gpt55.md`.
* `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D6_budget_reconciliation_gpt55.md`.
* `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_codexd3a/AntiCollapsePrime.lean` (D3'-A; STALLED-frozen).
* `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_codexd3c/Sharpness.lean` (D3'-C; STALLED-frozen).
* `seed_packs/fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md` (Family-A vs Family-B triage; Family-B "lower expected value" assessment is now under review per §4.2 question 5).
* `outputs/nogolog.jsonl` entries NOGO-000006 through NOGO-000009 (existing barrier chain; NOGO-000010 NOT filed by this decision).
* `RESEARCH_CONSTITUTION.md` (audit-only / no-fabrication / NoGoLog discipline rules).

---

## 8. Scope confirmation

This document writes only this single markdown file at `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/fp3b6_status_reclassification_and_fp3b7_dispatch_plan.md`. It does not:

* Write any Lean module or edit any Lean module.
* Append to `outputs/nogolog.jsonl` or `outputs/attempts.jsonl`.
* Edit `spec/known_guards.toml` or any spec file.
* Create `seed_packs/fp3b7_almost_natural_provenance/` (dispatcher action, not operator-decision action).
* Promote any `ProvenanceFilter_v1`.
* Write `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP language.
* Claim P ≠ NP, P = NP, NP ⊄ P/poly, NP ⊂ P/poly, or any other unconditional complexity separation.

The decision authorises the dispatcher to spin up the fp3b7 skeleton with only fp3b7-D0; the actual skeleton-creation commits are separate.
