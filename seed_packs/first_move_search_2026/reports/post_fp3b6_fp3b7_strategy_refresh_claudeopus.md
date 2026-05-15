# Post-FP3b strategy refresh — claudeopus

**Slot:** post-FP3b strategy refresh.
**Handle:** claudeopus.
**Branch reviewed against:** `main` @ `482012e`.

This is **markdown-only operator-side strategic decision input.** It writes only this file. No Lean, no JSONL, no spec, no known_guards, no trust-root, no new seed pack skeleton, no ProvenanceFilter / SourceTheorem / gap_from / ResearchGapWitness / FP-4 / final endpoint / P ≠ NP language.

---

## 1. Executive verdict

```text
stop_fp3b_provenance_route
```

The FP3b provenance-filter line is **exhausted as a mainline route to `NP_not_subset_PpolyDAG`**. Five design subspaces are dead (V2-A, V2-A.1, V2-B/D, fp3b6 Family A, fp3b7 Family B). The remaining markdown salvage paths (fp3b6_budget_repair) re-discover the same structural binds under different symbols. Continuing iteration on filter design has decreasing marginal value and increasing risk of pattern-matching into previously-killed traps.

The honest move is to (a) declare the filter-design programme stopped, (b) keep all FP3b artifacts as documented closure / NoGo evidence, and (c) pivot to a non-filter direction. The most plausible non-filter pivot is direct meta-complexity / restricted-model MCSP source work against the repo's existing magnification bridge interface, but the pessimistic prior is that this will also RED-light at its own D0 — see §8 for the qualified recommendation.

---

## 2. What fp3b6 taught us

`fp3b6_distinguisher_matrix_provenance` was opened per fp3b5 strategic audit §6 as Family A (top-ranked of Q1/Q3/Q4 candidates). It produced **valid local content** but is **STALLED for the magnification-bridge interpretation**.

Concretely:

* **D3'-A** (`V_codexd3a/AntiCollapsePrime.lean`): `andPayload_no_sparse_fingerprintSeparation` — kernel-checked anti-collapse theorem stating that under budget `m*k + ρ ≤ widthFn n`, no `m`-row, `k`-sparse fingerprint matrix can separate the payload-anchor YES set from the tail-fixed payload-window-far NO set at radius 1. The proof is a real combinatorial support-union argument, not a degenerate self-separation triviality. **Valid as a local anti-collapse fact.**
* **D3'-C** (`V_codexd3c/Sharpness.lean`): `payloadIdentity_separates_payloadYes_farNo` — with `m = widthFn n` and `k = 1`, the payload-identity matrix **does** separate the same YES/NO at radius 1. The budget cliff at `m*k = widthFn n` is **sharp**.
* **D5-tight** (`reports/D5_tight_parameter_extraction_gpt55.md`): Atserias–Müller arXiv:2503.24061 v1 theorem-level parameters. Full distinguisher footprint `m_AM·w_AM = O(n^{7+ε})`. Sampled fingerprint footprint `r·w_AM = Θ(n^{γ+ε})`. Oracle/kernel footprint `10r log m_AM = Θ(n^γ log n)`. **None** of these is `O(log n)` in any inspected theorem regime.
* **D6** (`reports/D6_budget_reconciliation_gpt55.md`): the **structural double-bind**. The same logarithmic window that keeps NOGO-000006 arbitrary truth-table hardwiring polynomial (`2^{widthFn n} = poly(n)` requires `widthFn n = O(log n)`) also makes the payload small enough that any AM-scale fingerprint with footprint `> widthFn n` can simply query every payload bit. **Neither parameter can be moved without breaking the other side.**

The fp3b6 lesson is therefore not "the matrix/fingerprint shape is wrong" but **"matrix/fingerprint provenance constrained to the polynomial-hardwiring window is too narrow to reach the magnification regime, and no nearby budget repair fixes this."**

---

## 3. What fp3b7 taught us

`fp3b7_almost_natural_provenance` was opened as Family B per the fp3b6 STALLED reclassification (PR #1260, fp3b6 audits §4). It was opened with a single barrier-aware feasibility slot fp3b7-D0 to avoid pattern-matching into a Family A-style trap. After D0 + D0.1 + D0.1-second-review, fp3b7 RED-lighted (`audits/fp3b7_red_light_operator_decision_gpt55.md`).

The D0.1 specification produced one concrete candidate predicate: `AlmostNaturalProvenance_BC` (Sparse Structured-Payload Promise with Payload-Independent Provenance Certificate). It passed three of four review gates:

* **Non-largeness:** passed. Accepted set `T_n` has size `2^{polylog n}` in the full `BoolFun(n) = 2^{2^n}` universe, conditional on D0.1 caps for payloads, lift data, wrappers, promise tags being held fixed.
* **Non-circularity:** passed for the written predicate. Membership is by positive structured-index / lift / certificate checks, not by "not in PpolyDAG" or "no small witness" language.
* **Hardwiring rejection (NOGO-000006):** passed under strict accounting. Arbitrary all-essential log-width `ttFormula` payloads are rejected because they would need `Θ(n)` payload bits in the certificate, exceeding the polylog cost threshold.
* **Usefulness toward `PpolyDAG`: FAILED / likely too weak.**

The fp3b7 double-bind, identified in `D0_1_second_review_gpt55.md` §9 and registered in the RED-light decision:

```text
Either the certificate is genuinely cheap and payload-independent,
or the target may be useful for PpolyDAG lower bounds,
but not both.

  Cheap certificate => low-description target
    => accepted function has small nonuniform DAG via public evaluator + (d,i)
    => cannot witness NP_not_subset_PpolyDAG.

  Restrictive certificate that rejects hardwiring also rejects arbitrary useful targets
    => generic hard NP slice has no reason to land in PayloadClass.

  Broadening for usefulness => reawakens Razborov–Rudich largeness
    OR encodes the lower bound inside PayloadClass / promise tag (circularity).
```

The fp3b7 lesson is therefore **"the safety achieved by Family B is achieved by making `T_n` too narrow to support a `PpolyDAG` source theorem, and broadening `T_n` re-enters the natural-proofs danger zone or smuggles a hidden hardness assumption."**

This is **structurally the same shape** as the fp3b6 double-bind: a parameter that makes the route safe also makes it useless for the target, and the parameter cannot be moved.

---

## 4. What FP3b route as a whole has established

Despite the strategic failure, the FP3b route produced durable scientific artifacts that constrain future filter design:

**NoGoLog entries (kernel-checked formal witnesses):**

* **NOGO-000006** — arbitrary all-essential log-width `ttFormula` payload hardwiring satisfies support-cardinality filters.
* **NOGO-000007** — support-cardinality-only filter meta-barrier: any such filter admitting an honest sublinear-support witness admits a canonical hardwiring twin with the same support profile.
* **NOGO-000008** — tautological-seed rewrite attack defeats syntactic-only V2-* filters.
* **NOGO-000009** — V2-A normalisation meta-barrier: any structural normaliser that defeats NOGO-000008 also kills V2-A's own non-vacuity witness.

**Lean theorem pair (local-only but kernel-checked):**

* **fp3b6 D3'-A + D3'-C** — `andPayload_no_sparse_fingerprintSeparation` and `payloadIdentity_separates_payloadYes_farNo`. Tightly characterizes the log-window sparse-fingerprint anti-collapse cliff. The pair is a clean budget-sharpness statement for sparse-distinguisher provenance.

**Markdown closure / barrier evidence:**

* **fp3b6 D5-tight + D6** — Atserias–Müller theorem-level parameter extraction and the structural log-window-vs-AM-footprint double-bind. Documents why sparse-fingerprint provenance cannot operate in the magnification regime under polynomial-size hardwiring.
* **fp3b7 D0.1 + second review + RED-light decision** — `AlmostNaturalProvenance_BC` specification and the cheap-certificate-vs-useful-target double-bind. Documents why almost-natural promise/sparse-target provenance is safe-but-narrow.

**Aggregate lesson.** Every filter design we've tried hits one of:

```text
NOGO-000007  support-cardinality collapse
NOGO-000008  syntactic-rewrite attack
NOGO-000009  normalise-then-syntax self-defeat
fp3b6 bind   log-window cliff incompatible with magnification footprint
fp3b7 bind   cheap certificate => easy target; broad usefulness => natural/circular
```

This is **five distinct closures for filter-shaped provenance approaches**, with the last two being **structural double-binds, not removable obstructions**. The pattern is strong enough that "yet another filter family" should be treated as low-prior absent a specific reason to expect it escapes all five.

---

## 5. Remaining viable families

I propose three families, ranked by my estimate of strategic plausibility. All three are **non-filter** in shape. None is recommended for immediate full-Round-1 dispatch; each gets a single sharp D0 question.

### Family B-MCSP — direct meta-complexity / restricted-model MCSP source

**Core idea.** Do **not** build a provenance filter. Directly attack the existing repo source-theorem obligation (`SearchMCSPWeakLowerBound`, `VerifiedNPDAGLowerBoundSource`) by Lean-formalizing a restricted-model MCSP lower bound from the existing meta-complexity literature (e.g., Cheraghchi–Hirahara–Myrisiotis–Yoshida STACS 2021's one-tape Turing machine `N^{1.99}` bound or branching-program `N^{1.5-o(1)}` bound for MCSP / MKtP). Use the repo's existing magnification scaffolding (`pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`, `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean`) to bridge from the restricted bound to a `PpolyDAG`-relevant source.

**Why not support-cardinality-only.** It is not a filter at all. Support cardinality plays no role; this attacks the source-theorem side directly.

**Why not displayed-syntax-only.** Same — it operates on meta-complexity (MCSP truth-table size), not on formula syntax.

**Why not immediately natural-proof-shaped.** Restricted-model MCSP lower bounds (one-tape TM, branching programs, formulas) are barrier-aware precisely because they avoid the natural-proofs trap by **restricting the computational model**, not by restricting the property's largeness/usefulness. CHMY 2021 explicitly cites this restricted-model strategy. The natural-proofs barrier does not directly apply to restricted-model lower bounds; algebrization barriers are model-dependent and have been navigated for specific restricted models.

**How it might produce `ResearchGapWitness.dagSeparation`.** The pessimistic path: even a Lean-formalized restricted-model MCSP lower bound does **not** by itself give `NP_not_subset_PpolyDAG`. It would discharge one component of the magnification bridge that the repo has already scaffolded. Other bridge components (compression magnification, locality-aware reduction) would still be required. The route is `restricted-model MCSP bound → SearchMCSPWeakLowerBound → magnification → ResearchGapWitness.dagSeparation`. Each arrow is non-trivial. The honest claim is "this is the route the repo's scaffolding was built for", not "this gets us to P ≠ NP".

**Immediate NoGo / barrier risk.**

* Magnification-component non-triviality. The repo's `PpolyDAG`-relevant magnification bridge may itself require lower-bound regimes beyond what restricted-model MCSP provides directly.
* The CHMY-style restricted bounds are `N^{1.5}` to `N^{1.99}` polynomial regimes. The magnification threshold needed for `NP_not_subset_PpolyDAG` via existing literature is typically `n^{1+ε}` or worse, and the bridge from CHMY-style polynomial bounds to that threshold is the open part. The fp3b6 D5-tight extraction already noted that Oliveira–Pich–Santhanam ToC 2021 magnification thresholds (`s_1(N) = 2^{βn}/cn`, `s_2(N) = 2^{βn}` etc.) live in regimes not directly served by CHMY constants.
* Relativization: MCSP itself sits on the boundary of relativization barriers. Some restricted-model lower bounds for MCSP relativize and some do not; the chosen specific bound must be checked.
* Natural proofs: any general-purpose MCSP lower bound technique can become natural in expressive computational models. Restricted-model bounds avoid this **for those specific models**, but escalation to general models is hard.

**D0 question.** "Is there at least one restricted-model MCSP lower bound from the literature (CHMY 2021, Cheraghchi et al., Ilango et al., Hirahara et al. 2019+) whose **proof structure** can plausibly be Lean-formalized in months **and** whose **statement shape** matches the `SearchMCSPWeakLowerBound` interface in `pnp4/Pnp4/Frontier/`, **and** is the gap between that bound's parameters and the repo's actual magnification-bridge needs small enough to be bridgeable without a new lower-bound theorem?"

### Family E — formal barrier theorem for FP3b

**Core idea.** Do not search for another filter. Instead, formalize a **class-level Lean theorem** that captures the structural double-binds documented in fp3b6 D6 and fp3b7 D0.1-second-review, in the same discipline as NOGO-000007's `any_honest_sublinear_support_witness_has_hardwiring_twin` and NOGO-000009's V2_A_NormaliseMetaBarrier. The deliverable is a single kernel-checked barrier theorem stating something like: "For any provenance predicate Π satisfying [precisely-specified safety properties — non-largeness via sparse `T_n`, payload-independence via short public index, polynomial certificate cost], the accepted set admits small nonuniform DAGs."

**Why not support-cardinality-only.** It is a meta-theorem about predicates, not a predicate.

**Why not displayed-syntax-only.** Meta-theorem operates on semantic conditions of provenance predicates.

**Why not immediately natural-proof-shaped.** It is a barrier theorem stating that a class of predicates **cannot** be useful in the lower-bound sense — the opposite of a useful natural property.

**How it might produce `ResearchGapWitness.dagSeparation`.** **It does not.** This family explicitly does not advance toward `NP_not_subset_PpolyDAG`. Its value is (a) closing FP3b with kernel-checked discipline parity to NOGO-000006–000009, allowing legitimate NOGO-000010 filing, and (b) constraining future operators so they don't reopen filter-design routes that the barrier theorem rules out. **It is documentation, not progress.**

**Immediate NoGo / barrier risk.** The class-level statement may be hard to formalize precisely. "Sparse `T_n`", "payload-independent", "short public index" are all currently informal; turning them into Lean predicates without smuggling support-cardinality (NOGO-000007) or syntactic conditions (NOGO-000008) is non-trivial. Failure mode: the formal statement is so generic that it also covers honest provenance predicates we'd want to keep alive (overshooting), or so specific that it only kills the exact `AlmostNaturalProvenance_BC` definition (undershooting, giving no class-level closure).

**D0 question.** "Is there a Lean-formalizable precise class of provenance predicates that **provably contains** the V2-A, fp3b6 Family A, and `AlmostNaturalProvenance_BC` candidates **and** for which a class-level theorem `accepted_set_has_small_nonuniform_DAG` can be proven without circular reference to `PpolyDAG` membership? What would the smallest such class look like?"

### Family A-PC — proof-complexity / bounded-arithmetic fourth-barrier interface

**Core idea.** Per the Q1 first-move report (`interesting_but_blocked` verdict), extend the existing `pnp3/Barrier/` interface with a **proof-complexity / feasible-unprovability barrier** as a sibling to NaturalProofs / Relativization / Algebrization. The new barrier would assert that certain provenance-filter-validation statements cannot be proved in weak feasible theories (S^1_2, V^0, APC_1), with corresponding witness-extraction consequences (KPT, LEARN-uniform, Student-Teacher) that would contradict the arbitrary-payload family of NOGO-000006.

**Why not support-cardinality-only.** It is a meta-theoretic barrier on proof systems, not a filter.

**Why not displayed-syntax-only.** Same — it operates on proof-system strength, not formula syntax.

**Why not immediately natural-proof-shaped.** It is sibling to natural proofs, not subsumed by it. Q1's cited literature explicitly classifies proof-complexity barriers as **adjacent to** natural proofs (Pich-Santhanam 2019 et seq.).

**How it might produce `ResearchGapWitness.dagSeparation`.** **Indirectly.** It would screen out filter routes that have feasible-unprovability obstructions, freeing effort for routes that don't. It is a **negative screen**, not a positive route. As Q1 itself notes, "the proof-theoretic obstruction can only be useful as a negative screen on proposed filters, not as a way to rehabilitate an overbroad one."

**Immediate NoGo / barrier risk.** Formalizing actual bounded-arithmetic metatheorems (KPT witnessing, APC_1, S^1_2) inside Lean is a multi-year effort, as the Q1 report itself notes. A minimal "abstract extraction contract" interface is feasible in months but doesn't directly produce any new closure for fp3b6 or fp3b7 retrospectively; both already have their own (different) double-binds that don't obviously route through proof-complexity unprovability.

**D0 question.** "Does the existing fp3b6 log-window double-bind or fp3b7 cheap-certificate double-bind retrospectively fit into a proof-complexity / feasible-unprovability barrier interface, or are they orthogonal to that barrier? If they are orthogonal, what kind of filter route (if any) would the proof-complexity barrier rule out, and is that route relevant to the repo's current source-theorem search?"

### Families excluded with reasoning

* **C. Cross-length coherence revisited, semantic.** Already tried as V2-B and rejected via priority refresh (`hold_for_nonvacuity`, parity-specific). The semantic version remains a syntactic-trap risk per NOGO-000008/009 lesson chain. The fp3b7 audit explicitly warns that "semantic + constructive + broadly useful would reawaken natural proofs" (D0.1 second review §7). Excluded.
* **D. Algebraic / finite-field / SOS.** Genuinely different from filter design. **However**, classical polynomial-method lower bounds (Razborov–Smolensky for AC^0[p], constant-depth poly threshold) are inherently natural in the Razborov–Rudich sense — they exhibit a large, constructive, useful property. SOS lower bounds against polynomial-time algorithms operate in a different regime than `P/poly` adversaries and the bridge to `NP_not_subset_PpolyDAG` is non-obvious. The route is plausible but has higher background-required cost than B-MCSP and a more delicate natural-proofs interaction. Excluded for D0 priority, not in principle.

---

## 6. Best next seed pack

If a single new seed pack is dispatched, my recommendation is:

```text
seed_packs/fp3b8_mcsp_direct_source_D0/
```

with only the D0 slot from Family B-MCSP above:

**D0 question (verbatim):**

> Is there at least one restricted-model MCSP lower bound from the post-2018 meta-complexity literature whose proof structure can plausibly be Lean-formalized in months **and** whose statement shape matches the existing `SearchMCSPWeakLowerBound` interface in `pnp4/Pnp4/Frontier/` **and** whose parameter regime is close enough to the repo's actual magnification-bridge needs that the bridge can be discharged without a new lower-bound theorem? If yes, identify the specific paper and bound. If no, identify the gap and assess whether the gap is closeable by existing literature or requires open research.

**Allowed scope for fp3b8-D0:** markdown-only, like fp3b7-D0; ~200–600 LOC; single handle; bibliographic verification of all cited papers; explicit `[verified]` / `[unverified]` tags on every constant; cross-checked against NOGO-000006–000009 (none of which directly applies to non-filter source-theorem work, but the cross-check should confirm orthogonality, not assume it).

**Forbidden inside fp3b8-D0:** no Lean, no NoGoLog append, no `ProvenanceFilter_v1` promotion (no filter at all), no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / endpoint / P ≠ NP. The D0 is a feasibility check, not a source-theorem dispatch.

**Acceptance criteria.**

* `GREEN-light`: D0 report identifies a specific restricted-model MCSP lower bound, confirms its Lean-formalizability, confirms its statement shape matches `SearchMCSPWeakLowerBound`, and gives a credible (paper-level, not Lean-level) account of how to discharge the magnification gap. Operator then dispatches fp3b8 Round 1 in a separate decision.
* `RED-light`: D0 report concludes that no existing restricted-model MCSP bound is suitable (either Lean-formalizability is multi-year, or statement shape doesn't match, or the gap is too large). Operator then considers Family E or accepts that the repo target is currently beyond reach with available tools.
* `INCONCLUSIVE`: D0 report explicitly says the question requires deeper paper-level investigation than markdown-only can provide. Operator decides whether to escalate or treat as RED-light.

**Pessimistic prior:** my honest estimate is that fp3b8-D0 lands somewhere between RED-light and INCONCLUSIVE. The reasons fp3b6 / fp3b7 failed are not specific to filter design; they reflect that the repo target (`NP_not_subset_PpolyDAG` via existing magnification scaffolding) is genuinely hard and the published literature does not contain a near-discharge of `SearchMCSPWeakLowerBound`. A RED-light D0 would still be valuable: it would inform whether the right next move is Family E (barrier formalization to close out FP3b cleanly) or a step further out (alternative source theorems, new magnification frameworks, accept-and-document).

---

## 7. NoGoLog recommendation

```text
yes, but only after Lean formal class theorem
```

Reasoning:

* **NOGO-000006 through 000009 all have kernel-checked `formal_witness` fields** pointing to Lean theorems. Filing NOGO-000010 (fp3b6) and NOGO-000011 (fp3b7) as **markdown-only** entries would dilute this discipline. The existing fp3b6 STALLED and fp3b7 RED-LIGHT decisions are intentionally documented as markdown audits, not as NoGoLog entries.
* Filing them as kernel-checked NoGoLog entries requires a Lean-formalized class-level theorem (Family E above). The fp3b6 double-bind needs internalization of "AM-style fingerprint footprint exceeds `widthFn n`" as a Lean predicate, which is currently informal. The fp3b7 double-bind needs internalization of "short-index public payload class with payload-independent certificate has small nonuniform DAGs", which is currently informal.
* **Therefore: defer NoGoLog filing until either** (a) Family E is dispatched and produces a kernel-checked class-level barrier theorem, **or** (b) operator explicitly decides to widen NoGoLog discipline to permit markdown-only entries. I do **not** recommend (b) — it would weaken the strongest existing discipline in the repo.

**Lightweight alternative.** A future audit-only worker may register the structural double-binds as **design constraints** under `seed_packs/fp3b6_*/audits/` and `seed_packs/fp3b7_*/audits/` (e.g., `design_constraints_DC001_payload_window_hiding.md` per the fp3b6 reclassification document §5.4). These would be route-design lessons, not NoGoLog entries. This is a low-priority but cheap artifact.

---

## 8. Final recommendation

**Stop the FP3b provenance-filter route.**

The five closures (V2-A / V2-A.1 / V2-B+D, fp3b6 Family A, fp3b7 Family B) cover the design space densely enough that I don't see a sixth filter family escaping all five closure patterns. The two most recent failures (fp3b6, fp3b7) are **structural double-binds**, not removable parameter mismatches. fp3b6_budget_repair would be a sixth attempt at the same family A under different symbols and is not justified.

**Pivot direction (one step, not a programme).** Dispatch a single sharp markdown-only D0 slot:

```text
seed_packs/fp3b8_mcsp_direct_source_D0/
```

asking the **exact** D0 question stated in §6 verbatim:

> Is there at least one restricted-model MCSP lower bound from the post-2018 meta-complexity literature whose proof structure can plausibly be Lean-formalized in months **and** whose statement shape matches the existing `SearchMCSPWeakLowerBound` interface in `pnp4/Pnp4/Frontier/` **and** whose parameter regime is close enough to the repo's actual magnification-bridge needs that the bridge can be discharged without a new lower-bound theorem?

This is a one-step pivot away from filter design, into the source-theorem side that the repo's scaffolding (`SearchMCSPWeakLowerBound`, `PvsNPBridgeRequirements`, etc.) was built to consume. It is **markdown-only**, **single-handle**, **single-slot**, and gated on operator countersign before any further dispatch.

**If fp3b8-D0 RED-lights** (my pessimistic prior), the next operator decision should be between:

* Family E (formal barrier theorem to close FP3b with discipline parity to NOGO-000006–000009; produces NOGO-000010 + NOGO-000011 honestly); or
* Acceptance that the repo target is currently beyond reach with existing literature and existing scaffolding, with corresponding governance reclassification (e.g., the entire "search-MCSP weak lower bound" interface marked `OPEN-stalled` pending future literature).

**If fp3b8-D0 GREEN-lights**, dispatch fp3b8 Round 1 as a focused source-theorem formalization track and continue normal operator review cadence.

**What is explicitly NOT recommended.**

* No `fp3b6_budget_repair`. Same reasoning as in fp3b6 STALLED reclassification §3.
* No re-opening of V2-* under new names.
* No fp3b9 / fp3b10 multi-family fan-out. The signal-to-noise ratio of "search for yet another filter family" is now poor.
* No NoGoLog markdown-only entries (per §7).

**Honest meta-note (for operator awareness).** The pattern of the last six months — three distinct failure modes across five filter design subspaces, with the last two being structural double-binds — suggests that "filter-shaped provenance" may be a **systematically inadequate abstraction** for the repo target. This is a research-level observation, not a tactical one. A formal articulation of why (Family E) would be a valuable scientific contribution even if it does not advance `NP_not_subset_PpolyDAG` directly.

---

## Output summary

```
Task: post-FP3b strategy refresh
Handle: claudeopus
Branch: main
Commit before: 482012e
Commit after: (this PR's commit on claude/build-proof-verification-s2pI5)
Changed files:
  seed_packs/first_move_search_2026/reports/post_fp3b6_fp3b7_strategy_refresh_claudeopus.md

Outcome: REPORT_LANDED

report path: seed_packs/first_move_search_2026/reports/post_fp3b6_fp3b7_strategy_refresh_claudeopus.md
executive verdict: stop_fp3b_provenance_route
best next family: B-MCSP (direct restricted-model meta-complexity, non-filter)
proposed seed pack: seed_packs/fp3b8_mcsp_direct_source_D0/  (D0 slot only, markdown-only)
why this avoids fp3b6/fp3b7 failures:
  - not a provenance filter, so support-cardinality (NOGO-000007), syntactic
    (NOGO-000008), and normalise-then-filter (NOGO-000009) closures do not apply
  - operates on the source-theorem side of the existing magnification bridge,
    not on filter design, so the fp3b6 log-window-vs-AM-footprint double-bind
    does not apply
  - restricted-model lower bounds are barrier-aware by model restriction, not
    by largeness restriction, so the fp3b7 cheap-certificate-vs-useful-target
    double-bind does not apply
NoGoLog recommendation: yes, but only after Lean formal class theorem
commands run:
  - git fetch / checkout main / pull --ff-only → 482012e
  - reading: fp3b6 audits (reclassification + D5tight+D3primeC+D6 review),
    fp3b6 reports (D5_tight, D6), fp3b7 audits (red_light_operator_decision),
    fp3b7 reports (D0, D0.1, D0.1_second_review), fp3b5 strategic audit,
    first-move-search Q1, NoGoLog NOGO-000006–000009, pnp3/Barrier/* headers
  - ./scripts/check.sh — NOT RUN (no Lean toolchain in operator-review env;
    CI green at upstream merges, this report writes only markdown)
  - lake build PnP3 Pnp4 — NOT RUN (same reason; markdown-only deliverable)

Scope violations: none
```
