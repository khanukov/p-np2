# Polynomial-time formalism D0 — four-way comparative review + synthesis (claudeopus)

**Slot:** Polynomial-time formalism scoping D0 — operator decision (comparative review of four parallel codex dispatches).
**Handle:** claudeopus (claude-opus-4-7).
**Branch reviewed against:** `main` @ `d367652`.

**Review subjects:**

| Version | PR | Commit | LOC | Result |
| --- | --- | --- | --- | --- |
| **V4** | #1293 | `03cce45` | 284 | **merged** at `d367652` |
| V1 | #1292 | `2dac4e4` | 383 | closed |
| V3 | #1294 | `fb972aa` | 209 | closed |
| V2 | #1295 | `c033280` | 200 | closed |

All four reports are markdown-only scoping decisions per the retrospective §8.2 specification (Path B prerequisite). All four reach **unanimous verdict**: `GREEN-light_formalism_investment` with 2-4 week cost estimate.

This is **operator-scoped review**. No Lean edits, no JSONL / spec / known_guards / trust-root edits, no `ProvenanceFilter_v1` promotion, no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claims, no R1-C implementation.

---

## 1. Verdict

```text
merged_V4 (PR #1293, 03cce45) as canonical D0 report
closed_V1 (PR #1292) — largest, most thorough cost decomposition
closed_V3 (PR #1294) — most concrete dependency listing  
closed_V2 (PR #1295) — most explicit post-formalism prerequisite list
```

**All four converge on:**

* Verdict: **`GREEN-light_formalism_investment`** (unanimous).
* Cost: **2-4 weeks** for narrow TM-backed adapter (multi-month for general compiler layer — not recommended).
* Bridge target: **`PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L`**.
* R1-C: **still gated even after formalism** — the polynomial-time formalism removes an engineering blocker, not the mathematical blocker (PpolyDAG-compatible self-reduction remains missing).

**V4 chosen as canonical** because it has the most candid operator-decision support — see §2.

---

## 2. Why V4 was chosen

### 2.1 Most candid framing

V4 §9 is the only one of the four to write explicitly:

> Even if the polynomial-time formalism lands, **R1-C does not become automatically plausible**. ... Honest R1-C impact: the formalism removes an engineering blocker, not the mathematical blocker.

V4 §10 is the only one to provide an explicit operator-appetite-dependent fallback:

> If operator appetite for 2-4 weeks of infrastructure work is low, the fallback is `do_one_more_scoping_pass` focused specifically on direct-TM construction feasibility for prefix parsers and tree-circuit verification.

This is the right framing for a scoping decision — operator-decision-supportive, not formalism-advocate.

### 2.2 Recognition of R1-B2a real obligations

V4 §8.5 is the only one to explicitly acknowledge:

> **Parser-side malformed rejection and length-convention facts are already stated as real quantified obligations.**

V1/V2/V3 treat all R1-B2a parser obligations as "still `Prop`-only" — which is materially inaccurate after the V4 R1-B2a landing (`47dd408`). V4 correctly recognizes that:

* `malformed_inputs_rejected` is a real `∀ {m} y, parsePrefixInput parser y = none → PrefixExtensionLanguage parser m y = false` theorem on the R1-B2a record.
* `length_convention_matches_M` is a real `∀ {m} y input, parsePrefixInput parser y = some input → m = M input.n` theorem.

The other three reports inadvertently misrepresent R1-B2a's current state.

### 2.3 Most concrete next-pack structure

V4 §5 + §7 + §10 together propose a **4-module plan** with clear boundaries:

1. Polynomial-bound and padding utilities (certificate-length domination, ambient-length conversion).
2. `PolyTimeVerifierSpec` interface + bridge theorem to `NP_TM`.
3. Toy proof-of-concept verifier (non-vacuity check).
4. Future `PrefixExtensionLanguage` instantiation (separately authorised).

This is more actionable than V1's cost breakdown alone or V2's prerequisite list alone.

---

## 3. Synthesis: best content from all four reports

Even though V1/V2/V3 are closed, their unique strengths are captured here.

### 3.1 From V1 (PR #1292, 383 LOC) — narrow vs general cost separation

V1 §7 is the **most rigorous cost breakdown** across two scenarios:

* **Narrow TM-backed adapter (recommended):** 2-3 small Lean modules, low-medium risk. Direct bridge theorem if the spec stores a TM and exactly the `NP_TM`-shaped proofs.
* **General compiler layer (NOT recommended for this seed):** likely 6+ modules, high risk, multi-month effort. A general compiler from high-level pnp4 functions to internal TM model is useful but much larger than the immediate goal.

V1 also flags the **anti-faking criterion**: the bridge theorem must reject staged `Prop` runtime placeholders as sufficient evidence. This is essential to avoid recreating the wrapper-around-contract pattern.

### 3.2 From V2 (PR #1295, 200 LOC) — six prerequisites checklist

V2 §8 enumerates exactly what remains missing for `PrefixExtensionLanguage_in_NP` after the formalism lands:

1. A concrete parser or verified parser artifact for the prefix serialization.
2. Parser soundness, malformed-input rejection, and length-convention proofs.
3. A concrete codec decoder with polynomial runtime in ambient length.
4. A polynomial witness-size proof compatible with pnp3 certificate padding.
5. A polynomial relation verifier for prefix agreement, decode, size check, truth-table lookup/evaluation, and relation checking.
6. A final correctness proof matching `PrefixExtensionLanguage_accepts_iff` but using the executable verifier as implementation.

**Important caveat:** V2 mis-states (2) as "still missing" — V4 R1-B2a already provides parser soundness, malformed-input rejection, and length-convention proofs as real ∀-quantified theorems. So the corrected V2 list is: items (1), (3), (4), (5), (6) — five remaining prerequisites, not six.

### 3.3 From V3 (PR #1294, 209 LOC) — concrete dependency map

V3 §4 provides the most concrete enumeration of existing pnp3 infrastructure modules to use:

* **`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`** — `TM` structure with `runTime`, `accepts`.
* **`pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/**`** — atomic programs, phased programs, copying, unary-at-offset routines, encodings.
* **`pnp3/Complexity/PsubsetPpolyInternal/StraightLine.lean`, `StraightLineBuilder.lean`, `StraightLineSemantics.lean`, `TreeToStraight.lean`, `Simulation.lean`** — circuit/simulation machinery.
* **`pnp3/Complexity/Interfaces.lean`** — `Language`, `NP`, `NP_TM`, `certificateLength n k = n^k + k`, `concatBitstring`.

V3's missing-pieces list:

* No general executable-function-to-TM compiler in pnp4.
* No pnp4 polynomial-time verifier class tied to `NP_TM`.
* No direct parser-runtime proof object.
* No complete certificate-padding convention for prefix witnesses.

These are the **specific items** the formalism pack needs to add.

### 3.4 Cross-report consensus

All four agree on:

* The pnp3 `NP_TM` definition is the right target; do not modify it.
* The pnp4-side bridge must contain a real TM (or compiler to one), not just `Prop` placeholders.
* The 2-4 week scope must avoid scope creep into a general compiler layer.
* R1-C is **not** unlocked by this formalism alone; the self-reduction blocker remains.

This consensus is robust evidence that the architectural diagnosis is correct.

---

## 4. The decision being scoped

This D0 report addresses Path B from the retrospective:

```text
Path B (polynomial-time formalism scoping):
  Operator-level markdown decision document asking whether to invest in
  a polynomial-time formalism for pnp4. Markdown-only D0. Either GREEN-light
  (recommend investing) or RED-light (recommend not investing).
```

**Outcome: GREEN-light, with caveats.** The investment is justified **IF** the operator wants to keep the contract_expansion track resumable in the future. The investment is **NOT** justified **IF** the operator's only goal is faster progress toward `ResearchGapWitness`, because R1-C remains gated by the separate mathematical blocker.

### 4.1 The decision the operator now faces

Given GREEN-light scoping:

**Option B.1 — Proceed with formalism investment.**
* Dispatch a narrow 2-4 week formalism pack: `seed_packs/polynomial_time_formalism_implementation_R1/` or similar.
* 3-5 Lean modules implementing `PolyTimeVerifierSpec` + bridge theorem + toy verifier.
* Outcome: reusable NP-bridge infrastructure. R1-C still gated.

**Option B.2 — Defer formalism investment.**
* Keep the GREEN-light verdict as documentation.
* Do not dispatch implementation pack.
* Contract_expansion remains STALLED.
* Operator can revisit later (months/years out) with full context.

**Option B.3 — Fallback "one-more-scoping-pass" (V4-suggested).**
* If 2-4 weeks feels too long, dispatch a smaller scoping pass on direct-TM construction feasibility specifically for prefix parsers and tree-circuit verification.
* Outcome: more granular cost estimate before committing to the larger pack.

### 4.2 What this D0 does NOT do

* It does **not** authorize implementation work — that requires a separate operator decision.
* It does **not** unblock R1-C — R1-C remains gated on the missing self-reduction.
* It does **not** claim the formalism leads to `ResearchGapWitness` — only that it removes an engineering blocker.

---

## 5. Recommended next action

```text
operator_decision_needed
```

The four reports unanimously recommend `invest_in_formalism` as the next-pack verdict. But this is **operator-cost-dependent**, not auto-actionable.

**My operator-side recommendation:**

If the operator is willing to commit **2-4 weeks of focused Lean engineering**: proceed with **Option B.1** (dispatch implementation pack).

If the operator wants to **preserve the option without immediate investment**: choose **Option B.2** (defer; keep this D0 as documentation).

If the operator wants **more granular cost data before committing**: choose **Option B.3** (one more scoping pass on direct-TM feasibility).

**My honest preference: Option B.2 (defer).** Reasoning:

* The retrospective's Path C primary recommendation (stop R1-cadence, document closure) is already executed.
* This D0 report extends the documentation with a concrete formalism design and cost estimate.
* Investing 2-4 weeks in formalism produces reusable infrastructure but does **not** materially move the needle on `ResearchGapWitness`, because R1-C remains gated.
* Future operator (months/years out) can pick up where we are with full context.

But **Option B.1 is defensible** if the operator values having `PrefixExtensionLanguage_in_NP` as a real theorem for its own sake (e.g., as a publishable formal verification result) independent of the P-vs-NP route.

**I do not recommend Option B.3** — V4 itself proposes B.3 as a fallback only "if operator appetite for 2-4 weeks is low", which is already the same as B.2 (defer).

---

## 6. What is NOT recommended

* **Do not** open R1-C even after the formalism lands. The self-reduction is still missing from literature.
* **Do not** open R1-B3 / R1-B4 / R1-Bn under the contract_expansion track — these were ruled out by the retrospective.
* **Do not** treat this D0 as completed Path B work — it is only **scoping**, not implementation. Implementation requires a separate operator dispatch.
* **Do not** dispatch the polynomial-time formalism implementation pack speculatively. It requires explicit operator commitment to the 2-4 week effort.
* **Do not** add `True` placeholders for runtime fields in any future pack. V1's anti-faking criterion applies.

---

## 7. Forward state of the contract_expansion track

After this D0 lands, the track status is:

```text
Status:       STALLED (per retrospective Path C closure)
Augmentation: Path B scoping GREEN-lighted; implementation deferred to operator decision
Resume conditions:
  * External literature progress on PpolyDAG-compatible self-reduction, OR
  * Explicit operator decision to invest 2-4 weeks in polynomial-time formalism
    (Option B.1), OR
  * A new family of contract_expansion attacks (not in the closed family) is
    identified.

R1-C status: GATED (unchanged; <30% clean-landing prior)
```

The kill-machine framework's posture is unchanged: continue to document accurately, do not pretend progress beyond what exists.

---

## 8. Output summary

```
Task: Polynomial-time formalism D0 four-way comparative review + synthesis
Handle: claudeopus
Branch: main
Versions reviewed:
  V1 = PR #1292, commit 2dac4e4, 383 LOC (closed)
  V2 = PR #1295, commit c033280, 200 LOC (closed)
  V3 = PR #1294, commit fb972aa, 209 LOC (closed)
  V4 = PR #1293, commit 03cce45, 284 LOC (MERGED as canonical at d367652)
Common verdict (all 4 unanimous): GREEN-light_formalism_investment
Common cost estimate: 2-4 weeks for narrow TM-backed adapter
Common bridge target: PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L
R1-C status: gated even after formalism lands (separate mathematical blocker)
Why V4 won:
  1. Most candid framing — explicit operator-decision support
  2. Only version to recognize R1-B2a's REAL ∀-quantified parser obligations
  3. Most concrete 4-module next-pack structure
  4. Explicit fallback option (do_one_more_scoping_pass)
V1/V2/V3 unique strengths preserved in synthesis:
  - V1: narrow vs general compiler cost separation; anti-faking criterion
  - V2: six-item post-formalism prerequisites checklist (corrected to 5 items)
  - V3: concrete dependency map (TuringEncoding, TuringToolkit, etc.)
Cross-report consensus: pnp3 NP_TM is the right target; bridge must contain real TM;
  scope must avoid general compiler layer; R1-C remains gated.
Recommended next action: operator_decision_needed
  Option B.1: dispatch formalism implementation pack (2-4 wks)
  Option B.2: defer; keep D0 as documentation (my preference)
  Option B.3: one-more-scoping-pass on direct-TM construction (V4-suggested fallback)
Actions taken:
  - V4 (PR #1293) merged at d3676520
  - V1/V2/V3 (PRs #1292/#1294/#1295) closed with explanatory comments
  - Synthesis review written
Commands run:
  - git fetch / sync to main → d367652
  - read all 4 reports (1076 LOC total)
  - mcp__github__merge_pull_request 1293
  - mcp__github__update_pull_request 1292, 1294, 1295 (state=closed)
  - lake build / scripts/check.sh → NOT RUN (markdown-only)
  - rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4 → no output (verified)
Scope violations: none
```
